import Cordis.DeepSeekCurlBytePrefixTimeout
import Cordis.DeepSeekCurlProviderAssemblyIncremental
import Cordis.DeepSeekAssemblerToolRound

/-!
# Byte-framed provider/tool prefixes

This module composes the process byte-prefix reader, including its typed timeout branch, with
provider assembly and dependent tool execution.  A completed byte stream carries the same
provider, assembly, and execution certificates as the line-oriented adapter.  Fuel exhaustion,
cancellation, and timeout instead retain a provider prefix snapshot; none is reclassified as a
completed provider response.

The result is still bounded local-process evidence.  It does not claim provider obedience,
credential or executable authenticity, backpressure, reconnects, arbitrary process cleanup,
persistence, or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlBytePrefixProviderAssemblyTool

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlBytePrefixTimeout
open Cordis.DeepSeekCurlProviderAssemblyIncremental
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamIncremental

inductive BytePrefixToolRoundError where
  | client (error : BytePrefixClientError)
  | provider (error : PrefixProviderError)
  | assembly (error : AssemblyError)
  | execution (error : ToolRoundError)
deriving DecidableEq

structure PendingByteProviderPrefix (policy : LinePolicy) where
  observed : TimedBytePrefixResponse policy
  provider : PrefixSnapshot
  provider_eq : buildSnapshot observed.state.typed.body = .ok provider

structure CompletedByteToolPrefix
    {Model Capability : Type}
    (policy : LinePolicy)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) where
  observed : TimedBytePrefixResponse policy
  provider : PrefixSnapshot
  provider_eq : buildSnapshot observed.state.typed.body = .ok provider
  certificate : Certificate provider.provider.chunks
  certificate_eq : finishSnapshot provider = .ok certificate
  execution : ExecutionCertificate cfg before certificate.result
  execution_eq : executeAssembledTools cfg before certificate.result = .ok execution

inductive BytePrefixToolResult
    (policy : LinePolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) where
  | pending (pendingPrefix : PendingByteProviderPrefix policy)
  | completed (round : CompletedByteToolPrefix policy cfg before)

theorem PendingByteProviderPrefix.body_eq
    {policy : LinePolicy}
    (pendingPrefix : PendingByteProviderPrefix policy) :
    pendingPrefix.provider.body = pendingPrefix.observed.state.typed.body :=
  buildSnapshot_body pendingPrefix.provider_eq

theorem CompletedByteToolPrefix.body_eq
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : CompletedByteToolPrefix policy cfg before) :
    round.provider.body = round.observed.state.typed.body :=
  buildSnapshot_body round.provider_eq

theorem CompletedByteToolPrefix.assembly_exact
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : CompletedByteToolPrefix policy cfg before) :
    assemble round.provider.provider.state = .ok round.certificate.result := by
  exact finishSnapshot_exact round.certificate_eq

theorem CompletedByteToolPrefix.execution_exact
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : CompletedByteToolPrefix policy cfg before) :
    executeAssembledTools cfg before round.certificate.result = .ok round.execution :=
  round.execution_eq

def buildPending {policy : LinePolicy} (observed : TimedBytePrefixResponse policy) :
    Except PrefixProviderError (PendingByteProviderPrefix policy) :=
  match providerEq : buildSnapshot observed.state.typed.body with
  | .error error => .error error
  | .ok provider => .ok { observed, provider, provider_eq := providerEq }

def buildCompleted
    {Model Capability : Type}
    {policy : LinePolicy}
    (observed : TimedBytePrefixResponse policy)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) :
    Except BytePrefixToolRoundError (CompletedByteToolPrefix policy cfg before) :=
  match providerEq : buildSnapshot observed.state.typed.body with
  | .error error => .error (.provider error)
  | .ok provider =>
      match finished : finishSnapshot provider with
      | .error error => .error (.assembly error)
      | .ok certificate =>
          match executionEq : executeAssembledTools cfg before certificate.result with
          | .error error => .error (.execution error)
          | .ok execution => .ok {
              observed
              provider
              provider_eq := providerEq
              certificate
              certificate_eq := finished
              execution
              execution_eq := executionEq
            }

def executeWithTimeout
    {Model Capability : Type}
    (policy : LinePolicy)
    (maxReads chunkSize : Nat)
    (timeoutMs : UInt32)
    (config : ProcessConfig)
    (request : HttpRequest)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) :
    IO (Except BytePrefixToolRoundError
      (BytePrefixToolResult policy cfg before)) := do
  match ← executeSseBytePrefixWithTimeout policy maxReads chunkSize timeoutMs config request with
  | .error error => pure (.error (.client error))
  | .ok observed =>
      match observed.stop with
      | .completed _ =>
          match buildCompleted observed cfg before with
          | .error error => pure (.error error)
          | .ok round => pure (.ok (.completed round))
      | .fuelExhausted | .cancelled _ _ _ | .timedOut _ _ =>
          match buildPending observed with
          | .error error => pure (.error (.provider error))
          | .ok pendingPrefix => pure (.ok (.pending pendingPrefix))

def appendCompleted
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : CompletedByteToolPrefix policy cfg before)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  let assistant := appendAssistant session turn step round.certificate.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  appendToolResults assistant turn step session.nextSeq round.execution (by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append])

theorem appendCompleted_messages
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : CompletedByteToolPrefix policy cfg before)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendCompleted session turn step round sourceEventSeqs sourcesNodup sourcesEarlier).messages =
      session.messages ++
        [.assistant (toAssistantView round.certificate.result).content
          (StreamSession.toSessionToolCalls
            (toAssistantView round.certificate.result)
            (sequentialAssignment 0 (toAssistantView round.certificate.result)))] ++
        executedToolMessages 0 round.execution.executions := by
  let assistant := appendAssistant session turn step round.certificate.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  have assistantMessages := appendAssistant_messages session turn step
    round.certificate.result sourceEventSeqs sourcesNodup sourcesEarlier
  have assistantNext : session.nextSeq < assistant.nextSeq := by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append]
  have toolMessages := appendToolResults_messages assistant turn step session.nextSeq
    round.execution assistantNext
  change
    (appendToolResults assistant turn step session.nextSeq
      round.execution assistantNext).messages = _
  rw [toolMessages, assistantMessages]

def counterProcess : ProcessConfig :=
  Cordis.DeepSeekCurlBytePrefix.fixtureProcess DeepSeekProviderStreamAssembly.counterBody

def counterRequest : HttpRequest :=
  Cordis.DeepSeekCurlTransport.fixtureRequest.request

def counterTerminalRun : IO (Except BytePrefixToolRoundError
    (BytePrefixToolResult (LinePolicy.never) Cordis.Harness.counterConfig 2)) :=
  executeWithTimeout (LinePolicy.never) 4096 1 500 counterProcess counterRequest
    Cordis.Harness.counterConfig 2

def timeoutProcess : ProcessConfig := blockedBytePrefixProcess

def timeoutRun : IO (Except BytePrefixToolRoundError
    (BytePrefixToolResult (LinePolicy.never) Cordis.Harness.counterConfig 2)) :=
  executeWithTimeout (LinePolicy.never) 32 4096 100 timeoutProcess counterRequest
    Cordis.Harness.counterConfig 2

def counterTerminalSummary : IO Bool := do
  match ← counterTerminalRun with
  | .error _ => pure false
  | .ok (.pending _) => pure false
  | .ok (.completed round) =>
      let session := appendCompleted (Session.Session.empty Session.noExtensions) 1 0 round
        [] (by simp) (by simp)
      pure (round.observed.state.typed.line == 8 &&
        round.observed.state.typed.body = DeepSeekProviderStreamAssembly.counterBody &&
        round.execution.after == 5 &&
        round.execution.calls.length == 1 &&
        round.execution.executions.length == 1 &&
        session.messages.length == 2 && session.nextSeq == 2)

def timeoutSummary : IO Bool := do
  match ← timeoutRun with
  | .error _ => pure false
  | .ok (.completed _) => pure false
  | .ok (.pending pending) =>
      pure (pending.observed.isTimedOut && pending.observed.state.typed.line == 0 &&
        pending.provider.raw.isEmpty && pending.provider.provider.chunks.isEmpty)

end Cordis.DeepSeekCurlBytePrefixProviderAssemblyTool
