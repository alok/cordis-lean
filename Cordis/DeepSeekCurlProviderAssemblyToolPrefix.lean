import Cordis.DeepSeekCurlPrefix
import Cordis.DeepSeekCurlProviderAssemblyIncremental
import Cordis.DeepSeekAssemblerToolRound

/-!
# Process-backed provider/tool prefixes

This module keeps an unfinished process prefix instead of collapsing fuel exhaustion or
cancellation into an ordinary error.  Accepted lines are projected into the rich multi-call and
provider assembler states; only the completed branch is allowed to carry dependent tool execution
and session append certificates.  The stopped branches retain their exact line policy and prefix
state, so a caller can decide how to resume or discard them without fabricating a response.

The process remains a synchronous, line-oriented fixture.  Byte framing, blocked-read interruption,
backpressure, reconnects, credentials, executable trust, persistence, external effects, and
deployed Harness equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlProviderAssemblyToolPrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlProviderAssemblyIncremental
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamIncremental

inductive PrefixToolRoundError where
  | client (error : PrefixClientError)
  | provider (error : PrefixProviderError)
  | assembly (error : AssemblyError)
  | execution (error : ToolRoundError)
deriving DecidableEq, Repr

structure PendingProviderPrefix (policy : LinePolicy) where
  observed : PrefixResponse policy
  provider : PrefixSnapshot
  provider_eq : buildSnapshot observed.state.body = .ok provider

structure CompletedToolPrefix
    {Model Capability : Type}
    (policy : LinePolicy)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) where
  observed : PrefixResponse policy
  provider : PrefixSnapshot
  provider_eq : buildSnapshot observed.state.body = .ok provider
  certificate : Certificate provider.provider.chunks
  certificate_eq : finishSnapshot provider = .ok certificate
  execution : ExecutionCertificate cfg before certificate.result
  execution_eq : executeAssembledTools cfg before certificate.result = .ok execution

inductive PrefixToolResult
    (policy : LinePolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) where
  | pending (pendingPrefix : PendingProviderPrefix policy)
  | completed (round : CompletedToolPrefix policy cfg before)

theorem PendingProviderPrefix.body_eq
    {policy : LinePolicy}
    (pendingPrefix : PendingProviderPrefix policy) :
    pendingPrefix.provider.body = pendingPrefix.observed.state.body :=
  buildSnapshot_body pendingPrefix.provider_eq

theorem CompletedToolPrefix.body_eq
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : CompletedToolPrefix policy cfg before) :
    round.provider.body = round.observed.state.body :=
  buildSnapshot_body round.provider_eq

theorem CompletedToolPrefix.assembly_exact
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : CompletedToolPrefix policy cfg before) :
    assemble round.provider.provider.state = .ok round.certificate.result := by
  exact finishSnapshot_exact round.certificate_eq

theorem CompletedToolPrefix.execution_exact
    {Model Capability : Type}
    {policy : LinePolicy}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : CompletedToolPrefix policy cfg before) :
    executeAssembledTools cfg before round.certificate.result = .ok round.execution :=
  round.execution_eq

def buildPending {policy : LinePolicy} (observed : PrefixResponse policy) :
    Except PrefixProviderError (PendingProviderPrefix policy) :=
  match providerEq : buildSnapshot observed.state.body with
  | .error error => .error error
  | .ok provider => .ok { observed, provider, provider_eq := providerEq }

def buildCompleted
    {Model Capability : Type}
    {policy : LinePolicy}
    (observed : PrefixResponse policy)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) :
    Except PrefixToolRoundError (CompletedToolPrefix policy cfg before) :=
  match providerEq : buildSnapshot observed.state.body with
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

def executeWith
    {Model Capability : Type}
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) :
    IO (Except PrefixToolRoundError (PrefixToolResult policy cfg before)) := do
  match ← executeSsePrefix policy maxReads config request with
  | .error error => pure (.error (.client error))
  | .ok observed =>
      match observed.stop with
      | .completed _ =>
          match buildCompleted observed cfg before with
          | .error error => pure (.error error)
          | .ok round => pure (.ok (.completed round))
      | .fuelExhausted | .cancelled _ _ _ =>
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
    (round : CompletedToolPrefix policy cfg before)
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
    (round : CompletedToolPrefix policy cfg before)
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
  DeepSeekCurlProviderAssemblyIncremental.counterProcess

def counterRequest : HttpRequest :=
  DeepSeekCurlProviderAssemblyIncremental.counterRequest

def counterPendingRun : IO (Except PrefixToolRoundError
    (PrefixToolResult (LinePolicy.atLine 4 "fuel:counter")
      Cordis.Harness.counterConfig 2)) :=
  executeWith (LinePolicy.atLine 4 "fuel:counter") 64 counterProcess counterRequest
    Cordis.Harness.counterConfig 2

def counterTerminalRun : IO (Except PrefixToolRoundError
    (PrefixToolResult (LinePolicy.never) Cordis.Harness.counterConfig 2)) :=
  executeWith LinePolicy.never 64 counterProcess counterRequest Cordis.Harness.counterConfig 2

def counterPendingSummary : IO Bool := do
  match ← counterPendingRun with
  | .error _ => pure false
  | .ok (.pending pendingPrefix) =>
      pure (pendingPrefix.observed.state.line == 4 &&
        pendingPrefix.observed.isCancelled && pendingPrefix.provider.raw.length == 3)
  | .ok (.completed _) => pure false

def counterTerminalSummary : IO Bool := do
  match ← counterTerminalRun with
  | .error _ => pure false
  | .ok (.pending _) => pure false
  | .ok (.completed round) =>
      let session := appendCompleted (Session.Session.empty Session.noExtensions) 1 0 round []
        (by simp) (by simp)
      pure (round.observed.state.line == 9 &&
        round.execution.after == 5 &&
        round.execution.calls.length == 1 &&
        round.execution.executions.length == 1 &&
        session.messages.length == 2 && session.nextSeq == 2)

end Cordis.DeepSeekCurlProviderAssemblyToolPrefix
