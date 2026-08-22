import Cordis.DeepSeekAssemblerToolRound
import Cordis.DeepSeekCurlProviderAssemblyIncremental

/-!
# Process-backed incremental provider assembly to a dependent tool round

This module consumes the process-line incremental certificate without reparsing the completed
body.  Its final source-shaped assembly is projected directly into the existing dependent
`FunctionCall` admission/execution path, then the assistant and certified tool-result messages are
appended to the proof-carrying session.  The process, prefix, assembly, execution, and session
certificates remain separate fields.

The fixture is deterministic and local.  Network reachability, credentials, executable trust,
blocked-read interruption, backpressure, cancellation, persistence, external effects, and
deployed Harness equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekCurlProviderAssemblyToolRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekCurlProviderAssemblyIncremental
open Cordis.DeepSeekCurlIncremental
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekSessionRunner

inductive ProcessToolRoundError where
  | provider (error : PrefixProviderError)
  | execution (error : ToolRoundError)
deriving DecidableEq, Repr

structure ProcessedToolRound
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  provider : Processed body
  execution : ExecutionCertificate cfg before provider.certificate.result
  execution_eq :
    executeAssembledTools cfg before provider.certificate.result = .ok execution

def executeWith
    {Model Capability : Type}
    (maxReads : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) :
    IO (Except ProcessToolRoundError
      (Sigma fun body : String => ProcessedToolRound cfg before body)) := do
  match ← DeepSeekCurlProviderAssemblyIncremental.execute maxReads config request with
  | .error error => pure (.error (.provider error))
  | .ok ⟨body, provider⟩ =>
      match executionEq : executeAssembledTools cfg before provider.certificate.result with
      | .error error => pure (.error (.execution error))
      | .ok execution => pure (.ok ⟨body, {
          provider
          execution
          execution_eq := executionEq
        }⟩)

theorem ProcessedToolRound.assembly_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : ProcessedToolRound cfg before body) :
    assemble round.provider.final.provider.state =
      .ok round.provider.certificate.result
    := by
  exact DeepSeekCurlProviderAssemblyIncremental.finishSnapshot_exact
    round.provider.certificate_eq

theorem ProcessedToolRound.execution_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : ProcessedToolRound cfg before body) :
    executeAssembledTools cfg before round.provider.certificate.result = .ok round.execution :=
  round.execution_eq

def appendRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ProcessedToolRound cfg before body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  let assistant := appendAssistant session turn step round.provider.certificate.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  appendToolResults assistant turn step session.nextSeq round.execution (by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append])

theorem appendRound_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (round : ProcessedToolRound cfg before body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendRound session turn step round sourceEventSeqs sourcesNodup sourcesEarlier).messages =
      session.messages ++
        [.assistant (toAssistantView round.provider.certificate.result).content
          (StreamSession.toSessionToolCalls
            (toAssistantView round.provider.certificate.result)
            (sequentialAssignment 0 (toAssistantView round.provider.certificate.result)))] ++
        executedToolMessages 0 round.execution.executions := by
  let assistant := appendAssistant session turn step round.provider.certificate.result
    sourceEventSeqs sourcesNodup sourcesEarlier
  have assistantMessages := appendAssistant_messages session turn step
    round.provider.certificate.result sourceEventSeqs sourcesNodup sourcesEarlier
  have assistantNext : session.nextSeq < assistant.nextSeq := by
    change session.nextSeq < assistant.nextSeq
    simp [assistant, appendAssistant, StreamSession.appendAssistant,
      StreamSession.toAssistantPayload, Session.Session.appendSurface,
      Session.Session.append]
  have toolMessages := appendToolResults_messages assistant turn step session.nextSeq
    round.execution assistantNext
  change (appendToolResults assistant turn step session.nextSeq round.execution assistantNext).messages = _
  rw [toolMessages, assistantMessages]

def counterProcess : ProcessConfig :=
  DeepSeekCurlProviderAssemblyIncremental.counterProcess

def counterRequest : HttpRequest :=
  DeepSeekCurlProviderAssemblyIncremental.counterRequest

def counterRun : IO (Except ProcessToolRoundError
    (Sigma fun body : String =>
      ProcessedToolRound Cordis.Harness.counterConfig 2 body)) :=
  executeWith 64 counterProcess counterRequest Cordis.Harness.counterConfig 2

def counterFinalSession : IO (Option (Session.Session Session.noExtensions)) := do
  match ← counterRun with
  | .error _ => pure none
  | .ok ⟨_, round⟩ =>
      pure (some (appendRound (Session.Session.empty Session.noExtensions) 1 0 round []
        (by simp) (by simp)))

def counterSummary : IO Bool := do
  match ← counterRun with
  | .error _ => pure false
  | .ok ⟨_, round⟩ =>
      match ← counterFinalSession with
      | none => pure false
      | some session =>
          pure (round.provider.accepted.length == 9 &&
            round.execution.after == 5 &&
            round.execution.calls.length == 1 &&
            round.execution.executions.length == 1 &&
            session.messages.length == 2 && session.nextSeq == 2)

end Cordis.DeepSeekCurlProviderAssemblyToolRound
