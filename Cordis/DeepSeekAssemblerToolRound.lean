import Cordis.DeepSeekProviderAssembler
import Cordis.DeepSeekHarness
import Cordis.Harness

/-!
# Assembled assistant to dependent tool round

This module closes the next typed seam after `DeepSeekProviderAssembler`: a successful
source-shaped assembly is projected to the existing assistant-message view, its provider tool
calls are converted to `FunctionCall` values, and those calls are admitted/policy-checked/executed
by the generic dependent Harness. The execution certificate keeps the exact call list and the
model-indexed `ExecutedTool` values; session append helpers then reuse the existing numeric-ID and
tool-result certificates.

The input remains post-decoder assembly. Provider call-ID authenticity, wire decoding, external
tool effects, and deployed Harness equivalence remain outside this bridge.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekAssemblerToolRound

open Cordis
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekHarness

def toRichBlock : Block → RichStream.ContentBlock
  | .text content => .text content
  | .reasoning content => .reasoning content
  | .toolCall id name arguments => .toolCall id name arguments

def toAssistantView (assembled : Assembled) : RichStream.AssistantMessageView :=
  RichStream.toAssistantMessageView (assembled.blocks.map toRichBlock)

def toFunctionCalls (assembled : Assembled) : List DeepSeekApi.FunctionCall :=
  (toAssistantView assembled).rawToolCalls.map (fun call => {
    id := call.providerId
    name := call.name
    arguments := call.rawArguments
  })

structure ExecutionCertificate
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (assembled : Assembled) where
  calls : List DeepSeekApi.FunctionCall
  calls_eq : calls = toFunctionCalls assembled
  after : Model
  executions : List (ExecutedTool cfg)
  execution_eq : executeFunctionCalls cfg before calls = .ok (after, executions)

/-- Execute exactly the calls visible in the assembled assistant view. -/
def executeAssembledTools
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (assembled : Assembled) :
    Except ToolRoundError (ExecutionCertificate cfg before assembled) :=
  let calls := toFunctionCalls assembled
  match executionEq : executeFunctionCalls cfg before calls with
  | .error error => .error error
  | .ok (after, executions) => .ok {
      calls
      calls_eq := rfl
      after
      executions
      execution_eq := executionEq
    }

def appendAssistant
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (assembled : Assembled)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    Session.Session Session.noExtensions :=
  let view := toAssistantView assembled
  let assignment := DeepSeekSessionRunner.sequentialAssignment 0 view
  StreamSession.appendAssistant session turn step view assignment sourceEventSeqs
    sourcesNodup sourcesEarlier

theorem appendAssistant_messages
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (assembled : Assembled)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < session.nextSeq) :
    (appendAssistant session turn step assembled sourceEventSeqs sourcesNodup
      sourcesEarlier).messages =
      session.messages ++ [.assistant (toAssistantView assembled).content
        (StreamSession.toSessionToolCalls (toAssistantView assembled)
          (DeepSeekSessionRunner.sequentialAssignment 0 (toAssistantView assembled)))] := by
  simp [appendAssistant, StreamSession.appendAssistant, StreamSession.toAssistantPayload,
    Session.Session.appendSurface, Session.Session.append, Session.Session.messages_eq_surface]

def appendToolResults
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (assistantSeq : Nat)
    {before : Model}
    {assembled : Assembled}
    (execution : ExecutionCertificate cfg before assembled)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.Session Session.noExtensions :=
  appendExecutedToolResults session turn step 0 assistantSeq execution.executions
    assistantSeqEarlier

theorem appendToolResults_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step assistantSeq : Nat)
    {before : Model}
    {assembled : Assembled}
    (execution : ExecutionCertificate cfg before assembled)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendToolResults session turn step assistantSeq execution assistantSeqEarlier).messages =
      session.messages ++ executedToolMessages 0 execution.executions := by
  exact appendExecutedToolResults_messages session turn step 0 assistantSeq
    execution.executions assistantSeqEarlier

/-! ## Concrete dependent counter witness -/

namespace Example

def counterAssembled : Assembled := {
  role := "assistant"
  blocks := [
    .text "I will increment.",
    .toolCall "counter-call-0" "counter_increment"
      (Cordis.Examples.Counter.rawIncrement { amount := 3, limit := 10 }).arguments.compress
  ]
  usage := none
  finish := .toolCalls
  replayState := none
}

def counterExecution :
    Except ToolRoundError
      (ExecutionCertificate Cordis.Harness.counterConfig 2 counterAssembled) :=
  executeAssembledTools Cordis.Harness.counterConfig 2 counterAssembled

def counterAfter : Option Nat :=
  match counterExecution with
  | .error _ => none
  | .ok execution => some execution.after

def counterSession : Session.Session Session.noExtensions :=
  appendAssistant (Session.Session.empty Session.noExtensions) 1 0 counterAssembled []
    (by simp) (by simp)

theorem counter_session_messages :
    counterSession.messages =
      [.assistant (toAssistantView counterAssembled).content
        (StreamSession.toSessionToolCalls (toAssistantView counterAssembled)
          (DeepSeekSessionRunner.sequentialAssignment 0 (toAssistantView counterAssembled)))] := by
  rw [Session.Session.messages_eq_surface]
  simp [counterSession, appendAssistant, StreamSession.appendAssistant,
    StreamSession.toAssistantPayload, Session.Session.appendSurface,
    Session.Session.append, Session.Session.empty]

def counterFinalSession : Option (Session.Session Session.noExtensions) :=
  match counterExecution with
  | .error _ => none
  | .ok execution =>
      some (appendToolResults counterSession 1 0 0 execution (by
        change 0 < counterSession.nextSeq
        simp [counterSession, appendAssistant, StreamSession.appendAssistant,
          Session.Session.appendSurface, Session.Session.append]))

def counterFinalSummary : Bool :=
  match counterFinalSession with
  | none => false
  | some session =>
      session.messages.length == 2 && session.nextSeq == 2

end Example

end Cordis.DeepSeekAssemblerToolRound
