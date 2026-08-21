import Cordis.DeepSeekCurlOutcome
import Cordis.DeepSeekHarness
import Cordis.DeepSeekSessionRunner

/-!
# Rich terminal outcomes into the conversation runner

`DeepSeekOutcomeSession` intentionally targets the small append-only `Runner`. The deployed
Harness-facing continuation uses `DeepSeekHarness.ConversationRunner`, which also carries the
model/tool-count invariant. This module bridges the two response representations without
pretending that a rich-stream certificate is a non-streaming API response: it appends the
finished rich assistant view, exposes its completed provider calls as ordinary `FunctionCall`
values for the existing dependent executor, and preserves provider failures as a separate result.

Tool execution, policy, retries, cancellation, persistence, and external process trust remain
the existing caller-controlled boundaries. The process fixtures exercise only this local typed
handoff.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekOutcomeConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlOutcome
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamFailure
open Cordis.DeepSeekTerminalOutcome

def projectedFunctionCalls (view : RichStream.AssistantMessageView) : List FunctionCall :=
  view.rawToolCalls.map (fun call => {
    id := call.providerId
    name := call.name
    arguments := call.rawArguments
  })

theorem projectedFunctionCalls_length (view : RichStream.AssistantMessageView) :
    (projectedFunctionCalls view).length = view.rawToolCalls.length := by
  simp [projectedFunctionCalls]

def appendFinished
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    ConversationRunner :=
  let assistantView := finished.finished.view
  let assignment := sequentialAssignment runner.nextCall assistantView
  let session := StreamSession.appendAssistant runner.session runner.turn runner.step
    assistantView assignment sourceEventSeqs sourcesNodup sourcesEarlier
  {
    session
    turn := runner.turn
    step := runner.step + 1
    nextCall := runner.nextCall + assistantView.rawToolCalls.length
    toolCallCount_eq_nextCall := by
      have messages_eq :
          session.messages = runner.session.messages ++ [.assistant assistantView.content
            (StreamSession.toSessionToolCalls assistantView assignment)] := by
        simp [session, StreamSession.appendAssistant, Session.Session.appendSurface,
          Session.Session.append, Session.Session.messages_eq_surface,
          StreamSession.toAssistantPayload]
      simp only [messages_eq]
      rw [toolCallCount_append]
      rw [runner.toolCallCount_eq_nextCall]
      simp [toolCallCount, messageToolCallCount,
        StreamSession.toSessionToolCalls_length]
  }

theorem appendFinished_session_messages
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant finished.finished.view.content
        (StreamSession.toSessionToolCalls finished.finished.view
          (sequentialAssignment runner.nextCall finished.finished.view))] := by
  change (StreamSession.appendAssistant runner.session runner.turn runner.step
      finished.finished.view (sequentialAssignment runner.nextCall finished.finished.view)
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  simp [StreamSession.appendAssistant, Session.Session.appendSurface,
    Session.Session.append, Session.Session.messages_eq_surface,
    StreamSession.toAssistantPayload]

theorem appendFinished_nextSeq
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  rfl

theorem appendFinished_nextCall
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall + finished.finished.view.rawToolCalls.length := by
  rfl

inductive DispatchError where
  | bridge (error : DeepSeekSessionBridge.BridgeError)
deriving DecidableEq, Repr

inductive DispatchResult (body : String) where
  | providerFailure
      (validated : ValidatedFailureStream body)
      (runner : ConversationRunner)
  | assistant
      (finished : FinishedResponse body)
      (runner : ConversationRunner)

def dispatchOutcome
    {body : String}
    (runner : ConversationRunner)
    (outcome : TerminalOutcome body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except DispatchError (DispatchResult body) :=
  match outcome with
  | .failure validated =>
      .ok (.providerFailure validated runner)
  | .text validated =>
      match finishResponse (.text validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.assistant finished
            (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier))
  | .tool validated =>
      match finishResponse (.tool validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.assistant finished
            (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier))
  | .mixed validated =>
      match finishResponse (.mixed validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.assistant finished
            (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier))
  | .multi validated =>
      match finishResponse (.multi validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          .ok (.assistant finished
            (appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier))

theorem dispatchOutcome_providerFailure
    {body : String}
    (runner : ConversationRunner)
    (validated : ValidatedFailureStream body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    dispatchOutcome runner (.failure validated) sourceEventSeqs sourcesNodup sourcesEarlier =
      .ok (.providerFailure validated runner) := by
  rfl

inductive ClientError where
  | transport (error : OutcomeClientError)
  | dispatch (error : DispatchError)
deriving DecidableEq, Repr

/-! ## Dependent tool execution after a rich terminal outcome -/

structure ExecutedRound
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  finished : FinishedResponse body
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  executions : List (ExecutedTool cfg)
  executions_eq :
    executeFunctionCalls cfg before
        (projectedFunctionCalls finished.finished.view) =
      .ok (finalModel, executions)
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq

inductive ExecutionError where
  | bridge (error : DeepSeekSessionBridge.BridgeError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

inductive ExecutionResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  | providerFailure
      (validated : ValidatedFailureStream body)
      (runner : ConversationRunner)
  | assistant (round : ExecutedRound cfg before body)

private theorem appendFinished_assistantSeqEarlier
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    runner.session.nextSeq <
      (appendFinished runner finished sourceEventSeqs sourcesNodup
        sourcesEarlier).session.nextSeq := by
  rw [appendFinished_nextSeq]
  exact Nat.lt_succ_self _

private theorem appendFinished_assistantSeq_eq
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    runner.session.nextSeq + 1 =
      (appendFinished runner finished sourceEventSeqs sourcesNodup
        sourcesEarlier).session.nextSeq := by
  rw [appendFinished_nextSeq]

private def executeFinished
    {Model Capability : Type}
    {body : String}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (finished : FinishedResponse body)
    (assistantRunner : ConversationRunner)
    (callBase assistantSeq : Nat)
    (assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq)
    (assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq) :
    Except ToolRoundError (ExecutedRound cfg before body) :=
  match executionEq : executeFunctionCalls cfg before
      (projectedFunctionCalls finished.finished.view) with
  | .error error => .error error
  | .ok (finalModel, executions) =>
      .ok {
        finished
        assistantRunner
        runner := ConversationRunner.appendToolResults assistantRunner callBase assistantSeq
          executions assistantSeqEarlier
        finalModel
        executions
        executions_eq := executionEq
        assistantSeq
        assistantSeq_eq := assistantSeq_eq
      }

private def executeFinishedForOutcome
    {Model Capability : Type}
    {body : String}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except ExecutionError (ExecutionResult cfg before body) :=
  let assistantSeq := runner.session.nextSeq
  let assistantRunner := appendFinished runner finished sourceEventSeqs sourcesNodup sourcesEarlier
  match executeFinished cfg before finished assistantRunner runner.nextCall assistantSeq
      (appendFinished_assistantSeqEarlier runner finished sourceEventSeqs sourcesNodup
        sourcesEarlier)
      (appendFinished_assistantSeq_eq runner finished sourceEventSeqs sourcesNodup
        sourcesEarlier) with
  | .error error => .error (.tool error)
  | .ok round => .ok (.assistant round)

def executeOutcomeWithTools
    {Model Capability : Type}
    {body : String}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (outcome : TerminalOutcome body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except ExecutionError (ExecutionResult cfg before body) :=
  match outcome with
  | .failure validated => .ok (.providerFailure validated runner)
  | .text validated =>
      match finishResponse (.text validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          executeFinishedForOutcome cfg before runner finished sourceEventSeqs
            sourcesNodup sourcesEarlier
  | .tool validated =>
      match finishResponse (.tool validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          executeFinishedForOutcome cfg before runner finished sourceEventSeqs
            sourcesNodup sourcesEarlier
  | .mixed validated =>
      match finishResponse (.mixed validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          executeFinishedForOutcome cfg before runner finished sourceEventSeqs
            sourcesNodup sourcesEarlier
  | .multi validated =>
      match finishResponse (.multi validated) with
      | .error error => .error (.bridge error)
      | .ok finished =>
          executeFinishedForOutcome cfg before runner finished sourceEventSeqs
            sourcesNodup sourcesEarlier

inductive ExecutionClientError where
  | transport (error : OutcomeClientError)
  | execution (error : ExecutionError)
deriving DecidableEq, Repr

def executeAndRunOutcome
    {Model Capability : Type}
    (config : DeepSeekCurlTransport.ProcessConfig)
    (request : HttpRequest)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ExecutionClientError
      (Sigma fun body : String => ExecutionResult cfg before body)) := do
  match ← executeOutcome config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, processed⟩ =>
      match executeOutcomeWithTools cfg before runner processed.outcome sourceEventSeqs
          sourcesNodup sourcesEarlier with
      | .error error => pure (.error (.execution error))
      | .ok result => pure (.ok ⟨body, result⟩)

def executeAndDispatchOutcome
    (config : DeepSeekCurlTransport.ProcessConfig)
    (request : HttpRequest)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ClientError (Sigma fun body : String => DispatchResult body)) := do
  match ← executeOutcome config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, processed⟩ =>
      match dispatchOutcome runner processed.outcome sourceEventSeqs
          sourcesNodup sourcesEarlier with
      | .error error => pure (.error (.dispatch error))
      | .ok result => pure (.ok ⟨body, result⟩)

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    (runner : ConversationRunner) :
    ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

/-! The rich tool fixture uses `lookup`; this parallel body targets the certified counter tool. -/

def counterToolStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-tool"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "counter-call-0"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "counter_read"),
          ("arguments", .str "null")
        ])
      ]])
    ]),
    ("finish_reason", .null)
  ]])
]

def counterToolFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-tool"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "counter-call-0"),
        ("function", .mkObj [])
      ]])
    ]),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 4)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 3)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 7))
  ])
]

def counterToolStreamBody : String :=
  "data: " ++ Lean.Json.compress counterToolStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress counterToolFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def fixtureFailureDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekStreamFailure.exampleContentFilterBody)
    DeepSeekCurlTransport.fixtureRequest.request (ConversationRunner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureTextDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichStream.exampleTextStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (ConversationRunner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureToolDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichToolStream.exampleToolStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (ConversationRunner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureMixedDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichMixedStream.mixedStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (ConversationRunner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureMultiDispatch : IO (Except ClientError
    (Sigma fun body : String => DispatchResult body)) :=
  executeAndDispatchOutcome
    (fixtureProcess DeepSeekRichMultiStream.multiBody)
    DeepSeekCurlTransport.fixtureRequest.request (ConversationRunner.empty 1) []
    emptySourcesNodup (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureFailureExecution : IO (Except ExecutionClientError
    (Sigma fun body : String =>
      ExecutionResult Cordis.Harness.counterConfig 0 body)) :=
  executeAndRunOutcome
    (fixtureProcess DeepSeekStreamFailure.exampleContentFilterBody)
    DeepSeekCurlTransport.fixtureRequest.request Cordis.Harness.counterConfig 0
    (ConversationRunner.empty 1) [] emptySourcesNodup
    (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureTextExecution : IO (Except ExecutionClientError
    (Sigma fun body : String =>
      ExecutionResult Cordis.Harness.counterConfig 0 body)) :=
  executeAndRunOutcome
    (fixtureProcess DeepSeekRichStream.exampleTextStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request Cordis.Harness.counterConfig 0
    (ConversationRunner.empty 1) [] emptySourcesNodup
    (emptySourcesEarlier (ConversationRunner.empty 1))

def fixtureCounterToolExecution : IO (Except ExecutionClientError
    (Sigma fun body : String =>
      ExecutionResult Cordis.Harness.counterConfig 0 body)) :=
  executeAndRunOutcome
    (fixtureProcess counterToolStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request Cordis.Harness.counterConfig 0
    (ConversationRunner.empty 1) [] emptySourcesNodup
    (emptySourcesEarlier (ConversationRunner.empty 1))

end Cordis.DeepSeekOutcomeConversation
