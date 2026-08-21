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

end Cordis.DeepSeekOutcomeConversation
