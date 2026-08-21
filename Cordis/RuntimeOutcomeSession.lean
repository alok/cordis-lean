import Cordis.RuntimeOutcomeRefinement
import Cordis.DeepSeekSessionRunner

/-!
# Current-Harness outcomes at the local session boundary

`RuntimeOutcomeRefinement` classifies the current JSON-AST stream subset as either a successful
rich trace or a normalized in-band `error`/`aborted` failure. This module supplies the next small
composition: a successful certificate may be finished and appended to the existing pure session
runner, while a failure certificate is returned with the runner unchanged.

The failure branch deliberately does not invent an assistant message, retry, cancellation event,
or provider policy. The input JSON list remains the source index for the successful certificate,
and the normalized failure certificate remains available to the caller. Transport, persistence,
session-event synthesis, and deployed TypeScript equivalence stay outside this boundary.
-/

set_option autoImplicit false

namespace Cordis.RuntimeOutcomeSession

open Cordis
open Cordis.DeepSeekSessionBridge
open Cordis.DeepSeekSessionRunner
open Cordis.RuntimeOutcomeRefinement

/-- A successful current-Harness JSON certificate finished at the rich/session boundary. -/
structure FinishedJson (input : List Lean.Json) where
  source : RuntimeRefinement.ValidatedJsonTrace input
  finished : FinishedAssistant source.validated

/-- Finish a successful JSON refinement without erasing its dependent source certificate. -/
def finishJson {input : List Lean.Json}
    (validated : RuntimeRefinement.ValidatedJsonTrace input) :
    Except DeepSeekSessionBridge.BridgeError (FinishedJson input) :=
  match DeepSeekSessionBridge.finishAssistant validated.validated with
  | .error error => .error error
  | .ok finished => .ok { source := validated, finished }

/-- Append a finished JSON trace using the existing sequential local call-ID assignment. -/
def appendJson
    (runner : Runner)
    {input : List Lean.Json}
    (finished : FinishedJson input)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Runner :=
  let assignment := sequentialAssignment runner.nextCall finished.finished.view
  let session := DeepSeekSessionBridge.appendFinishedAssistant
    runner.session runner.turn runner.step finished.finished assignment sourceEventSeqs
    sourcesNodup sourcesEarlier
  {
    session
    turn := runner.turn
    step := runner.step + 1
    nextCall := runner.nextCall + finished.finished.view.rawToolCalls.length
    nextSeq_eq_step := by
      change runner.session.nextSeq + 1 = runner.step + 1
      rw [runner.nextSeq_eq_step]
    toolCallCount_eq_nextCall := by
      have messages_eq := DeepSeekSessionBridge.appendFinishedAssistant_messages
        runner.session runner.turn runner.step finished.finished assignment sourceEventSeqs
        sourcesNodup sourcesEarlier
      simp only [session, messages_eq]
      rw [toolCallCount_append]
      rw [runner.toolCallCount_eq_nextCall]
      simp [toolCallCount, messageToolCallCount,
        StreamSession.toSessionToolCalls_length]
  }

theorem appendJson_messages
    (runner : Runner)
    {input : List Lean.Json}
    (finished : FinishedJson input)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendJson runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant finished.finished.view.content
        (StreamSession.toSessionToolCalls finished.finished.view
          (sequentialAssignment runner.nextCall finished.finished.view))] := by
  change (DeepSeekSessionBridge.appendFinishedAssistant runner.session runner.turn runner.step
      finished.finished (sequentialAssignment runner.nextCall finished.finished.view)
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  exact DeepSeekSessionBridge.appendFinishedAssistant_messages runner.session runner.turn
    runner.step finished.finished (sequentialAssignment runner.nextCall finished.finished.view)
    sourceEventSeqs sourcesNodup sourcesEarlier

theorem appendJson_nextSeq
    (runner : Runner)
    {input : List Lean.Json}
    (finished : FinishedJson input)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendJson runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  change runner.session.nextSeq + 1 = runner.session.nextSeq + 1
  rfl

theorem appendJson_nextCall
    (runner : Runner)
    {input : List Lean.Json}
    (finished : FinishedJson input)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendJson runner finished sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall + finished.finished.view.rawToolCalls.length := by
  rfl

/-- The session-facing result preserves normalized failures and appends only successes. -/
inductive DispatchResult (input : List Lean.Json) where
  | failure
      (validated : RuntimeFailureRefinement.ValidatedFailureTrace input)
      (runner : Runner)
  | appended
      (finished : FinishedJson input)
      (runner : Runner)

/-- Failure is a bridge error only when the successful trace is not terminal. -/
def dispatchOutcome
    (runner : Runner)
    {input : List Lean.Json}
    (outcome : RuntimeOutcomeRefinement.ValidatedOutcome input)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except DeepSeekSessionBridge.BridgeError (DispatchResult input) :=
  match outcome with
  | .failure validated => .ok (.failure validated runner)
  | .success validated =>
      match finishJson validated with
      | .error error => .error error
      | .ok finished =>
          .ok (.appended finished
            (appendJson runner finished sourceEventSeqs sourcesNodup sourcesEarlier))

theorem dispatchOutcome_failure
    (runner : Runner)
    {input : List Lean.Json}
    (validated : RuntimeFailureRefinement.ValidatedFailureTrace input)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    dispatchOutcome runner (.failure validated) sourceEventSeqs sourcesNodup sourcesEarlier =
      .ok (.failure validated runner) := by
  rfl

theorem dispatchOutcome_success
    (runner : Runner)
    {input : List Lean.Json}
    (validated : RuntimeRefinement.ValidatedJsonTrace input)
    (finished : FinishedJson input)
    (finish : finishJson validated = .ok finished)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    dispatchOutcome runner (.success validated) sourceEventSeqs sourcesNodup sourcesEarlier =
      .ok (.appended finished
        (appendJson runner finished sourceEventSeqs sourcesNodup sourcesEarlier)) := by
  simp [dispatchOutcome, finish]

/-! ## Validation plus dispatch -/

inductive DispatchError where
  | validation (error : RuntimeOutcomeRefinement.ValidationError)
  | bridge (error : DeepSeekSessionBridge.BridgeError)
deriving DecidableEq, Repr

def validateAndDispatch
    (runner : Runner)
    (input : List Lean.Json)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except DispatchError (DispatchResult input) :=
  match RuntimeOutcomeRefinement.validateOutcome input with
  | .error error => .error (.validation error)
  | .ok outcome =>
      match dispatchOutcome runner outcome sourceEventSeqs sourcesNodup sourcesEarlier with
      | .error error => .error (.bridge error)
      | .ok result => .ok result

theorem validateAndDispatch_failureExample
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    validateAndDispatch runner RuntimeFailureRefinement.exampleJson sourceEventSeqs
      sourcesNodup sourcesEarlier =
      .ok (.failure RuntimeFailureRefinement.exampleValidated runner) := by
  rfl

def exampleFinished : FinishedJson RuntimeRefinement.exampleJson := {
  source := RuntimeRefinement.exampleJsonValidated
  finished := {
    blocks := [.text "hello"]
    terminal := ⟨RuntimeRefinement.exampleUsage.toLocal, .stop, none, rfl⟩
  }
}

theorem validateAndDispatch_successExample
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    validateAndDispatch runner RuntimeRefinement.exampleJson sourceEventSeqs
      sourcesNodup sourcesEarlier =
      .ok (.appended exampleFinished
        (appendJson runner exampleFinished
          sourceEventSeqs sourcesNodup sourcesEarlier)) := by
  rfl

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    (runner : Runner) : ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

def fixtureFailureDispatch :
    Except DispatchError (DispatchResult RuntimeFailureRefinement.exampleJson) :=
  validateAndDispatch (Runner.empty 1) RuntimeFailureRefinement.exampleJson []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

def fixtureSuccessDispatch : Except DispatchError (DispatchResult RuntimeRefinement.exampleJson) :=
  validateAndDispatch (Runner.empty 1) RuntimeRefinement.exampleJson []
    emptySourcesNodup (emptySourcesEarlier (Runner.empty 1))

end Cordis.RuntimeOutcomeSession
