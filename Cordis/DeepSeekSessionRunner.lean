import Cordis.DeepSeekRichStream
import Cordis.DeepSeekRichToolStream
import Cordis.DeepSeekSessionBridge

/-!
# Proof-carrying DeepSeek assistant session runner

This module composes the accepted DeepSeek stream boundaries instead of treating them as isolated
parsers. A response is accepted only as a text or one-tool rich trace, terminal extraction is
explicit, and each append advances a typed session runner while preserving a tool-call-count
invariant. Numeric IDs are allocated locally from the runner's count; provider string IDs remain
payload data and are not authenticated or treated as globally stable identities.

The runner is intentionally pure and append-only. HTTP, cancellation, persistence, external tool
execution, and the full deployed Harness event/session union remain separate boundaries.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSessionRunner

open Cordis
open Cordis.RichStream

inductive AcceptedResponse (body : String) where
  | text (validated : DeepSeekRichStream.ValidatedTextStream body)
  | tool (validated : DeepSeekRichToolStream.ValidatedToolStream body)

structure FinishedResponse (body : String) where
  source : AcceptedResponse body
  raw : List RichStream.RawChunk
  validated : RichStream.ValidatedTrace RichStream.State.initial raw
  finished : DeepSeekSessionBridge.FinishedAssistant validated

inductive ResponseError where
  | text (error : DeepSeekRichStream.TextStreamError)
  | tool (error : DeepSeekRichToolStream.ToolStreamError)
  | terminal (error : DeepSeekSessionBridge.BridgeError)
deriving DecidableEq, Repr

def acceptText (body : String) :
    Except DeepSeekRichStream.TextStreamError (AcceptedResponse body) :=
  match DeepSeekRichStream.validateTextStream body with
  | .error error => .error error
  | .ok validated => .ok (.text validated)

def acceptTool (body : String) :
    Except DeepSeekRichToolStream.ToolStreamError (AcceptedResponse body) :=
  match DeepSeekRichToolStream.validateToolStream body with
  | .error error => .error error
  | .ok validated => .ok (.tool validated)

def finishResponse {body : String} (response : AcceptedResponse body) :
    Except DeepSeekSessionBridge.BridgeError (FinishedResponse body) :=
  match response with
  | .text validated =>
      match DeepSeekSessionBridge.finishAssistant validated.rich with
      | .error error => .error error
      | .ok finished => .ok {
          source := .text validated
          raw := validated.raw
          validated := validated.rich
          finished
        }
  | .tool validated =>
      match DeepSeekSessionBridge.finishAssistant validated.rich with
      | .error error => .error error
      | .ok finished => .ok {
          source := .tool validated
          raw := validated.raw
          validated := validated.rich
          finished
        }

def finishText (body : String) :
    Except ResponseError (FinishedResponse body) :=
  match acceptText body with
  | .error error => .error (.text error)
  | .ok response =>
      match finishResponse response with
      | .error error => .error (.terminal error)
      | .ok finished => .ok finished

def finishTool (body : String) :
    Except ResponseError (FinishedResponse body) :=
  match acceptTool body with
  | .error error => .error (.tool error)
  | .ok response =>
      match finishResponse response with
      | .error error => .error (.terminal error)
      | .ok finished => .ok finished

def messageToolCallCount : Session.Message → Nat
  | .assistant _ calls => calls.length
  | _ => 0

def toolCallCount (messages : List Session.Message) : Nat :=
  (messages.map messageToolCallCount).sum

@[simp] theorem toolCallCount_append
    (left right : List Session.Message) :
    toolCallCount (left ++ right) = toolCallCount left + toolCallCount right := by
  simp [toolCallCount, List.sum_append]

def sequentialAssignment
    (base : Nat) (view : RichStream.AssistantMessageView) :
    StreamSession.CallIdAssignment view where
  ids := (List.range view.rawToolCalls.length).map (fun offset => {
    value := base + offset
  })
  length_eq := by simp
  nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    exact List.Pairwise.map (R := fun left right : Nat => left ≠ right)
      (S := fun left right : CallId => left ≠ right)
      (fun offset => ({ value := base + offset } : CallId))
      (by
        intro left right different equal
        apply different
        exact Nat.add_left_cancel (congrArg CallId.value equal))
      (List.nodup_iff_pairwise_ne.mp (List.nodup_range))

structure Runner where
  session : Session.Session Session.noExtensions
  turn : Nat
  step : Nat
  nextCall : Nat
  nextSeq_eq_step : session.nextSeq = step
  toolCallCount_eq_nextCall : toolCallCount session.messages = nextCall

namespace Runner

def empty (turn : Nat := 1) : Runner where
  session := Session.Session.empty Session.noExtensions
  turn
  step := 0
  nextCall := 0
  nextSeq_eq_step := rfl
  toolCallCount_eq_nextCall := by rfl

def append
    (runner : Runner)
    {body : String}
    (finished : FinishedResponse body)
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

theorem append_session_messages
    (runner : Runner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (append runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant finished.finished.view.content
      (StreamSession.toSessionToolCalls finished.finished.view
          (sequentialAssignment runner.nextCall finished.finished.view))] := by
  change (DeepSeekSessionBridge.appendFinishedAssistant runner.session runner.turn runner.step
      finished.finished (sequentialAssignment runner.nextCall finished.finished.view)
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  exact DeepSeekSessionBridge.appendFinishedAssistant_messages runner.session runner.turn
    runner.step finished.finished (sequentialAssignment runner.nextCall finished.finished.view)
    sourceEventSeqs sourcesNodup sourcesEarlier

theorem append_nextSeq
    (runner : Runner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (append runner finished sourceEventSeqs sourcesNodup sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  change runner.session.nextSeq + 1 = runner.session.nextSeq + 1
  rfl

theorem append_nextCall
    (runner : Runner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (append runner finished sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall + finished.finished.view.rawToolCalls.length := by
  rfl

def appendText
    (runner : Runner)
    (body : String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except ResponseError Runner :=
  match finishText body with
  | .error error => .error error
  | .ok finished => .ok (append runner finished sourceEventSeqs sourcesNodup sourcesEarlier)

def appendTool
    (runner : Runner)
    (body : String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except ResponseError Runner :=
  match finishTool body with
  | .error error => .error error
  | .ok finished => .ok (append runner finished sourceEventSeqs sourcesNodup sourcesEarlier)

end Runner

end Cordis.DeepSeekSessionRunner
