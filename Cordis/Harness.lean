import Cordis.Examples.CounterWire
import Cordis.Protocol

/-!
# Deterministic proof-carrying harness

The reference runner is deliberately pure and credential-free. It validates
raw counter calls, executes only admitted dependent calls, and emits the same
turn/step/call/result bracket used by DeepSeek Harness. Every `RunnerState`
stores a proof that replaying its emitted log from the initial state yields its
current protocol state.
-/

namespace Cordis.Harness

open Cordis
open Cordis.Examples.Counter

/-- The externally visible disposition of one settled call. -/
inductive CallOutcome where
  | succeeded
  | rejected (error : AdmissionError)
  | providerFailed (message : String)
deriving BEq, DecidableEq, Repr

/-- Audit data for a settled call, without retaining its raw JSON value. -/
structure CallRecord where
  id : CallId
  name : String
  before : Nat
  after : Nat
  outcome : CallOutcome
deriving BEq, DecidableEq, Repr

/-- Internal failures of the deterministic runner itself. -/
inductive RunnerError where
  | protocol (error : ValidationError)
  | notInStep (state : RuntimeState)
deriving DecidableEq, Repr

/-- Replaying an appended suffix is the same as replaying in two stages. -/
theorem replayRaw_append
    (start : RuntimeState)
    (first second : List RuntimeEvent) :
    replayRaw start (first ++ second) =
      match replayRaw start first with
      | .error error => .error error
      | .ok middle => replayRaw middle second := by
  induction first generalizing start with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, replayRaw]
      cases applied : applyRaw start event with
      | error error => rfl
      | ok middle =>
          change
            replayRaw middle (rest ++ second) =
              match replayRaw middle rest with
              | .error error => .error error
              | .ok state => replayRaw state second
          exact inductionHypothesis middle

/--
Pure runtime state. `replayProof` rules out divergence between the in-memory
protocol state and the append-only event log.
-/
structure RunnerState where
  model : Nat
  protocol : RuntimeState
  nextCall : Nat
  log : List RuntimeEvent
  records : List CallRecord
  replayProof : replayRaw (.ready 0) log = .ok protocol

namespace RunnerState

def initial (model : Nat) : RunnerState where
  model := model
  protocol := .ready 0
  nextCall := 0
  log := []
  records := []
  replayProof := rfl

/-- Append one checked protocol event while extending the replay certificate. -/
def emit (state : RunnerState) (event : RuntimeEvent) : Except RunnerError RunnerState :=
  match applied : applyRaw state.protocol event with
  | .error error => .error (.protocol error)
  | .ok next =>
      .ok {
        state with
        protocol := next
        log := state.log ++ [event]
        replayProof := by
          rw [replayRaw_append, state.replayProof]
          change replayRaw state.protocol [event] = .ok next
          simp only [replayRaw, applied]
          rfl
      }

/-- Open the first turn and first model step. -/
def beginSession (state : RunnerState) : Except RunnerError RunnerState := do
  let inTurn ← state.emit (.turnStart 0)
  inTurn.emit (.stepStart 0 0)

private def settle
    (state : RunnerState)
    (turn step : Nat)
    (id : CallId)
    (record : CallRecord) : Except RunnerError RunnerState := do
  let recorded := { state with records := state.records ++ [record] }
  recorded.emit (.toolResult turn step id)

/--
Dispatch one raw call. Rejections and provider failures still emit a matching
result, so no protocol obligation leaks from a failed tool boundary.
-/
def dispatch (state : RunnerState) (raw : RawCall) : Except RunnerError RunnerState :=
  match state.protocol with
  | .step turn step _ => do
      let id : CallId := { value := state.nextCall }
      let opened ← state.emit (.toolCall turn step id)
      let opened := { opened with nextCall := state.nextCall + 1 }
      match validateRaw state.model raw with
      | .error error =>
          settle opened turn step id {
            id := id
            name := raw.name
            before := state.model
            after := state.model
            outcome := .rejected error
          }
      | .ok call =>
          match view.execute call with
          | .error message =>
              settle opened turn step id {
                id := id
                name := raw.name
                before := state.model
                after := state.model
                outcome := .providerFailed message
              }
          | .ok reply =>
              let after := reply.value.after
              settle { opened with model := after } turn step id {
                id := id
                name := raw.name
                before := state.model
                after := after
                outcome := .succeeded
              }
  | state => .error (.notInStep state)

/-- Dispatch calls in model order. -/
def dispatchAll : RunnerState -> List RawCall -> Except RunnerError RunnerState
  | state, [] => .ok state
  | state, call :: rest => do
      let next ← state.dispatch call
      dispatchAll next rest

/-- Close the current step and turn after all calls have settled. -/
def finishSession (state : RunnerState) : Except RunnerError RunnerState :=
  match state.protocol with
  | .step turn step _ => do
      let inTurn ← state.emit (.stepEnd turn step)
      inTurn.emit (.turnEnd turn (step + 1))
  | protocol => .error (.notInStep protocol)

/-- Run one deterministic turn from an initial counter state. -/
def runScript (initialModel : Nat) (calls : List RawCall) : Except RunnerError RunnerState := do
  let started ← (initial initialModel).beginSession
  let settled ← started.dispatchAll calls
  settled.finishSession

end RunnerState

/-- A statically typed two-call session used to exercise the intrinsic protocol API. -/
def certifiedTwoCallTrace : Trace (.ready 0) (.ready 1) :=
  .cons (.turnStart 0) <|
  .cons (.stepStart 0 0) <|
  .cons (.toolCall ⟨0⟩ (by simp)) <|
  .cons (.toolResult ⟨0⟩ (by simp)) <|
  .cons (.toolCall ⟨1⟩ (by simp)) <|
  .cons (.toolResult ⟨1⟩ (by simp)) <|
  .cons (.stepEnd 0 0) <|
  .cons (.turnEnd 0 1) .nil

/-- Erasing the static example yields a runtime log accepted to its exact endpoint. -/
theorem certifiedTwoCallTrace_replays :
    replayRaw (.ready 0) certifiedTwoCallTrace.erase = .ok (.ready 1) :=
  replayRaw_eraseTrace certifiedTwoCallTrace

def demoCalls : List RawCall := [
  rawRead,
  rawIncrement { amount := 3, limit := 10 },
  rawRead,
  rawUnknown
]

def demo : Except RunnerError RunnerState :=
  RunnerState.runScript 2 demoCalls

end Cordis.Harness
