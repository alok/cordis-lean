import Std

/-!
# Indexed session protocol

The static API makes illegal session transitions unrepresentable. The runtime API mirrors the
same vocabulary and validates untrusted event streams before they reach typed code.
-/

namespace Cordis

/-- Stable identity assigned to one tool invocation within a session. -/
structure CallId where
  value : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Session phases indexed by their exact turn, step, and live tool-call identifiers. -/
inductive SessionState where
  | ready (nextTurn : Nat)
  | turn (turn nextStep : Nat)
  | step (turn step : Nat) (pending : List CallId)
  deriving DecidableEq, Repr

/-- Live call identifiers are unique whenever a step is open. -/
def SessionState.WellFormed : SessionState → Prop
  | .ready _ => True
  | .turn _ _ => True
  | .step _ _ pending => pending.Nodup

/--
A legal session event. Its indices state both the required predecessor and the unique successor.
-/
inductive Event : SessionState → SessionState → Type where
  | turnStart (turn : Nat) : Event (.ready turn) (.turn turn 0)
  | stepStart (turn step : Nat) : Event (.turn turn step) (.step turn step [])
  | toolCall {turn step : Nat} {pending : List CallId}
      (id : CallId) (fresh : id ∉ pending) :
      Event (.step turn step pending) (.step turn step (id :: pending))
  | toolResult {turn step : Nat} {pending : List CallId}
      (id : CallId) (wasPending : id ∈ pending) :
      Event (.step turn step pending) (.step turn step (pending.erase id))
  | stepEnd (turn step : Nat) : Event (.step turn step []) (.turn turn (step + 1))
  | turnEnd (turn nextStep : Nat) : Event (.turn turn nextStep) (.ready (turn + 1))

/-- A compositional sequence whose adjacent states match by construction. -/
inductive Trace : SessionState → SessionState → Type where
  | nil {state : SessionState} : Trace state state
  | cons {start middle finish : SessionState} :
      Event start middle → Trace middle finish → Trace start finish

namespace Trace

/-- Compose two traces at their shared boundary state. -/
def append {start middle finish : SessionState} :
    Trace start middle → Trace middle finish → Trace start finish
  | .nil, suffix => suffix
  | .cons event rest, suffix => .cons event (append rest suffix)

/-- Regard one legal event as a trace. -/
def single {start finish : SessionState}
    (event : Event start finish) : Trace start finish :=
  .cons event .nil

end Trace

/-- Runtime session state used at the untrusted replay boundary. -/
inductive RuntimeState where
  | ready (nextTurn : Nat)
  | turn (turn nextStep : Nat)
  | step (turn step : Nat) (pending : List CallId)
  deriving DecidableEq, Repr

/-- Runtime event vocabulary persisted by a harness event log. -/
inductive RuntimeEvent where
  | turnStart (turn : Nat)
  | stepStart (turn step : Nat)
  | toolCall (turn step : Nat) (id : CallId)
  | toolResult (turn step : Nat) (id : CallId)
  | stepEnd (turn step : Nat)
  | turnEnd (turn nextStep : Nat)
  deriving DecidableEq, Repr

/-- Structured reasons why an untrusted event does not extend the current session. -/
inductive ValidationError where
  | wrongPhase (state : RuntimeState) (event : RuntimeEvent)
  | turnMismatch (expected actual : Nat)
  | stepMismatch (expected actual : Nat)
  | duplicateCall (id : CallId)
  | orphanResult (id : CallId)
  | pendingCallsRemain (pending : List CallId)
  deriving DecidableEq, Repr

/-- Forget static indices while retaining all runtime state data. -/
def eraseState : SessionState → RuntimeState
  | .ready nextTurn => .ready nextTurn
  | .turn turn nextStep => .turn turn nextStep
  | .step turn step pending => .step turn step pending

namespace Event

/-- Forget the proofs carried by a legal event. -/
def erase {start finish : SessionState} : Event start finish → RuntimeEvent
  | .turnStart turn => .turnStart turn
  | .stepStart turn step => .stepStart turn step
  | .toolCall (turn := turn) (step := step) id _ => .toolCall turn step id
  | .toolResult (turn := turn) (step := step) id _ => .toolResult turn step id
  | .stepEnd turn step => .stepEnd turn step
  | .turnEnd turn nextStep => .turnEnd turn nextStep

end Event

namespace Trace

/-- Erase a typed trace to the event list persisted by a runtime harness. -/
def erase {start finish : SessionState} : Trace start finish → List RuntimeEvent
  | .nil => []
  | .cons event rest => event.erase :: rest.erase

end Trace

/-- Validate and apply one untrusted event. -/
def applyRaw : RuntimeState → RuntimeEvent → Except ValidationError RuntimeState
  | .ready expectedTurn, .turnStart actualTurn =>
      if expectedTurn = actualTurn then
        .ok (.turn expectedTurn 0)
      else
        .error (.turnMismatch expectedTurn actualTurn)
  | .turn turn nextStep, .stepStart actualTurn actualStep =>
      if turn ≠ actualTurn then
        .error (.turnMismatch turn actualTurn)
      else if nextStep ≠ actualStep then
        .error (.stepMismatch nextStep actualStep)
      else
        .ok (.step turn nextStep [])
  | .step turn step pending, .toolCall actualTurn actualStep id =>
      if turn ≠ actualTurn then
        .error (.turnMismatch turn actualTurn)
      else if step ≠ actualStep then
        .error (.stepMismatch step actualStep)
      else if id ∈ pending then
        .error (.duplicateCall id)
      else
        .ok (.step turn step (id :: pending))
  | .step turn step pending, .toolResult actualTurn actualStep id =>
      if turn ≠ actualTurn then
        .error (.turnMismatch turn actualTurn)
      else if step ≠ actualStep then
        .error (.stepMismatch step actualStep)
      else if id ∈ pending then
        .ok (.step turn step (pending.erase id))
      else
        .error (.orphanResult id)
  | .step turn step pending, .stepEnd actualTurn actualStep =>
      if turn ≠ actualTurn then
        .error (.turnMismatch turn actualTurn)
      else if step ≠ actualStep then
        .error (.stepMismatch step actualStep)
      else if pending.isEmpty then
        .ok (.turn turn (step + 1))
      else
        .error (.pendingCallsRemain pending)
  | .turn turn nextStep, .turnEnd actualTurn actualNextStep =>
      if turn ≠ actualTurn then
        .error (.turnMismatch turn actualTurn)
      else if nextStep ≠ actualNextStep then
        .error (.stepMismatch nextStep actualNextStep)
      else
        .ok (.ready (turn + 1))
  | state, event => .error (.wrongPhase state event)

/-- Validate an untrusted event log from left to right. -/
def replayRaw : RuntimeState → List RuntimeEvent → Except ValidationError RuntimeState
  | state, [] => .ok state
  | state, event :: rest => do
      let next ← applyRaw state event
      replayRaw next rest

/-- Every typed transition preserves uniqueness of live call identifiers. -/
theorem Event.preservesWellFormed {start finish : SessionState}
    (event : Event start finish) :
    start.WellFormed → finish.WellFormed := by
  intro wellFormed
  cases event with
  | turnStart => trivial
  | stepStart => simp [SessionState.WellFormed]
  | toolCall id fresh =>
      exact List.nodup_cons.mpr ⟨fresh, wellFormed⟩
  | toolResult id _ =>
      exact List.Nodup.erase id wellFormed
  | stepEnd => trivial
  | turnEnd => trivial

/-- A typed result event can only name a call that was pending in its predecessor. -/
theorem Event.noOrphanResult
    {turn step : Nat} {pending : List CallId} {finish : SessionState}
    (event : Event (.step turn step pending) finish)
    (resultId : CallId)
    (erasesToResult : event.erase = .toolResult turn step resultId) :
    resultId ∈ pending := by
  cases event with
  | toolCall callId fresh => simp [Event.erase] at erasesToResult
  | toolResult callId wasPending =>
      simp [Event.erase] at erasesToResult
      subst callId
      exact wasPending
  | stepEnd => simp [Event.erase] at erasesToResult

/-- Erasing and checking one typed event produces its statically known successor. -/
@[simp] theorem applyRaw_eraseEvent {start finish : SessionState}
    (event : Event start finish) :
    applyRaw (eraseState start) event.erase = .ok (eraseState finish) := by
  cases event <;> simp [applyRaw, eraseState, Event.erase, *]

/-- Trace composition erases to list concatenation. -/
theorem Trace.erase_append
    {start middle finish : SessionState}
    (first : Trace start middle) (second : Trace middle finish) :
    (first.append second).erase = first.erase ++ second.erase := by
  induction first with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp [Trace.append, Trace.erase, inductionHypothesis]

/-- Every erased typed trace is accepted and reaches its statically known terminal state. -/
@[simp] theorem replayRaw_eraseTrace {start finish : SessionState}
    (trace : Trace start finish) :
    replayRaw (eraseState start) trace.erase = .ok (eraseState finish) := by
  induction trace with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      rw [Trace.erase, replayRaw, applyRaw_eraseEvent]
      exact inductionHypothesis

/-- Well-formedness propagates over a complete typed trace. -/
theorem Trace.preservesWellFormed {start finish : SessionState}
    (trace : Trace start finish) :
    start.WellFormed → finish.WellFormed := by
  intro wellFormed
  induction trace with
  | nil => exact wellFormed
  | cons event rest inductionHypothesis =>
      exact inductionHypothesis (event.preservesWellFormed wellFormed)

end Cordis
