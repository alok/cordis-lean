/-!
# Proof-carrying reversible effects

An `Applied State before` records the state produced by one effect together with a
state-dependent, one-sided inverse. The only required law is that applying that inverse to
the produced state recovers `before`. In particular, `undo` need not be a two-sided inverse
and need not recover `before` from an arbitrary state.

Sequential composition runs effects from left to right and composes their inverses in the
opposite order. `UndoStack` makes the same LIFO discipline explicit in an indexed data type.
-/

namespace Cordis

universe u

/-- The result of applying a reversible effect at `before`.

The inverse is allowed to close over `before`, so it may depend on the state at which the
effect was applied. Its contract is intentionally one-sided: it must recover `before` from
`after`, but no behavior is prescribed away from `after`.
-/
structure Applied (State : Type u) (before : State) where
  /-- The state immediately after the effect. -/
  after : State
  /-- A state-dependent inverse captured when the effect runs. -/
  undo : State → State
  /-- Running the captured inverse on the produced state recovers the input state. -/
  undo_after : undo after = before

/-- A reversible effect produces an `Applied` result indexed by its input state. -/
def Effect (State : Type u) := (before : State) → Applied State before

namespace Applied

variable {State : Type u} {before : State}

/-- Two applied effects are equal when their produced states and inverse functions agree. -/
@[ext]
theorem ext {left right : Applied State before}
    (after_eq : left.after = right.after)
    (undo_eq : left.undo = right.undo) : left = right := by
  cases left with
  | mk leftAfter leftUndo leftLaw =>
      cases right with
      | mk rightAfter rightUndo rightLaw =>
          cases after_eq
          cases undo_eq
          rfl

end Applied

namespace Effect

variable {State : Type u}

/-- The effect that leaves the state unchanged. -/
def identity : Effect State := fun before ↦
  { after := before
    undo := fun current ↦ current
    undo_after := rfl }

/-- Run `first` and then `second`, recording their inverses in LIFO order. -/
def seq (first second : Effect State) : Effect State := fun before ↦
  let firstApplied := first before
  let secondApplied := second firstApplied.after
  { after := secondApplied.after
    undo := firstApplied.undo ∘ secondApplied.undo
    undo_after := by
      exact Eq.trans (congrArg firstApplied.undo secondApplied.undo_after)
        firstApplied.undo_after }

/-- The state produced by a sequential effect is the state produced by its second effect. -/
@[simp]
theorem seq_after (first second : Effect State) (before : State) :
    (seq first second before).after = (second (first before).after).after := rfl

/-- Sequential recovery runs the second inverse before the first inverse. -/
@[simp]
theorem seq_undo (first second : Effect State) (before current : State) :
    (seq first second before).undo current =
      (first before).undo ((second (first before).after).undo current) := rfl

/-- Every sequentially composed effect recovers the state at which it was applied. -/
@[simp]
theorem seq_recovers (first second : Effect State) (before : State) :
    (seq first second before).undo (seq first second before).after = before :=
  (seq first second before).undo_after

/-- `identity` is a left identity for sequential composition. -/
@[simp]
theorem identity_seq (effect : Effect State) : seq identity effect = effect := by
  funext before
  apply Applied.ext
  · rfl
  · funext current
    rfl

/-- `identity` is a right identity for sequential composition. -/
@[simp]
theorem seq_identity (effect : Effect State) : seq effect identity = effect := by
  funext before
  apply Applied.ext
  · rfl
  · funext current
    rfl

/-- Sequential composition is associative extensionally. -/
theorem seq_assoc (first second third : Effect State) :
    seq (seq first second) third = seq first (seq second third) := by
  funext before
  apply Applied.ext
  · rfl
  · funext current
    rfl

/-- Replace the current state and capture it as the inverse's recovery target.

This small effect demonstrates why an inverse is state-dependent: every application of
`replace next` returns the same successor, but its inverse closes over a different predecessor.
-/
def replace (next : State) : Effect State := fun before ↦
  { after := next
    undo := fun _ ↦ before
    undo_after := rfl }

end Effect

/-- A compiled LIFO recovery function indexed by its initial and current states. -/
structure UndoAccumulator (State : Type u) (before after : State) where
  /-- Recover an earlier state from a current state. -/
  recover : State → State
  /-- The accumulator recovers its indexed start from its indexed end. -/
  recover_after : recover after = before

namespace UndoAccumulator

variable {State : Type u}

/-- The empty accumulator recovers a state by doing nothing. -/
def empty (state : State) : UndoAccumulator State state state where
  recover := fun current ↦ current
  recover_after := rfl

/-- Add one applied effect to an accumulator.

The new inverse runs first; the prior accumulator then recovers the earlier prefix.
-/
def push {before middle : State}
    (accumulator : UndoAccumulator State before middle)
    (step : Applied State middle) : UndoAccumulator State before step.after where
  recover := accumulator.recover ∘ step.undo
  recover_after := by
    exact Eq.trans (congrArg accumulator.recover step.undo_after)
      accumulator.recover_after

/-- `push` exposes the same LIFO order as effect composition. -/
@[simp]
theorem push_recover {before middle : State}
    (accumulator : UndoAccumulator State before middle)
    (step : Applied State middle) (current : State) :
    (push accumulator step).recover current = accumulator.recover (step.undo current) := rfl

/-- A pushed accumulator recovers its original prefix state. -/
@[simp]
theorem push_recovers {before middle : State}
    (accumulator : UndoAccumulator State before middle)
    (step : Applied State middle) :
    (push accumulator step).recover step.after = before :=
  (push accumulator step).recover_after

end UndoAccumulator

/-- An explicit LIFO stack of inverses, indexed by the states at both ends of the run. -/
inductive UndoStack (State : Type u) : State → State → Type u
  /-- No effects separate a state from itself. -/
  | nil (state : State) : UndoStack State state state
  /-- Append an applied effect to a previously accumulated prefix. -/
  | push {before middle : State}
      (prior : UndoStack State before middle)
      (step : Applied State middle) : UndoStack State before step.after

namespace UndoStack

variable {State : Type u}

/-- Apply the inverse stack to a current state, newest inverse first. -/
def recover {before after : State}
    (stack : UndoStack State before after) (current : State) : State :=
  match stack with
  | .nil _ => current
  | .push prior step => recover prior (step.undo current)

/-- A singleton stack contains one applied effect. -/
def singleton {before : State} (step : Applied State before) :
    UndoStack State before step.after :=
  .push (.nil before) step

/-- Run an effect at the stack's current endpoint and push its captured inverse. -/
def pushEffect {before after : State}
    (stack : UndoStack State before after) (effect : Effect State) :
    UndoStack State before (effect after).after :=
  .push stack (effect after)

/-- Recovery through an empty stack is the identity. -/
@[simp]
theorem recover_nil (state current : State) :
    recover (.nil state) current = current := rfl

/-- Recovery through a pushed stack runs the newest inverse first. -/
@[simp]
theorem recover_push {before middle : State}
    (prior : UndoStack State before middle)
    (step : Applied State middle) (current : State) :
    recover (.push prior step) current = recover prior (step.undo current) := rfl

/-- Every well-indexed stack recovers its initial state from its terminal state. -/
@[simp]
theorem recover_after {before after : State} (stack : UndoStack State before after) :
    recover stack after = before := by
  induction stack with
  | nil => rfl
  | push prior step ih =>
      exact Eq.trans (congrArg prior.recover step.undo_after) ih

/-- Compile an explicit stack into a proof-carrying recovery accumulator. -/
def toAccumulator {before after : State} (stack : UndoStack State before after) :
    UndoAccumulator State before after where
  recover := stack.recover
  recover_after := stack.recover_after

/-- Compiling a stack does not change its recovery function. -/
@[simp]
theorem toAccumulator_recover {before after : State}
    (stack : UndoStack State before after) (current : State) :
    stack.toAccumulator.recover current = stack.recover current := rfl

end UndoStack

/-!
## Observational recovery

The observational variant replaces equality with a `Setoid`. An inverse must respect the
setoid relation so that the recovery proof composes through an observationally equal
intermediate state.
-/

namespace Observational

/-- An applied effect that recovers its input up to observational equivalence. -/
structure Applied (State : Type u) [Setoid State] (before : State) where
  /-- The state immediately after the effect. -/
  after : State
  /-- The state-dependent observational inverse. -/
  undo : State → State
  /-- The inverse respects observational equivalence. -/
  undo_respects : ∀ {left right}, left ≈ right → undo left ≈ undo right
  /-- Applying the inverse to the produced state recovers the input observationally. -/
  undo_after : undo after ≈ before

namespace Applied

variable {State : Type u} [Setoid State] {before : State}

/-- Observationally applied effects are equal when their data fields agree. -/
@[ext]
theorem ext {left right : Applied State before}
    (after_eq : left.after = right.after)
    (undo_eq : left.undo = right.undo) : left = right := by
  cases left with
  | mk leftAfter leftUndo leftRespects leftLaw =>
      cases right with
      | mk rightAfter rightUndo rightRespects rightLaw =>
          cases after_eq
          cases undo_eq
          rfl

end Applied

/-- A reversible effect whose recovery law is stated modulo a `Setoid`. -/
def Effect (State : Type u) [Setoid State] :=
  (before : State) → Applied State before

namespace Effect

variable {State : Type u} [Setoid State]

/-- The observational identity effect. -/
def identity : Effect State := fun before ↦
  { after := before
    undo := fun current ↦ current
    undo_respects := fun related ↦ related
    undo_after := Setoid.refl before }

/-- Sequential observational composition, with inverses installed in LIFO order. -/
def seq (first second : Effect State) : Effect State := fun before ↦
  let firstApplied := first before
  let secondApplied := second firstApplied.after
  { after := secondApplied.after
    undo := firstApplied.undo ∘ secondApplied.undo
    undo_respects := fun related ↦
      firstApplied.undo_respects (secondApplied.undo_respects related)
    undo_after :=
      Setoid.trans
        (firstApplied.undo_respects secondApplied.undo_after)
        firstApplied.undo_after }

/-- Observational sequential recovery runs the newest inverse first. -/
@[simp]
theorem seq_undo (first second : Effect State) (before current : State) :
    (seq first second before).undo current =
      (first before).undo ((second (first before).after).undo current) := rfl

/-- Sequential composition recovers its input up to observational equivalence. -/
theorem seq_recovers (first second : Effect State) (before : State) :
    (seq first second before).undo (seq first second before).after ≈ before :=
  (seq first second before).undo_after

/-- Observational identity is a left identity extensionally. -/
@[simp]
theorem identity_seq (effect : Effect State) : seq identity effect = effect := by
  funext before
  apply Applied.ext
  · rfl
  · funext current
    rfl

/-- Observational identity is a right identity extensionally. -/
@[simp]
theorem seq_identity (effect : Effect State) : seq effect identity = effect := by
  funext before
  apply Applied.ext
  · rfl
  · funext current
    rfl

/-- Observational sequential composition is associative extensionally. -/
theorem seq_assoc (first second third : Effect State) :
    seq (seq first second) third = seq first (seq second third) := by
  funext before
  apply Applied.ext
  · rfl
  · funext current
    rfl

end Effect

end Observational

section Examples

variable {State : Type u}

/-- Two replacements recover their common predecessor in reverse application order. -/
example (before middle after : State) :
    (Effect.seq (Effect.replace middle) (Effect.replace after) before).undo after = before :=
  rfl

/-- An explicit inverse stack has the same recovery behavior as sequential composition. -/
example (before middle after : State) :
    let first := Effect.replace middle before
    let second := Effect.replace after first.after
    let stack := UndoStack.push (UndoStack.singleton first) second
    UndoStack.recover stack second.after = before := by
  simp

end Examples

end Cordis
