import Cordis.Effect

/-!
# Certified finite batch scheduling

This module gives a pure, two-call batch a proof-carrying choice of evaluation order. The
certificate is deliberately stronger than forward commutation: it states that both orders
produce the same successor and that their captured LIFO recovery functions agree on every
state. Result stability is certified separately, so an implementation may evaluate the calls
in either order while still committing their results in the batch's declared model order.

Nothing here starts tasks, performs `IO`, or claims that external effects are safe to run in
parallel. It is a model-level theorem for finite, pure effects.
-/

set_option autoImplicit false

namespace Cordis

universe u v w

namespace Effect

variable {State : Type u}

/-- Strong independence of two effects at one predecessor state.

`successor_eq` is ordinary forward commutation. `recovery_eq` is the additional law needed
for reversible effects: the complete LIFO inverse captured by either order has identical
behavior, not merely the same value at the common successor.
-/
structure IndependentAt
    (first second : Effect State) (before : State) : Prop where
  /-- Both evaluation orders reach the same modeled successor. -/
  successor_eq :
    (second (first before).after).after =
      (first (second before).after).after
  /-- The complete recovery functions captured by both orders agree pointwise. -/
  recovery_eq : ∀ current : State,
    (first before).undo ((second (first before).after).undo current) =
      (second before).undo ((first (second before).after).undo current)

/-- Strong independence at every possible predecessor state. -/
def Independent (first second : Effect State) : Prop :=
  ∀ before, IndependentAt first second before

namespace IndependentAt

variable {first second : Effect State} {before : State}

/-- Strong independence is symmetric. -/
theorem symm (certificate : IndependentAt first second before) :
    IndependentAt second first before where
  successor_eq := certificate.successor_eq.symm
  recovery_eq := fun current ↦ (certificate.recovery_eq current).symm

/-- Certified orders produce the same successor through `Effect.seq`. -/
theorem seq_after_eq (certificate : IndependentAt first second before) :
    (Effect.seq first second before).after =
      (Effect.seq second first before).after :=
  certificate.successor_eq

/-- Certified orders expose the same composed recovery function. -/
theorem seq_undo_eq
    (certificate : IndependentAt first second before) (current : State) :
    (Effect.seq first second before).undo current =
      (Effect.seq second first before).undo current :=
  certificate.recovery_eq current

/-- Strong independence identifies the complete proof-carrying applied effects. -/
theorem seq_applied_eq (certificate : IndependentAt first second before) :
    Effect.seq first second before = Effect.seq second first before := by
  apply Applied.ext certificate.seq_after_eq
  funext current
  exact certificate.seq_undo_eq current

end IndependentAt

end Effect

/-- A pure call consists of a reversible model effect and a result computed from its input.

The result function is intentionally explicit. If another effect is evaluated first, the call
sees a different input state; a batch certificate must therefore prove result stability rather
than assuming it from state commutation.
-/
structure PureCall (State : Type u) (Result : Type v) where
  /-- The reversible modeled state transition. -/
  effect : Effect State
  /-- The pure result observed at the state where this call is evaluated. -/
  result : State → Result

/-- A finite batch of exactly two heterogeneous calls in declared model order. -/
structure TwoBatch (State : Type u) (FirstResult : Type v) (SecondResult : Type w) where
  /-- The first call in model and result-commit order. -/
  first : PureCall State FirstResult
  /-- The second call in model and result-commit order. -/
  second : PureCall State SecondResult

namespace TwoBatch

variable {State : Type u} {FirstResult : Type v} {SecondResult : Type w}

/-- A two-call certificate combining reversible independence with result stability. -/
structure IndependentAt
    (batch : TwoBatch State FirstResult SecondResult) (before : State) : Prop where
  /-- The effects have equal successors and equal composed recovery behavior. -/
  effects : Effect.IndependentAt batch.first.effect batch.second.effect before
  /-- The first result is unchanged when the second effect is evaluated first. -/
  first_result_stable :
    batch.first.result (batch.second.effect before).after =
      batch.first.result before
  /-- The second result is unchanged when the first effect is evaluated first. -/
  second_result_stable :
    batch.second.result (batch.first.effect before).after =
      batch.second.result before

end TwoBatch

/-- The two semantic evaluation orders permitted by a certified batch. -/
inductive EvaluationOrder where
  /-- Evaluate calls in their declared model order. -/
  | model
  /-- Evaluate the second call first, then restore declared result order. -/
  | swapped
deriving DecidableEq, Repr

/-- The result of a batch, indexed by the state from which it was evaluated. -/
structure BatchOutcome
    (State : Type u) (FirstResult : Type v) (SecondResult : Type w) (before : State) where
  /-- The proof-carrying successor and recovery action. -/
  applied : Applied State before
  /-- Results in declared order, regardless of evaluation order. -/
  outputs : FirstResult × SecondResult

namespace BatchOutcome

variable {State : Type u} {FirstResult : Type v} {SecondResult : Type w} {before : State}

/-- Batch outcomes are equal when their applied effect and ordered outputs agree. -/
@[ext]
theorem ext {left right : BatchOutcome State FirstResult SecondResult before}
    (applied_eq : left.applied = right.applied)
    (outputs_eq : left.outputs = right.outputs) : left = right := by
  cases left
  cases right
  cases applied_eq
  cases outputs_eq
  rfl

/-- Every batch outcome recovers the state at which its evaluation began. -/
@[simp]
theorem recovers (outcome : BatchOutcome State FirstResult SecondResult before) :
    outcome.applied.undo outcome.applied.after = before :=
  outcome.applied.undo_after

end BatchOutcome

/-- A two-call batch carrying strong independence evidence at its indexed start state. -/
structure CertifiedTwoBatch
    (State : Type u) (FirstResult : Type v) (SecondResult : Type w) (before : State) where
  /-- The ordered batch to evaluate. -/
  batch : TwoBatch State FirstResult SecondResult
  /-- Evidence authorizing either pure evaluation order at `before`. -/
  independent : batch.IndependentAt before

namespace CertifiedTwoBatch

variable {State : Type u} {FirstResult : Type v} {SecondResult : Type w} {before : State}

/-- Evaluate a certified batch in either semantic order.

Even in the swapped case, the output type and value order remain `(first, second)`. This is a
pure model evaluator; it is not an asynchronous or `IO` scheduler.
-/
def execute
    (certified : CertifiedTwoBatch State FirstResult SecondResult before)
    (order : EvaluationOrder) :
    BatchOutcome State FirstResult SecondResult before :=
  match order with
  | .model =>
      { applied := Effect.seq certified.batch.first.effect certified.batch.second.effect before
        outputs :=
          (certified.batch.first.result before,
            certified.batch.second.result (certified.batch.first.effect before).after) }
  | .swapped =>
      { applied := Effect.seq certified.batch.second.effect certified.batch.first.effect before
        outputs :=
          (certified.batch.first.result (certified.batch.second.effect before).after,
            certified.batch.second.result before) }

/-- The model-order evaluator uses model-order effect composition. -/
@[simp]
theorem execute_model_applied
    (certified : CertifiedTwoBatch State FirstResult SecondResult before) :
    (certified.execute .model).applied =
      Effect.seq certified.batch.first.effect certified.batch.second.effect before := rfl

/-- The swapped evaluator uses reverse effect composition. -/
@[simp]
theorem execute_swapped_applied
    (certified : CertifiedTwoBatch State FirstResult SecondResult before) :
    (certified.execute .swapped).applied =
      Effect.seq certified.batch.second.effect certified.batch.first.effect before := rfl

/-- Both certified evaluations reach the same modeled successor. -/
theorem execute_after_eq
    (certified : CertifiedTwoBatch State FirstResult SecondResult before) :
    (certified.execute .model).applied.after =
      (certified.execute .swapped).applied.after :=
  certified.independent.effects.seq_after_eq

/-- Both certified evaluations install the same recovery action on every state. -/
theorem execute_undo_eq
    (certified : CertifiedTwoBatch State FirstResult SecondResult before)
    (current : State) :
    (certified.execute .model).applied.undo current =
      (certified.execute .swapped).applied.undo current :=
  certified.independent.effects.seq_undo_eq current

/-- The complete proof-carrying applied effects are independent of evaluation order. -/
theorem execute_applied_eq
    (certified : CertifiedTwoBatch State FirstResult SecondResult before) :
    (certified.execute .model).applied =
      (certified.execute .swapped).applied :=
  certified.independent.effects.seq_applied_eq

/-- Swapped evaluation commits exactly the model-order result pair. -/
theorem execute_outputs_eq
    (certified : CertifiedTwoBatch State FirstResult SecondResult before) :
    (certified.execute .model).outputs =
      (certified.execute .swapped).outputs := by
  apply Prod.ext
  · exact certified.independent.first_result_stable.symm
  · exact certified.independent.second_result_stable

/-- Every permitted evaluation commits results in the batch's declared model order. -/
theorem execute_outputs_in_model_order
    (certified : CertifiedTwoBatch State FirstResult SecondResult before)
    (order : EvaluationOrder) :
    (certified.execute order).outputs =
      (certified.batch.first.result before,
        certified.batch.second.result (certified.batch.first.effect before).after) := by
  cases order with
  | model => rfl
  | swapped =>
      calc
        (certified.execute .swapped).outputs =
            (certified.execute .model).outputs := certified.execute_outputs_eq.symm
        _ = _ := rfl

/-- The complete batch outcome is independent of the certified evaluation order. -/
theorem execute_eq
    (certified : CertifiedTwoBatch State FirstResult SecondResult before) :
    certified.execute .model = certified.execute .swapped := by
  apply BatchOutcome.ext
  · exact certified.execute_applied_eq
  · exact certified.execute_outputs_eq

/-- Any two permitted orders return the same proof-carrying, model-ordered outcome. -/
theorem execute_order_irrelevant
    (certified : CertifiedTwoBatch State FirstResult SecondResult before)
    (left right : EvaluationOrder) :
    certified.execute left = certified.execute right := by
  cases left <;> cases right
  · rfl
  · exact certified.execute_eq
  · exact certified.execute_eq.symm
  · rfl

/-- Either certified evaluation order recovers the indexed predecessor state. -/
@[simp]
theorem execute_recovers
    (certified : CertifiedTwoBatch State FirstResult SecondResult before)
    (order : EvaluationOrder) :
    (certified.execute order).applied.undo (certified.execute order).applied.after = before :=
  (certified.execute order).recovers

end CertifiedTwoBatch

end Cordis
