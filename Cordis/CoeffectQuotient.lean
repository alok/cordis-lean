import Cordis.QuotientEffect

/-!
# Coeffect operations on the contextual quotient

This module connects Definition 24's key-local operation laws to Definition 33's finite-context
equivalence and Definition 37's observational inverse contract. For related input contexts, the
same key-local operation has related lifted successors, pointwise-related lifted inverses, and
equal outcomes. A single lifted application is also packaged as an observational `Applied`
value over the context `Setoid`.

The result is the generator-level quotient law needed before the paper's operation independence
argument. It does not construct Definition 34 tests, close transformations under a monoid,
prove Theorem 40 for those monoids, or establish Theorem 42.
-/

set_option autoImplicit false

namespace Cordis.Coeffect.Quotient

universe u v w

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

/-- The local exact inverse applied only to one dependent binding. -/
def undoAt
    {key : Key} {before : Value key}
    (applied : Cordis.Applied (Value key) before)
    (context : Context Key Value) : Context Key Value :=
  match context key with
  | none => context
  | some value => setAt context key (applied.undo value)

/-- Related local applications map related whole contexts to related whole contexts. -/
theorem undoAt_related
    (coeffects : (key : Key) → CoeffectAt (Value key))
    {key : Key} (op : (coeffects key).Op) (input : (coeffects key).Input op)
    {leftBefore rightBefore : Value key}
    (beforeRelated : (coeffects key).equivalence.r leftBefore rightBefore)
    (leftEnabled : (coeffects key).Enabled op input leftBefore)
    (rightEnabled : (coeffects key).Enabled op input rightBefore)
    {leftCurrent rightCurrent : Context Key Value}
    (currentRelated : Observational.Related (Observational.equivalencesOf coeffects)
      leftCurrent rightCurrent) :
    Observational.Related (Observational.equivalencesOf coeffects)
      (undoAt ((coeffects key).run op input leftBefore leftEnabled).1 leftCurrent)
      (undoAt ((coeffects key).run op input rightBefore rightEnabled).1 rightCurrent) := by
  let equivalences := Observational.equivalencesOf coeffects
  cases leftLookup : leftCurrent key with
  | none =>
      cases rightLookup : rightCurrent key with
      | none =>
          simpa [undoAt, leftLookup, rightLookup] using currentRelated
      | some rightValue =>
          have samePresence := Observational.related_isSome_eq equivalences
            currentRelated key
          simp [leftLookup, rightLookup] at samePresence
  | some leftValue =>
      cases rightLookup : rightCurrent key with
      | none =>
          have samePresence := Observational.related_isSome_eq equivalences
            currentRelated key
          simp [leftLookup, rightLookup] at samePresence
      | some rightValue =>
          have valuesRelated :=
            ((Observational.related_iff equivalences leftCurrent rightCurrent).1
              currentRelated).2 key leftValue rightValue leftLookup rightLookup
          have undoneRelated := (coeffects key).undo_respects op input beforeRelated
            leftEnabled rightEnabled valuesRelated
          simpa [undoAt, leftLookup, rightLookup] using
            Observational.setAt_related equivalences currentRelated key undoneRelated

/-- The existing exact context lift uses `undoAt` as its concrete inverse. -/
@[simp]
theorem lift_undo_eq
    (coeffects : (key : Key) → CoeffectAt (Value key))
    {key : Key} (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (context : Context Key Value) (present : Present context key)
    (enabled : (coeffects key).Enabled op input present.value)
    (current : Context Key Value) :
    ((coeffects key).lift op input context present enabled).1.undo current =
      undoAt ((coeffects key).run op input present.value enabled).1 current :=
  rfl

/-- Related lifted operations retain successor, inverse, and outcome relations together. -/
structure LiftResultsRelated
    (equivalences : Observational.Equivalences Key Value)
    {leftBefore rightBefore : Context Key Value}
    {Outcome : Type w}
    (left : Cordis.Applied (Context Key Value) leftBefore × Outcome)
    (right : Cordis.Applied (Context Key Value) rightBefore × Outcome) : Prop where
  /-- The lifted successor contexts are related. -/
  after : Observational.Related equivalences left.1.after right.1.after
  /-- The captured whole-context inverses are pointwise related. -/
  undo : ∀ current,
    Observational.Related equivalences (left.1.undo current) (right.1.undo current)
  /-- The typed operation outcomes are equal. -/
  outcome : left.2 = right.2

/-- Definition 24's respect laws survive the lift to Definition 33 contexts. -/
theorem lift_results_related
    (coeffects : (key : Key) → CoeffectAt (Value key))
    {key : Key} (op : (coeffects key).Op) (input : (coeffects key).Input op)
    {left right : Context Key Value}
    (contextsRelated : Observational.Related (Observational.equivalencesOf coeffects) left right)
    (leftPresent : Present left key) (rightPresent : Present right key)
    (leftEnabled : (coeffects key).Enabled op input leftPresent.value)
    (rightEnabled : (coeffects key).Enabled op input rightPresent.value) :
    LiftResultsRelated (Observational.equivalencesOf coeffects)
      ((coeffects key).lift op input left leftPresent leftEnabled)
      ((coeffects key).lift op input right rightPresent rightEnabled) := by
  let equivalences := Observational.equivalencesOf coeffects
  have valuesRelated :=
    ((Observational.related_iff equivalences left right).1 contextsRelated).2
      key leftPresent.value rightPresent.value leftPresent.lookup_eq rightPresent.lookup_eq
  refine {
    after := ?_
    undo := ?_
    outcome := (coeffects key).outcome_respects op input valuesRelated
      leftEnabled rightEnabled
  }
  · change Observational.Related equivalences
      (setAt left key ((coeffects key).run op input leftPresent.value leftEnabled).1.after)
      (setAt right key ((coeffects key).run op input rightPresent.value rightEnabled).1.after)
    exact Observational.setAt_related equivalences contextsRelated key
      ((coeffects key).after_respects op input valuesRelated leftEnabled rightEnabled)
  · intro current
    rw [lift_undo_eq, lift_undo_eq]
    exact undoAt_related coeffects op input valuesRelated leftEnabled rightEnabled
      (Observational.related_refl equivalences current)

/-- Package one exact lifted operation as a Definition 37 observational application. -/
def liftApplied
    (coeffects : (key : Key) → CoeffectAt (Value key))
    {key : Key} (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (context : Context Key Value) (present : Present context key)
    (enabled : (coeffects key).Enabled op input present.value) :
    @Cordis.Observational.Applied (Context Key Value)
      (Observational.contextSetoid (Observational.equivalencesOf coeffects)) context := by
  let equivalences := Observational.equivalencesOf coeffects
  letI : Setoid (Context Key Value) := Observational.contextSetoid equivalences
  let exact := ((coeffects key).lift op input context present enabled).1
  exact {
    after := exact.after
    undo := exact.undo
    undo_respects := by
      intro left right related
      rw [lift_undo_eq, lift_undo_eq]
      exact undoAt_related coeffects op input
        ((coeffects key).equivalence.refl present.value) enabled enabled related
    undo_after := by
      rw [exact.undo_after]
      exact Observational.related_refl equivalences context
  }

/-!
## Heterogeneous example
-/

namespace Example

inductive ExampleKey where
  | counter
  | label
deriving DecidableEq, Repr

def ExampleValue : ExampleKey → Type
  | .counter => Nat
  | .label => String

def counterCoeffect : CoeffectAt Nat where
  equivalence := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }
  Op := Unit
  Input := fun _ ↦ Nat
  Outcome := fun _ ↦ Nat
  Enabled := fun _ _ _ ↦ True
  enabledDecidable := fun _ _ _ ↦ inferInstance
  run := fun _ amount before _ ↦
    ({
      after := before + amount
      undo := fun current ↦ current - amount
      undo_after := Nat.add_sub_cancel before amount
    }, before)
  enabled_respects := by simp
  after_respects := by
    intro _ amount left right related _ _
    exact congrArg (fun value ↦ value + amount) related
  undo_respects := by
    intro _ amount left right _ _ _ leftCurrent rightCurrent related
    exact congrArg (fun value ↦ value - amount) related
  outcome_respects := by
    intro _ _ left right related _ _
    exact related

def labelCoeffect : CoeffectAt String where
  equivalence := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }
  Op := Unit
  Input := fun _ ↦ String
  Outcome := fun _ ↦ Nat
  Enabled := fun _ _ _ ↦ True
  enabledDecidable := fun _ _ _ ↦ inferInstance
  run := fun _ suffix before _ ↦
    ({
      after := before ++ suffix
      undo := fun _ ↦ before
      undo_after := rfl
    }, before.length)
  enabled_respects := by simp
  after_respects := by
    intro _ suffix left right related _ _
    exact congrArg (fun value ↦ value ++ suffix) related
  undo_respects := by
    intro _ _ left right initialRelated _ _ _ _ _
    exact initialRelated
  outcome_respects := by
    intro _ _ left right related _ _
    exact congrArg String.length related

def coeffects : (key : ExampleKey) → CoeffectAt (ExampleValue key)
  | .counter => counterCoeffect
  | .label => labelCoeffect

def empty : Context ExampleKey ExampleValue := Coeffect.empty
def left : Context ExampleKey ExampleValue :=
  setAt (setAt empty .counter (show ExampleValue .counter from (3 : Nat)))
    .label (show ExampleValue .label from "a")
def right : Context ExampleKey ExampleValue :=
  setAt (setAt empty .counter (show ExampleValue .counter from (3 : Nat)))
    .label (show ExampleValue .label from "a")

def leftCounter : Present left .counter where
  value := show ExampleValue .counter from (3 : Nat)
  lookup_eq := by simp [left, empty, setAt]

def rightCounter : Present right .counter where
  value := show ExampleValue .counter from (3 : Nat)
  lookup_eq := by simp [right, empty, setAt]

def counterOp : counterCoeffect.Op := show Unit from ()
def counterAmount : counterCoeffect.Input counterOp := show Nat from 4

theorem contexts_related : Observational.Related
    (Observational.equivalencesOf coeffects) left right :=
  Observational.related_refl _ left

theorem counter_lifts_related :
    LiftResultsRelated (Observational.equivalencesOf coeffects)
      (counterCoeffect.lift counterOp counterAmount left leftCounter trivial)
      (counterCoeffect.lift counterOp counterAmount right rightCounter trivial) :=
  lift_results_related coeffects (key := .counter) counterOp counterAmount
    contexts_related leftCounter rightCounter trivial trivial

/-- Both lifted outcomes retain the exact pre-increment value. -/
theorem counter_outcomes_equal :
    (counterCoeffect.lift counterOp counterAmount left leftCounter trivial).2 =
      (counterCoeffect.lift counterOp counterAmount right rightCounter trivial).2 :=
  counter_lifts_related.outcome

end Example

end Cordis.Coeffect.Quotient
