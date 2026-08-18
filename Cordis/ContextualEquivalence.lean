import Cordis.Coeffect

/-!
# Observational equivalence for finite coeffect contexts

This module mechanizes the finite-context portion of Definition 33 of the CORDIS paper at
revision `948a07b369c62adb3b12e102458be5c18dfb69b9`. Two contexts are related exactly when
they have the same presence shape and their values at every present key are related by that
key's equivalence. The relation is packaged as a `Setoid`, so the observational effect core in
`Cordis.Effect` can use it directly.

The principal consequences stated immediately after Definition 33 are proved here:
satisfaction is invariant under contextual equivalence, and notification classification is
invariant when both endpoints are replaced by related contexts. This file does not construct
the operation-test indistinguishability of Definitions 34--35, the recursive unified context of
Definition 32, or the coeffect-mediated independence theorem of Definitions 39--42.
-/

namespace Cordis.Coeffect.Observational

universe u v

/-- Lift a relation to optional bindings without relating presence to absence. -/
inductive OptionRelated {State : Type v} (relation : State → State → Prop) :
    Option State → Option State → Prop where
  /-- Two absent bindings are related. -/
  | none : OptionRelated relation none none
  /-- Two present bindings are related exactly when their values are. -/
  | some {left right : State} : relation left right →
      OptionRelated relation (some left) (some right)

namespace OptionRelated

variable {State : Type v} {relation : State → State → Prop}

/-- Lifting a reflexive relation to options remains reflexive. -/
theorem refl (reflexive : ∀ value, relation value value) :
    ∀ value : Option State, OptionRelated relation value value
  | Option.none => OptionRelated.none
  | Option.some value => OptionRelated.some (reflexive value)

/-- Lifting a symmetric relation to options remains symmetric. -/
theorem symm (symmetric : ∀ {left right}, relation left right → relation right left) :
  ∀ {left right : Option State}, OptionRelated relation left right →
      OptionRelated relation right left
  | _, _, .none => OptionRelated.none
  | _, _, .some related => OptionRelated.some (symmetric related)

/-- Lifting a transitive relation to options remains transitive. -/
theorem trans
    (transitive : ∀ {left middle right},
      relation left middle → relation middle right → relation left right) :
    ∀ {left middle right : Option State},
      OptionRelated relation left middle →
      OptionRelated relation middle right →
      OptionRelated relation left right
  | _, _, _, .none, .none => OptionRelated.none
  | _, _, _, .some leftRelated, .some rightRelated =>
      OptionRelated.some (transitive leftRelated rightRelated)

/-- Related optional bindings have exactly the same presence bit. -/
theorem isSome_eq {left right : Option State}
    (related : OptionRelated relation left right) : left.isSome = right.isSome := by
  cases related <;> rfl

end OptionRelated

section Context

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

/-- Definition 33's family of key-local observational equivalences. -/
abbrev Equivalences (Key : Type u) (Value : Key → Type v) :=
  (key : Key) → Setoid (Value key)

/-- Extract Definition 33's equivalence family from Definition 24 coeffects. -/
@[instance_reducible]
def equivalencesOf (coeffects : (key : Key) → CoeffectAt (Value key)) :
    Equivalences Key Value :=
  fun key ↦ (coeffects key).equivalence

/-- Definition 33 for the finite dependent context of Definition 22. -/
def Related (equivalences : Equivalences Key Value)
    (left right : Context Key Value) : Prop :=
  ∀ key, OptionRelated (equivalences key).r (left key) (right key)

/-- Pointwise form of equality of the finite domains in Definition 33. -/
def SameDomain (left right : Context Key Value) : Prop :=
  ∀ key, (left key).isSome = (right key).isSome

/-- The value clause of Definition 33, stated only where both bindings are present. -/
def ValuesRelated (equivalences : Equivalences Key Value)
    (left right : Context Key Value) : Prop :=
  ∀ key (leftValue rightValue : Value key),
    left key = some leftValue → right key = some rightValue →
      (equivalences key).r leftValue rightValue

/-- The option lift is exactly the paper's domain-and-pointwise-values conjunction. -/
theorem related_iff (equivalences : Equivalences Key Value)
    (left right : Context Key Value) :
    Related equivalences left right ↔
      SameDomain left right ∧ ValuesRelated equivalences left right := by
  constructor
  · intro related
    constructor
    · intro key
      exact OptionRelated.isSome_eq (related key)
    · intro key leftValue rightValue leftLookup rightLookup
      have atKey := related key
      rw [leftLookup, rightLookup] at atKey
      cases atKey with
      | some valuesRelated => exact valuesRelated
  · rintro ⟨sameDomain, valuesRelated⟩ key
    cases leftLookup : left key with
    | none =>
        cases rightLookup : right key with
        | none => exact OptionRelated.none
        | some rightValue =>
            have presence := sameDomain key
            simp [leftLookup, rightLookup] at presence
    | some leftValue =>
        cases rightLookup : right key with
        | none =>
            have presence := sameDomain key
            simp [leftLookup, rightLookup] at presence
        | some rightValue =>
            exact OptionRelated.some
              (valuesRelated key leftValue rightValue leftLookup rightLookup)

/-- Every finite dependent context is related to itself. -/
theorem related_refl (equivalences : Equivalences Key Value) :
    ∀ context, Related equivalences context context := by
  intro context key
  exact OptionRelated.refl (equivalences key).iseqv.refl (context key)

/-- Contextual observational equivalence is symmetric. -/
theorem related_symm (equivalences : Equivalences Key Value) :
    ∀ {left right}, Related equivalences left right → Related equivalences right left := by
  intro left right related key
  exact OptionRelated.symm (equivalences key).iseqv.symm (related key)

/-- Contextual observational equivalence is transitive. -/
theorem related_trans (equivalences : Equivalences Key Value) :
    ∀ {left middle right},
      Related equivalences left middle →
      Related equivalences middle right →
      Related equivalences left right := by
  intro left middle right leftRelated rightRelated key
  exact OptionRelated.trans (relation := (equivalences key).r)
    (fun first second ↦ (equivalences key).iseqv.trans first second)
    (leftRelated key) (rightRelated key)

/-- Definition 33 supplies a `Setoid` for the observational effect semantics. -/
def contextSetoid (equivalences : Equivalences Key Value) : Setoid (Context Key Value) where
  r := Related equivalences
  iseqv := {
    refl := related_refl equivalences
    symm := related_symm equivalences
    trans := related_trans equivalences
  }

/-- Related contexts have the same domain, expressed as pointwise presence equality. -/
theorem related_isSome_eq (equivalences : Equivalences Key Value)
    {left right : Context Key Value} (related : Related equivalences left right) (key : Key) :
    (left key).isSome = (right key).isSome :=
  OptionRelated.isSome_eq (related key)

/-- Updating related contexts with related values preserves contextual equivalence. -/
theorem setAt_related (equivalences : Equivalences Key Value)
    {left right : Context Key Value} (contextsRelated : Related equivalences left right)
    (key : Key) {leftValue rightValue : Value key}
    (valuesRelated : (equivalences key).r leftValue rightValue) :
    Related equivalences (setAt left key leftValue) (setAt right key rightValue) := by
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    simpa using OptionRelated.some valuesRelated
  · simpa [setAt_other, same] using contextsRelated candidate

/-- Removing the same key from related contexts preserves contextual equivalence. -/
theorem removeAt_related (equivalences : Equivalences Key Value)
    {left right : Context Key Value} (contextsRelated : Related equivalences left right)
    (key : Key) :
    Related equivalences (removeAt left key) (removeAt right key) := by
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    simpa using (OptionRelated.none :
      OptionRelated (equivalences key).r none none)
  · simpa [removeAt_other, same] using contextsRelated candidate

/-- Definition 23's local insertion inverse respects Definition 33 equivalence. -/
def setApplied (equivalences : Equivalences Key Value)
    (context : Context Key Value) (key : Key) (value : Value key)
    (absent : Absent context key) :
    @Cordis.Observational.Applied (Context Key Value) (contextSetoid equivalences) context := by
  letI : Setoid (Context Key Value) := contextSetoid equivalences
  exact {
    after := setAt context key value
    undo := fun current ↦ removeAt current key
    undo_respects := fun related ↦ removeAt_related equivalences related key
    undo_after := by
      rw [removeAt_setAt_of_absent context key value absent]
      exact related_refl equivalences context
  }

/-- The observational insertion still recovers its exact input up to Definition 33. -/
theorem setApplied_recovers (equivalences : Equivalences Key Value)
    (context : Context Key Value) (key : Key) (value : Value key)
    (absent : Absent context key) :
    Related equivalences
      (removeAt (setAt context key value) key) context := by
  rw [removeAt_setAt_of_absent context key value absent]
  exact related_refl equivalences context

/-- Satisfaction factors through the quotient by Definition 33. -/
theorem satisfies_iff_of_related (equivalences : Equivalences Key Value)
    (spec : Spec Key) {left right : Context Key Value}
    (related : Related equivalences left right) :
    Satisfies left spec ↔ Satisfies right spec := by
  constructor
  · intro satisfied
    apply (satisfies_iff right spec).2
    intro key required
    rw [← related_isSome_eq equivalences related key]
    exact (satisfies_iff left spec).1 satisfied key required
  · intro satisfied
    apply (satisfies_iff left spec).2
    intro key required
    rw [related_isSome_eq equivalences related key]
    exact (satisfies_iff right spec).1 satisfied key required

/-- Notification classification is well-defined on contextual equivalence classes. -/
theorem notify_eq_of_related (equivalences : Equivalences Key Value)
    (spec : Spec Key)
    {leftBefore rightBefore leftAfter rightAfter : Context Key Value}
    (beforeRelated : Related equivalences leftBefore rightBefore)
    (afterRelated : Related equivalences leftAfter rightAfter) :
    notify spec leftBefore leftAfter = notify spec rightBefore rightAfter := by
  have beforeIff := satisfies_iff_of_related equivalences spec beforeRelated
  have afterIff := satisfies_iff_of_related equivalences spec afterRelated
  by_cases leftBeforeSat : Satisfies leftBefore spec <;>
    by_cases leftAfterSat : Satisfies leftAfter spec
  · have rightBeforeSat : Satisfies rightBefore spec := beforeIff.mp leftBeforeSat
    have rightAfterSat : Satisfies rightAfter spec := afterIff.mp leftAfterSat
    simp [notify, leftBeforeSat, leftAfterSat, rightBeforeSat, rightAfterSat]
  · have rightBeforeSat : Satisfies rightBefore spec := beforeIff.mp leftBeforeSat
    have rightAfterNotSat : ¬Satisfies rightAfter spec := fun rightAfterSat ↦
      leftAfterSat (afterIff.mpr rightAfterSat)
    simp [notify, leftBeforeSat, leftAfterSat, rightBeforeSat, rightAfterNotSat]
  · have rightBeforeNotSat : ¬Satisfies rightBefore spec := fun rightBeforeSat ↦
      leftBeforeSat (beforeIff.mpr rightBeforeSat)
    have rightAfterSat : Satisfies rightAfter spec := afterIff.mp leftAfterSat
    simp [notify, leftBeforeSat, leftAfterSat, rightBeforeNotSat, rightAfterSat]
  · have rightBeforeNotSat : ¬Satisfies rightBefore spec := fun rightBeforeSat ↦
      leftBeforeSat (beforeIff.mpr rightBeforeSat)
    have rightAfterNotSat : ¬Satisfies rightAfter spec := fun rightAfterSat ↦
      leftAfterSat (afterIff.mpr rightAfterSat)
    simp [notify, leftBeforeSat, leftAfterSat, rightBeforeNotSat, rightAfterNotSat]

end Context

/-!
## Heterogeneous quotient example
-/

namespace Example

open Cordis.Coeffect.Example

/-- The counter observer sees parity; the label observer sees exact strings. -/
@[instance_reducible]
def equivalences : Equivalences Key Value
  | .counter => {
      r := fun left right : Nat ↦ left % 2 = right % 2
      iseqv := {
        refl := fun _ ↦ rfl
        symm := fun related ↦ related.symm
        trans := fun leftRelated rightRelated ↦ leftRelated.trans rightRelated
      }
    }
  | .label => {
      r := Eq
      iseqv := {
        refl := Eq.refl
        symm := Eq.symm
        trans := Eq.trans
      }
    }

/-- A fully satisfied context with odd counter value `1`. -/
def left : Context Key Value :=
  setAt (setAt initial .counter (show Value .counter from (1 : Nat)))
    .label (show Value .label from "ready")

/-- An extensionally different context with observationally equal odd counter value `3`. -/
def right : Context Key Value :=
  setAt (setAt initial .counter (show Value .counter from (3 : Nat)))
    .label (show Value .label from "ready")

/-- The two exact contexts differ. -/
theorem left_ne_right : left ≠ right := by
  intro equal
  have counterEqual := congrArg (fun context : Context Key Value ↦ context .counter) equal
  change (some (1 : Nat)) = some 3 at counterEqual
  simp at counterEqual

/-- Nevertheless, Definition 33 relates them at every dependent key. -/
theorem left_related_right : Related equivalences left right := by
  intro key
  cases key with
  | counter =>
      change OptionRelated (fun left right : Nat ↦ left % 2 = right % 2)
        (some 1) (some 3)
      exact OptionRelated.some rfl
  | label =>
      change OptionRelated Eq (some "ready") (some "ready")
      exact OptionRelated.some rfl

/-- Satisfaction cannot distinguish the two exact representations. -/
example : Satisfies left dependencies ↔ Satisfies right dependencies :=
  satisfies_iff_of_related equivalences dependencies left_related_right

/-- A related replacement of both endpoints leaves notification unchanged. -/
example : notify dependencies left (removeAt left .label) =
    notify dependencies right (removeAt right .label) := by
  apply notify_eq_of_related equivalences dependencies left_related_right
  exact removeAt_related equivalences left_related_right .label

end Example

end Cordis.Coeffect.Observational
