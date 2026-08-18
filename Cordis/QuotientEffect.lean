import Cordis.ContextualEquivalence

/-!
# Quotient-respecting reversible effects

This module mechanizes the generic map/effect layer of CORDIS paper Definitions 36--37 and
the finite-composition core of Lemma 38, at revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

Definition 36 distinguishes a map that respects observational equivalence from two maps that
are pointwise related. `AppliedRelated` lifts the paper's pair relation to the existing
proof-carrying observational effect result. Definition 37's recovery and inverse-respect laws
are already fields of `Cordis.Observational.Applied`; `Admissible` adds the missing requirement
that the effect itself maps related inputs to related successor/inverse pairs.

`Program` proves the finite compositional statement used by Lemma 38: a sequence of admissible
effects remains admissible, its accumulated inverse respects the state relation, and applying
that inverse to the reached endpoint recovers the start up to the relation. The file does not
claim every equality from paper Section 3.1, transformation-monoid independence, Definitions
34--35 or 39--42, or the global component/fiber trace result.
-/

set_option autoImplicit false

namespace Cordis.Observational.Quotient

universe u

variable {State : Type u} [Setoid State]

/-- Definition 36: a state map descends to the observational quotient. -/
def Respects (map : State → State) : Prop :=
  ∀ {left right}, left ≈ right → map left ≈ map right

/-- Definition 36: two maps descend to the same map on the quotient. -/
def MapRelated (left right : State → State) : Prop :=
  ∀ state, left state ≈ right state

/-- Identity respects every equivalence relation. -/
theorem respects_id : Respects (id : State → State) :=
  fun related ↦ related

/-- Composition of quotient-respecting maps respects the quotient. -/
theorem Respects.comp {outer inner : State → State}
    (outerRespects : Respects outer) (innerRespects : Respects inner) :
    Respects (outer ∘ inner) :=
  fun related ↦ outerRespects (innerRespects related)

/-- Pointwise map relatedness is reflexive. -/
theorem mapRelated_refl (map : State → State) : MapRelated map map :=
  fun state ↦ Setoid.refl (map state)

/-- Pointwise map relatedness is symmetric. -/
theorem MapRelated.symm {left right : State → State}
    (related : MapRelated left right) : MapRelated right left :=
  fun state ↦ Setoid.symm (related state)

/-- Pointwise map relatedness is transitive. -/
theorem MapRelated.trans {first second third : State → State}
    (firstSecond : MapRelated first second) (secondThird : MapRelated second third) :
    MapRelated first third :=
  fun state ↦ Setoid.trans (firstSecond state) (secondThird state)

/-- Related outer and inner maps compose when the first outer map respects the quotient. -/
theorem MapRelated.comp
    {leftOuter rightOuter leftInner rightInner : State → State}
    (leftOuterRespects : Respects leftOuter)
    (outerRelated : MapRelated leftOuter rightOuter)
    (innerRelated : MapRelated leftInner rightInner) :
    MapRelated (leftOuter ∘ leftInner) (rightOuter ∘ rightInner) := by
  intro state
  exact Setoid.trans (leftOuterRespects (innerRelated state))
    (outerRelated (rightInner state))

/-- Definition 36's relation on effect-result pairs, ignoring proof-field representation. -/
structure AppliedRelated
    {leftBefore rightBefore : State}
    (left : Applied State leftBefore) (right : Applied State rightBefore) : Prop where
  /-- The successor states are observationally related. -/
  after : left.after ≈ right.after
  /-- The yielded inverse maps are pointwise observationally related. -/
  undo : MapRelated left.undo right.undo

namespace AppliedRelated

/-- Pair relatedness is reflexive. -/
theorem refl {before : State} (applied : Applied State before) :
    AppliedRelated applied applied where
  after := Setoid.refl applied.after
  undo := mapRelated_refl applied.undo

/-- Pair relatedness is symmetric. -/
theorem symm
    {leftBefore rightBefore : State}
    {left : Applied State leftBefore} {right : Applied State rightBefore}
    (related : AppliedRelated left right) : AppliedRelated right left where
  after := Setoid.symm related.after
  undo := related.undo.symm

/-- Pair relatedness is transitive. -/
theorem trans
    {firstBefore secondBefore thirdBefore : State}
    {first : Applied State firstBefore}
    {second : Applied State secondBefore}
    {third : Applied State thirdBefore}
    (firstSecond : AppliedRelated first second)
    (secondThird : AppliedRelated second third) :
    AppliedRelated first third where
  after := Setoid.trans firstSecond.after secondThird.after
  undo := firstSecond.undo.trans secondThird.undo

end AppliedRelated

/-- Definition 37: an observational effect also respects related starting states.

The effect's result type already requires recovery up to `≈` and requires every yielded inverse
to respect `≈`; this field supplies the remaining map-to-pair condition.
-/
structure Admissible (effect : Effect State) : Prop where
  /-- Related inputs yield related successors and pointwise-related inverse maps. -/
  effect_respects : ∀ {left right}, left ≈ right →
    AppliedRelated (effect left) (effect right)

namespace Admissible

/-- The observational identity effect is admissible. -/
theorem identity : Admissible (Effect.identity : Effect State) where
  effect_respects := by
    intro left right related
    exact {
      after := related
      undo := mapRelated_refl id
    }

/-- Sequential composition preserves Definition 37 admissibility. -/
theorem seq
    {first second : Effect State}
    (firstAdmissible : Admissible first)
    (secondAdmissible : Admissible second) :
    Admissible (Effect.seq first second) where
  effect_respects := by
    intro left right startsRelated
    let firstRelated := firstAdmissible.effect_respects startsRelated
    let secondRelated := secondAdmissible.effect_respects firstRelated.after
    refine {
      after := secondRelated.after
      undo := ?_
    }
    intro current
    change
      (first left).undo ((second (first left).after).undo current) ≈
        (first right).undo ((second (first right).after).undo current)
    exact Setoid.trans
      ((first left).undo_respects (secondRelated.undo current))
      (firstRelated.undo ((second (first right).after).undo current))

/-- Every admitted effect's yielded inverse respects observational equivalence. -/
theorem undo_respects
    {effect : Effect State} (_admissible : Admissible effect) (before : State) :
    Respects (effect before).undo :=
  fun related ↦ (effect before).undo_respects related

/-- Every admitted effect recovers its exact input up to observational equivalence. -/
theorem recovers
    {effect : Effect State} (_admissible : Admissible effect) (before : State) :
    (effect before).undo (effect before).after ≈ before :=
  (effect before).undo_after

end Admissible

/-- A finite word of Definition 37-admissible effects. -/
inductive Program (State : Type u) [Setoid State] where
  /-- The empty word. -/
  | nil
  /-- One admissible effect followed by another finite word. -/
  | cons (effect : Effect State) (admissible : Admissible effect) (rest : Program State)

namespace Program

/-- Interpret a finite word by LIFO sequential effect composition. -/
def run : Program State → Effect State
  | .nil => Effect.identity
  | .cons effect _ rest => Effect.seq effect rest.run

/-- Every certified finite word remains Definition 37-admissible. -/
theorem run_admissible (program : Program State) : Admissible program.run := by
  induction program with
  | nil => exact Admissible.identity
  | cons effect admissible rest inductionHypothesis =>
      exact admissible.seq inductionHypothesis

/-- Lemma 38 core: the accumulated inverse of a reachable finite word respects `≈`. -/
theorem accumulated_inverse_respects (program : Program State) (before : State) :
    Respects (program.run before).undo :=
  program.run_admissible.undo_respects before

/-- Lemma 38 core: the accumulated inverse recovers the initial state up to `≈`. -/
theorem recovers (program : Program State) (before : State) :
    (program.run before).undo (program.run before).after ≈ before :=
  program.run_admissible.recovers before

end Program

/-!
## Equality specialization
-/

/-- Equality as the observational relation, recovering Definition 8's exact reading. -/
def equalitySetoid (State : Type u) : Setoid State where
  r := Eq
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }

/-- Any exact witnessed effect becomes an observational effect under equality. -/
def ofExact (effect : Cordis.Effect State) :
    @Effect State (equalitySetoid State) := by
  letI : Setoid State := equalitySetoid State
  intro before
  exact {
    after := (effect before).after
    undo := (effect before).undo
    undo_respects := by
      intro left right equal
      cases equal
      exact Eq.refl _
    undo_after := (effect before).undo_after
  }

/-! The ambient setoid is intentionally omitted: this theorem installs equality explicitly. -/
omit [Setoid State] in
/-- An exact effect is Definition 37-admissible when equality-related inputs yield equal data. -/
theorem ofExact_admissible
    (effect : Cordis.Effect State) :
    @Admissible State (equalitySetoid State) (ofExact effect) := by
  letI : Setoid State := equalitySetoid State
  constructor
  intro left right equal
  cases equal
  exact AppliedRelated.refl (ofExact effect left)

/-!
## Executable quotient example
-/

namespace Example

/-- A state with one observed coordinate and one representation-private coordinate. -/
structure Model where
  visible : Nat
  hidden : Nat
deriving DecidableEq, Repr

/-- Observers compare only the published coordinate. -/
instance : Setoid Model where
  r := fun left right ↦ left.visible = right.visible
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun related ↦ related.symm
    trans := fun leftRelated rightRelated ↦ leftRelated.trans rightRelated
  }

/-- Increment the observed coordinate with a concrete local inverse. -/
def bumpVisible : Effect Model := fun before ↦
  {
    after := { before with visible := before.visible + 1 }
    undo := fun current ↦ { current with visible := current.visible - 1 }
    undo_respects := by
      intro left right related
      exact congrArg (fun value ↦ value - 1) related
    undo_after := by
      change before.visible + 1 - 1 = before.visible
      simp
  }

/-- Change only representation-private state. -/
def bumpHidden : Effect Model := fun before ↦
  {
    after := { before with hidden := before.hidden + 1 }
    undo := fun current ↦ { current with hidden := current.hidden - 1 }
    undo_respects := fun related ↦ related
    undo_after := rfl
  }

theorem bumpVisible_admissible : Admissible bumpVisible where
  effect_respects := by
    intro left right related
    exact {
      after := congrArg (fun value ↦ value + 1) related
      undo := fun current ↦ Setoid.refl _
    }

theorem bumpHidden_admissible : Admissible bumpHidden where
  effect_respects := by
    intro left right related
    exact {
      after := related
      undo := fun current ↦ Setoid.refl _
    }

/-- A two-stage admissible program mixing public and representation-private changes. -/
def program : Program Model :=
  .cons bumpVisible bumpVisible_admissible
    (.cons bumpHidden bumpHidden_admissible .nil)

def initial : Model := { visible := 4, hidden := 10 }

/-- The represented successor retains both concrete changes. -/
theorem program_after : (program.run initial).after = { visible := 5, hidden := 11 } := rfl

/-- The accumulated inverse recovers the initial state observationally. -/
theorem program_recovers : (program.run initial).undo (program.run initial).after ≈ initial :=
  program.recovers initial

end Example

end Cordis.Observational.Quotient
