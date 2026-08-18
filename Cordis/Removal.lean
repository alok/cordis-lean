import Cordis.Transformation
import Std

/-!
# Arbitrary removal and inverse-order recovery

This module mechanizes CORDIS paper Theorem 20 and Corollary 21 for finite lists of exact,
pairwise-independent effects at revision `948a07b369c62adb3b12e102458be5c18dfb69b9`.

`Execution` is indexed by its initial state, effect list, and final state, so each constructor
retains the state at which its effect was applied and therefore the exact inverse it yielded.
`RemovalTrace` runs a suffix twice: once after a chosen target effect and once with that effect
omitted. Every node stores the target/suffix independence certificate and equality of the
inverse the later effect yields in both executions.

The inverse-order corollary acts on `yieldedInverses`, the state-indexed inverses retained from
the original execution. It proves recovery for any permutation of those inverse functions. It
does not use whole-effect schedule reordering as a substitute for inverse permutation.

The scope is finite, exact, pure, and sequential. This module does not mechanize observational
quotients, infinite traces, asynchronous execution, components, fibers, or external effects.
-/

set_option autoImplicit false

namespace Cordis.Removal

universe u

variable {State : Type u}

/-!
## Indexed executions and retained inverses
-/

/-- Apply a finite effect list from left to right and return its final exact state. -/
def runState : List (Cordis.Effect State) → State → State
  | [], state => state
  | effect :: rest, state => runState rest (effect state).after

/-- An indexed execution retaining every application state through its constructor indices. -/
inductive Execution (State : Type u) :
    State → List (Cordis.Effect State) → State → Type u where
  /-- The empty execution starts and ends at the same state. -/
  | nil (state : State) : Execution State state [] state
  /-- Retain `before`; the tail begins at this application's exact successor. -/
  | cons (effect : Cordis.Effect State) {before final : State}
      {rest : List (Cordis.Effect State)}
      (tail : Execution State (effect before).after rest final) :
      Execution State before (effect :: rest) final

/-- Construct the canonical indexed execution of a finite effect list. -/
def execution (effects : List (Cordis.Effect State)) (before : State) :
    Execution State before effects (runState effects before) :=
  match effects with
  | [] => .nil before
  | effect :: rest => .cons effect (execution rest (effect before).after)

namespace Execution

/-- Read the concrete inverses retained by an indexed execution in application order. -/
def retainedInverses
    {before final : State} {effects : List (Cordis.Effect State)}
    (trace : Execution State before effects final) : List (State → State) :=
  match trace with
  | .nil _ => []
  | .cons effect tail => (effect before).undo :: tail.retainedInverses

end Execution

/-- Retain the concrete inverse each effect yields at its actual application state. -/
def yieldedInverses : List (Cordis.Effect State) → State → List (State → State)
  | [], _ => []
  | effect :: rest, before =>
      (effect before).undo :: yieldedInverses rest (effect before).after

@[simp]
theorem runState_nil (state : State) : runState [] state = state := rfl

@[simp]
theorem runState_cons (effect : Cordis.Effect State)
    (rest : List (Cordis.Effect State)) (state : State) :
    runState (effect :: rest) state = runState rest (effect state).after := rfl

@[simp]
theorem yieldedInverses_nil (state : State) : yieldedInverses [] state = [] := rfl

@[simp]
theorem yieldedInverses_cons (effect : Cordis.Effect State)
    (rest : List (Cordis.Effect State)) (state : State) :
    yieldedInverses (effect :: rest) state =
      (effect state).undo :: yieldedInverses rest (effect state).after := rfl

/-- The canonical indexed execution retains exactly `yieldedInverses`. -/
theorem execution_retainedInverses (effects : List (Cordis.Effect State)) (before : State) :
    (execution effects before).retainedInverses = yieldedInverses effects before := by
  induction effects generalizing before with
  | nil => rfl
  | cons effect rest induction =>
      simp [execution, Execution.retainedInverses, yieldedInverses, induction]

/-!
## Pairwise effect independence
-/

/-- One target effect is fully Definition 19-independent of every effect in a finite suffix. -/
def IndependentOf (target : Cordis.Effect State) (effects : List (Cordis.Effect State)) : Prop :=
  ∀ effect, effect ∈ effects → Transformation.Independent target effect

/-- Recursive pairwise Definition 19 independence for a finite application family. -/
def PairwiseIndependent : List (Cordis.Effect State) → Prop
  | [] => True
  | effect :: rest => IndependentOf effect rest ∧ PairwiseIndependent rest

theorem PairwiseIndependent.head
    {effect : Cordis.Effect State} {rest : List (Cordis.Effect State)}
    (pairwise : PairwiseIndependent (effect :: rest)) : IndependentOf effect rest :=
  pairwise.1

theorem PairwiseIndependent.tail
    {effect : Cordis.Effect State} {rest : List (Cordis.Effect State)}
    (pairwise : PairwiseIndependent (effect :: rest)) : PairwiseIndependent rest :=
  pairwise.2

/-!
## Theorem 20 as a target/suffix paired trace
-/

/-- One retained proof that a later effect yielded the same inverse with the target present or
omitted.
-/
structure LaterInverseAgreement (State : Type u) where
  effect : Cordis.Effect State
  originalBefore : State
  omittedBefore : State
  inverse_eq : (effect originalBefore).undo = (effect omittedBefore).undo

/-- The two Theorem 20(1) equations at one intermediate suffix boundary. -/
structure RemovalStateAgreement (target : Cordis.Effect State) (targetSeed : State) where
  original : State
  omitted : State
  forward_relation : original = (target omitted).after
  target_inverse_relation : (target targetSeed).undo original = omitted

/-- A paired suffix execution witnessing Theorem 20 at every step. -/
inductive RemovalTrace (target : Cordis.Effect State) (targetSeed : State) :
    State → State → List (Cordis.Effect State) → State → State → Type u where
  /-- At suffix end, retain the forward-target and target-inverse relationships. -/
  | nil (original omitted : State)
      (forward_relation : original = (target omitted).after)
      (target_inverse_relation : (target targetSeed).undo original = omitted) :
      RemovalTrace target targetSeed original omitted [] original omitted
  /-- Retain one later inverse equality and continue from both exact successors. -/
  | cons (original omitted : State) (effect : Cordis.Effect State)
      {rest : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
      (forward_relation : original = (target omitted).after)
      (target_inverse_relation : (target targetSeed).undo original = omitted)
      (independent : Transformation.Independent target effect)
      (inverse_eq : (effect original).undo = (effect omitted).undo)
      (tail : RemovalTrace target targetSeed
        (effect original).after (effect omitted).after rest finalOriginal finalOmitted) :
      RemovalTrace target targetSeed original omitted (effect :: rest)
        finalOriginal finalOmitted

namespace RemovalTrace

/-- The original suffix endpoint is the target forward map of the omitted endpoint. -/
theorem final_forward_relation
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) :
    finalOriginal = (target finalOmitted).after := by
  induction trace with
  | nil _ _ forward _ => exact forward
  | cons _ _ _ _ _ _ _ _ induction => exact induction

/-- The target's retained inverse removes it from the complete original suffix endpoint. -/
theorem final_target_inverse_relation
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) :
    (target targetSeed).undo finalOriginal = finalOmitted := by
  induction trace with
  | nil _ _ _ inverse => exact inverse
  | cons _ _ _ _ _ _ _ _ induction => exact induction

/-- Extract all later application states and yielded-inverse equalities. -/
def inverseAgreements
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) : List (LaterInverseAgreement State) :=
  match trace with
  | .nil _ _ _ _ => []
  | .cons original omitted effect _ _ _ inverse tail =>
      ⟨effect, original, omitted, inverse⟩ :: tail.inverseAgreements

/-- Extract Theorem 20(1)'s state equations at every suffix boundary, including the endpoint. -/
def stateAgreements
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) : List (RemovalStateAgreement target targetSeed) :=
  match trace with
  | .nil original omitted forward inverse => [⟨original, omitted, forward, inverse⟩]
  | .cons original omitted _ forward inverse _ _ tail =>
      ⟨original, omitted, forward, inverse⟩ :: tail.stateAgreements

/-- The extracted agreements retain exactly the suffix's effects in order. -/
theorem inverseAgreements_effects
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) :
    trace.inverseAgreements.map LaterInverseAgreement.effect = effects := by
  induction trace with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ induction =>
      simp [inverseAgreements, induction]

/-- Every suffix occurrence has an explicit agreement carrying both application states and the
equality of the inverse yielded there.
-/
theorem suffix_occurrence_has_inverseAgreement
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) {effect : Cordis.Effect State}
    (member : effect ∈ effects) :
    ∃ agreement, agreement ∈ trace.inverseAgreements ∧
      agreement.effect = effect ∧
      (agreement.effect agreement.originalBefore).undo =
        (agreement.effect agreement.omittedBefore).undo := by
  induction trace with
  | nil => simp at member
  | cons original omitted head forward inverse independent inverseSame tail induction =>
      simp only [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst effect
        exact ⟨⟨head, original, omitted, inverseSame⟩, by simp [inverseAgreements], rfl,
          inverseSame⟩
      · obtain ⟨agreement, agreementMember, effectEqual, inverseEqual⟩ :=
          induction tailMember
        exact ⟨agreement, by simp [inverseAgreements, agreementMember], effectEqual,
          inverseEqual⟩

/-- One state agreement is retained before every suffix effect and one at the final endpoint. -/
theorem stateAgreements_length
    {target : Cordis.Effect State} {targetSeed original omitted : State}
    {effects : List (Cordis.Effect State)} {finalOriginal finalOmitted : State}
    (trace : RemovalTrace target targetSeed original omitted effects
      finalOriginal finalOmitted) :
    trace.stateAgreements.length = effects.length + 1 := by
  induction trace with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ induction =>
      simp [stateAgreements, induction, Nat.add_assoc]

end RemovalTrace

/-!
## Building the removal trace from Definition 19 independence
-/

/-- Advance the Theorem 20 invariant through one foreign effect. -/
theorem RemovalTrace.step
    (target : Cordis.Effect State) (targetSeed original omitted : State)
    (effect : Cordis.Effect State)
    (forward_relation : original = (target omitted).after)
    (target_inverse_relation : (target targetSeed).undo original = omitted)
    (independent : Transformation.Independent target effect) :
    original = (target omitted).after ∧
      (target targetSeed).undo original = omitted ∧
      (effect original).undo = (effect omitted).undo ∧
      (effect original).after = (target (effect omitted).after).after ∧
      (target targetSeed).undo (effect original).after = (effect omitted).after := by
  let targetForward : Transformation.Endomorphism State := fun state ↦ (target state).after
  let effectForward : Transformation.Endomorphism State := fun state ↦ (effect state).after
  have inverseSame : (effect original).undo = (effect omitted).undo := by
    have stable := independent.second_inverse_stable
      (Transformation.Closure.generator
        (Transformation.EffectGenerator.forward :
          Transformation.EffectGenerator target targetForward)) omitted
    rw [forward_relation]
    exact stable
  have forwardsCommute := independent.transformations_commute
    (Transformation.Closure.generator
      (Transformation.EffectGenerator.forward :
        Transformation.EffectGenerator target targetForward))
    (Transformation.Closure.generator
      (Transformation.EffectGenerator.forward :
        Transformation.EffectGenerator effect effectForward))
  have nextForward :
      (effect original).after = (target (effect omitted).after).after := by
    rw [forward_relation]
    exact (forwardsCommute omitted).symm
  have inverseCommutes := independent.transformations_commute
    (Transformation.Closure.generator
      (Transformation.EffectGenerator.inverse targetSeed :
        Transformation.EffectGenerator target (target targetSeed).undo))
    (Transformation.Closure.generator
      (Transformation.EffectGenerator.forward :
        Transformation.EffectGenerator effect effectForward))
  have nextInverse :
      (target targetSeed).undo (effect original).after = (effect omitted).after := by
    exact Eq.trans (inverseCommutes original)
      (congrArg effectForward target_inverse_relation)
  exact ⟨forward_relation, target_inverse_relation, inverseSame, nextForward, nextInverse⟩

/-- Build Theorem 20's paired trace for an arbitrary finite foreign suffix. -/
def buildRemovalTrace
    (target : Cordis.Effect State) (targetSeed original omitted : State)
    (effects : List (Cordis.Effect State))
    (independent : IndependentOf target effects)
    (forward_relation : original = (target omitted).after)
    (target_inverse_relation : (target targetSeed).undo original = omitted) :
    RemovalTrace target targetSeed original omitted effects
      (runState effects original) (runState effects omitted) :=
  match effects with
  | [] => .nil original omitted forward_relation target_inverse_relation
  | effect :: rest =>
      let headIndependent := independent effect (by simp)
      let advanced := RemovalTrace.step target targetSeed original omitted effect
        forward_relation target_inverse_relation headIndependent
      .cons original omitted effect advanced.1 advanced.2.1 headIndependent advanced.2.2.1
        (buildRemovalTrace target targetSeed (effect original).after (effect omitted).after rest
          (fun candidate member ↦ independent candidate (by simp [member]))
          advanced.2.2.2.1 advanced.2.2.2.2)

/-- The canonical Theorem 20 trace starts immediately after the target application. -/
def removalTrace (target : Cordis.Effect State) (targetSeed : State)
    (suffix : List (Cordis.Effect State)) (independent : IndependentOf target suffix) :
    RemovalTrace target targetSeed (target targetSeed).after targetSeed suffix
      (runState suffix (target targetSeed).after) (runState suffix targetSeed) :=
  buildRemovalTrace target targetSeed (target targetSeed).after targetSeed suffix independent
    rfl (target targetSeed).undo_after

/-- Theorem 20(1), first equation, for a target/prefix/suffix decomposition. -/
theorem removal_forward_relation
    (prefixEffects : List (Cordis.Effect State)) (target : Cordis.Effect State)
    (suffix : List (Cordis.Effect State)) (initial : State)
    (independent : IndependentOf target suffix) :
    let targetSeed := runState prefixEffects initial
    runState suffix (target targetSeed).after =
      (target (runState suffix targetSeed)).after :=
  (removalTrace target (runState prefixEffects initial) suffix independent).final_forward_relation

/-- Theorem 20(1), removal equation: the retained target inverse reaches the omitted run. -/
theorem removal_inverse_relation
    (prefixEffects : List (Cordis.Effect State)) (target : Cordis.Effect State)
    (suffix : List (Cordis.Effect State)) (initial : State)
    (independent : IndependentOf target suffix) :
    let targetSeed := runState prefixEffects initial
    (target targetSeed).undo (runState suffix (target targetSeed).after) =
      runState suffix targetSeed :=
  (removalTrace target (runState prefixEffects initial) suffix independent)
    |>.final_target_inverse_relation

/-- Theorem 20(2): every later effect yields the same inverse in original and omitted runs. -/
theorem later_inverses_unchanged
    (target : Cordis.Effect State) (targetSeed : State)
    (suffix : List (Cordis.Effect State)) (independent : IndependentOf target suffix) :
    let trace := removalTrace target targetSeed suffix independent
    trace.inverseAgreements.map LaterInverseAgreement.effect = suffix ∧
      ∀ agreement, agreement ∈ trace.inverseAgreements →
        (agreement.effect agreement.originalBefore).undo =
          (agreement.effect agreement.omittedBefore).undo := by
  let trace := removalTrace target targetSeed suffix independent
  exact ⟨trace.inverseAgreements_effects, fun agreement _ ↦ agreement.inverse_eq⟩

/-!
## Corollary 21: arbitrary order of the retained inverses
-/

/-- Apply state transformations from left to right. -/
def applyMaps : List (State → State) → State → State
  | [], state => state
  | map :: rest, state => applyMaps rest (map state)

@[simp]
theorem applyMaps_nil (state : State) : applyMaps [] state = state := rfl

@[simp]
theorem applyMaps_cons (map : State → State) (rest : List (State → State))
    (state : State) : applyMaps (map :: rest) state = applyMaps rest (map state) := rfl

theorem applyMaps_append (first second : List (State → State)) (state : State) :
    applyMaps (first ++ second) state = applyMaps second (applyMaps first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons map rest induction =>
      simp only [List.cons_append, applyMaps_cons]
      exact induction (map state)

/-- Every pair of maps drawn from one finite family commutes. -/
structure CommutingMaps (maps : List (State → State)) : Prop where
  commute : ∀ {left}, left ∈ maps → ∀ {right}, right ∈ maps →
    Transformation.Commutes left right

namespace CommutingMaps

theorem tail {head : State → State} {maps : List (State → State)}
    (family : CommutingMaps (head :: maps)) : CommutingMaps maps where
  commute := by
    intro left leftMember right rightMember
    exact family.commute (by simp [leftMember]) (by simp [rightMember])

theorem permute {first second : List (State → State)}
    (family : CommutingMaps first) (permutation : first.Perm second) :
    CommutingMaps second where
  commute := by
    intro left leftMember right rightMember
    exact family.commute (permutation.mem_iff.mpr leftMember)
      (permutation.mem_iff.mpr rightMember)

end CommutingMaps

/-- Applying a commuting finite map family is invariant under arbitrary permutation. -/
theorem applyMaps_eq_of_perm
    {first second : List (State → State)} (permutation : first.Perm second)
    (family : CommutingMaps first) (state : State) :
    applyMaps first state = applyMaps second state := by
  induction permutation generalizing state with
  | nil => rfl
  | cons head permutation induction =>
      exact induction family.tail (head state)
  | swap left right rest =>
      simp only [applyMaps_cons]
      exact congrArg (applyMaps rest) (family.commute (by simp) (by simp) state)
  | trans firstPermutation secondPermutation firstInduction secondInduction =>
      exact (firstInduction family state).trans
        (secondInduction (family.permute firstPermutation) state)

/-- The retained LIFO inverse order always recovers the exact initial state. -/
theorem reverse_yieldedInverses_recovers
    (effects : List (Cordis.Effect State)) (before : State) :
    applyMaps (yieldedInverses effects before).reverse (runState effects before) = before := by
  induction effects generalizing before with
  | nil => rfl
  | cons effect rest induction =>
      rw [yieldedInverses_cons, List.reverse_cons, applyMaps_append, runState_cons]
      rw [induction (effect before).after]
      exact (effect before).undo_after

/-!
## Commutation of all retained inverse functions
-/

/-- The head effect's retained inverse commutes with every inverse yielded by an independent
suffix.
-/
theorem headInverse_commutes_yielded
    (head : Cordis.Effect State) (headSeed : State)
    (effects : List (Cordis.Effect State)) (before : State)
    (independent : IndependentOf head effects)
    {map : State → State} (member : map ∈ yieldedInverses effects before) :
    Transformation.Commutes (head headSeed).undo map := by
  induction effects generalizing before map with
  | nil => simp at member
  | cons effect rest induction =>
      simp only [yieldedInverses_cons, List.mem_cons] at member
      rcases member with equal | tailMember
      · subst map
        exact (independent effect (by simp)).transformations_commute
          (Transformation.Closure.generator
            (Transformation.EffectGenerator.inverse headSeed))
          (Transformation.Closure.generator
            (Transformation.EffectGenerator.inverse before :
              Transformation.EffectGenerator effect (effect before).undo))
      · exact induction (effect before).after
          (fun candidate candidateMember ↦ independent candidate (by simp [candidateMember]))
          tailMember

/-- Pairwise-independent effects yield a fully commuting retained inverse family. -/
theorem yieldedInverses_commuting
    (effects : List (Cordis.Effect State)) (before : State)
    (pairwise : PairwiseIndependent effects) :
    CommutingMaps (yieldedInverses effects before) := by
  induction effects generalizing before with
  | nil =>
      exact ⟨by simp⟩
  | cons effect rest induction =>
      let tailFamily := induction (effect before).after pairwise.tail
      constructor
      intro left leftMember right rightMember
      simp only [yieldedInverses_cons, List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftTail
      · rcases rightMember with rfl | rightTail
        · exact fun _ ↦ rfl
        · exact headInverse_commutes_yielded effect before rest (effect before).after
            pairwise.head rightTail
      · rcases rightMember with rfl | rightTail
        · exact (headInverse_commutes_yielded effect before rest (effect before).after
            pairwise.head leftTail).symm
        · exact tailFamily.commute leftTail rightTail

/-- Corollary 21: every permutation of the originally yielded inverses reaches the initial state. -/
theorem inverse_permutation_recovers
    (effects : List (Cordis.Effect State)) (before : State)
    (pairwise : PairwiseIndependent effects) (order : List (State → State))
    (permutation : (yieldedInverses effects before).Perm order) :
    applyMaps order (runState effects before) = before := by
  let inverses := yieldedInverses effects before
  have orderToReverse : order.Perm inverses.reverse :=
    permutation.symm.trans (List.reverse_perm inverses).symm
  have orderFamily := (yieldedInverses_commuting effects before pairwise).permute permutation
  exact Eq.trans
    (applyMaps_eq_of_perm orderToReverse orderFamily (runState effects before))
    (reverse_yieldedInverses_recovers effects before)

/-!
## Three-effect example
-/

namespace Example

open Cordis.Schedule

theorem independentXY : Transformation.Independent exampleX exampleY := by
  apply Transformation.Independent.of_generators
  · intro left right leftGenerated rightGenerated state
    cases leftGenerated <;> cases rightGenerated <;> cases state <;> rfl
  · intro map generated state
    cases generated <;> rfl
  · intro map generated state
    cases generated <;> rfl

theorem independentXZ : Transformation.Independent exampleX exampleZ := by
  apply Transformation.Independent.of_generators
  · intro left right leftGenerated rightGenerated state
    cases leftGenerated <;> cases rightGenerated <;> cases state <;> rfl
  · intro map generated state
    cases generated <;> rfl
  · intro map generated state
    cases generated <;> rfl

theorem independentYZ : Transformation.Independent exampleY exampleZ := by
  apply Transformation.Independent.of_generators
  · intro left right leftGenerated rightGenerated state
    cases leftGenerated <;> cases rightGenerated <;> cases state <;> rfl
  · intro map generated state
    cases generated <;> rfl
  · intro map generated state
    cases generated <;> rfl

def effects : List (Cordis.Effect Triple) := [exampleX, exampleY, exampleZ]

theorem pairwise : PairwiseIndependent effects := by
  change IndependentOf exampleX [exampleY, exampleZ] ∧
    PairwiseIndependent [exampleY, exampleZ]
  refine ⟨?_, ?_⟩
  · intro effect member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact independentXY
    · exact independentXZ
  · refine ⟨?_, ?_⟩
    · intro effect member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl
      exact independentYZ
    · exact ⟨fun _ member ↦ by simp at member, trivial⟩

def initial : Triple := { x := 10, y := 20, z := 30 }

def inverseX : Triple → Triple := (exampleX initial).undo
def afterX : Triple := (exampleX initial).after
def inverseY : Triple → Triple := (exampleY afterX).undo
def afterY : Triple := (exampleY afterX).after
def inverseZ : Triple → Triple := (exampleZ afterY).undo

def inverseOrder : List (Triple → Triple) := [inverseY, inverseX, inverseZ]

theorem retained_inverses : yieldedInverses effects initial = [inverseX, inverseY, inverseZ] :=
  rfl

theorem inverseOrder_permutation : (yieldedInverses effects initial).Perm inverseOrder := by
  rw [retained_inverses]
  exact (List.Perm.swap inverseX inverseY [inverseZ]).symm

/-- A non-LIFO inverse order still recovers the initial state. -/
example : applyMaps inverseOrder (runState effects initial) = initial :=
  inverse_permutation_recovers effects initial pairwise inverseOrder inverseOrder_permutation

/-- Removing the middle effect after the final state preserves the later `z` contribution. -/
example :
    inverseY (runState [exampleZ] (exampleY afterX).after) =
      runState [exampleZ] afterX :=
  removal_inverse_relation [exampleX] exampleY [exampleZ] initial
    (fun effect member ↦ by
      simp only [List.mem_singleton] at member
      subst effect
      exact independentYZ)

end Example

end Cordis.Removal
