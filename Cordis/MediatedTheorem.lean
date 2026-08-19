import Cordis.MediatedIndependence

/-!
# Finite whole-run mediated independence

This module continues the bounded proof of CORDIS Theorem 42 at paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

It proves that the non-circular `PairwiseOverlap` hypothesis restricts to every heterogeneous
continuation and implies exact interchange of the two complete finite execution orders. It also
identifies that the earlier closure API is too strong for partial computations because it
compares their individual domains instead of the domains of the two composite orders.

The first step is primitive interchange: promoting the existing finite key-word certificate to
equality of two dependent singleton-stage applications, including their totalized lifted
inverses on absent current bindings. `stageInterchangeComplete` proves that promotion. The
proof then retains typed outcomes explicitly and bubbles each root through every selected foreign
continuation to establish the complete whole-run result.

`BoundedPartialIndependence` corrects that issue by comparing `left; right` with `right; left`
directly while retaining conditional stability of the complete inverses yielded by the two
computations. It is a whole-run finite proxy, not the paper's full transformation-monoid
Definition 19 or the unrestricted statement of Theorem 42. Unit is proved as both a left and
right identity.
-/

set_option autoImplicit false

namespace Cordis.MediatedTheorem

open Cordis.MediatedIndependence

universe u v w

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

variable {coeffects : CoeffectFamily.{u, v, w} Key Value}

/-!
## All-outcome restriction of the overlap hypothesis
-/

/-- Restrict cross-stage overlap to one left continuation selected by any typed outcome. -/
theorem PairwiseOverlap.left_continuation
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects}
    {right : OperationIndependence.Computation coeffects}
    (overlap : PairwiseOverlap coeffects (.step key op input next) right)
    (outcome : (coeffects key).Outcome op) :
    PairwiseOverlap coeffects (next outcome) right := by
  intro leftStage rightStage leftOccurs rightOccurs
  exact overlap leftStage rightStage (.continuation outcome leftOccurs) rightOccurs

/-- Restrict cross-stage overlap to one right continuation selected by any typed outcome. -/
theorem PairwiseOverlap.right_continuation
    {left : OperationIndependence.Computation coeffects}
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects}
    (overlap : PairwiseOverlap coeffects left (.step key op input next))
    (outcome : (coeffects key).Outcome op) :
    PairwiseOverlap coeffects left (next outcome) := by
  intro leftStage rightStage leftOccurs rightOccurs
  exact overlap leftStage rightStage leftOccurs (.continuation outcome rightOccurs)

/-- The two root stages inherit the complete finite Definition 39 key certificate. -/
theorem PairwiseOverlap.roots
    {leftKey : Key} {leftOp : (coeffects leftKey).Op}
    {leftInput : (coeffects leftKey).Input leftOp} {leftNext}
    {rightKey : Key} {rightOp : (coeffects rightKey).Op}
    {rightInput : (coeffects rightKey).Input rightOp} {rightNext}
    (overlap : PairwiseOverlap coeffects
      (.step leftKey leftOp leftInput leftNext)
      (.step rightKey rightOp rightInput rightNext)) :
    OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey :=
  overlap ⟨leftKey, leftOp, leftInput⟩ ⟨rightKey, rightOp, rightInput⟩
    (.root leftKey leftOp leftInput leftNext)
    (.root rightKey rightOp rightInput rightNext)

/-!
## Corrected closure for partial computations
-/

/-- Execute two partial mediated computations in order and compose their retained inverses. -/
def runSequential
    (left right : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value) :
    Option (Cordis.Applied (Coeffect.Context Key Value) before) :=
  match left.run coeffects before with
  | none => none
  | some leftApplied =>
      match right.run coeffects leftApplied.after with
      | none => none
      | some rightApplied => some (composeApplied leftApplied rightApplied)

/-- Independence for partial computations compares the two composite orders directly.

Individual computations need not have equal domains. The requirement is that `left; right` and
`right; left` agree on definedness and, when defined, on successor and complete inverse action.
-/
structure BoundedPartialIndependence
    (left right : OperationIndependence.Computation coeffects) : Prop where
  orders_agree : ∀ before,
    match runSequential left right before, runSequential right left before with
    | none, none => True
    | some leftThenRight, some rightThenLeft =>
        leftThenRight.after = rightThenLeft.after ∧
          ∀ current, leftThenRight.undo current = rightThenLeft.undo current
    | _, _ => False
  yielded_inverse_stable : ∀ before leftApplied rightApplied,
    left.run coeffects before = some leftApplied →
    right.run coeffects before = some rightApplied →
    (∀ current,
      leftApplied.undo current =
        (match left.run coeffects rightApplied.after with
        | some moved => moved.undo current
        | none => leftApplied.undo current)) ∧
    (∀ current,
      rightApplied.undo current =
        (match right.run coeffects leftApplied.after with
        | some moved => moved.undo current
        | none => rightApplied.undo current))

/-- Observational version of the corrected partial closure. -/
structure BoundedPartialObservationalIndependence
    (left right : OperationIndependence.Computation coeffects) : Prop where
  orders_related : ∀ before,
    match runSequential left right before, runSequential right left before with
    | none, none => True
    | some leftThenRight, some rightThenLeft =>
        Coeffect.Observational.Related
          (Coeffect.Observational.equivalencesOf coeffects)
          leftThenRight.after rightThenLeft.after ∧
        ∀ current,
          Coeffect.Observational.Related
            (Coeffect.Observational.equivalencesOf coeffects)
            (leftThenRight.undo current) (rightThenLeft.undo current)
    | _, _ => False
  yielded_inverse_related : ∀ before leftApplied rightApplied,
    left.run coeffects before = some leftApplied →
    right.run coeffects before = some rightApplied →
    (∀ current,
      Coeffect.Observational.Related
        (Coeffect.Observational.equivalencesOf coeffects)
        (leftApplied.undo current)
        (match left.run coeffects rightApplied.after with
        | some moved => moved.undo current
        | none => leftApplied.undo current)) ∧
    (∀ current,
      Coeffect.Observational.Related
        (Coeffect.Observational.equivalencesOf coeffects)
        (rightApplied.undo current)
        (match right.run coeffects leftApplied.after with
        | some moved => moved.undo current
        | none => rightApplied.undo current))

@[simp]
theorem composeApplied_identity_right
    {before : Coeffect.Context Key Value}
    (applied : Cordis.Applied (Coeffect.Context Key Value) before) :
    composeApplied applied (Cordis.Effect.identity applied.after) = applied := by
  apply Cordis.Applied.ext
  · rfl
  · funext current
    rfl

@[simp]
theorem composeApplied_identity_left
    {before : Coeffect.Context Key Value}
    (applied : Cordis.Applied (Coeffect.Context Key Value) before) :
    composeApplied (Cordis.Effect.identity before) applied = applied := by
  apply Cordis.Applied.ext
  · rfl
  · funext current
    rfl

theorem runSequential_pure_right
    (computation : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value) :
    runSequential computation .pure before = computation.run coeffects before := by
  unfold runSequential
  cases run : computation.run coeffects before with
  | none => rfl
  | some applied =>
      change some (composeApplied applied (Cordis.Effect.identity applied.after)) = some applied
      simp

theorem runSequential_pure_left
    (computation : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value) :
    runSequential .pure computation before = computation.run coeffects before := by
  unfold runSequential
  rw [OperationIndependence.Computation.run.eq_1]
  simp only [Cordis.Effect.identity]
  cases run : computation.run coeffects before with
  | none => rfl
  | some applied =>
      apply congrArg some
      exact composeApplied_identity_left applied

/-- Unit is a right identity for corrected partial mediated closure. -/
theorem partialClosure_pure_right
    (computation : OperationIndependence.Computation coeffects) :
    BoundedPartialIndependence computation .pure := by
  constructor
  intro before
  rw [runSequential_pure_right, runSequential_pure_left]
  cases computation.run coeffects before <;> simp
  · intro before leftApplied rightApplied leftRun rightRun
    change some (Cordis.Effect.identity before) = some rightApplied at rightRun
    have rightEqual := Option.some.inj rightRun
    subst rightApplied
    constructor
    · intro current
      simp only [Cordis.Effect.identity]
      rw [leftRun]
    · intro current
      rfl

/-- Unit is a left identity for corrected partial mediated closure. -/
theorem partialClosure_pure_left
    (computation : OperationIndependence.Computation coeffects) :
    BoundedPartialIndependence .pure computation := by
  constructor
  intro before
  rw [runSequential_pure_left, runSequential_pure_right]
  cases computation.run coeffects before <;> simp
  · intro before leftApplied rightApplied leftRun rightRun
    change some (Cordis.Effect.identity before) = some leftApplied at leftRun
    have leftEqual := Option.some.inj leftRun
    subst leftApplied
    constructor
    · intro current
      rfl
    · intro current
      simp only [Cordis.Effect.identity]
      rw [rightRun]

/-- Exact corrected closure implies the observational corrected closure. -/
theorem BoundedPartialIndependence.toObservational
    {left right : OperationIndependence.Computation coeffects}
    (closure : BoundedPartialIndependence left right) :
    BoundedPartialObservationalIndependence left right := by
  constructor
  intro before
  have exact := closure.orders_agree before
  cases leftRun : runSequential left right before with
  | none =>
      cases rightRun : runSequential right left before <;>
        simp [leftRun, rightRun] at exact ⊢
  | some leftApplied =>
      cases rightRun : runSequential right left before with
      | none => simp [leftRun, rightRun] at exact
      | some rightApplied =>
          simp [leftRun, rightRun] at exact ⊢
          constructor
          · rw [exact.1]
            exact Coeffect.Observational.related_refl
              (Coeffect.Observational.equivalencesOf coeffects) rightApplied.after
          · intro current
            rw [exact.2 current]
            exact Coeffect.Observational.related_refl
              (Coeffect.Observational.equivalencesOf coeffects) (rightApplied.undo current)
  · intro before leftApplied rightApplied leftRun rightRun
    have stable := closure.yielded_inverse_stable before leftApplied rightApplied
      leftRun rightRun
    constructor
    · intro current
      rw [← stable.1 current]
      exact Coeffect.Observational.related_refl
        (Coeffect.Observational.equivalencesOf coeffects) (leftApplied.undo current)
    · intro current
      rw [← stable.2 current]
      exact Coeffect.Observational.related_refl
        (Coeffect.Observational.equivalencesOf coeffects) (rightApplied.undo current)

/-- Unit is a right identity for corrected observational closure. -/
theorem partialObservationalClosure_pure_right
    (computation : OperationIndependence.Computation coeffects) :
    BoundedPartialObservationalIndependence computation .pure :=
  (partialClosure_pure_right computation).toObservational

/-- Unit is a left identity for corrected observational closure. -/
theorem partialObservationalClosure_pure_left
    (computation : OperationIndependence.Computation coeffects) :
    BoundedPartialObservationalIndependence .pure computation :=
  (partialClosure_pure_left computation).toObservational

/-!
## Primitive-stage interchange
-/

def singleton
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op) :
    OperationIndependence.Computation coeffects :=
  .step key op input (fun _ ↦ .pure)

def forwardWord
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op) :
    OperationalEquivalence.Test (coeffects key) := [.forward op input]

/-- Dropping proof and inverse data from one singleton computation recovers its finite-word
context transformation.
-/
theorem singleton_run_after
    (key : Key) (op : (coeffects key).Op)
    (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value) :
    ((singleton key op input).run coeffects before).map Cordis.Applied.after =
      OperationIndependence.transformAt coeffects key (forwardWord key op input) before := by
  simp [singleton, forwardWord,
    OperationIndependence.Computation.run.eq_2,
    OperationIndependence.transformAt, OperationIndependence.localTransition,
    OperationIndependence.runLocal, OperationIndependence.applyLocal,
    Cordis.Effect.identity]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

/-- Dropping inverse data from two singleton computations yields the two lifted forward words. -/
theorem runSequential_singletons_after
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (before : Coeffect.Context Key Value) :
    (runSequential (singleton leftKey leftOp leftInput)
      (singleton rightKey rightOp rightInput) before).map Cordis.Applied.after =
      (OperationIndependence.transformAt coeffects leftKey
        (forwardWord leftKey leftOp leftInput) before).bind
        (OperationIndependence.transformAt coeffects rightKey
          (forwardWord rightKey rightOp rightInput)) := by
  cases leftRun : (singleton leftKey leftOp leftInput).run coeffects before with
  | none =>
      have leftTransform := singleton_run_after leftKey leftOp leftInput before
      rw [leftRun] at leftTransform
      have leftNone : OperationIndependence.transformAt coeffects leftKey
          (forwardWord leftKey leftOp leftInput) before = none := leftTransform.symm
      simp [runSequential, leftRun, leftNone]
  | some leftApplied =>
      have leftTransform := singleton_run_after leftKey leftOp leftInput before
      rw [leftRun] at leftTransform
      have leftSome : OperationIndependence.transformAt coeffects leftKey
          (forwardWord leftKey leftOp leftInput) before = some leftApplied.after :=
        leftTransform.symm
      cases rightRun : (singleton rightKey rightOp rightInput).run coeffects
        leftApplied.after with
      | none =>
          have rightTransform := singleton_run_after rightKey rightOp rightInput
            leftApplied.after
          rw [rightRun] at rightTransform
          have rightNone : OperationIndependence.transformAt coeffects rightKey
              (forwardWord rightKey rightOp rightInput) leftApplied.after = none :=
            rightTransform.symm
          simp [runSequential, leftRun, rightRun, leftSome, rightNone]
      | some rightApplied =>
          have rightTransform := singleton_run_after rightKey rightOp rightInput
            leftApplied.after
          rw [rightRun] at rightTransform
          have rightSome : OperationIndependence.transformAt coeffects rightKey
              (forwardWord rightKey rightOp rightInput) leftApplied.after =
                some rightApplied.after := rightTransform.symm
          simp [runSequential, leftRun, rightRun, leftSome, rightSome, composeApplied]

/-- The totalized lifted inverse is identity when its dependent binding is absent. -/
theorem undoAt_of_none
    {key : Key} {before : Value key} (applied : Cordis.Applied (Value key) before)
    (current : Coeffect.Context Key Value) (lookup : current key = none) :
    Coeffect.Quotient.undoAt applied current = current := by
  simp [Coeffect.Quotient.undoAt, lookup]

/-- The totalized lifted inverse updates exactly one present dependent binding. -/
theorem undoAt_of_some
    {key : Key} {before : Value key} (applied : Cordis.Applied (Value key) before)
    (current : Coeffect.Context Key Value) (value : Value key)
    (lookup : current key = some value) :
    Coeffect.Quotient.undoAt applied current =
      Coeffect.setAt current key (applied.undo value) := by
  simp [Coeffect.Quotient.undoAt, lookup]

/-- Two concrete yielded inverses commute after lifting when their key-word certificate says
their inverse generators commute.
-/
theorem liftedInverses_commute
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp) (leftSeed : Value leftKey)
    (leftEnabled : (coeffects leftKey).Enabled leftOp leftInput leftSeed)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp) (rightSeed : Value rightKey)
    (rightEnabled : (coeffects rightKey).Enabled rightOp rightInput rightSeed)
    (independent : OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey)
    (current : Coeffect.Context Key Value) :
    Coeffect.Quotient.undoAt
        ((coeffects leftKey).run leftOp leftInput leftSeed leftEnabled).1
        (Coeffect.Quotient.undoAt
          ((coeffects rightKey).run rightOp rightInput rightSeed rightEnabled).1 current) =
      Coeffect.Quotient.undoAt
        ((coeffects rightKey).run rightOp rightInput rightSeed rightEnabled).1
        (Coeffect.Quotient.undoAt
          ((coeffects leftKey).run leftOp leftInput leftSeed leftEnabled).1 current) := by
  let leftWord : OperationalEquivalence.Test (coeffects leftKey) :=
    [.inverse leftOp leftInput leftSeed leftEnabled]
  let rightWord : OperationalEquivalence.Test (coeffects rightKey) :=
    [.inverse rightOp rightInput rightSeed rightEnabled]
  have commute := independent.words_commute leftWord rightWord current
  by_cases same : leftKey = rightKey
  · subst rightKey
    cases lookup : current leftKey with
    | none => simp [Coeffect.Quotient.undoAt, lookup]
    | some value =>
        simp [OperationIndependence.transformAt, OperationIndependence.applyLocal,
          OperationIndependence.localTransition, OperationIndependence.runLocal,
          leftWord, rightWord, Coeffect.Quotient.undoAt, lookup] at commute ⊢
        exact commute.symm
  · cases leftLookup : current leftKey with
    | none =>
        cases rightLookup : current rightKey with
        | none => simp [Coeffect.Quotient.undoAt, leftLookup, rightLookup]
        | some rightValue =>
            simp [Coeffect.Quotient.undoAt, leftLookup, rightLookup,
              Coeffect.setAt_other, same]
    | some leftValue =>
        cases rightLookup : current rightKey with
        | none =>
            simp [Coeffect.Quotient.undoAt, leftLookup, rightLookup,
              Coeffect.setAt_other, Ne.symm same]
        | some rightValue =>
            simp [OperationIndependence.transformAt, OperationIndependence.applyLocal,
              OperationIndependence.localTransition, OperationIndependence.runLocal,
              leftWord, rightWord, Coeffect.Quotient.undoAt, leftLookup, rightLookup,
              Coeffect.setAt_other, same, Ne.symm same] at commute ⊢
            exact commute.symm

/-- Lift a `ForwardData` inverse to the totalized whole-context behavior of `CoeffectAt.lift`. -/
def liftDataUndo (key : Key) {op : (coeffects key).Op}
    (data : OperationIndependence.ForwardData (coeffects key) op)
    (current : Coeffect.Context Key Value) : Coeffect.Context Key Value :=
  match current key with
  | none => current
  | some value => Coeffect.setAt current key (data.undo value)

/-- Seed/enabled witness retained from one successful singleton stage. -/
structure SingletonWitness
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value)
    (applied : Cordis.Applied (Coeffect.Context Key Value) before) where
  seed : Value key
  lookup : before key = some seed
  enabled : (coeffects key).Enabled op input seed
  after_eq : applied.after = Coeffect.setAt before key
    ((coeffects key).run op input seed enabled).1.after
  undo_eq : applied.undo = fun current ↦
    Coeffect.Quotient.undoAt ((coeffects key).run op input seed enabled).1 current

/-- A successful singleton run exposes exactly the `ForwardData` inspected at its start. -/
theorem singleton_run_has_data
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value)
    (applied : Cordis.Applied (Coeffect.Context Key Value) before)
    (ran : (singleton key op input).run coeffects before = some applied) :
    ∃ data, OperationIndependence.inspectForwardAt coeffects key op input before = some data ∧
      applied.after = Coeffect.setAt before key data.after ∧
      applied.undo = liftDataUndo key data := by
  simp [singleton, OperationIndependence.Computation.run.eq_2] at ran
  split at ran
  · contradiction
  · rename_i value lookup
    split at ran
    · rename_i enabled
      have appliedEqual := Option.some.inj ran
      subst applied
      let data : OperationIndependence.ForwardData (coeffects key) op :=
        ⟨((coeffects key).run op input value enabled).1.after,
          ((coeffects key).run op input value enabled).1.undo,
          ((coeffects key).run op input value enabled).2⟩
      refine ⟨data, ?_, rfl, ?_⟩
      · simp [OperationIndependence.inspectForwardAt, lookup, enabled, data]
      · funext current
        change
          (match current key with
          | none => current
          | some currentValue =>
              Coeffect.setAt current key
                (((coeffects key).run op input value enabled).1.undo currentValue)) = _
        rfl
    · contradiction

/-- A successful singleton run retains the exact local seed and enabledness witness needed to
identify the state-dependent inverse it yielded.
-/
def singleton_run_has_witness
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value)
    (applied : Cordis.Applied (Coeffect.Context Key Value) before)
    (ran : (singleton key op input).run coeffects before = some applied) :
    SingletonWitness key op input before applied := by
  simp [singleton, OperationIndependence.Computation.run.eq_2] at ran
  split at ran
  · contradiction
  · rename_i value lookup
    split at ran
    · rename_i enabled
      have appliedEqual := Option.some.inj ran
      subst applied
      exact {
        seed := value
        lookup := lookup
        enabled := enabled
        after_eq := rfl
        undo_eq := by
          funext current
          rfl
      }
    · contradiction

/-- One enabled root stage, retaining the dependent seed and exact typed outcome. -/
structure EnabledStage
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value) where
  seed : Value key
  lookup : before key = some seed
  enabled : (coeffects key).Enabled op input seed

namespace EnabledStage

/-- The exact lifted application retained by an enabled stage. -/
def applied
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : EnabledStage (coeffects := coeffects) key op input before) :
    Cordis.Applied (Coeffect.Context Key Value) before :=
  (stageResult coeffects key op input before stage.seed stage.lookup stage.enabled).1

/-- The heterogeneous outcome that chooses this stage's continuation. -/
def outcome
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : EnabledStage (coeffects := coeffects) key op input before) :
    (coeffects key).Outcome op :=
  (stageResult coeffects key op input before stage.seed stage.lookup stage.enabled).2

/-- The local successor, yielded inverse, and outcome retained together. -/
def data
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : EnabledStage (coeffects := coeffects) key op input before) :
    OperationIndependence.ForwardData (coeffects key) op :=
  ⟨((coeffects key).run op input stage.seed stage.enabled).1.after,
    ((coeffects key).run op input stage.seed stage.enabled).1.undo,
    ((coeffects key).run op input stage.seed stage.enabled).2⟩

/-- Inspecting an enabled stage recovers its retained local data exactly. -/
theorem inspect_eq_some
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : EnabledStage (coeffects := coeffects) key op input before) :
    OperationIndependence.inspectForwardAt coeffects key op input before = some stage.data := by
  simp [OperationIndependence.inspectForwardAt, stage.lookup, stage.enabled, data]

end EnabledStage

/-- A successful `step` split into its enabled root and selected successful continuation. -/
structure StepRunWitness
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value)
    (applied : Cordis.Applied (Coeffect.Context Key Value) before) where
  head : EnabledStage (coeffects := coeffects) key op input before
  tail : Cordis.Applied (Coeffect.Context Key Value) head.applied.after
  tail_run : (next head.outcome).run coeffects head.applied.after = some tail
  applied_eq : applied = composeApplied head.applied tail

/-- Every successful mediated step has a complete root/continuation witness. -/
def step_run_has_witness
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value)
    (applied : Cordis.Applied (Coeffect.Context Key Value) before)
    (ran : (OperationIndependence.Computation.step key op input next).run coeffects before =
      some applied) :
    StepRunWitness (coeffects := coeffects) key op input next before applied := by
  simp [OperationIndependence.Computation.run.eq_2] at ran
  split at ran
  · contradiction
  · rename_i value lookup
    split at ran
    · rename_i enabled
      split at ran
      · contradiction
      · rename_i continuation continuationRun
        have appliedEqual := Option.some.inj ran
        subst applied
        exact {
          head := ⟨value, lookup, enabled⟩
          tail := continuation
          tail_run := continuationRun
          applied_eq := rfl
        }
    · contradiction

/-- Reassemble a successful mediated step from an enabled head and its selected tail. -/
theorem step_run_of_enabled
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value)
    (head : EnabledStage (coeffects := coeffects) key op input before)
    (tail : Cordis.Applied (Coeffect.Context Key Value) head.applied.after)
    (tailRun : (next head.outcome).run coeffects head.applied.after = some tail) :
    (OperationIndependence.Computation.step key op input next).run coeffects before =
      some (composeApplied head.applied tail) := by
  rw [OperationIndependence.Computation.run.eq_2]
  split
  · rename_i absent
    rw [head.lookup] at absent
    contradiction
  · rename_i value lookup
    have valueEqual : value = head.seed := Option.some.inj (lookup.symm.trans head.lookup)
    subst value
    simp only
    split
    · rename_i enabled
      unfold EnabledStage.applied EnabledStage.outcome stageResult at tailRun
      unfold EnabledStage.applied stageResult at ⊢
      rw [tailRun]
      rfl
    · rename_i disabled
      exact False.elim (disabled head.enabled)

/-- An enabled root followed by unit runs as exactly its lifted application. -/
theorem singleton_run_of_enabled
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value)
    (head : EnabledStage (coeffects := coeffects) key op input before) :
    (singleton key op input).run coeffects before = some head.applied := by
  have ran := step_run_of_enabled key op input (fun _ ↦ .pure) before head
    (Cordis.Effect.identity head.applied.after) rfl
  simpa [singleton] using ran

/-- A successful singleton application paired with the seed witness that recovers its typed
outcome. Keeping the returned `Applied` avoids transports across propositionally equal contexts.
-/
structure ExecutedStage
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value) where
  applied : Cordis.Applied (Coeffect.Context Key Value) before
  ran : (singleton key op input).run coeffects before = some applied
  witness : SingletonWitness key op input before applied

namespace ExecutedStage

/-- The enabled local stage underlying a successful singleton execution. -/
def enabledStage
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : ExecutedStage (coeffects := coeffects) key op input before) :
    EnabledStage (coeffects := coeffects) key op input before :=
  ⟨stage.witness.seed, stage.witness.lookup, stage.witness.enabled⟩

/-- The returned singleton application is exactly its underlying lifted application. -/
theorem applied_eq_enabledStage
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : ExecutedStage (coeffects := coeffects) key op input before) :
    stage.applied = stage.enabledStage.applied := by
  apply Cordis.Applied.ext
  · exact stage.witness.after_eq
  · exact stage.witness.undo_eq

/-- The heterogeneous outcome recovered from the exact singleton seed. -/
def outcome
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : ExecutedStage (coeffects := coeffects) key op input before) :
    (coeffects key).Outcome op :=
  ((coeffects key).run op input stage.witness.seed stage.witness.enabled).2

/-- The complete local forward data recovered from the exact singleton seed. -/
def data
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : ExecutedStage (coeffects := coeffects) key op input before) :
    OperationIndependence.ForwardData (coeffects key) op :=
  ⟨((coeffects key).run op input stage.witness.seed stage.witness.enabled).1.after,
    ((coeffects key).run op input stage.witness.seed stage.witness.enabled).1.undo,
    stage.outcome⟩

/-- Inspecting an executed singleton recovers its retained data exactly. -/
theorem inspect_eq_some
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : ExecutedStage (coeffects := coeffects) key op input before) :
    OperationIndependence.inspectForwardAt coeffects key op input before = some stage.data := by
  simp [OperationIndependence.inspectForwardAt, stage.witness.lookup, stage.witness.enabled,
    data, outcome]

end ExecutedStage

/-- Regard an enabled lifted root as its exact singleton execution. -/
def EnabledStage.toExecuted
    {key : Key} {op : (coeffects key).Op} {input : (coeffects key).Input op}
    {before : Coeffect.Context Key Value}
    (stage : EnabledStage (coeffects := coeffects) key op input before) :
    ExecutedStage (coeffects := coeffects) key op input before :=
  {
    applied := stage.applied
    ran := singleton_run_of_enabled key op input before stage
    witness := {
      seed := stage.seed
      lookup := stage.lookup
      enabled := stage.enabled
      after_eq := rfl
      undo_eq := rfl
    }
  }

/-- Inspecting a forward result and retaining only its successor is the singleton word
transformation.
-/
theorem inspectForward_transform
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value) :
    (OperationIndependence.inspectForwardAt coeffects key op input before).map
        (fun data ↦ Coeffect.setAt before key data.after) =
      OperationIndependence.transformAt coeffects key (forwardWord key op input) before := by
  simp [OperationIndependence.inspectForwardAt, OperationIndependence.transformAt,
    OperationIndependence.applyLocal, OperationIndependence.localTransition,
    OperationIndependence.runLocal, forwardWord]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

/-- A successful inspection reconstructs a successful singleton application with the same
successor and totalized inverse.
-/
theorem singleton_run_of_inspect
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : Coeffect.Context Key Value)
    (data : OperationIndependence.ForwardData (coeffects key) op)
    (inspected : OperationIndependence.inspectForwardAt coeffects key op input before =
      some data) :
    ∃ applied, (singleton key op input).run coeffects before = some applied ∧
      applied.after = Coeffect.setAt before key data.after ∧
      applied.undo = liftDataUndo key data := by
  cases ran : (singleton key op input).run coeffects before with
  | none =>
      have runAfter := singleton_run_after key op input before
      rw [ran] at runAfter
      have inspectedAfter := inspectForward_transform key op input before
      rw [inspected] at inspectedAfter
      simp at runAfter inspectedAfter
      have impossible := runAfter.trans inspectedAfter.symm
      cases impossible
  | some applied =>
      obtain ⟨runData, runInspected, afterEqual, undoEqual⟩ :=
        singleton_run_has_data key op input before applied ran
      have dataEqual : runData = data := Option.some.inj (runInspected.symm.trans inspected)
      subst runData
      exact ⟨applied, rfl, afterEqual, undoEqual⟩

/-- Foreign singleton execution preserves the complete inverse yielded by the left stage. -/
theorem singleton_left_inverse_stable
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (independent : OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey)
    (before : Coeffect.Context Key Value)
    (leftApplied rightApplied : Cordis.Applied (Coeffect.Context Key Value) before)
    (leftRun : (singleton leftKey leftOp leftInput).run coeffects before = some leftApplied)
    (rightRun : (singleton rightKey rightOp rightInput).run coeffects before =
      some rightApplied) :
    leftApplied.undo =
      (match (singleton leftKey leftOp leftInput).run coeffects rightApplied.after with
      | some moved => moved.undo
      | none => leftApplied.undo) := by
  obtain ⟨leftData, leftInspected, leftAfter, leftUndo⟩ :=
    singleton_run_has_data leftKey leftOp leftInput before leftApplied leftRun
  have rightTransform := singleton_run_after rightKey rightOp rightInput before
  rw [rightRun] at rightTransform
  have rightWordRun : OperationIndependence.transformAt coeffects rightKey
      (forwardWord rightKey rightOp rightInput) before = some rightApplied.after :=
    rightTransform.symm
  have movedInspected := independent.left_data_stable leftOp leftInput
    (forwardWord rightKey rightOp rightInput) before rightApplied.after rightWordRun
  rw [leftInspected] at movedInspected
  obtain ⟨moved, movedRun, movedAfter, movedUndo⟩ :=
    singleton_run_of_inspect leftKey leftOp leftInput rightApplied.after leftData
      movedInspected
  rw [movedRun]
  exact leftUndo.trans movedUndo.symm

/-- Foreign singleton execution preserves the complete inverse yielded by the right stage. -/
theorem singleton_right_inverse_stable
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (independent : OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey)
    (before : Coeffect.Context Key Value)
    (leftApplied rightApplied : Cordis.Applied (Coeffect.Context Key Value) before)
    (leftRun : (singleton leftKey leftOp leftInput).run coeffects before = some leftApplied)
    (rightRun : (singleton rightKey rightOp rightInput).run coeffects before =
      some rightApplied) :
    rightApplied.undo =
      (match (singleton rightKey rightOp rightInput).run coeffects leftApplied.after with
      | some moved => moved.undo
      | none => rightApplied.undo) := by
  obtain ⟨rightData, rightInspected, rightAfter, rightUndo⟩ :=
    singleton_run_has_data rightKey rightOp rightInput before rightApplied rightRun
  have leftTransform := singleton_run_after leftKey leftOp leftInput before
  rw [leftRun] at leftTransform
  have leftWordRun : OperationIndependence.transformAt coeffects leftKey
      (forwardWord leftKey leftOp leftInput) before = some leftApplied.after :=
    leftTransform.symm
  have movedInspected := independent.right_data_stable rightOp rightInput
    (forwardWord leftKey leftOp leftInput) before leftApplied.after leftWordRun
  rw [rightInspected] at movedInspected
  obtain ⟨moved, movedRun, movedAfter, movedUndo⟩ :=
    singleton_run_of_inspect rightKey rightOp rightInput leftApplied.after rightData
      movedInspected
  rw [movedRun]
  exact rightUndo.trans movedUndo.symm

/-- Semantic interchange of two primitive Definition 41 stages before their continuations.

The certificate retains definedness, the common successor, and equality of the two complete
composed inverse functions. `StageInterchange` intentionally erases operation outcomes;
recursive use therefore also needs the separate outcome-alignment theorem below.
-/
def StageInterchange
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp) : Prop :=
  BoundedPartialIndependence
    (.step leftKey leftOp leftInput (fun _ ↦ .pure))
    (.step rightKey rightOp rightInput (fun _ ↦ .pure))

/-- The primitive promotion statement.

Every finite key-independence certificate derived by `PairwiseOverlap` furnishes the root
`StageInterchange` law. This alone is not recursive Theorem 42 because its result erases the
typed outcomes that select continuations.
-/
def StageInterchangeComplete
    (coeffects : CoeffectFamily.{u, v, w} Key Value) : Prop :=
  ∀ (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp),
    OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey →
    StageInterchange (coeffects := coeffects)
      leftKey leftOp leftInput rightKey rightOp rightInput

/-- Finite key-word independence promotes to complete primitive-stage interchange. -/
theorem stageInterchangeComplete : StageInterchangeComplete coeffects := by
  intro leftKey leftOp leftInput rightKey rightOp rightInput independent
  let left := singleton leftKey leftOp leftInput
  let right := singleton rightKey rightOp rightInput
  constructor
  · intro before
    change
      (match runSequential left right before, runSequential right left before with
      | none, none => True
      | some leftThenRight, some rightThenLeft =>
          leftThenRight.after = rightThenLeft.after ∧
            ∀ current, leftThenRight.undo current = rightThenLeft.undo current
      | _, _ => False)
    have mappedEqual :
        (runSequential left right before).map Cordis.Applied.after =
          (runSequential right left before).map Cordis.Applied.after := by
      calc
        _ = (OperationIndependence.transformAt coeffects leftKey
              (forwardWord leftKey leftOp leftInput) before).bind
              (OperationIndependence.transformAt coeffects rightKey
                (forwardWord rightKey rightOp rightInput)) :=
          runSequential_singletons_after leftKey leftOp leftInput rightKey rightOp
            rightInput before
        _ = (OperationIndependence.transformAt coeffects rightKey
              (forwardWord rightKey rightOp rightInput) before).bind
              (OperationIndependence.transformAt coeffects leftKey
                (forwardWord leftKey leftOp leftInput)) :=
          independent.words_commute _ _ before
        _ = _ :=
          (runSequential_singletons_after rightKey rightOp rightInput leftKey leftOp
            leftInput before).symm
    cases leftCompositeRun : runSequential left right before with
    | none =>
        cases rightCompositeRun : runSequential right left before with
        | none => exact True.intro
        | some rightComposite =>
            rw [leftCompositeRun, rightCompositeRun] at mappedEqual
            cases mappedEqual
    | some leftComposite =>
        cases rightCompositeRun : runSequential right left before with
        | none =>
            rw [leftCompositeRun, rightCompositeRun] at mappedEqual
            cases mappedEqual
        | some rightComposite =>
            rw [leftCompositeRun, rightCompositeRun] at mappedEqual
            have afterEqual := Option.some.inj mappedEqual
            cases leftInitialRun : left.run coeffects before with
            | none => simp [runSequential, leftInitialRun] at leftCompositeRun
            | some leftInitial =>
                cases rightMovedRun : right.run coeffects leftInitial.after with
                | none =>
                    simp [runSequential, leftInitialRun, rightMovedRun] at leftCompositeRun
                | some rightMoved =>
                    have leftCompositeEqual :
                        composeApplied leftInitial rightMoved = leftComposite := by
                      simpa [runSequential, leftInitialRun, rightMovedRun] using
                        Option.some.inj (congrArg some leftCompositeRun)
                    subst leftComposite
                    cases rightInitialRun : right.run coeffects before with
                    | none => simp [runSequential, rightInitialRun] at rightCompositeRun
                    | some rightInitial =>
                        cases leftMovedRun : left.run coeffects rightInitial.after with
                        | none =>
                            simp [runSequential, rightInitialRun, leftMovedRun]
                              at rightCompositeRun
                        | some leftMoved =>
                            have rightCompositeEqual :
                                composeApplied rightInitial leftMoved = rightComposite := by
                              simpa [runSequential, rightInitialRun, leftMovedRun] using
                                Option.some.inj (congrArg some rightCompositeRun)
                            subst rightComposite
                            have leftStable := singleton_left_inverse_stable
                              leftKey leftOp leftInput rightKey rightOp rightInput independent
                              before leftInitial rightInitial leftInitialRun rightInitialRun
                            rw [leftMovedRun] at leftStable
                            have rightStable := singleton_right_inverse_stable
                              leftKey leftOp leftInput rightKey rightOp rightInput independent
                              before leftInitial rightInitial leftInitialRun rightInitialRun
                            rw [rightMovedRun] at rightStable
                            have leftStable' : leftInitial.undo = leftMoved.undo := by
                              simpa using leftStable
                            have rightStable' : rightInitial.undo = rightMoved.undo := by
                              simpa using rightStable
                            let leftWitness := singleton_run_has_witness leftKey leftOp leftInput
                              before leftInitial leftInitialRun
                            let rightWitness := singleton_run_has_witness rightKey rightOp
                              rightInput before rightInitial rightInitialRun
                            constructor
                            · exact afterEqual
                            · intro current
                              change leftInitial.undo (rightMoved.undo current) =
                                rightInitial.undo (leftMoved.undo current)
                              rw [← rightStable', ← leftStable']
                              rw [leftWitness.undo_eq, rightWitness.undo_eq]
                              exact liftedInverses_commute leftKey leftOp leftInput
                                leftWitness.seed leftWitness.enabled rightKey rightOp rightInput
                                rightWitness.seed rightWitness.enabled independent current
  · intro before leftApplied rightApplied leftRun rightRun
    constructor
    · intro current
      have stable := singleton_left_inverse_stable leftKey leftOp leftInput rightKey rightOp
        rightInput independent before leftApplied rightApplied leftRun rightRun
      cases movedRun : left.run coeffects rightApplied.after with
      | none =>
          change (singleton leftKey leftOp leftInput).run coeffects rightApplied.after = none
            at movedRun
          unfold singleton at movedRun
          rw [movedRun]
      | some moved =>
          change (singleton leftKey leftOp leftInput).run coeffects rightApplied.after = some moved
            at movedRun
          unfold singleton at movedRun stable
          rw [movedRun] at stable ⊢
          exact congrFun stable current
    · intro current
      have stable := singleton_right_inverse_stable leftKey leftOp leftInput rightKey rightOp
        rightInput independent before leftApplied rightApplied leftRun rightRun
      cases movedRun : right.run coeffects leftApplied.after with
      | none =>
          change (singleton rightKey rightOp rightInput).run coeffects leftApplied.after = none
            at movedRun
          unfold singleton at movedRun
          rw [movedRun]
      | some moved =>
          change (singleton rightKey rightOp rightInput).run coeffects
            leftApplied.after = some moved at movedRun
          unfold singleton at movedRun stable
          rw [movedRun] at stable ⊢
          exact congrFun stable current

/-- The typed root data selected before either order is unchanged after the other root runs.

Unlike `StageInterchange`, this certificate retains each `ForwardData.outcome`; its equal data
objects therefore select definitionally the same continuations after an adjacent swap.
-/
def StageOutcomeAlignment
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp) : Prop :=
  ∀ before leftApplied rightApplied,
    (singleton leftKey leftOp leftInput).run coeffects before = some leftApplied →
    (singleton rightKey rightOp rightInput).run coeffects before = some rightApplied →
    ∃ leftData rightData,
      OperationIndependence.inspectForwardAt coeffects leftKey leftOp leftInput before =
          some leftData ∧
        OperationIndependence.inspectForwardAt coeffects leftKey leftOp leftInput
            rightApplied.after = some leftData ∧
        OperationIndependence.inspectForwardAt coeffects rightKey rightOp rightInput before =
            some rightData ∧
        OperationIndependence.inspectForwardAt coeffects rightKey rightOp rightInput
            leftApplied.after = some rightData

/-- Finite Definition 39 data stability supplies the heterogeneous root-outcome alignment that
`StageInterchange` itself deliberately erases.
-/
theorem stageOutcomeAlignment
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (independent : OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey) :
    StageOutcomeAlignment (coeffects := coeffects)
      leftKey leftOp leftInput rightKey rightOp rightInput := by
  intro before leftApplied rightApplied leftRun rightRun
  obtain ⟨leftData, leftInspected, leftAfter, leftUndo⟩ :=
    singleton_run_has_data leftKey leftOp leftInput before leftApplied leftRun
  obtain ⟨rightData, rightInspected, rightAfter, rightUndo⟩ :=
    singleton_run_has_data rightKey rightOp rightInput before rightApplied rightRun
  have rightTransform := singleton_run_after rightKey rightOp rightInput before
  rw [rightRun] at rightTransform
  have rightWordRun : OperationIndependence.transformAt coeffects rightKey
      (forwardWord rightKey rightOp rightInput) before = some rightApplied.after :=
    rightTransform.symm
  have leftMoved := independent.left_data_stable leftOp leftInput
    (forwardWord rightKey rightOp rightInput) before rightApplied.after rightWordRun
  rw [leftInspected] at leftMoved
  have leftTransform := singleton_run_after leftKey leftOp leftInput before
  rw [leftRun] at leftTransform
  have leftWordRun : OperationIndependence.transformAt coeffects leftKey
      (forwardWord leftKey leftOp leftInput) before = some leftApplied.after :=
    leftTransform.symm
  have rightMoved := independent.right_data_stable rightOp rightInput
    (forwardWord leftKey leftOp leftInput) before leftApplied.after leftWordRun
  rw [rightInspected] at rightMoved
  exact ⟨leftData, rightData, leftInspected, leftMoved, rightInspected, rightMoved⟩

/-- Primitive exact behavior and typed branch alignment, kept as two explicit obligations. -/
structure StageInterchangeWithOutcomes
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp) : Prop where
  interchange : StageInterchange (coeffects := coeffects)
    leftKey leftOp leftInput rightKey rightOp rightInput
  outcomes : StageOutcomeAlignment (coeffects := coeffects)
    leftKey leftOp leftInput rightKey rightOp rightInput

/-- The finite key certificate proves both parts needed before continuation recursion. -/
theorem stageInterchangeWithOutcomes
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (independent : OperationIndependence.FiniteKeyIndependent coeffects leftKey rightKey) :
    StageInterchangeWithOutcomes (coeffects := coeffects)
      leftKey leftOp leftInput rightKey rightOp rightInput :=
  ⟨stageInterchangeComplete leftKey leftOp leftInput rightKey rightOp rightInput independent,
    stageOutcomeAlignment leftKey leftOp leftInput rightKey rightOp rightInput independent⟩

/-- A successful adjacent order `left; right` reconstructed in the reverse order, retaining the
two typed outcomes and the exact inverse equalities needed by a surrounding continuation.
-/
structure ExecutedStageSwap
    {leftKey : Key} {leftOp : (coeffects leftKey).Op}
    {leftInput : (coeffects leftKey).Input leftOp}
    {rightKey : Key} {rightOp : (coeffects rightKey).Op}
    {rightInput : (coeffects rightKey).Input rightOp}
    {before : Coeffect.Context Key Value}
    (leftInitial : ExecutedStage (coeffects := coeffects)
      leftKey leftOp leftInput before)
    (rightMoved : ExecutedStage (coeffects := coeffects)
      rightKey rightOp rightInput leftInitial.applied.after) where
  rightInitial : ExecutedStage (coeffects := coeffects)
    rightKey rightOp rightInput before
  leftMoved : ExecutedStage (coeffects := coeffects)
    leftKey leftOp leftInput rightInitial.applied.after
  left_outcome : leftMoved.outcome = leftInitial.outcome
  right_outcome : rightInitial.outcome = rightMoved.outcome
  after_eq : rightMoved.applied.after = leftMoved.applied.after
  left_undo_eq : leftMoved.applied.undo = leftInitial.applied.undo
  right_undo_eq : rightMoved.applied.undo = rightInitial.applied.undo
  undo_order_eq : ∀ current,
    leftInitial.applied.undo (rightMoved.applied.undo current) =
      rightInitial.applied.undo (leftMoved.applied.undo current)

/-- The finite generator-word certificate swaps two concrete executed stages without erasing
their heterogeneous outcomes.
-/
def swap_executed_stages
    {leftKey : Key} {leftOp : (coeffects leftKey).Op}
    {leftInput : (coeffects leftKey).Input leftOp}
    {rightKey : Key} {rightOp : (coeffects rightKey).Op}
    {rightInput : (coeffects rightKey).Input rightOp}
    {before : Coeffect.Context Key Value}
    (leftInitial : ExecutedStage (coeffects := coeffects)
      leftKey leftOp leftInput before)
    (rightMoved : ExecutedStage (coeffects := coeffects)
      rightKey rightOp rightInput leftInitial.applied.after)
    (independent : OperationIndependence.FiniteKeyIndependent
      coeffects leftKey rightKey) :
    ExecutedStageSwap leftInitial rightMoved := by
  let left := singleton leftKey leftOp leftInput
  let right := singleton rightKey rightOp rightInput
  have leftCompositeRun : runSequential left right before =
      some (composeApplied leftInitial.applied rightMoved.applied) := by
    change runSequential (singleton leftKey leftOp leftInput)
      (singleton rightKey rightOp rightInput) before = _
    simp [runSequential, leftInitial.ran, rightMoved.ran]
  have agreement :=
    (stageInterchangeComplete leftKey leftOp leftInput rightKey rightOp rightInput independent)
      |>.orders_agree before
  change
    (match runSequential left right before, runSequential right left before with
    | none, none => True
    | some leftThenRight, some rightThenLeft =>
        leftThenRight.after = rightThenLeft.after ∧
          ∀ current, leftThenRight.undo current = rightThenLeft.undo current
    | _, _ => False) at agreement
  rw [leftCompositeRun] at agreement
  cases rightInitialRun : right.run coeffects before with
  | none => simp [runSequential, rightInitialRun] at agreement
  | some rightInitialApplied =>
      cases leftMovedRun : left.run coeffects rightInitialApplied.after with
      | none => simp [runSequential, rightInitialRun, leftMovedRun] at agreement
      | some leftMovedApplied =>
          simp [runSequential, rightInitialRun, leftMovedRun] at agreement
          let rightInitial : ExecutedStage (coeffects := coeffects)
              rightKey rightOp rightInput before := {
            applied := rightInitialApplied
            ran := rightInitialRun
            witness := singleton_run_has_witness rightKey rightOp rightInput before
              rightInitialApplied rightInitialRun
          }
          let leftMoved : ExecutedStage (coeffects := coeffects)
              leftKey leftOp leftInput rightInitial.applied.after := {
            applied := leftMovedApplied
            ran := leftMovedRun
            witness := singleton_run_has_witness leftKey leftOp leftInput
              rightInitialApplied.after leftMovedApplied leftMovedRun
          }
          have leftStable := singleton_left_inverse_stable leftKey leftOp leftInput
            rightKey rightOp rightInput independent before leftInitial.applied
            rightInitial.applied leftInitial.ran rightInitial.ran
          rw [leftMoved.ran] at leftStable
          have rightStable := singleton_right_inverse_stable leftKey leftOp leftInput
            rightKey rightOp rightInput independent before leftInitial.applied
            rightInitial.applied leftInitial.ran rightInitial.ran
          rw [rightMoved.ran] at rightStable
          have rightTransform := singleton_run_after rightKey rightOp rightInput before
          rw [rightInitial.ran] at rightTransform
          have rightWordRun : OperationIndependence.transformAt coeffects rightKey
              (forwardWord rightKey rightOp rightInput) before =
                some rightInitial.applied.after := rightTransform.symm
          have leftData := independent.left_data_stable leftOp leftInput
            (forwardWord rightKey rightOp rightInput) before rightInitial.applied.after
            rightWordRun
          rw [leftInitial.inspect_eq_some, leftMoved.inspect_eq_some] at leftData
          have leftDataEq := Option.some.inj leftData
          have leftTransform := singleton_run_after leftKey leftOp leftInput before
          rw [leftInitial.ran] at leftTransform
          have leftWordRun : OperationIndependence.transformAt coeffects leftKey
              (forwardWord leftKey leftOp leftInput) before =
                some leftInitial.applied.after := leftTransform.symm
          have rightData := independent.right_data_stable rightOp rightInput
            (forwardWord leftKey leftOp leftInput) before leftInitial.applied.after leftWordRun
          rw [rightMoved.inspect_eq_some, rightInitial.inspect_eq_some] at rightData
          have rightDataEq := Option.some.inj rightData
          exact {
            rightInitial := rightInitial
            leftMoved := leftMoved
            left_outcome := congrArg OperationIndependence.ForwardData.outcome leftDataEq
            right_outcome :=
              congrArg OperationIndependence.ForwardData.outcome rightDataEq.symm
            after_eq := agreement.1
            left_undo_eq := by simpa using leftStable.symm
            right_undo_eq := by simpa using rightStable.symm
            undo_order_eq := agreement.2
          }

/-!
## Proof-erased recursive semantics

The dependent index on `Applied` is essential for recovery but awkward for swapping an
outcome-selected suffix across propositionally equal intermediate contexts. `RawResult` erases
only that proof index: it retains the exact successor and the complete yielded inverse function.
The theorem below reconnects this evaluator to `Computation.run` before any closure result is
stated.
-/

/-- Exact successor and complete yielded inverse, with only the recovery proof erased. -/
structure RawResult (Key : Type u) [DecidableEq Key] (Value : Key → Type v) where
  after : Coeffect.Context Key Value
  undo : Coeffect.Context Key Value → Coeffect.Context Key Value

/-- Raw results are extensional in their successor and yielded inverse. -/
theorem RawResult.ext {left right : RawResult Key Value}
    (after : left.after = right.after) (undo : left.undo = right.undo) : left = right := by
  cases left
  cases right
  simp_all

/-- Erase only the predecessor index and recovery proof from an exact application. -/
def RawResult.ofApplied
    {before : Coeffect.Context Key Value}
    (applied : Cordis.Applied (Coeffect.Context Key Value) before) : RawResult Key Value :=
  ⟨applied.after, applied.undo⟩

/-- The raw identity result. -/
def RawResult.identity (context : Coeffect.Context Key Value) : RawResult Key Value :=
  ⟨context, id⟩

/-- Exact sequential composition after proof-index erasure. -/
def RawResult.comp (first second : RawResult Key Value) : RawResult Key Value :=
  ⟨second.after, first.undo ∘ second.undo⟩

/-- Lift one inspected local result to its exact whole-context raw behavior. -/
def rawStage (key : Key) {op : (coeffects key).Op}
    (before : Coeffect.Context Key Value)
    (data : OperationIndependence.ForwardData (coeffects key) op) : RawResult Key Value :=
  ⟨Coeffect.setAt before key data.after, liftDataUndo key data⟩

/-- Proof-erased executable semantics for finite outcome-mediated computations. -/
def evaluate (computation : OperationIndependence.Computation coeffects)
    (context : Coeffect.Context Key Value) : Option (RawResult Key Value) :=
  (computation.run coeffects context).map RawResult.ofApplied

/-- The raw evaluator is exactly `Computation.run` with only proof/index data forgotten. -/
theorem evaluate_eq_run_map
    (computation : OperationIndependence.Computation coeffects)
    (context : Coeffect.Context Key Value) :
    evaluate computation context =
      (computation.run coeffects context).map RawResult.ofApplied := rfl

@[simp]
theorem evaluate_pure (context : Coeffect.Context Key Value) :
    evaluate (coeffects := coeffects) .pure context = some (RawResult.identity context) := by
  apply congrArg some
  apply RawResult.ext
  · rfl
  · funext current
    rfl

/-- The erased semantics exposes exactly the inspected root data and selected continuation. -/
theorem evaluate_step
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects)
    (context : Coeffect.Context Key Value) :
    evaluate (.step key op input next) context =
      match OperationIndependence.inspectForwardAt coeffects key op input context with
      | none => none
      | some data =>
          match evaluate (next data.outcome) (rawStage key context data).after with
          | none => none
          | some tail => some ((rawStage key context data).comp tail) := by
  simp [evaluate, OperationIndependence.Computation.run.eq_2,
    OperationIndependence.inspectForwardAt]
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> simp_all [RawResult.ofApplied, RawResult.comp, rawStage,
    Coeffect.CoeffectAt.lift]
  all_goals
    apply congrArg some
    apply RawResult.ext
    · rfl
    · funext current
      rfl

/-- Seed/enabled evidence hidden inside one successful forward inspection. -/
structure InspectWitness
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (context : Coeffect.Context Key Value)
    (data : OperationIndependence.ForwardData (coeffects key) op) where
  seed : Value key
  lookup : context key = some seed
  enabled : (coeffects key).Enabled op input seed
  data_eq : data =
    ⟨((coeffects key).run op input seed enabled).1.after,
      ((coeffects key).run op input seed enabled).1.undo,
      ((coeffects key).run op input seed enabled).2⟩

/-- Every successful inspection retains a seed/enabled witness for its yielded inverse. -/
def inspect_has_witness
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (context : Coeffect.Context Key Value)
    (data : OperationIndependence.ForwardData (coeffects key) op)
    (inspected : OperationIndependence.inspectForwardAt coeffects key op input context =
      some data) :
    InspectWitness (coeffects := coeffects) key op input context data := by
  simp [OperationIndependence.inspectForwardAt] at inspected
  split at inspected
  · contradiction
  · rename_i seed lookup
    split at inspected
    · rename_i enabled
      have equal := Option.some.inj inspected
      subst data
      exact ⟨seed, lookup, enabled, rfl⟩
    · contradiction

/-- Exact adjacent interchange at the proof-erased level, retaining the same data objects and
hence the same heterogeneous outcomes in both orders.
-/
structure RawStageInterchange
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (before : Coeffect.Context Key Value)
    (leftData : OperationIndependence.ForwardData (coeffects leftKey) leftOp)
    (rightData : OperationIndependence.ForwardData (coeffects rightKey) rightOp) : Prop where
  right_initial : OperationIndependence.inspectForwardAt coeffects rightKey rightOp
    rightInput before = some rightData
  left_moved : OperationIndependence.inspectForwardAt coeffects leftKey leftOp leftInput
    (rawStage rightKey before rightData).after = some leftData
  after_eq : (rawStage rightKey (rawStage leftKey before leftData).after rightData).after =
    (rawStage leftKey (rawStage rightKey before rightData).after leftData).after
  undo_eq : ∀ current,
    (rawStage leftKey before leftData).undo
        ((rawStage rightKey (rawStage leftKey before leftData).after rightData).undo current) =
      (rawStage rightKey before rightData).undo
        ((rawStage leftKey (rawStage rightKey before rightData).after leftData).undo current)

/-- `FiniteKeyIndependent` proves adjacent interchange while preserving the exact forward data
that drives both continuations.
-/
theorem rawStage_interchange
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (rightKey : Key) (rightOp : (coeffects rightKey).Op)
    (rightInput : (coeffects rightKey).Input rightOp)
    (before : Coeffect.Context Key Value)
    (leftData : OperationIndependence.ForwardData (coeffects leftKey) leftOp)
    (rightData : OperationIndependence.ForwardData (coeffects rightKey) rightOp)
    (leftInspected : OperationIndependence.inspectForwardAt coeffects leftKey leftOp
      leftInput before = some leftData)
    (rightMovedInspected : OperationIndependence.inspectForwardAt coeffects rightKey rightOp
      rightInput (rawStage leftKey before leftData).after = some rightData)
    (independent : OperationIndependence.FiniteKeyIndependent
      coeffects leftKey rightKey) :
    RawStageInterchange (coeffects := coeffects) leftKey leftOp leftInput
      rightKey rightOp rightInput before leftData rightData := by
  have leftTransform := inspectForward_transform leftKey leftOp leftInput before
  rw [leftInspected] at leftTransform
  have leftWordRun : OperationIndependence.transformAt coeffects leftKey
      (forwardWord leftKey leftOp leftInput) before =
        some (rawStage leftKey before leftData).after := by
    simpa [rawStage] using leftTransform.symm
  have rightInitial := independent.right_data_stable rightOp rightInput
    (forwardWord leftKey leftOp leftInput) before (rawStage leftKey before leftData).after
    leftWordRun
  rw [rightMovedInspected] at rightInitial
  have rightInitialInspected : OperationIndependence.inspectForwardAt coeffects rightKey
      rightOp rightInput before = some rightData := rightInitial.symm
  have rightTransform := inspectForward_transform rightKey rightOp rightInput before
  rw [rightInitialInspected] at rightTransform
  have rightWordRun : OperationIndependence.transformAt coeffects rightKey
      (forwardWord rightKey rightOp rightInput) before =
        some (rawStage rightKey before rightData).after := by
    simpa [rawStage] using rightTransform.symm
  have leftMoved := independent.left_data_stable leftOp leftInput
    (forwardWord rightKey rightOp rightInput) before (rawStage rightKey before rightData).after
    rightWordRun
  rw [leftInspected] at leftMoved
  have leftMovedInspected : OperationIndependence.inspectForwardAt coeffects leftKey leftOp
      leftInput (rawStage rightKey before rightData).after = some leftData := leftMoved
  have rightMovedTransform := inspectForward_transform rightKey rightOp rightInput
    (rawStage leftKey before leftData).after
  rw [rightMovedInspected] at rightMovedTransform
  have leftMovedTransform := inspectForward_transform leftKey leftOp leftInput
    (rawStage rightKey before rightData).after
  rw [leftMovedInspected] at leftMovedTransform
  have words := independent.words_commute (forwardWord leftKey leftOp leftInput)
    (forwardWord rightKey rightOp rightInput) before
  rw [leftWordRun, rightWordRun] at words
  simp only [Option.bind_some] at words
  rw [rightMovedTransform.symm, leftMovedTransform.symm] at words
  have finalAfter := Option.some.inj words
  let leftWitness := inspect_has_witness leftKey leftOp leftInput before leftData leftInspected
  let rightWitness := inspect_has_witness rightKey rightOp rightInput before rightData
    rightInitialInspected
  refine {
    right_initial := rightInitialInspected
    left_moved := leftMovedInspected
    after_eq := finalAfter
    undo_eq := ?_
  }
  intro current
  rw [leftWitness.data_eq, rightWitness.data_eq]
  change
    Coeffect.Quotient.undoAt
        ((coeffects leftKey).run leftOp leftInput leftWitness.seed leftWitness.enabled).1
        (Coeffect.Quotient.undoAt
          ((coeffects rightKey).run rightOp rightInput rightWitness.seed
            rightWitness.enabled).1 current) =
      Coeffect.Quotient.undoAt
        ((coeffects rightKey).run rightOp rightInput rightWitness.seed
          rightWitness.enabled).1
        (Coeffect.Quotient.undoAt
          ((coeffects leftKey).run leftOp leftInput leftWitness.seed
            leftWitness.enabled).1 current)
  exact liftedInverses_commute leftKey leftOp leftInput leftWitness.seed
    leftWitness.enabled rightKey rightOp rightInput rightWitness.seed rightWitness.enabled
    independent current

/-- One fixed root key is Definition 39-independent of every syntactic stage in a computation. -/
def RootOverlaps
    (leftKey : Key) (right : OperationIndependence.Computation coeffects) : Prop :=
  ∀ rightStage, Occurs rightStage right →
    OperationIndependence.FiniteKeyIndependent coeffects leftKey rightStage.key

/-- Restrict root overlap to any typed continuation of the foreign computation. -/
theorem RootOverlaps.continuation
    {leftKey rightKey : Key} {rightOp : (coeffects rightKey).Op}
    {rightInput : (coeffects rightKey).Input rightOp} {rightNext}
    (overlap : RootOverlaps (coeffects := coeffects) leftKey
      (.step rightKey rightOp rightInput rightNext))
    (outcome : (coeffects rightKey).Outcome rightOp) :
    RootOverlaps (coeffects := coeffects) leftKey (rightNext outcome) := by
  intro stage occurs
  exact overlap stage (.continuation outcome occurs)

/-- Successful motion of one fixed root across a complete foreign computation. The same
`leftData` occurs before and after the foreign run, so its typed outcome selects the same branch.
-/
def RawStageMovesAcross
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (right : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value)
    (leftData : OperationIndependence.ForwardData (coeffects leftKey) leftOp)
    (rightMoved : RawResult Key Value) : Prop :=
  ∃ rightInitial,
    evaluate right before = some rightInitial ∧
    OperationIndependence.inspectForwardAt coeffects leftKey leftOp leftInput
        rightInitial.after = some leftData ∧
    rightMoved.after = (rawStage leftKey rightInitial.after leftData).after ∧
    rightMoved.undo = rightInitial.undo ∧
    ∀ current,
      (rawStage leftKey before leftData).undo (rightMoved.undo current) =
        rightInitial.undo ((rawStage leftKey rightInitial.after leftData).undo current)

/-- A root stage bubbles across an arbitrary finite, outcome-dependent computation by induction
over every selected foreign continuation.
-/
theorem rawStage_movesAcross
    (leftKey : Key) (leftOp : (coeffects leftKey).Op)
    (leftInput : (coeffects leftKey).Input leftOp)
    (right : OperationIndependence.Computation coeffects)
    (overlap : RootOverlaps (coeffects := coeffects) leftKey right)
    (before : Coeffect.Context Key Value)
    (leftData : OperationIndependence.ForwardData (coeffects leftKey) leftOp)
    (leftInspected : OperationIndependence.inspectForwardAt coeffects leftKey leftOp
      leftInput before = some leftData)
    (rightMoved : RawResult Key Value)
    (rightMovedRun : evaluate right (rawStage leftKey before leftData).after =
      some rightMoved) :
    RawStageMovesAcross (coeffects := coeffects) leftKey leftOp leftInput right before
      leftData rightMoved := by
  induction right generalizing before rightMoved with
  | pure =>
      rw [evaluate_pure] at rightMovedRun
      have rightMovedEq := Option.some.inj rightMovedRun
      subst rightMoved
      refine ⟨RawResult.identity before, evaluate_pure before, ?_, rfl, ?_, ?_⟩
      · exact leftInspected
      · funext current
        rfl
      · intro current
        rfl
  | step rightKey rightOp rightInput rightNext induction =>
      rw [evaluate_step] at rightMovedRun
      cases rightInspected : OperationIndependence.inspectForwardAt coeffects rightKey
        rightOp rightInput (rawStage leftKey before leftData).after with
      | none => simp [rightInspected] at rightMovedRun
      | some rightData =>
          rw [rightInspected] at rightMovedRun
          change
            (match evaluate (rightNext rightData.outcome)
              (rawStage rightKey (rawStage leftKey before leftData).after rightData).after with
            | none => none
            | some tail =>
                some ((rawStage rightKey
                  (rawStage leftKey before leftData).after rightData).comp tail)) =
              some rightMoved at rightMovedRun
          cases tailMovedRun : evaluate (rightNext rightData.outcome)
            (rawStage rightKey (rawStage leftKey before leftData).after rightData).after with
          | none => simp [tailMovedRun] at rightMovedRun
          | some tailMoved =>
              rw [tailMovedRun] at rightMovedRun
              have rightMovedEq := Option.some.inj rightMovedRun
              subst rightMoved
              have roots := overlap ⟨rightKey, rightOp, rightInput⟩
                (.root rightKey rightOp rightInput rightNext)
              have adjacent := rawStage_interchange leftKey leftOp leftInput rightKey rightOp
                rightInput before leftData rightData leftInspected rightInspected roots
              have tailMovedRun' : evaluate (rightNext rightData.outcome)
                  (rawStage leftKey (rawStage rightKey before rightData).after leftData).after =
                    some tailMoved := by
                rw [← adjacent.after_eq]
                exact tailMovedRun
              have tailOverlap := overlap.continuation rightData.outcome
              obtain ⟨tailInitial, tailInitialRun, leftAfterTail, tailAfter,
                  tailUndo, tailOrder⟩ :=
                induction rightData.outcome tailOverlap
                  (rawStage rightKey before rightData).after adjacent.left_moved tailMoved
                  tailMovedRun'
              let rightInitial :=
                (rawStage rightKey before rightData).comp tailInitial
              have rightInitialRun : evaluate
                  (.step rightKey rightOp rightInput rightNext) before = some rightInitial := by
                rw [evaluate_step, adjacent.right_initial]
                change
                  (match evaluate (rightNext rightData.outcome)
                    (rawStage rightKey before rightData).after with
                  | none => none
                  | some tail => some ((rawStage rightKey before rightData).comp tail)) = _
                rw [tailInitialRun]
              refine ⟨rightInitial, rightInitialRun, leftAfterTail, tailAfter, ?_, ?_⟩
              · funext current
                exact congrArg (rawStage rightKey before rightData).undo
                  (congrFun tailUndo current)
              · intro current
                change
                  (rawStage leftKey before leftData).undo
                      ((rawStage rightKey
                          (rawStage leftKey before leftData).after rightData).undo
                        (tailMoved.undo current)) =
                    (rawStage rightKey before rightData).undo
                      (tailInitial.undo
                        ((rawStage leftKey tailInitial.after leftData).undo current))
                calc
                  _ = (rawStage rightKey before rightData).undo
                      ((rawStage leftKey
                        (rawStage rightKey before rightData).after leftData).undo
                          (tailMoved.undo current)) := adjacent.undo_eq _
                  _ = _ := congrArg (rawStage rightKey before rightData).undo
                    (tailOrder current)

/-- One successful `left; right` execution reconstructed as `right; left`, retaining exact
successors, individual yielded inverses, and the two complete composed inverse orders.
-/
def RawSuccessfulSwap
    (left right : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value)
    (leftInitial rightMoved : RawResult Key Value) : Prop :=
  ∃ rightInitial leftMoved,
    evaluate right before = some rightInitial ∧
    evaluate left rightInitial.after = some leftMoved ∧
    rightMoved.after = leftMoved.after ∧
    leftMoved.undo = leftInitial.undo ∧
    rightMoved.undo = rightInitial.undo ∧
    ∀ current,
      leftInitial.undo (rightMoved.undo current) =
        rightInitial.undo (leftMoved.undo current)

/-- Pairwise overlap swaps any successful finite mediated execution by structural induction on
the left computation and all of its typed outcome-selected continuations.
-/
theorem rawComputation_swap_success
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right)
    (before : Coeffect.Context Key Value)
    (leftInitial : RawResult Key Value)
    (leftInitialRun : evaluate left before = some leftInitial)
    (rightMoved : RawResult Key Value)
    (rightMovedRun : evaluate right leftInitial.after = some rightMoved) :
    RawSuccessfulSwap (coeffects := coeffects) left right before leftInitial rightMoved := by
  induction left generalizing before leftInitial rightMoved with
  | pure =>
      rw [evaluate_pure] at leftInitialRun
      have leftInitialEq := Option.some.inj leftInitialRun
      subst leftInitial
      refine ⟨rightMoved, RawResult.identity rightMoved.after, rightMovedRun,
        evaluate_pure rightMoved.after, rfl, ?_, rfl, ?_⟩
      · funext current
        rfl
      · intro current
        rfl
  | step leftKey leftOp leftInput leftNext induction =>
      rw [evaluate_step] at leftInitialRun
      cases leftInspected : OperationIndependence.inspectForwardAt coeffects leftKey leftOp
        leftInput before with
      | none => simp [leftInspected] at leftInitialRun
      | some leftData =>
          rw [leftInspected] at leftInitialRun
          change
            (match evaluate (leftNext leftData.outcome)
              (rawStage leftKey before leftData).after with
            | none => none
            | some tail => some ((rawStage leftKey before leftData).comp tail)) =
              some leftInitial at leftInitialRun
          cases tailInitialRun : evaluate (leftNext leftData.outcome)
            (rawStage leftKey before leftData).after with
          | none => simp [tailInitialRun] at leftInitialRun
          | some tailInitial =>
              rw [tailInitialRun] at leftInitialRun
              have leftInitialEq := Option.some.inj leftInitialRun
              subst leftInitial
              have tailOverlap := PairwiseOverlap.left_continuation overlap leftData.outcome
              obtain ⟨rightAfterRoot, tailMoved, rightAfterRootRun, tailMovedRun,
                  tailAfter, tailUndo, rightTailUndo, tailOrder⟩ :=
                induction leftData.outcome tailOverlap
                  (rawStage leftKey before leftData).after tailInitial tailInitialRun
                  rightMoved rightMovedRun
              have rootOverlap : RootOverlaps (coeffects := coeffects) leftKey right := by
                intro rightStage rightOccurs
                exact overlap ⟨leftKey, leftOp, leftInput⟩ rightStage
                  (.root leftKey leftOp leftInput leftNext) rightOccurs
              obtain ⟨rightInitial, rightInitialRun, leftMovedInspected, rootAfter,
                  rightRootUndo, rootOrder⟩ :=
                rawStage_movesAcross leftKey leftOp leftInput right rootOverlap before leftData
                  leftInspected rightAfterRoot rightAfterRootRun
              have tailMovedRun' : evaluate (leftNext leftData.outcome)
                  (rawStage leftKey rightInitial.after leftData).after = some tailMoved := by
                rw [← rootAfter]
                exact tailMovedRun
              let leftMoved := (rawStage leftKey rightInitial.after leftData).comp tailMoved
              have leftMovedRun : evaluate
                  (.step leftKey leftOp leftInput leftNext) rightInitial.after =
                    some leftMoved := by
                rw [evaluate_step, leftMovedInspected]
                change
                  (match evaluate (leftNext leftData.outcome)
                    (rawStage leftKey rightInitial.after leftData).after with
                  | none => none
                  | some tail =>
                      some ((rawStage leftKey rightInitial.after leftData).comp tail)) = _
                rw [tailMovedRun']
              refine ⟨rightInitial, leftMoved, rightInitialRun, leftMovedRun, tailAfter,
                ?_, rightTailUndo.trans rightRootUndo, ?_⟩
              · funext current
                exact congrArg (rawStage leftKey before leftData).undo
                  (congrFun tailUndo current)
              · intro current
                change
                  (rawStage leftKey before leftData).undo
                      (tailInitial.undo (rightMoved.undo current)) =
                    rightInitial.undo
                      ((rawStage leftKey rightInitial.after leftData).undo
                        (tailMoved.undo current))
                calc
                  _ = (rawStage leftKey before leftData).undo
                      (rightAfterRoot.undo (tailMoved.undo current)) :=
                    congrArg (rawStage leftKey before leftData).undo (tailOrder current)
                  _ = _ := rootOrder (tailMoved.undo current)

/-- The finite key certificate is symmetric after exchanging its oriented stability fields. -/
theorem finiteKeyIndependent_symm
    {left right : Key}
    (independent : OperationIndependence.FiniteKeyIndependent coeffects left right) :
    OperationIndependence.FiniteKeyIndependent coeffects right left where
  words_commute := by
    intro rightWord leftWord context
    exact (independent.words_commute leftWord rightWord context).symm
  left_data_stable := by
    intro op input leftWord context after ran
    exact independent.right_data_stable op input leftWord context after ran
  right_data_stable := by
    intro op input rightWord context after ran
    exact independent.left_data_stable op input rightWord context after ran

/-- Pairwise syntactic overlap is symmetric. -/
theorem PairwiseOverlap.symm
    {left right : OperationIndependence.Computation coeffects}
    (overlap : PairwiseOverlap coeffects left right) :
    PairwiseOverlap coeffects right left := by
  intro rightStage leftStage rightOccurs leftOccurs
  exact finiteKeyIndependent_symm (overlap leftStage rightStage leftOccurs rightOccurs)

/-- Proof-erased execution of two complete computations in order. -/
def evaluateSequential
    (left right : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value) : Option (RawResult Key Value) :=
  match evaluate left before with
  | none => none
  | some leftInitial =>
      match evaluate right leftInitial.after with
      | none => none
      | some rightMoved => some (leftInitial.comp rightMoved)

/-- Any successful proof-erased composite run has an equal result in the reverse order. -/
theorem evaluateSequential_swap_success
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right)
    (before : Coeffect.Context Key Value)
    (result : RawResult Key Value)
    (ran : evaluateSequential left right before = some result) :
    evaluateSequential right left before = some result := by
  cases leftInitialRun : evaluate left before with
  | none => simp [evaluateSequential, leftInitialRun] at ran
  | some leftInitial =>
      rw [evaluateSequential, leftInitialRun] at ran
      change
        (match evaluate right leftInitial.after with
        | none => none
        | some rightMoved => some (leftInitial.comp rightMoved)) = some result at ran
      cases rightMovedRun : evaluate right leftInitial.after with
      | none => simp [rightMovedRun] at ran
      | some rightMoved =>
          rw [rightMovedRun] at ran
          have resultEq := Option.some.inj ran
          subst result
          obtain ⟨rightInitial, leftMoved, rightInitialRun, leftMovedRun, afterEq,
              leftUndo, rightUndo, orderEq⟩ :=
            rawComputation_swap_success left right overlap before leftInitial leftInitialRun
              rightMoved rightMovedRun
          rw [evaluateSequential, rightInitialRun]
          change
            (match evaluate left rightInitial.after with
            | none => none
            | some leftMoved => some (rightInitial.comp leftMoved)) = _
          rw [leftMovedRun]
          apply congrArg some
          apply RawResult.ext
          · exact afterEq.symm
          · funext current
            exact (orderEq current).symm

/-- The two proof-erased composite orders agree on definedness and exact complete results. -/
theorem evaluateSequential_commute
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right)
    (before : Coeffect.Context Key Value) :
    evaluateSequential left right before = evaluateSequential right left before := by
  cases leftRun : evaluateSequential left right before with
  | none =>
      cases rightRun : evaluateSequential right left before with
      | none => rfl
      | some result =>
          have reverse := evaluateSequential_swap_success right left
            (PairwiseOverlap.symm overlap) before result rightRun
          rw [leftRun] at reverse
          contradiction
  | some result =>
      exact (evaluateSequential_swap_success left right overlap before result leftRun).symm

/-- Correct whole-run partial independence at the proof-erased level. This still quantifies only
over complete finite mediated runs, not all words in the paper's transformation monoids.
-/
structure RawMediatedIndependence
    (left right : OperationIndependence.Computation coeffects) : Prop where
  orders_equal : ∀ before,
    evaluateSequential left right before = evaluateSequential right left before
  yielded_stable : ∀ before leftInitial rightInitial,
    evaluate left before = some leftInitial →
    evaluate right before = some rightInitial →
    (match evaluate left rightInitial.after with
    | none => True
    | some leftMoved => leftMoved.undo = leftInitial.undo) ∧
    (match evaluate right leftInitial.after with
    | none => True
    | some rightMoved => rightMoved.undo = rightInitial.undo)

/-- Pairwise Definition 39 overlap proves exact finite whole-run interchange and conditional
yielded-inverse stability for the proof-erased evaluator.
-/
theorem pairwiseOverlap_rawMediatedIndependence
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right) :
    RawMediatedIndependence (coeffects := coeffects) left right := by
  constructor
  · exact evaluateSequential_commute left right overlap
  · intro before leftInitial rightInitial leftInitialRun rightInitialRun
    constructor
    · cases leftMovedRun : evaluate left rightInitial.after with
      | none => trivial
      | some leftMoved =>
          obtain ⟨leftAtStart, rightAfterLeft, leftAtStartRun, rightAfterLeftRun,
              finalAfter, rightUndo, leftUndo, orderEq⟩ :=
            rawComputation_swap_success right left (PairwiseOverlap.symm overlap) before
              rightInitial rightInitialRun leftMoved leftMovedRun
          have leftAtStartEq : leftAtStart = leftInitial :=
            Option.some.inj (leftAtStartRun.symm.trans leftInitialRun)
          exact leftUndo.trans (congrArg RawResult.undo leftAtStartEq)
    · cases rightMovedRun : evaluate right leftInitial.after with
      | none => trivial
      | some rightMoved =>
          obtain ⟨rightAtStart, leftAfterRight, rightAtStartRun, leftAfterRightRun,
              finalAfter, leftUndo, rightUndo, orderEq⟩ :=
            rawComputation_swap_success left right overlap before leftInitial leftInitialRun
              rightMoved rightMovedRun
          have rightAtStartEq : rightAtStart = rightInitial :=
            Option.some.inj (rightAtStartRun.symm.trans rightInitialRun)
          exact rightUndo.trans (congrArg RawResult.undo rightAtStartEq)

/-- Erasing a sequential exact run is exactly sequential composition of its erased results. -/
theorem evaluateSequential_eq_runSequential_map
    (left right : OperationIndependence.Computation coeffects)
    (before : Coeffect.Context Key Value) :
    evaluateSequential left right before =
      (runSequential left right before).map RawResult.ofApplied := by
  cases leftRun : left.run coeffects before with
  | none => simp [evaluateSequential, evaluate, runSequential, leftRun]
  | some leftApplied =>
      cases rightRun : right.run coeffects leftApplied.after with
      | none =>
          simp [evaluateSequential, evaluate, runSequential, leftRun, rightRun,
            RawResult.ofApplied]
      | some rightApplied =>
          simp [evaluateSequential, evaluate, runSequential, leftRun, rightRun,
            RawResult.ofApplied, RawResult.comp, composeApplied]

/-- Reinsert the exact `Applied` recovery witnesses after the structural proof has compared their
successors and complete inverse functions.
-/
theorem RawMediatedIndependence.toBoundedPartial
    {left right : OperationIndependence.Computation coeffects}
    (independent : RawMediatedIndependence (coeffects := coeffects) left right) :
    BoundedPartialIndependence (coeffects := coeffects) left right := by
  constructor
  · intro before
    have rawEqual := independent.orders_equal before
    rw [evaluateSequential_eq_runSequential_map,
      evaluateSequential_eq_runSequential_map] at rawEqual
    change
      (match runSequential left right before, runSequential right left before with
      | none, none => True
      | some leftThenRight, some rightThenLeft =>
          leftThenRight.after = rightThenLeft.after ∧
            ∀ current, leftThenRight.undo current = rightThenLeft.undo current
      | _, _ => False)
    cases leftRun : runSequential left right before with
    | none =>
        cases rightRun : runSequential right left before with
        | none => exact True.intro
        | some rightApplied =>
            rw [leftRun, rightRun] at rawEqual
            cases rawEqual
    | some leftApplied =>
        cases rightRun : runSequential right left before with
        | none =>
            rw [leftRun, rightRun] at rawEqual
            cases rawEqual
        | some rightApplied =>
            rw [leftRun, rightRun] at rawEqual
            have resultEqual := Option.some.inj rawEqual
            constructor
            · exact congrArg RawResult.after resultEqual
            · intro current
              exact congrFun (congrArg RawResult.undo resultEqual) current
  · intro before leftApplied rightApplied leftRun rightRun
    have leftRawRun : evaluate left before = some (RawResult.ofApplied leftApplied) := by
      simp [evaluate, leftRun]
    have rightRawRun : evaluate right before = some (RawResult.ofApplied rightApplied) := by
      simp [evaluate, rightRun]
    have stable := independent.yielded_stable before (RawResult.ofApplied leftApplied)
      (RawResult.ofApplied rightApplied) leftRawRun rightRawRun
    simp only [RawResult.ofApplied] at stable
    constructor
    · intro current
      cases movedRun : left.run coeffects rightApplied.after with
      | none => rfl
      | some moved =>
          have movedRawRun : evaluate left rightApplied.after =
              some (RawResult.ofApplied moved) := by
            simp [evaluate, movedRun]
          rw [movedRawRun] at stable
          exact congrFun stable.1.symm current
    · intro current
      cases movedRun : right.run coeffects leftApplied.after with
      | none => rfl
      | some moved =>
          have movedRawRun : evaluate right leftApplied.after =
              some (RawResult.ofApplied moved) := by
            simp [evaluate, movedRun]
          rw [movedRawRun] at stable
          exact congrFun stable.2.symm current

/-- Exact finite whole-run analogue of Theorem 42: all syntactically cross-occurring Definition
41 operations satisfying the finite Definition 39 certificate yield commuting complete partial
runs and stable yielded inverses.

This theorem concerns the modeled generator-word language and complete finite runs. It is not a
claim about arbitrary external effects or a replacement for the paper's full transformation
monoids.
-/
theorem pairwiseOverlap_boundedPartialIndependence
    (left right : OperationIndependence.Computation coeffects)
    (overlap : PairwiseOverlap coeffects left right) :
    BoundedPartialIndependence (coeffects := coeffects) left right :=
  (pairwiseOverlap_rawMediatedIndependence left right overlap).toBoundedPartial

/-- Bounded observational whole-run conclusion for partial computations. -/
def PartialPairwiseOverlapComplete
    (coeffects : CoeffectFamily.{u, v, w} Key Value) : Prop :=
  ∀ left right, PairwiseOverlap coeffects left right →
    BoundedPartialObservationalIndependence (coeffects := coeffects) left right

/-- The exact finite theorem implies its Definition 33 observational quotient form. -/
theorem partialPairwiseOverlapComplete : PartialPairwiseOverlapComplete coeffects := by
  intro left right overlap
  exact (pairwiseOverlap_boundedPartialIndependence left right overlap).toObservational

/-!
## Heterogeneous branching base case
-/

namespace Example

open Cordis.MediatedIndependence.BranchExample

/-- The existing `Nat`-outcome/`String`-continuation path commutes with unit under the
corrected partial definition.
-/
theorem branching_with_pure :
    BoundedPartialIndependence
      (coeffects := Cordis.Coeffect.Quotient.Example.coeffects) computation .pure :=
  partialClosure_pure_right computation

def missing : Coeffect.Context Cordis.Coeffect.Quotient.Example.ExampleKey
    Cordis.Coeffect.Quotient.Example.ExampleValue := Coeffect.empty

theorem branching_missing :
    computation.run Cordis.Coeffect.Quotient.Example.coeffects missing = none := rfl

/-- Overlap with unit is vacuous because unit contains no stage. -/
theorem overlap_with_pure :
    PairwiseOverlap Cordis.Coeffect.Quotient.Example.coeffects computation .pure := by
  intro leftStage rightStage leftOccurs rightOccurs
  cases rightOccurs

/-- The previous observational closure API rejects partial computation versus unit because it
compares their individual domains.
-/
theorem old_observationalClosure_fails :
    ¬ObservationalMediatedClosure
      Cordis.Coeffect.Quotient.Example.coeffects computation .pure := by
  intro closure
  have agreement := closure.orders_related missing
  rw [branching_missing] at agreement
  simp [OperationIndependence.Computation.run] at agreement

/-- The previous exact API has the same individual-domain problem. -/
theorem old_exactClosure_fails :
    ¬OperationIndependence.MediatedClosure
      Cordis.Coeffect.Quotient.Example.coeffects computation .pure := by
  intro closure
  have agreement := closure.orders_agree missing
  rw [branching_missing] at agreement
  simp [OperationIndependence.Computation.run] at agreement

/-- The vacuous overlap certificate refutes the old `PairwiseOverlapComplete` statement. -/
theorem old_pairwiseOverlapComplete_fails :
    ¬PairwiseOverlapComplete Cordis.Coeffect.Quotient.Example.coeffects := by
  intro complete
  exact old_observationalClosure_fails (complete computation .pure overlap_with_pure)

/-- The intrinsic path still identifies the selected two-stage execution. -/
example : computation.run Cordis.Coeffect.Quotient.Example.coeffects
    Cordis.Coeffect.Quotient.Example.left = some applied :=
  path.run_eq_some

namespace IndependentBranching

/-- Three heterogeneous coordinates make the non-vacuous cross-computation example explicit. -/
inductive DemoKey where
  | counter
  | label
  | flag
deriving DecidableEq, Repr

def DemoValue : DemoKey → Type
  | .counter => Nat
  | .label => String
  | .flag => Bool

/-- A Boolean operation with a Boolean outcome, independent of the number/string computation. -/
def flagCoeffect : Coeffect.CoeffectAt Bool where
  equivalence := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }
  Op := Unit
  Input := fun _ ↦ Unit
  Outcome := fun _ ↦ Bool
  Enabled := fun _ _ _ ↦ True
  enabledDecidable := fun _ _ _ ↦ isTrue trivial
  run := fun _ _ before _ ↦
    ({
      after := !before
      undo := fun current ↦ !current
      undo_after := by cases before <;> rfl
    }, before)
  enabled_respects := by simp
  after_respects := by
    intro _ _ left right equal _ _
    subst right
    rfl
  undo_respects := by
    intro _ _ left right initialEqual _ _ leftCurrent rightCurrent currentEqual
    subst right
    subst rightCurrent
    rfl
  outcome_respects := by
    intro _ _ left right equal _ _
    exact equal

def demoCoeffects : (key : DemoKey) → Coeffect.CoeffectAt (DemoValue key)
  | .counter => Cordis.Coeffect.Quotient.Example.counterCoeffect
  | .label => Cordis.Coeffect.Quotient.Example.labelCoeffect
  | .flag => flagCoeffect

def counterOp : (demoCoeffects .counter).Op := show Unit from ()
def counterInput : (demoCoeffects .counter).Input counterOp := show Nat from 4
def labelOp : (demoCoeffects .label).Op := show Unit from ()
def flagOp : (demoCoeffects .flag).Op := show Unit from ()
def flagInput : (demoCoeffects .flag).Input flagOp := show Unit from ()

/-- The `Nat` outcome chooses a `String` input, so this is genuinely heterogeneous branching. -/
def leftNext (previous : (demoCoeffects .counter).Outcome counterOp) :
    OperationIndependence.Computation demoCoeffects :=
  .step .label labelOp
    (if (show Nat from previous) = 3 then
      show String from "-three"
    else
      show String from "-other")
    (fun _ ↦ .pure)

def leftComputation : OperationIndependence.Computation demoCoeffects :=
  .step .counter counterOp counterInput leftNext

/-- The foreign computation has a Boolean outcome and touches only the third coordinate. -/
def rightComputation : OperationIndependence.Computation demoCoeffects :=
  .step .flag flagOp flagInput (fun _ ↦ .pure)

theorem left_occurs_key {stage : StageSyntax demoCoeffects}
    (occurs : Occurs stage leftComputation) :
    stage.key = .counter ∨ stage.key = .label := by
  cases occurs with
  | root => exact Or.inl rfl
  | continuation outcome tailOccurs =>
      change Occurs stage (leftNext outcome) at tailOccurs
      unfold leftNext at tailOccurs
      cases tailOccurs with
      | root => exact Or.inr rfl
      | continuation _ impossible => cases impossible

theorem right_occurs_key {stage : StageSyntax demoCoeffects}
    (occurs : Occurs stage rightComputation) : stage.key = .flag := by
  cases occurs with
  | root => rfl
  | continuation _ impossible => cases impossible

/-- Every actual cross pair is at distinct keys, so Theorem 40 supplies its full finite
generator-word certificate.
-/
theorem overlap : PairwiseOverlap demoCoeffects leftComputation rightComputation := by
  intro leftStage rightStage leftOccurs rightOccurs
  have rightKey := right_occurs_key rightOccurs
  rcases left_occurs_key leftOccurs with leftKey | leftKey
  · rw [leftKey, rightKey]
    exact OperationIndependence.distinctKeys_finiteIndependent demoCoeffects
      .counter .flag (by intro equal; cases equal)
  · rw [leftKey, rightKey]
    exact OperationIndependence.distinctKeys_finiteIndependent demoCoeffects
      .label .flag (by intro equal; cases equal)

/-- Non-vacuous heterogeneous branching satisfies the exact corrected finite theorem. -/
theorem independent : BoundedPartialIndependence
    (coeffects := demoCoeffects) leftComputation rightComputation :=
  pairwiseOverlap_boundedPartialIndependence leftComputation rightComputation overlap

def initialCounter : DemoValue .counter := show Nat from 3
def initialLabel : DemoValue .label := show String from "a"
def initialFlag : DemoValue .flag := show Bool from false

def initial : Coeffect.Context DemoKey DemoValue :=
  Coeffect.setAt
    (Coeffect.setAt
      (Coeffect.setAt Coeffect.empty .counter initialCounter)
      .label initialLabel)
    .flag initialFlag

theorem left_run_isSome : (leftComputation.run demoCoeffects initial).isSome = true := rfl
theorem right_run_isSome : (rightComputation.run demoCoeffects initial).isSome = true := rfl

def leftApplied : Cordis.Applied (Coeffect.Context DemoKey DemoValue) initial :=
  (leftComputation.run demoCoeffects initial).get left_run_isSome

def expectedLabel : DemoValue .label := show String from "a-three"

/-- The selected branch used the `Nat` result as the `String` operation input. -/
example : leftApplied.after .label = some expectedLabel := rfl

/-- The concrete heterogeneous branch retains exact LIFO recovery. -/
example : leftApplied.undo leftApplied.after = initial := leftApplied.undo_after

end IndependentBranching

end Example

end Cordis.MediatedTheorem
