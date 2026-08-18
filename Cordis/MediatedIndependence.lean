import Cordis.OperationIndependence
import Cordis.Transformation
import Cordis.Removal

/-!
# Realized mediated branches and the exact Theorem 42 boundary

This module attacks the bounded CORDIS Theorem 42 frontier at paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

`RealizedPath` is an intrinsic execution witness for Definition 41. Every constructor retains
the stage key, operation, typed input, typed outcome, application state, lifted successor,
state-dependent yielded inverse, and a tail indexed by the continuation selected by that exact
outcome. `RealizedPath.run_eq_some` connects every witness soundly to `Computation.run`.

The paper reads Definition 19 and Theorem 42 after Lemma 38 up to observational equivalence.
The repository's current `MediatedClosure`, however, asks for exact equality of successor
contexts and inverse functions. A finite counterexample below uses operations whose local
successors, inverses, and outcomes respect universal observational equivalence, but whose two
orders choose different exact representatives. It therefore refutes promotion from that
quotient reading to exact `MediatedClosure`.

`ExactRepresentativeCoherence` isolates the missing equality-strength law. This module does
not assume it and call the result Theorem 42; nor does it replace branch closure with adjacent
effect swapping.
-/

set_option autoImplicit false

namespace Cordis.MediatedIndependence

universe u v w

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

abbrev DepContext (Key : Type u) [DecidableEq Key] (Value : Key → Type v) :=
  Coeffect.Context Key Value

abbrev CoeffectFamily (Key : Type u) (Value : Key → Type v) :=
  (key : Key) → Coeffect.CoeffectAt.{v, w} (Value key)

/-!
## Intrinsic Definition 41 execution paths
-/

/-- Compose two already-applied effects in the LIFO order of Definition 41. -/
def composeApplied {State : Type u} {before : State}
    (first : Cordis.Applied State before)
    (second : Cordis.Applied State first.after) : Cordis.Applied State before where
  after := second.after
  undo := first.undo ∘ second.undo
  undo_after := by
    exact Eq.trans (congrArg first.undo second.undo_after) first.undo_after

/-- The exact lifted result of one enabled Definition 41 stage. -/
def stageResult
    (coeffects : CoeffectFamily.{u, v, w} Key Value)
    (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
    (before : DepContext Key Value) (value : Value key) (lookup : before key = some value)
    (enabled : (coeffects key).Enabled op input value) :
    Cordis.Applied (DepContext Key Value) before × (coeffects key).Outcome op :=
  (coeffects key).lift op input before ⟨value, lookup⟩ enabled

/-- A reified stage retaining all heterogeneous and state-dependent execution data. -/
structure RealizedStage
    (coeffects : CoeffectFamily.{u, v, w} Key Value) where
  key : Key
  op : (coeffects key).Op
  input : (coeffects key).Input op
  outcome : (coeffects key).Outcome op
  before : DepContext Key Value
  after : DepContext Key Value
  undo : DepContext Key Value → DepContext Key Value

/-- Intrinsic realized branch of an outcome-mediated computation. -/
inductive RealizedPath
    (coeffects : CoeffectFamily.{u, v, w} Key Value) :
    (computation : OperationIndependence.Computation coeffects) →
      (before : DepContext Key Value) →
        Cordis.Applied (DepContext Key Value) before → Type (max u v w) where
  /-- The unit branch has no stages and applies the identity effect. -/
  | pure (context : DepContext Key Value) :
      RealizedPath coeffects .pure context (Cordis.Effect.identity context)
  /-- One enabled stage followed by the continuation selected by its exact outcome. -/
  | step (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op)
      (next : (coeffects key).Outcome op → OperationIndependence.Computation coeffects)
      (before : DepContext Key Value) (value : Value key) (lookup : before key = some value)
      (enabled : (coeffects key).Enabled op input value)
      (continuation : Cordis.Applied (DepContext Key Value)
        (stageResult coeffects key op input before value lookup enabled).1.after)
      (tail : RealizedPath coeffects
        (next (stageResult coeffects key op input before value lookup enabled).2)
        (stageResult coeffects key op input before value lookup enabled).1.after continuation)
      (sound : OperationIndependence.Computation.run coeffects
        (.step key op input next) before =
          some (composeApplied
            (stageResult coeffects key op input before value lookup enabled).1 continuation)) :
      RealizedPath coeffects (.step key op input next) before
        (composeApplied (stageResult coeffects key op input before value lookup enabled).1
          continuation)

namespace RealizedPath

/-- Extract all realized stages in execution order. -/
def stages
    {coeffects : CoeffectFamily.{u, v, w} Key Value}
    {computation : OperationIndependence.Computation coeffects}
    {before : DepContext Key Value}
    {applied : Cordis.Applied (DepContext Key Value) before}
    (path : RealizedPath coeffects computation before applied) :
    List (RealizedStage coeffects) :=
  match path with
  | .pure _ => []
  | .step key op input _ before value lookup enabled continuation tail _ =>
      let stage := stageResult _ key op input before value lookup enabled
      ⟨key, op, input, stage.2, before, stage.1.after, stage.1.undo⟩ :: tail.stages

/-- Every intrinsic path denotes the same successful execution as `Computation.run`. -/
theorem run_eq_some
    {coeffects : CoeffectFamily.{u, v, w} Key Value}
    {computation : OperationIndependence.Computation coeffects}
    {before : DepContext Key Value}
    {applied : Cordis.Applied (DepContext Key Value) before}
    (path : RealizedPath coeffects computation before applied) :
    computation.run coeffects before = some applied := by
  cases path with
  | pure => rfl
  | step _ _ _ _ _ _ _ _ _ _ sound => exact sound

end RealizedPath

/-!
## Syntactic occurrence and non-circular overlap hypotheses
-/

/-- One operation call occurring in Definition 41 syntax. -/
structure StageSyntax
    (coeffects : CoeffectFamily.{u, v, w} Key Value) where
  key : Key
  op : (coeffects key).Op
  input : (coeffects key).Input op

/-- A stage occurs at the root or in one of the outcome-selected continuations. -/
inductive Occurs
    {coeffects : CoeffectFamily.{u, v, w} Key Value} :
    StageSyntax coeffects → OperationIndependence.Computation coeffects → Prop where
  | root (key : Key) (op : (coeffects key).Op) (input : (coeffects key).Input op) next :
      Occurs ⟨key, op, input⟩ (.step key op input next)
  | continuation {stage : StageSyntax coeffects} {key : Key}
      {op : (coeffects key).Op} {input : (coeffects key).Input op} {next}
      (outcome : (coeffects key).Outcome op) (occurs : Occurs stage (next outcome)) :
      Occurs stage (.step key op input next)

/-- Pairwise cross-computation hypothesis over all syntactically possible branches.

`FiniteKeyIndependent` includes arbitrary finite forward/inverse words and stability of the
complete successor/inverse/outcome data. This predicate does not mention realized paths or
`MediatedClosure`, so it is non-circular.
-/
def PairwiseOverlap
    (coeffects : CoeffectFamily.{u, v, w} Key Value)
    (left right : OperationIndependence.Computation coeffects) : Prop :=
  ∀ leftStage rightStage, Occurs leftStage left → Occurs rightStage right →
    OperationIndependence.FiniteKeyIndependent coeffects leftStage.key rightStage.key

/-!
## Observational mediated closure and equality-strength boundary
-/

/-- The quotient-reading analogue of `OperationIndependence.MediatedClosure`.

Both orders must agree on definedness. Successful orders need only produce Definition 33
related successors and related inverse actions. The second field is the observational form of
stability for the complete inverse yielded by either computation under the other.
-/
structure ObservationalMediatedClosure
    (coeffects : CoeffectFamily.{u, v, w} Key Value)
    (left right : OperationIndependence.Computation coeffects) : Prop where
  orders_related : ∀ before,
    match left.run coeffects before, right.run coeffects before with
    | none, none => True
    | some leftApplied, some rightApplied =>
        match right.run coeffects leftApplied.after,
          left.run coeffects rightApplied.after with
        | some leftThenRight, some rightThenLeft =>
            Coeffect.Observational.Related
              (Coeffect.Observational.equivalencesOf coeffects)
              leftThenRight.after rightThenLeft.after ∧
            (∀ current,
              Coeffect.Observational.Related
                (Coeffect.Observational.equivalencesOf coeffects)
                (leftApplied.undo (leftThenRight.undo current))
                (rightApplied.undo (rightThenLeft.undo current)))
        | _, _ => False
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

/-- The still-unproved structural induction frontier: pairwise syntactic overlap must promote
to observational closure for all outcome-selected branches.
-/
def PairwiseOverlapComplete
    (coeffects : CoeffectFamily.{u, v, w} Key Value) : Prop :=
  ∀ left right, PairwiseOverlap coeffects left right →
    ObservationalMediatedClosure coeffects left right

/-- The missing law required to turn observationally related representatives into the exact
equalities demanded by the current `MediatedClosure` API.
-/
def ExactRepresentativeCoherence
    (equivalences : Coeffect.Observational.Equivalences Key Value) : Prop :=
  ∀ {left right : DepContext Key Value},
    Coeffect.Observational.Related equivalences left right → left = right

/-- Representative coherence promotes the observational certificate to exact closure. -/
theorem ObservationalMediatedClosure.toExact
    {coeffects : CoeffectFamily.{u, v, w} Key Value}
    {left right : OperationIndependence.Computation coeffects}
    (closure : ObservationalMediatedClosure coeffects left right)
    (coherent : ExactRepresentativeCoherence
      (Coeffect.Observational.equivalencesOf coeffects)) :
    OperationIndependence.MediatedClosure coeffects left right := by
  constructor
  · intro before
    have related := closure.orders_related before
    cases leftRun : left.run coeffects before with
    | none =>
        cases rightRun : right.run coeffects before <;>
          simp [leftRun, rightRun] at related ⊢
    | some leftApplied =>
        cases rightRun : right.run coeffects before with
        | none => simp [leftRun, rightRun] at related
        | some rightApplied =>
            cases leftThenRightRun : right.run coeffects leftApplied.after with
            | none => simp [leftRun, rightRun, leftThenRightRun] at related
            | some leftThenRight =>
                cases rightThenLeftRun : left.run coeffects rightApplied.after with
                | none =>
                    simp [leftRun, rightRun, leftThenRightRun, rightThenLeftRun] at related
                | some rightThenLeft =>
                    simp [leftRun, rightRun, leftThenRightRun, rightThenLeftRun] at related ⊢
                    exact ⟨coherent related.1, fun current ↦ coherent (related.2 current)⟩
  · intro before leftApplied rightApplied leftRun rightRun
    have related := closure.yielded_inverse_related before leftApplied rightApplied
      leftRun rightRun
    exact ⟨fun current ↦ coherent (related.1 current),
      fun current ↦ coherent (related.2 current)⟩

/-!
## Finite quotient counterexample
-/

namespace Counterexample

inductive ExampleKey where
  | cell
deriving DecidableEq, Repr

structure Cell where
  hidden : Bool
deriving DecidableEq, Repr

def ExampleValue : ExampleKey → Type
  | .cell => Cell

inductive Op where
  | writeFalse
  | writeTrue
deriving DecidableEq, Repr

def Input : Op → Type
  | .writeFalse => Unit
  | .writeTrue => Unit

def Outcome : Op → Type
  | .writeFalse => Unit
  | .writeTrue => Unit

def universalCellSetoid : Setoid Cell where
  r := fun _ _ ↦ True
  iseqv := {
    refl := fun _ ↦ trivial
    symm := fun _ ↦ trivial
    trans := fun _ _ ↦ trivial
  }

/-- Both writes are observationally identical but select different exact representatives. -/
def cellCoeffect : Coeffect.CoeffectAt Cell where
  equivalence := universalCellSetoid
  Op := Op
  Input := Input
  Outcome := Outcome
  Enabled := fun _ _ _ ↦ True
  enabledDecidable := fun _ _ _ ↦ isTrue trivial
  run op _ before _ :=
    match op with
    | .writeFalse =>
        ({ after := ⟨false⟩
           undo := fun _ ↦ before
           undo_after := rfl }, ())
    | .writeTrue =>
        ({ after := ⟨true⟩
           undo := fun _ ↦ before
           undo_after := rfl }, ())
  enabled_respects := by simp
  after_respects := by
    intro op input left right related leftEnabled rightEnabled
    trivial
  undo_respects := by
    intro op input left right related leftEnabled rightEnabled leftCurrent rightCurrent
      currentsRelated
    trivial
  outcome_respects := by
    intro op input left right related leftEnabled rightEnabled
    cases op <;> rfl

def coeffects : (key : ExampleKey) → Coeffect.CoeffectAt (ExampleValue key)
  | .cell => cellCoeffect

def initialCell : ExampleValue .cell := ⟨false⟩
def initial : Coeffect.Context ExampleKey ExampleValue :=
  Coeffect.setAt Coeffect.empty .cell initialCell

def falseOp : (coeffects .cell).Op := show Op from .writeFalse
def trueOp : (coeffects .cell).Op := show Op from .writeTrue
def falseInput : (coeffects .cell).Input falseOp := show Unit from ()
def trueInput : (coeffects .cell).Input trueOp := show Unit from ()

def falseComputation : OperationIndependence.Computation coeffects :=
  .step .cell falseOp falseInput (fun _ ↦ .pure)

def trueComputation : OperationIndependence.Computation coeffects :=
  .step .cell trueOp trueInput (fun _ ↦ .pure)

theorem false_run_isSome : (falseComputation.run coeffects initial).isSome = true := rfl
theorem true_run_isSome : (trueComputation.run coeffects initial).isSome = true := rfl

theorem initial_lookup : initial .cell = some initialCell := by simp [initial]

def falseStage :=
  stageResult coeffects .cell falseOp falseInput initial initialCell initial_lookup trivial

def trueStage :=
  stageResult coeffects .cell trueOp trueInput initial initialCell initial_lookup trivial

def falseApplied : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue) initial :=
  composeApplied falseStage.1 (Cordis.Effect.identity falseStage.1.after)

def trueApplied : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue) initial :=
  composeApplied trueStage.1 (Cordis.Effect.identity trueStage.1.after)

/-- Both exact results are related by the paper's quotient relation. -/
theorem results_related :
    Coeffect.Observational.Related (Coeffect.Observational.equivalencesOf coeffects)
      falseApplied.after trueApplied.after := by
  intro key
  cases key
  exact Coeffect.Observational.OptionRelated.some trivial

/-- Under universal value equivalence, equal presence is sufficient for context relatedness. -/
theorem related_of_presence_eq
    {left right : Coeffect.Context ExampleKey ExampleValue}
    (presence : (left .cell).isSome = (right .cell).isSome) :
    Coeffect.Observational.Related (Coeffect.Observational.equivalencesOf coeffects)
      left right := by
  intro key
  cases key
  cases leftLookup : left .cell with
  | none =>
      cases rightLookup : right .cell with
      | none => exact Coeffect.Observational.OptionRelated.none
      | some value => simp [leftLookup, rightLookup] at presence
  | some leftValue =>
      cases rightLookup : right .cell with
      | none => simp [leftLookup, rightLookup] at presence
      | some rightValue => exact Coeffect.Observational.OptionRelated.some trivial

theorem false_run_eq : falseComputation.run coeffects initial = some falseApplied := rfl
theorem true_run_eq : trueComputation.run coeffects initial = some trueApplied := rfl

theorem true_after_false_isSome :
    (trueComputation.run coeffects falseApplied.after).isSome = true := rfl

theorem false_after_true_isSome :
    (falseComputation.run coeffects trueApplied.after).isSome = true := rfl

def falseCell : ExampleValue .cell := ⟨false⟩
def trueCell : ExampleValue .cell := ⟨true⟩

theorem falseApplied_lookup : falseApplied.after .cell = some falseCell := rfl
theorem trueApplied_lookup : trueApplied.after .cell = some trueCell := rfl

def trueAfterFalseStage :=
  stageResult coeffects .cell trueOp trueInput falseApplied.after falseCell
    falseApplied_lookup trivial

def falseAfterTrueStage :=
  stageResult coeffects .cell falseOp falseInput trueApplied.after trueCell
    trueApplied_lookup trivial

def falseThenTrue : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue)
    falseApplied.after :=
  composeApplied trueAfterFalseStage.1 (Cordis.Effect.identity trueAfterFalseStage.1.after)

def trueThenFalse : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue)
    trueApplied.after :=
  composeApplied falseAfterTrueStage.1 (Cordis.Effect.identity falseAfterTrueStage.1.after)

theorem falseThenTrue_run_eq :
    trueComputation.run coeffects falseApplied.after = some falseThenTrue := rfl

theorem trueThenFalse_run_eq :
    falseComputation.run coeffects trueApplied.after = some trueThenFalse := rfl

/-- At the concrete realized branch, both order-successors satisfy the quotient conclusion. -/
theorem sequential_results_related :
    Coeffect.Observational.Related (Coeffect.Observational.equivalencesOf coeffects)
      falseThenTrue.after trueThenFalse.after := by
  intro key
  cases key
  exact Coeffect.Observational.OptionRelated.some trivial

/-- The two execution orders choose different exact representatives. -/
theorem exact_orders_differ : falseThenTrue.after ≠ trueThenFalse.after := by
  intro equal
  have atCell := congrArg (fun context ↦ context .cell) equal
  change some (show ExampleValue .cell from ⟨true⟩) =
    some (show ExampleValue .cell from ⟨false⟩) at atCell
  have cellEqual := Option.some.inj atCell
  have hiddenEqual := congrArg Cell.hidden cellEqual
  cases hiddenEqual

/-- Consequently the exact `MediatedClosure` conclusion is unavailable without representative
coherence, even though the quotient identifies the results.
-/
theorem exact_mediatedClosure_fails :
    ¬OperationIndependence.MediatedClosure coeffects falseComputation trueComputation := by
  intro closure
  have agreement := closure.orders_agree initial
  rw [false_run_eq, true_run_eq] at agreement
  simp only at agreement
  rw [falseThenTrue_run_eq, trueThenFalse_run_eq] at agreement
  exact exact_orders_differ agreement.1

/-- Universal cell equivalence does not determine exact representatives. -/
theorem representative_coherence_fails :
    ¬ExactRepresentativeCoherence (Coeffect.Observational.equivalencesOf coeffects) := by
  intro coherent
  have equal := coherent results_related
  have atCell := congrArg (fun context ↦ context .cell) equal
  change some (show ExampleValue .cell from ⟨false⟩) =
    some (show ExampleValue .cell from ⟨true⟩) at atCell
  have cellEqual := Option.some.inj atCell
  have hiddenEqual := congrArg Cell.hidden cellEqual
  cases hiddenEqual

end Counterexample

/-!
## Heterogeneous branching path example
-/

namespace BranchExample

open Cordis.Coeffect.Quotient.Example

def labelOp : labelCoeffect.Op := show Unit from ()
def counterValue : ExampleValue .counter := show Nat from 3
def labelValue : ExampleValue .label := show String from "a"
def selectedSuffix : labelCoeffect.Input labelOp := show String from "-three"
def otherSuffix : labelCoeffect.Input labelOp := show String from "-other"

def finish (_ : labelCoeffect.Outcome labelOp) : OperationIndependence.Computation coeffects :=
  .pure

def labelComputation (suffix : labelCoeffect.Input labelOp) :
    OperationIndependence.Computation coeffects :=
  .step .label labelOp suffix finish

def choose (previous : counterCoeffect.Outcome counterOp) :
    OperationIndependence.Computation coeffects :=
  if (show Nat from previous) = 3 then labelComputation selectedSuffix
  else labelComputation otherSuffix

def computation : OperationIndependence.Computation coeffects :=
  .step .counter counterOp counterAmount choose

def firstStage :=
  stageResult coeffects .counter counterOp counterAmount left counterValue
    leftCounter.lookup_eq trivial

theorem firstStage_outcome : firstStage.2 = counterValue := rfl

theorem label_lookup : firstStage.1.after .label = some labelValue := rfl

def secondStage :=
  stageResult coeffects .label labelOp selectedSuffix firstStage.1.after labelValue
    label_lookup trivial

def finalApplied : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue) secondStage.1.after :=
  Cordis.Effect.identity secondStage.1.after

def terminalPath : RealizedPath coeffects .pure secondStage.1.after finalApplied :=
  .pure secondStage.1.after

def secondPath : RealizedPath coeffects (labelComputation selectedSuffix) firstStage.1.after
    (composeApplied secondStage.1 finalApplied) :=
  RealizedPath.step (coeffects := coeffects) .label labelOp selectedSuffix finish
    firstStage.1.after labelValue label_lookup trivial finalApplied terminalPath (by rfl)

def applied : Cordis.Applied (Coeffect.Context ExampleKey ExampleValue) left :=
  composeApplied firstStage.1 (composeApplied secondStage.1 finalApplied)

/-- The first `Nat` outcome selects the `String`-argument continuation witnessed by
`secondPath`.
-/
def path : RealizedPath coeffects computation left applied :=
  RealizedPath.step (coeffects := coeffects) .counter counterOp counterAmount choose left
    counterValue leftCounter.lookup_eq trivial (composeApplied secondStage.1 finalApplied)
    secondPath (by rfl)

example : computation.run coeffects left = some applied := path.run_eq_some
example : path.stages.length = 2 := rfl
example : applied.after .label = some (show ExampleValue .label from "a-three") := rfl
example : applied.undo applied.after = left := applied.undo_after

end BranchExample

/-!
The counterexample is not a refutation of the paper's quotient-reading Theorem 42: its two
orders are observationally related. It is a kernel-checked refutation of upgrading those
hypotheses to the exact equality currently required by `MediatedClosure`. A future full theorem
must prove `PairwiseOverlapComplete` for the observational mediated closure, or additionally
assume `ExactRepresentativeCoherence` when an exact `MediatedClosure` result is required.
-/

end Cordis.MediatedIndependence
