import Cordis.GlobalIteratorIndependence

/-!
# Bounded global transposition ingredients

This module implements the bounded consequences specified in
`docs/GLOBAL_TRANSPOSITION_SPEC.md`, against CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

Definition 60 independence gives an exact raw execution diamond for two reachable iterator
codes and exact or `EffectEquiv`-relational squares for explicitly totalized global step maps.
Lifecycle phases retain syntactic `UndoCode`s, so `LifecycleYieldAgrees` names the strictly
stronger equality needed before lifting a raw diamond through L-Iter or L-Finish edits. A finite
counterexample shows that equal interpreted inverse functions do not imply equal stored codes.

The structural `setPhase` commutation theorem and the noncircular
`ForeignPhaseCompatibility` contract expose two further ingredients for a later lifecycle
transposition theorem. The contract is deliberately stated below `Transition` and `Step`, using
only `executeOne`, exact source lookup, foreign phase editing, and lifecycle-yield agreement.

This module does not prove off-source totalization, derive `ProgramRespects` from `EffectEquiv`,
or show that iterators ignore foreign control. It does not assign every landing to one fixed
program/oracle occurrence, preserve lifecycle guards or targets, transpose lifecycle steps, or
prove either clause of paper Lemma 71. Lemmas 68, 70, and 72, mixed-trace reordering, Theorem 61,
Corollary 62, and confluence also remain outside this bounded layer.
-/

set_option autoImplicit false

namespace Cordis.GlobalTransposition

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus
open Cordis.GlobalLifecycle Cordis.GlobalTemporal
open Cordis.GlobalIteratorIndependence

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Raw Definition 60 execution diamond -/

/-- The two off-axis successful executions, stable yields, and common raw endpoint. -/
structure ForwardDiamond
    {dynamics : Dynamics sig catalog Ambient}
    {left right : Program dynamics}
    {leftCode rightCode : sig.IteratorCode} {origin : State catalog Ambient}
    (leftStep : IterationStep dynamics left.owner leftCode origin)
    (rightStep : IterationStep dynamics right.owner rightCode origin) where
  rightAfterLeft : IterationStep dynamics right.owner rightCode leftStep.after
  leftAfterRight : IterationStep dynamics left.owner leftCode rightStep.after
  right_executed :
    executeOne dynamics right.oracle rightCode leftStep.after = .ok rightAfterLeft
  left_executed :
    executeOne dynamics left.oracle leftCode rightStep.after = .ok leftAfterRight
  right_yield : YieldAgrees rightAfterLeft rightStep
  left_yield : YieldAgrees leftAfterRight leftStep
  endpoint_eq : rightAfterLeft.after = leftAfterRight.after

/-- All three Definition 60 fields are used: both yield-stability directions construct the
off-axis executions, and closure commutation identifies their raw successors. -/
noncomputable def independent_forward_diamond
    {dynamics : Dynamics sig catalog Ambient}
    {left right : Program dynamics}
    (independent : Independent left right)
    {leftCode rightCode : sig.IteratorCode} {origin : State catalog Ambient}
    (leftReachable : Reach left leftCode) (rightReachable : Reach right rightCode)
    (leftStep : IterationStep dynamics left.owner leftCode origin)
    (rightStep : IterationStep dynamics right.owner rightCode origin)
    (leftExecuted : executeOne dynamics left.oracle leftCode origin = .ok leftStep)
    (rightExecuted : executeOne dynamics right.oracle rightCode origin = .ok rightStep) :
    ForwardDiamond leftStep rightStep := by
  have leftForwardAtOrigin : forward left leftCode origin = some leftStep.after := by
    simp [forward, leftExecuted]
  have rightForwardAtOrigin : forward right rightCode origin = some rightStep.after := by
    simp [forward, rightExecuted]
  have rightExists := independent.right_yield_stable
    (.generator (.forward leftReachable)) rightReachable origin rightStep
      leftStep.after rightExecuted leftForwardAtOrigin
  let rightAfterLeft := Classical.choose rightExists
  have rightAfterLeftExecuted := (Classical.choose_spec rightExists).1
  have rightYield := (Classical.choose_spec rightExists).2
  have rightForwardAfterLeft :
      forward right rightCode leftStep.after = some rightAfterLeft.after := by
    unfold forward
    rw [rightAfterLeftExecuted]
  have leftExists := independent.left_yield_stable
    (.generator (.forward rightReachable)) leftReachable origin leftStep
      rightStep.after leftExecuted rightForwardAtOrigin
  let leftAfterRight := Classical.choose leftExists
  have leftAfterRightExecuted := (Classical.choose_spec leftExists).1
  have leftYield := (Classical.choose_spec leftExists).2
  have leftForwardAfterRight :
      forward left leftCode rightStep.after = some leftAfterRight.after := by
    unfold forward
    rw [leftAfterRightExecuted]
  have commute := independent.transformations_commute
    (.generator (.forward leftReachable)) (.generator (.forward rightReachable))
  have atOrigin := commute origin
  unfold Cordis.PartialTransformation.comp at atOrigin
  rw [rightForwardAtOrigin, leftForwardAtOrigin] at atOrigin
  simp only [Option.bind_some] at atOrigin
  rw [leftForwardAfterRight,
    rightForwardAfterLeft] at atOrigin
  exact {
    rightAfterLeft := rightAfterLeft
    leftAfterRight := leftAfterRight
    right_executed := rightAfterLeftExecuted
    left_executed := leftAfterRightExecuted
    right_yield := rightYield
    left_yield := leftYield
    endpoint_eq := Option.some.inj atOrigin.symm
  }

/-! ## Explicitly totalized global step-map squares -/

/-- One global step with both its off-source totalization and program/owner closure evidence. -/
structure TotalProgramStep
    {dynamics : Dynamics sig catalog Ambient}
    (effect : EffectEquiv dynamics) (program : Program dynamics)
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  map : TotalStepMap effect step
  generated : StepMapMember program step

namespace TotalProgramStep

/-- Exact representative commutation of the supplied total maps. Totality is rewritten from the
certificate and is never inferred from an indexed source execution. -/
theorem commute_exact
    {dynamics : Dynamics sig catalog Ambient} {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics}
    (independent : Independent leftProgram rightProgram)
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {leftStep : Step dynamics inertia leftBefore leftAfter}
    {rightStep : Step dynamics inertia rightBefore rightAfter}
    (left : TotalProgramStep effect leftProgram leftStep)
    (right : TotalProgramStep effect rightProgram rightStep)
    (state : State catalog Ambient) :
    left.map.apply (right.map.apply state) =
      right.map.apply (left.map.apply state) := by
  have commutes := independent.transformations_commute
    left.generated.member right.generated.member
  have atState := commutes state
  unfold Cordis.PartialTransformation.comp at atState
  rw [right.map.total state, left.map.total state] at atState
  simp only [Option.bind_some] at atState
  rw [left.map.total (right.map.apply state),
    right.map.total (left.map.apply state)] at atState
  exact Option.some.inj atState

/-- The same square directly under the temporal effect relation. -/
theorem commute_effect
    {dynamics : Dynamics sig catalog Ambient} {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics}
    (independent : ObservationalIndependent effect leftProgram rightProgram)
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {leftStep : Step dynamics inertia leftBefore leftAfter}
    {rightStep : Step dynamics inertia rightBefore rightAfter}
    (left : TotalProgramStep effect leftProgram leftStep)
    (right : TotalProgramStep effect rightProgram rightStep)
    (state : State catalog Ambient) :
    effect.setoid.r
      (left.map.apply (right.map.apply state))
      (right.map.apply (left.map.apply state)) := by
  have commutes : Cordis.ObservationalPartialTransformation.Commutes
      effect.setoid.r (GlobalTemporal.Step.partialMap leftStep)
        (GlobalTemporal.Step.partialMap rightStep) :=
    independent.transformations_commute
      left.generated.member right.generated.member
  have outputs := commutes (leftState := state) (rightState := state)
    (effect.setoid.refl state)
  change Coeffect.Observational.OptionRelated effect.setoid.r
    ((GlobalTemporal.Step.partialMap rightStep state).bind
      (GlobalTemporal.Step.partialMap leftStep))
    ((GlobalTemporal.Step.partialMap leftStep state).bind
      (GlobalTemporal.Step.partialMap rightStep)) at outputs
  rw [right.map.total state, left.map.total state] at outputs
  simp only [Option.bind_some] at outputs
  rw [left.map.total (right.map.apply state),
    right.map.total (left.map.apply state)] at outputs
  cases outputs with
  | some related => exact related

end TotalProgramStep

/-! ## Lifecycle-visible yield agreement -/

/-- Stronger agreement for information written into lifecycle phases. Unlike Definition 60's
semantic inverse relation, this retains exact syntactic `UndoCode` equality. -/
structure LifecycleYieldAgrees
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {code : sig.IteratorCode} {leftState rightState : State catalog Ambient}
    (left : IterationStep dynamics program.owner code leftState)
    (right : IterationStep dynamics program.owner code rightState) : Prop where
  undo_eq : left.undo = right.undo
  continuation : left.next = right.next
  kind : sourceKind left = sourceKind right

namespace LifecycleYieldAgrees

theorem toYieldAgrees
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {code : sig.IteratorCode} {leftState rightState : State catalog Ambient}
    {left : IterationStep dynamics program.owner code leftState}
    {right : IterationStep dynamics program.owner code rightState}
    (agrees : LifecycleYieldAgrees left right) : YieldAgrees left right where
  inverse := by rw [agrees.undo_eq]
  continuation := agrees.continuation
  kind := agrees.kind

end LifecycleYieldAgrees

/-! ## Structural phase-edit commutation -/

/-- Updating two distinct names commutes exactly. This theorem says nothing about iterator
definedness or yield stability after either edit. -/
theorem setPhase_commute
    (state : State catalog Ambient) (leftName rightName : sig.Name)
    (leftFiber rightFiber : Fiber catalog)
    (leftPhase : Phase (catalog.declaration leftFiber.component))
    (rightPhase : Phase (catalog.declaration rightFiber.component))
    (different : leftName ≠ rightName) :
    setPhase (setPhase state leftName leftFiber leftPhase)
        rightName rightFiber rightPhase =
      setPhase (setPhase state rightName rightFiber rightPhase)
        leftName leftFiber leftPhase := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [setPhase, GlobalState.mk.injEq]
      exact ⟨trivial, trivial,
        Coeffect.setAt_commute registry leftName rightName different
          { leftFiber with phase := leftPhase }
          { rightFiber with phase := rightPhase }⟩

/-! ## Noncircular future phase-frame contract -/

/-- The lower-level premise missing before a raw forward diamond can pass through a foreign
phase edit. It mentions neither lifecycle transitions nor unified steps or swapped endpoints. -/
structure ForeignPhaseCompatibility
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics) : Prop where
  execute_setPhase :
    ∀ {code : sig.IteratorCode} {state : State catalog Ambient}
      {step : IterationStep dynamics program.owner code state}
      {foreignName : sig.Name} {foreignFiber : Fiber catalog}
      {foreignPhase : Phase (catalog.declaration foreignFiber.component)},
      Reach program code →
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      executeOne dynamics program.oracle code state = .ok step →
      ∃ movedStep,
        executeOne dynamics program.oracle code
            (setPhase state foreignName foreignFiber foreignPhase) = .ok movedStep ∧
        LifecycleYieldAgrees movedStep step ∧
        movedStep.after =
          setPhase step.after foreignName foreignFiber foreignPhase

/-! ## Noninjective interpreted-undo counterexample -/

namespace Counterexample

abbrev Signature : StaticSignature where
  Name := Unit
  Key := Unit
  ComponentId := Unit
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Bool
  Value _ := Unit
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def declaration : ComponentDecl Signature where
  dependencies := { keys := [], nodup := by simp }
  provision := []
  provision_nodup := by simp
  entry := ()

abbrev exampleCatalog : Catalog Signature where
  declaration _ := declaration

abbrev ExampleState := GlobalState exampleCatalog Bool

def fiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def state (ambient : Bool) : ExampleState where
  ambient := ambient
  nextBirth := 1
  registry := Coeffect.setAt Coeffect.empty () fiber

theorem state_present (ambient : Bool) : (state ambient).registry () = some fiber := rfl

def stateSetoid : Setoid ExampleState where
  r := Eq
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }

def runIterator (_owner : Unit) (_code : Unit) (before : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Bool) :=
  match before.registry () with
  | none => .error ()
  | some _ => .ok (.ordinary {
      after := before
      undo := before.ambient
      next := none
    })

def applyExternalUndo (_code : Bool) (before : ExampleState) : ExampleState := before

theorem runRelatedRefl
    (result : Except Unit (IteratorResult exampleCatalog Bool)) :
    RunRelated (fun left right : ExampleState ↦ left = right) result result := by
  cases result with
  | error error => exact .errors rfl
  | ok result =>
      cases result with
      | ordinary ordinary => exact .results (.ordinary rfl rfl rfl)
      | register request => exact .results (.register rfl rfl)

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := stateSetoid
  runIterator := runIterator
  applyExternalUndo := applyExternalUndo
  ordinary_recovers := by
    intro owner code before result runEq
    cases lookup : before.registry () with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst result
        rfl
  externalUndo_respects := by
    intro undo left right related
    subst right
    rfl
  ordinary_confined := by
    intro owner code before result runEq
    cases lookup : before.registry () with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst result
        exact {
          beforeFiber := current
          afterFiber := current
          before_present := lookup
          after_present := lookup
          component_eq := rfl
          parent_eq := rfl
          birth_eq := rfl
          retired_eq := rfl
          phase_eq := rfl
          other_unchanged := by
            intro name different
            exact False.elim (different (Subsingleton.elim _ _))
          table_writes := by
            unfold WritesWithinProvision
            intros
            rfl
          nextBirth_eq := rfl
        }
  ordinary_preserves_wellFormed := by
    intro owner code before result runEq wf
    cases lookup : before.registry () with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst result
        exact wf
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    subst right
    exact runRelatedRefl _
  ReadEquivalent _ left right := left = right
  read_refl := by intros; rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    subst right
    exact runRelatedRefl _
  retire_respects := by
    intro name left right related
    subst right
    rfl

def oracle : RegistrationOracle dynamics () Unit where
  certify _ _ := .error ()

def falseResult : OrdinaryResult exampleCatalog Bool where
  after := state false
  undo := false
  next := none

def trueResult : OrdinaryResult exampleCatalog Bool where
  after := state true
  undo := true
  next := none

def falseStep : IterationStep dynamics () () (state false) where
  after := falseResult.after
  undo := .external falseResult.undo
  next := falseResult.next
  source := .ordinary falseResult rfl
  recovers := rfl
  preserves_wellFormed := fun wf ↦ wf

def trueStep : IterationStep dynamics () () (state true) where
  after := trueResult.after
  undo := .external trueResult.undo
  next := trueResult.next
  source := .ordinary trueResult rfl
  recovers := rfl
  preserves_wellFormed := fun wf ↦ wf

theorem false_executed : executeOne dynamics oracle () (state false) = .ok falseStep := rfl

theorem true_executed : executeOne dynamics oracle () (state true) = .ok trueStep := rfl

def program : Program dynamics where
  owner := ()
  RegistrationError := Unit
  oracle := oracle
  root := ()

theorem interpreted_inverses_equal :
    dynamics.applyUndo falseStep.undo = dynamics.applyUndo trueStep.undo := rfl

theorem semantic_yields_agree :
    YieldAgrees (program := program) falseStep trueStep where
  inverse := rfl
  continuation := rfl
  kind := rfl

theorem undo_codes_differ : falseStep.undo ≠ trueStep.undo := by
  intro equal
  cases equal

theorem lifecycle_yields_do_not_agree :
    ¬LifecycleYieldAgrees (program := program) falseStep trueStep := by
  intro agrees
  exact undo_codes_differ agrees.undo_eq

end Counterexample

end Cordis.GlobalTransposition
