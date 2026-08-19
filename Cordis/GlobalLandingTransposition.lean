import Cordis.GlobalForeignPhase

/-!
# Exact program-aligned landing transposition

This module implements the bounded landing-only layer specified in
`docs/GLOBAL_LANDING_TRANSPOSITION_SPEC.md`, against CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

Ordinary iterator independence compares yielded inverse functions semantically. L-Iter and
L-Finish retain the syntactic `UndoCode`, so `ForwardLifecycleIndependent` separately requires
exact lifecycle-visible yield stability across the other program's raw forward generator. Under
that premise, both foreign-phase compatibility certificates, distinct owners, and a well-formed
common source, two program-aligned landing activations form an exact four-case diamond.

The theorem covers Iter/Iter, Iter/Finish, Finish/Iter, and Finish/Finish only. It does not cover
L-Begin, identify arbitrary trace steps with programs, establish episode-level root provenance,
transpose an existing trace, or prove paper Lemma 71, Theorem 61, Corollary 62, confluence, or
progress. Positive target preservation always requires source well-formedness; no theorem claims
full target-view equality or preservation from a target-free or ill-formed source.
-/

set_option autoImplicit false

namespace Cordis.GlobalLandingTransposition

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalIteratorIndependence Cordis.GlobalTransposition
open Cordis.GlobalForeignPhase

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Exact cross-forward lifecycle-yield stability -/

/-- Exact lifecycle-visible yield stability under one successful foreign possibly-undefined map. -/
def LifecycleYieldStable
    {dynamics : Dynamics sig catalog Ambient}
    (program : Program dynamics) (foreign : PartialMap catalog Ambient) : Prop :=
  ∀ {code : sig.IteratorCode}, Reach program code →
    ∀ seed step moved,
      executeOne dynamics program.oracle code seed = .ok step →
      foreign seed = some moved →
      ∃ movedStep,
        executeOne dynamics program.oracle code moved = .ok movedStep ∧
          LifecycleYieldAgrees movedStep step

/-- Semantic Definition 60 independence plus the exact cross-forward yield laws needed because
lifecycle phases retain syntactic undo codes. -/
structure ForwardLifecycleIndependent
    {dynamics : Dynamics sig catalog Ambient} (left right : Program dynamics) : Prop where
  independent : Independent left right
  left_under_right :
    ∀ {rightCode : sig.IteratorCode}, Reach right rightCode →
      LifecycleYieldStable left (forward right rightCode)
  right_under_left :
    ∀ {leftCode : sig.IteratorCode}, Reach left leftCode →
      LifecycleYieldStable right (forward left leftCode)

namespace LifecycleYieldAgrees

theorem refl
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {code : sig.IteratorCode} {state : State catalog Ambient}
    (step : IterationStep dynamics program.owner code state) :
    LifecycleYieldAgrees step step :=
  ⟨rfl, rfl, rfl⟩

theorem trans
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {code : sig.IteratorCode}
    {firstState secondState thirdState : State catalog Ambient}
    {first : IterationStep dynamics program.owner code firstState}
    {second : IterationStep dynamics program.owner code secondState}
    {third : IterationStep dynamics program.owner code thirdState}
    (left : LifecycleYieldAgrees first second)
    (right : LifecycleYieldAgrees second third) :
    LifecycleYieldAgrees first third :=
  ⟨left.undo_eq.trans right.undo_eq,
    left.continuation.trans right.continuation,
    left.kind.trans right.kind⟩

end LifecycleYieldAgrees

/-- The raw Definition 60 diamond strengthened with exact off-axis/common-source yield equality. -/
structure LifecycleForwardDiamond
    {dynamics : Dynamics sig catalog Ambient} {left right : Program dynamics}
    {leftCode rightCode : sig.IteratorCode} {origin : State catalog Ambient}
    (leftStep : IterationStep dynamics left.owner leftCode origin)
    (rightStep : IterationStep dynamics right.owner rightCode origin)
    extends ForwardDiamond leftStep rightStep where
  right_exact : LifecycleYieldAgrees rightAfterLeft rightStep
  left_exact : LifecycleYieldAgrees leftAfterRight leftStep

/-- Exact forward stability selects steps definitionally equal to the off-axis executions chosen
by the semantic raw diamond because `executeOne` is deterministic. -/
noncomputable def lifecycle_forward_diamond
    {dynamics : Dynamics sig catalog Ambient} {left right : Program dynamics}
    (exact : ForwardLifecycleIndependent left right)
    {leftCode rightCode : sig.IteratorCode} {origin : State catalog Ambient}
    (leftReachable : Reach left leftCode) (rightReachable : Reach right rightCode)
    (leftStep : IterationStep dynamics left.owner leftCode origin)
    (rightStep : IterationStep dynamics right.owner rightCode origin)
    (leftExecuted : executeOne dynamics left.oracle leftCode origin = .ok leftStep)
    (rightExecuted : executeOne dynamics right.oracle rightCode origin = .ok rightStep) :
    LifecycleForwardDiamond leftStep rightStep := by
  let raw := independent_forward_diamond exact.independent leftReachable rightReachable
    leftStep rightStep leftExecuted rightExecuted
  have leftForwardAtOrigin : forward left leftCode origin = some leftStep.after := by
    simp [forward, leftExecuted]
  have rightForwardAtOrigin : forward right rightCode origin = some rightStep.after := by
    simp [forward, rightExecuted]
  have rightExists := exact.right_under_left leftReachable rightReachable origin rightStep
    leftStep.after rightExecuted leftForwardAtOrigin
  let rightExactStep := Classical.choose rightExists
  have rightExactExecuted := (Classical.choose_spec rightExists).1
  have rightExact := (Classical.choose_spec rightExists).2
  have rightStepEq : rightExactStep = raw.rightAfterLeft :=
    Except.ok.inj (rightExactExecuted.symm.trans raw.right_executed)
  have leftExists := exact.left_under_right rightReachable leftReachable origin leftStep
    rightStep.after leftExecuted rightForwardAtOrigin
  let leftExactStep := Classical.choose leftExists
  have leftExactExecuted := (Classical.choose_spec leftExists).1
  have leftExact := (Classical.choose_spec leftExists).2
  have leftStepEq : leftExactStep = raw.leftAfterRight :=
    Except.ok.inj (leftExactExecuted.symm.trans raw.left_executed)
  exact {
    toForwardDiamond := raw
    right_exact := by
      rw [← rightStepEq]
      exact rightExact
    left_exact := by
      rw [← leftStepEq]
      exact leftExact
  }

/-! ## Program-aligned landing activations -/

/-- The existing landing's exact step is reproduced by the fixed program and fixed oracle. -/
structure LandingProgramWitness
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics program.owner code before beforeFiber) : Prop where
  reachable : Reach program code
  program_executed :
    executeOne dynamics program.oracle code before = .ok landing.step

theorem LandingProgramWitness.step_eq
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    {leftFiber rightFiber : Fiber catalog}
    {left : Landing dynamics program.owner code before leftFiber}
    {right : Landing dynamics program.owner code before rightFiber}
    (leftWitness : LandingProgramWitness program left)
    (rightWitness : LandingProgramWitness program right) : left.step = right.step :=
  Except.ok.inj (leftWitness.program_executed.symm.trans rightWitness.program_executed)

/-- Two legal bare landings with different stored undos cannot both belong to one fixed program. -/
theorem no_program_witness_of_undo_ne
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    {referenceFiber candidateFiber : Fiber catalog}
    {reference : Landing dynamics program.owner code before referenceFiber}
    {candidate : Landing dynamics program.owner code before candidateFiber}
    (referenceWitness : LandingProgramWitness program reference)
    (differentUndo : candidate.step.undo ≠ reference.step.undo) :
    ¬LandingProgramWitness program candidate := by
  intro candidateWitness
  exact differentUndo (congrArg IterationStep.undo
    (candidateWitness.step_eq referenceWitness))

/-- The two landing outcomes written by L-Iter and L-Finish. -/
inductive LandingOutcome
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) where
  | iter (next : sig.IteratorCode) (continues : step.next = some next)
  | finish (done : step.next = none)

/-- One complete L-Iter or L-Finish application whose exact landing also belongs to `program`. -/
structure ProgramAlignedLandingActivation
    {dynamics : Dynamics sig catalog Ambient}
    (program : Program dynamics) (before : State catalog Ambient) where
  fiber : Fiber catalog
  present : before.registry program.owner = some fiber
  code : sig.IteratorCode
  undos : List (UndoCode sig)
  committed : CommittedView (catalog.declaration fiber.component)
  phase : fiber.phase = .reloading code undos committed
  target : targetView before program.owner fiber = some committed
  landing : Landing dynamics program.owner code before fiber
  program_witness : LandingProgramWitness program landing
  outcome : LandingOutcome landing.step

namespace ProgramAlignedLandingActivation

/-- The actual phase payload written by this activation, never an arbitrary caller payload. -/
def nextPhase
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramAlignedLandingActivation program before) :
    Phase (catalog.declaration activation.landing.afterFiber.component) :=
  match activation.outcome with
  | .iter next _ => .reloading next (activation.landing.step.undo :: activation.undos)
      (activation.landing.component_eq.symm ▸ activation.committed)
  | .finish _ => .active (activation.landing.step.undo :: activation.undos)
      (activation.landing.component_eq.symm ▸ activation.committed)

/-- Exact endpoint of the represented lifecycle application. -/
def after
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramAlignedLandingActivation program before) :
    State catalog Ambient :=
  setPhase activation.landing.step.after program.owner activation.landing.afterFiber
    activation.nextPhase

/-- The represented actual L-Iter or L-Finish transition. -/
def transition
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (inertia : InertiaPolicy dynamics)
    (activation : ProgramAlignedLandingActivation program before) :
    Transition dynamics inertia before activation.after := by
  cases activation with
  | mk fiber present code undos committed phase target landing witness outcome =>
      cases outcome with
      | iter next continues =>
          exact .iter before program.owner fiber present code undos committed phase target
            landing next continues
      | finish done =>
          exact .finish before program.owner fiber present code undos committed phase target
            landing done

/-- Exact lifecycle rule represented by the landing outcome. -/
def rule
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramAlignedLandingActivation program before) : Rule :=
  match activation.outcome with
  | .iter .. => .iter
  | .finish .. => .finish

@[simp] theorem transition_rule
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (inertia : InertiaPolicy dynamics)
    (activation : ProgramAlignedLandingActivation program before) :
    (activation.transition inertia).rule = activation.rule := by
  cases activation with
  | mk fiber present code undos committed phase target landing witness outcome =>
      cases outcome <;> rfl

/-- Endpoint well-formedness is inherited from the represented lifecycle transition. -/
theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (inertia : InertiaPolicy dynamics)
    (activation : ProgramAlignedLandingActivation program before)
    (wf : WellFormed before) : WellFormed activation.after :=
  (activation.transition inertia).preservesWellFormed wf

/-- A full landing activation preserves every already-present distinct source fiber exactly. -/
theorem foreign_present_after
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramAlignedLandingActivation program before)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ program.owner)
    (present : before.registry name = some fiber) :
    activation.after.registry name = some fiber := by
  have rawPresent := GlobalTraceFacts.iteration_foreign_lookup activation.landing.step
    present different
  unfold after
  rw [setPhase_lookup_other _ program.owner name activation.landing.afterFiber
    activation.nextPhase different]
  exact rawPresent

/-- A foreign landing activation preserves an already-valid positive target. It does not claim
full target-view or active-context equality; L-Finish may introduce new active values. -/
theorem targetView_preserved_by_foreign_landing
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient} (inertia : InertiaPolicy dynamics)
    (wf : WellFormed before)
    (activation : ProgramAlignedLandingActivation program before)
    {consumer : sig.Name} {consumerFiber : Fiber catalog}
    (different : program.owner ≠ consumer)
    (consumerPresent : before.registry consumer = some consumerFiber)
    {committed : CommittedView (catalog.declaration consumerFiber.component)}
    (target : targetView before consumer consumerFiber = some committed) :
    activation.after.registry consumer = some consumerFiber ∧
      targetView activation.after consumer consumerFiber = some committed := by
  have consumerAfter := activation.foreign_present_after (Ne.symm different) consumerPresent
  refine ⟨consumerAfter, targetView_eq_of_isTarget
    (activation.preservesWellFormed inertia wf) ?_⟩
  let sourceTarget := targetView_sound wf target
  exact {
    present := consumerAfter
    not_retired := sourceTarget.not_retired
    resolves_active := by
      intro declared
      obtain ⟨providerFiber, providerPresent, providerActive, tablePresent⟩ :=
        sourceTarget.resolves_active declared
      have providerDifferent : committed.provider declared ≠ program.owner := by
        intro same
        rw [same, activation.present] at providerPresent
        have fiberEq := Option.some.inj providerPresent
        subst providerFiber
        rw [Fiber.Active, activation.phase] at providerActive
        exact providerActive
      exact ⟨providerFiber,
        activation.foreign_present_after providerDifferent providerPresent,
        providerActive, tablePresent⟩
  }

end ProgramAlignedLandingActivation

namespace Landing

/-- Reframe an off-axis base step using a common-source landing only as its exact fiber/control
template. No equality between `baseStep` and `template.step` is assumed. -/
def reframeFromTemplate
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    {code : sig.IteratorCode} {origin : State catalog Ambient}
    {sourceFiber : Fiber catalog}
    (template : Landing dynamics program.owner code origin sourceFiber)
    {baseState : State catalog Ambient}
    {baseStep : IterationStep dynamics program.owner code baseState}
    {foreignName : sig.Name} {foreignFiber : Fiber catalog}
    {foreignPhase : Phase (catalog.declaration foreignFiber.component)}
    (framed : PhaseFramedExecution program baseStep
      foreignName foreignFiber foreignPhase)
    (sourcePresent :
      (setPhase baseState foreignName foreignFiber foreignPhase).registry
        program.owner = some sourceFiber)
    (afterPresent :
      framed.movedStep.after.registry program.owner = some template.afterFiber) :
    Landing dynamics program.owner code
      (setPhase baseState foreignName foreignFiber foreignPhase) sourceFiber where
  RegistrationError := program.RegistrationError
  oracle := program.oracle
  step := framed.movedStep
  executed := framed.executed
  before_present := sourcePresent
  afterFiber := template.afterFiber
  after_present := afterPresent
  component_eq := template.component_eq
  phase_eq := template.phase_eq

end Landing

/-! ## Reconstructing actual moved activations -/

/-- One phase-framed raw execution rebuilt as an actual landing activation, with its lifecycle
phase identified with the common-source activation's phase. -/
structure ReframedActivation
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (original : ProgramAlignedLandingActivation program origin)
    {baseState : State catalog Ambient}
    {baseStep : IterationStep dynamics program.owner original.code baseState}
    {foreignName : sig.Name} {foreignFiber : Fiber catalog}
    {foreignPhase : Phase (catalog.declaration foreignFiber.component)}
    (framed : PhaseFramedExecution program baseStep
      foreignName foreignFiber foreignPhase) where
  activation : ProgramAlignedLandingActivation program
    (setPhase baseState foreignName foreignFiber foreignPhase)
  code_eq : activation.code = original.code
  undo_eq : activation.landing.step.undo = original.landing.step.undo
  continuation_eq : activation.landing.step.next = original.landing.step.next
  kind_eq : sourceKind activation.landing.step = sourceKind original.landing.step
  after_eq : activation.after =
    setPhase framed.movedStep.after program.owner original.landing.afterFiber
      original.nextPhase

/-- Rebuild a moved L-Iter/L-Finish from the off-axis framed step. Exact cross-forward yield
agreement is essential: semantic inverse equality cannot identify the stored lifecycle phase. -/
def reframeActivation
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (original : ProgramAlignedLandingActivation program origin)
    {baseState : State catalog Ambient}
    {baseStep : IterationStep dynamics program.owner original.code baseState}
    {foreignName : sig.Name} {foreignFiber : Fiber catalog}
    {foreignPhase : Phase (catalog.declaration foreignFiber.component)}
    (framed : PhaseFramedExecution program baseStep
      foreignName foreignFiber foreignPhase)
    (sourcePresent :
      (setPhase baseState foreignName foreignFiber foreignPhase).registry
        program.owner = some original.fiber)
    (targetMoved :
      targetView (setPhase baseState foreignName foreignFiber foreignPhase)
        program.owner original.fiber = some original.committed)
    (afterPresent : framed.movedStep.after.registry program.owner =
      some original.landing.afterFiber)
    (rawExact : LifecycleYieldAgrees baseStep original.landing.step) :
    ReframedActivation original framed := by
  let movedLanding :=
    Cordis.GlobalLandingTransposition.Landing.reframeFromTemplate program original.landing
      framed sourcePresent afterPresent
  have totalExact : LifecycleYieldAgrees movedLanding.step original.landing.step :=
    Cordis.GlobalLandingTransposition.LifecycleYieldAgrees.trans
      framed.yield_agrees rawExact
  let movedWitness : LandingProgramWitness program movedLanding := {
    reachable := original.program_witness.reachable
    program_executed := movedLanding.executed
  }
  cases outcomeEq : original.outcome with
  | iter next continues =>
      have movedContinues : movedLanding.step.next = some next :=
        totalExact.continuation.trans continues
      let moved : ProgramAlignedLandingActivation program
          (setPhase baseState foreignName foreignFiber foreignPhase) := {
        fiber := original.fiber
        present := sourcePresent
        code := original.code
        undos := original.undos
        committed := original.committed
        phase := original.phase
        target := targetMoved
        landing := movedLanding
        program_witness := movedWitness
        outcome := .iter next movedContinues
      }
      refine ⟨moved, rfl, totalExact.undo_eq, totalExact.continuation,
        totalExact.kind, ?_⟩
      unfold ProgramAlignedLandingActivation.after
        ProgramAlignedLandingActivation.nextPhase moved
      change setPhase framed.movedStep.after program.owner original.landing.afterFiber
          (.reloading next (movedLanding.step.undo :: original.undos)
            (original.landing.component_eq.symm ▸ original.committed)) =
        setPhase framed.movedStep.after program.owner original.landing.afterFiber
          original.nextPhase
      rw [totalExact.undo_eq]
      simp [ProgramAlignedLandingActivation.nextPhase, outcomeEq]
  | finish done =>
      have movedDone : movedLanding.step.next = none :=
        totalExact.continuation.trans done
      let moved : ProgramAlignedLandingActivation program
          (setPhase baseState foreignName foreignFiber foreignPhase) := {
        fiber := original.fiber
        present := sourcePresent
        code := original.code
        undos := original.undos
        committed := original.committed
        phase := original.phase
        target := targetMoved
        landing := movedLanding
        program_witness := movedWitness
        outcome := .finish movedDone
      }
      refine ⟨moved, rfl, totalExact.undo_eq, totalExact.continuation,
        totalExact.kind, ?_⟩
      unfold ProgramAlignedLandingActivation.after
        ProgramAlignedLandingActivation.nextPhase moved
      change setPhase framed.movedStep.after program.owner original.landing.afterFiber
          (.active (movedLanding.step.undo :: original.undos)
            (original.landing.component_eq.symm ▸ original.committed)) =
        setPhase framed.movedStep.after program.owner original.landing.afterFiber
          original.nextPhase
      rw [totalExact.undo_eq]
      simp [ProgramAlignedLandingActivation.nextPhase, outcomeEq]

/-! ## Exact four-case landing-activation diamond -/

/-- Both actual lifecycle orders and one exact shared final state. -/
structure LandingActivationDiamond
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (left : ProgramAlignedLandingActivation leftProgram origin)
    (right : ProgramAlignedLandingActivation rightProgram origin) where
  leftFirst : Transition dynamics inertia origin left.after
  rightFirst : Transition dynamics inertia origin right.after
  rightAfterLeft : ProgramAlignedLandingActivation rightProgram left.after
  leftAfterRight : ProgramAlignedLandingActivation leftProgram right.after
  final : State catalog Ambient
  left_then_right : rightAfterLeft.after = final
  right_then_left : leftAfterRight.after = final

/-- The four combinations Iter/Iter, Iter/Finish, Finish/Iter, and Finish/Finish share one exact
endpoint under semantic independence, exact cross-forward yield stability, and both phase-frame
certificates. -/
noncomputable def landing_activation_diamond
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {leftProgram rightProgram : Program dynamics} {origin : State catalog Ambient}
    (wf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (exact : ForwardLifecycleIndependent leftProgram rightProgram)
    (leftCompatible : ForeignPhaseCompatibility leftProgram)
    (rightCompatible : ForeignPhaseCompatibility rightProgram)
    (left : ProgramAlignedLandingActivation leftProgram origin)
    (right : ProgramAlignedLandingActivation rightProgram origin) :
    LandingActivationDiamond (inertia := inertia) left right := by
  let exactRaw := lifecycle_forward_diamond exact
    left.program_witness.reachable right.program_witness.reachable
    left.landing.step right.landing.step left.program_witness.program_executed
    right.program_witness.program_executed
  let framed := phase_framed_diamond exact.independent leftCompatible rightCompatible
    left.program_witness.reachable right.program_witness.reachable
    left.landing.step right.landing.step left.program_witness.program_executed
    right.program_witness.program_executed different left.landing.afterFiber
    right.landing.afterFiber left.landing.after_present right.landing.after_present
    left.nextPhase right.nextPhase
  have rightRawStepEq : exactRaw.rightAfterLeft = framed.raw.rightAfterLeft :=
    Except.ok.inj (exactRaw.right_executed.symm.trans framed.raw.right_executed)
  have leftRawStepEq : exactRaw.leftAfterRight = framed.raw.leftAfterRight :=
    Except.ok.inj (exactRaw.left_executed.symm.trans framed.raw.left_executed)
  have rightRawExact :
      LifecycleYieldAgrees framed.raw.rightAfterLeft right.landing.step := by
    rw [← rightRawStepEq]
    exact exactRaw.right_exact
  have leftRawExact :
      LifecycleYieldAgrees framed.raw.leftAfterRight left.landing.step := by
    rw [← leftRawStepEq]
    exact exactRaw.left_exact
  have rightSourceAndTarget := left.targetView_preserved_by_foreign_landing
    inertia wf different right.present right.target
  have leftSourceAndTarget := right.targetView_preserved_by_foreign_landing
    inertia wf (Ne.symm different) left.present left.target
  let rightMoved := reframeActivation right framed.rightAfterLeftEdit
    rightSourceAndTarget.1 rightSourceAndTarget.2 framed.right_present_before_final
    rightRawExact
  let leftMoved := reframeActivation left framed.leftAfterRightEdit
    leftSourceAndTarget.1 leftSourceAndTarget.2 framed.left_present_before_final
    leftRawExact
  let final := setPhase framed.rightAfterLeftEdit.movedStep.after rightProgram.owner
    right.landing.afterFiber right.nextPhase
  exact {
    leftFirst := left.transition inertia
    rightFirst := right.transition inertia
    rightAfterLeft := rightMoved.activation
    leftAfterRight := leftMoved.activation
    final := final
    left_then_right := rightMoved.after_eq
    right_then_left := leftMoved.after_eq.trans framed.endpoint_eq.symm
  }

/-! ## Raw-forward exact-yield counterexample -/

namespace YieldSyntaxGap

inductive ExternalUndo where
  | restore (ambient : Bool)
  | observe (tag : Bool)
  deriving DecidableEq

abbrev Signature : StaticSignature where
  Name := Bool
  Key := Unit
  ComponentId := Unit
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := ExternalUndo
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

def fiber (birth : Nat) : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := birth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def origin : ExampleState where
  ambient := false
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty false (fiber 0)) true (fiber 1)

@[simp] theorem origin_left_present : origin.registry false = some (fiber 0) := by
  simp [origin]

@[simp] theorem origin_right_present : origin.registry true = some (fiber 1) := by
  simp [origin]

def withAmbient (ambient : Bool) (state : ExampleState) : ExampleState := {
  state with ambient := ambient
}

@[simp] theorem withAmbient_registry (ambient : Bool) (state : ExampleState) :
    (withAmbient ambient state).registry = state.registry := rfl

@[simp] theorem withAmbient_nextBirth (ambient : Bool) (state : ExampleState) :
    (withAmbient ambient state).nextBirth = state.nextBirth := rfl

@[simp] theorem withAmbient_ambient (ambient : Bool) (state : ExampleState) :
    (withAmbient ambient state).ambient = ambient := rfl

def rawAfter (owner : Bool) (state : ExampleState) : ExampleState :=
  if owner then state else withAmbient true state

def selectedUndo (owner : Bool) (state : ExampleState) : ExternalUndo :=
  if owner then .observe state.ambient else .restore state.ambient

def result (owner : Bool) (state : ExampleState) :
    OrdinaryResult exampleCatalog Bool where
  after := rawAfter owner state
  undo := selectedUndo owner state
  next := none

def runIterator (owner : Bool) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Bool) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.ordinary (result owner state))

def applyExternalUndo (undo : ExternalUndo) (state : ExampleState) : ExampleState :=
  match undo with
  | .restore ambient => withAmbient ambient state
  | .observe _ => state

def ambientSetoid : Setoid ExampleState where
  r left right := left.ambient = right.ambient
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

theorem withAmbient_original (state : ExampleState) :
    withAmbient state.ambient state = state := by
  cases state
  rfl

theorem withAmbient_overwrite (first second : Bool) (state : ExampleState) :
    withAmbient first (withAmbient second state) = withAmbient first state := by
  cases state
  rfl

theorem wellFormed_withAmbient
    (ambient : Bool) {state : ExampleState} (wellFormed : WellFormed state) :
    WellFormed (withAmbient ambient state) := by
  exact {
    birth_bounded := wellFormed.birth_bounded
    parent_present := wellFormed.parent_present
    parent_older := wellFormed.parent_older
    provisions_unique := wellFormed.provisions_unique
    committed_provider_present := wellFormed.committed_provider_present
    committed_provider_installed := wellFormed.committed_provider_installed
  }

theorem runRelated_of_ambient_eq
    (owner : Bool) (left right : ExampleState)
    (related : left.ambient = right.ambient)
    (leftPresent : ∃ fiber, left.registry owner = some fiber)
    (rightPresent : ∃ fiber, right.registry owner = some fiber) :
    RunRelated ambientSetoid.r (runIterator owner () left) (runIterator owner () right) := by
  obtain ⟨leftFiber, leftLookup⟩ := leftPresent
  obtain ⟨rightFiber, rightLookup⟩ := rightPresent
  rw [runIterator, leftLookup, runIterator, rightLookup]
  exact .results (.ordinary (by
    change (rawAfter owner left).ambient = (rawAfter owner right).ambient
    cases owner <;> simp [rawAfter, related])
    (by cases owner <;> simp [result, selectedUndo, related]) rfl)

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := ambientSetoid
  runIterator := runIterator
  applyExternalUndo := applyExternalUndo
  ordinary_recovers := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        cases owner <;>
          simp [result, rawAfter, selectedUndo, applyExternalUndo,
            withAmbient_overwrite, withAmbient_original]
  externalUndo_respects := by
    intro undo left right related
    cases undo with
    | restore ambient => rfl
    | observe tag => exact related
  ordinary_confined := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        exact {
          beforeFiber := current
          afterFiber := current
          before_present := lookup
          after_present := by cases owner <;> exact lookup
          component_eq := rfl
          parent_eq := rfl
          birth_eq := rfl
          retired_eq := rfl
          phase_eq := rfl
          other_unchanged := by intros; cases owner <;> rfl
          table_writes := by
            unfold WritesWithinProvision
            intros
            rfl
          nextBirth_eq := by cases owner <;> rfl
        }
  ordinary_preserves_wellFormed := by
    intro owner code state found runEq wellFormed
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        cases owner
        · exact wellFormed_withAmbient true wellFormed
        · exact wellFormed
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    cases code
    exact runRelated_of_ambient_eq owner left right related
      ⟨leftFiber, leftPresent⟩ ⟨rightFiber, rightPresent⟩
  ReadEquivalent _ left right := left.ambient = right.ambient
  read_refl := by intros; rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    cases code
    exact runRelated_of_ambient_eq owner left right related
      ⟨leftFiber, leftPresent⟩ ⟨rightFiber, rightPresent⟩
  retire_respects := by
    intro name left right related
    change left.ambient = right.ambient at related
    change (retireByName left name).ambient = (retireByName right name).ambient
    unfold retireByName
    split <;> split <;> simp_all [retireFiber]

def oracle (owner : Bool) : RegistrationOracle dynamics owner Unit where
  certify _ _ := .error ()

def program (owner : Bool) : Program dynamics where
  owner := owner
  RegistrationError := Unit
  oracle := oracle owner
  root := ()

abbrev leftProgram := program false
abbrev rightProgram := program true

theorem run_success
    (owner : Bool) (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry owner = some current) :
    dynamics.runIterator owner () state = .ok (.ordinary (result owner state)) := by
  simp [dynamics, runIterator, present]

def successfulStep
    (owner : Bool) (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry owner = some current) :
    IterationStep dynamics owner () state where
  after := (result owner state).after
  undo := .external (result owner state).undo
  next := (result owner state).next
  source := .ordinary (result owner state) (run_success owner state current present)
  recovers := by
    change dynamics.equivalence.r
      (dynamics.applyExternalUndo (result owner state).undo (result owner state).after) state
    rw [dynamics.ordinary_recovers owner () state (result owner state)
      (run_success owner state current present)]
    exact dynamics.equivalence.refl state
  preserves_wellFormed := dynamics.ordinary_preserves_wellFormed owner () state
    (result owner state) (run_success owner state current present)

theorem successfulStep_executed
    (owner : Bool) (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry owner = some current) :
    executeOne dynamics (oracle owner) () state =
      .ok (successfulStep owner state current present) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success owner state current present)
  · rename_i found foundEq
    have resultEq : found = result owner state :=
      IteratorResult.ordinary.inj
        (Except.ok.inj (foundEq.symm.trans (run_success owner state current present)))
    subst found
    have proofEq : foundEq = run_success owner state current present := Subsingleton.elim _ _
    cases proofEq
    rfl
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success owner state current present)

def leftStep : IterationStep dynamics leftProgram.owner () origin :=
  successfulStep false origin (fiber 0) origin_left_present

def rightStep : IterationStep dynamics rightProgram.owner () origin :=
  successfulStep true origin (fiber 1) origin_right_present

def afterLeft : ExampleState := rawAfter false origin

@[simp] theorem afterLeft_right_present : afterLeft.registry true = some (fiber 1) := by
  simp [afterLeft, rawAfter, origin]

def rightAfterLeftStep : IterationStep dynamics rightProgram.owner () afterLeft :=
  successfulStep true afterLeft (fiber 1) afterLeft_right_present

@[simp] theorem leftStep_executed :
    executeOne dynamics leftProgram.oracle () origin = .ok leftStep :=
  successfulStep_executed false origin (fiber 0) origin_left_present

@[simp] theorem rightStep_executed :
    executeOne dynamics rightProgram.oracle () origin = .ok rightStep :=
  successfulStep_executed true origin (fiber 1) origin_right_present

@[simp] theorem rightAfterLeftStep_executed :
    executeOne dynamics rightProgram.oracle () afterLeft = .ok rightAfterLeftStep :=
  successfulStep_executed true afterLeft (fiber 1) afterLeft_right_present

theorem semantic_cross_yield :
    YieldAgrees (program := rightProgram) rightAfterLeftStep rightStep where
  inverse := rfl
  continuation := rfl
  kind := rfl

theorem cross_undo_codes_differ : rightAfterLeftStep.undo ≠ rightStep.undo := by
  intro equal
  cases equal

theorem no_exact_cross_yield :
    ¬LifecycleYieldAgrees (program := rightProgram) rightAfterLeftStep rightStep := by
  intro agrees
  exact cross_undo_codes_differ agrees.undo_eq

theorem forward_apply (owner : Bool) (state : ExampleState) :
    forward (program owner) () state =
      match state.registry owner with
      | none => none
      | some _ => some (rawAfter owner state) := by
  unfold forward
  simp only [program]
  cases lookup : state.registry owner with
  | none =>
      have raw : dynamics.runIterator owner () state = .error () := by
        simp [dynamics, runIterator, lookup]
      have failed : executeOne dynamics (oracle owner) () state = .error (.iterator ()) := by
        rw [executeOne.eq_def]
        split <;> simp_all
      rw [failed]
  | some current =>
      rw [successfulStep_executed owner state current lookup]
      rfl

theorem forward_success_eq
    (owner : Bool) (state moved : ExampleState)
    (transformed : forward (program owner) () state = some moved) :
    moved = rawAfter owner state := by
  rw [forward_apply] at transformed
  cases lookup : state.registry owner with
  | none => simp [lookup] at transformed
  | some current =>
      simp [lookup] at transformed
      exact transformed.symm

theorem right_executed_inverse_identity
    {state : ExampleState} {step : IterationStep dynamics true () state}
    (executed : executeOne dynamics (oracle true) () state = .ok step) :
    total (dynamics.applyUndo step.undo) =
      (Cordis.PartialTransformation.identity : PartialMap exampleCatalog Bool) := by
  obtain ⟨current, present⟩ := IterationStep.owner_present step
  have known := successfulStep_executed true state current present
  have stepEq : step = successfulStep true state current present :=
    Except.ok.inj (executed.symm.trans known)
  subst step
  rfl

theorem left_executed_inverse_withAmbient
    {state : ExampleState} {step : IterationStep dynamics false () state}
    (executed : executeOne dynamics (oracle false) () state = .ok step) :
    total (dynamics.applyUndo step.undo) = total (withAmbient state.ambient) := by
  obtain ⟨current, present⟩ := IterationStep.owner_present step
  have known := successfulStep_executed false state current present
  have stepEq : step = successfulStep false state current present :=
    Except.ok.inj (executed.symm.trans known)
  subst step
  rfl

theorem forward_forward_commutes :
    Cordis.PartialTransformation.Commutes
      (forward leftProgram ()) (forward rightProgram ()) := by
  intro state
  unfold Cordis.PartialTransformation.comp
  rw [forward_apply, forward_apply]
  cases leftLookup : state.registry false <;>
    cases rightLookup : state.registry true <;>
      simp [forward_apply, leftLookup, rightLookup, rawAfter]

theorem withAmbient_right_forward_commutes (ambient : Bool) :
    Cordis.PartialTransformation.Commutes
      (total (withAmbient ambient)) (forward rightProgram ()) := by
  intro state
  unfold Cordis.PartialTransformation.comp
  rw [forward_apply]
  cases lookup : state.registry true with
  | none => simp [lookup, total, forward_apply]
  | some current => simp [lookup, total, forward_apply, rawAfter]

theorem identity_commutes_left (map : PartialMap exampleCatalog Bool) :
    Cordis.PartialTransformation.Commutes map Cordis.PartialTransformation.identity := by
  intro state
  simp [Cordis.PartialTransformation.comp, Cordis.PartialTransformation.identity]

theorem generator_commutes
    {leftMap rightMap : PartialMap exampleCatalog Bool}
    (leftGenerated : Generator leftProgram leftMap)
    (rightGenerated : Generator rightProgram rightMap) :
    Cordis.PartialTransformation.Commutes leftMap rightMap := by
  cases leftGenerated with
  | forward leftReachable =>
      cases rightGenerated with
      | forward rightReachable => exact forward_forward_commutes
      | inverse rightReachable rightExecuted =>
          rw [right_executed_inverse_identity rightExecuted]
          exact identity_commutes_left _
  | inverse leftReachable leftExecuted =>
      rw [left_executed_inverse_withAmbient leftExecuted]
      cases rightGenerated with
      | forward rightReachable => exact withAmbient_right_forward_commutes _
      | inverse rightReachable rightExecuted =>
          rw [right_executed_inverse_identity rightExecuted]
          exact identity_commutes_left _

theorem observer_yields_agree
    {leftState rightState : ExampleState}
    {leftStep : IterationStep dynamics true () leftState}
    {rightStep : IterationStep dynamics true () rightState}
    (leftExecuted : executeOne dynamics (oracle true) () leftState = .ok leftStep)
    (rightExecuted : executeOne dynamics (oracle true) () rightState = .ok rightStep) :
    YieldAgrees (program := rightProgram) leftStep rightStep := by
  obtain ⟨leftFiber, leftPresent⟩ := IterationStep.owner_present leftStep
  obtain ⟨rightFiber, rightPresent⟩ := IterationStep.owner_present rightStep
  have leftKnown := successfulStep_executed true leftState leftFiber leftPresent
  have rightKnown := successfulStep_executed true rightState rightFiber rightPresent
  have leftEq : leftStep = successfulStep true leftState leftFiber leftPresent :=
    Except.ok.inj (leftExecuted.symm.trans leftKnown)
  have rightEq : rightStep = successfulStep true rightState rightFiber rightPresent :=
    Except.ok.inj (rightExecuted.symm.trans rightKnown)
  subst leftStep
  subst rightStep
  exact ⟨rfl, rfl, rfl⟩

theorem observer_stable_after_registry
    (seed moved : ExampleState) (registryEq : moved.registry = seed.registry)
    (step : IterationStep dynamics true () seed)
    (executed : executeOne dynamics (oracle true) () seed = .ok step) :
    ∃ movedStep,
      executeOne dynamics (oracle true) () moved = .ok movedStep ∧
        YieldAgrees (program := rightProgram) movedStep step := by
  obtain ⟨current, present⟩ := IterationStep.owner_present step
  have movedPresent : moved.registry true = some current := by
    rw [registryEq]
    exact present
  let movedStep := successfulStep true moved current movedPresent
  have movedExecuted := successfulStep_executed true moved current movedPresent
  exact ⟨movedStep, movedExecuted, observer_yields_agree movedExecuted executed⟩

theorem generator_yield_stable_left
    {map : PartialMap exampleCatalog Bool}
    (generated : Generator rightProgram map) : YieldStable leftProgram map := by
  intro code reachable seed step moved executed transformed
  cases code
  cases generated with
  | forward rightReachable =>
      have movedEq := forward_success_eq true seed moved transformed
      simp [rawAfter] at movedEq
      subst moved
      exact ⟨step, executed, YieldAgrees.refl step⟩
  | inverse rightReachable rightExecuted =>
      rw [right_executed_inverse_identity rightExecuted] at transformed
      have movedEq := Option.some.inj transformed
      subst moved
      exact ⟨step, executed, YieldAgrees.refl step⟩

theorem generator_yield_stable_right
    {map : PartialMap exampleCatalog Bool}
    (generated : Generator leftProgram map) : YieldStable rightProgram map := by
  intro code reachable seed step moved executed transformed
  cases code
  cases generated with
  | forward leftReachable =>
      have movedEq := forward_success_eq false seed moved transformed
      subst moved
      exact observer_stable_after_registry seed (rawAfter false seed) rfl step executed
  | @inverse code inverseState inverseStep leftReachable leftExecuted =>
      rw [left_executed_inverse_withAmbient leftExecuted] at transformed
      have movedEq := Option.some.inj transformed
      subst moved
      exact observer_stable_after_registry seed (withAmbient inverseState.ambient seed)
        rfl step executed

theorem programs_independent : Independent leftProgram rightProgram :=
  Independent.of_generators generator_commutes
    generator_yield_stable_left generator_yield_stable_right

theorem left_forward_at_origin : forward leftProgram () origin = some afterLeft := by
  rw [forward_apply]
  simp [origin_left_present, afterLeft]

theorem no_right_lifecycle_yield_stable :
    ¬LifecycleYieldStable rightProgram (forward leftProgram ()) := by
  intro stable
  obtain ⟨movedStep, movedExecuted, movedAgrees⟩ :=
    stable Reach.root origin rightStep afterLeft rightStep_executed left_forward_at_origin
  have movedEq : movedStep = rightAfterLeftStep :=
    Except.ok.inj (movedExecuted.symm.trans rightAfterLeftStep_executed)
  subst movedStep
  exact no_exact_cross_yield movedAgrees

theorem not_forward_lifecycle_independent :
    ¬ForwardLifecycleIndependent leftProgram rightProgram := by
  intro exact
  exact no_right_lifecycle_yield_stable (exact.right_under_left Reach.root)

theorem withAmbient_setPhase
    (ambient : Bool) (state : ExampleState) (name : Bool)
    (current : Fiber exampleCatalog)
    (phase : Phase (exampleCatalog.declaration current.component)) :
    withAmbient ambient (setPhase state name current phase) =
      setPhase (withAmbient ambient state) name current phase := by
  cases state
  rfl

theorem rawAfter_setPhase
    (owner : Bool) (state : ExampleState) (name : Bool)
    (current : Fiber exampleCatalog)
    (phase : Phase (exampleCatalog.declaration current.component)) :
    rawAfter owner (setPhase state name current phase) =
      setPhase (rawAfter owner state) name current phase := by
  cases owner
  · exact withAmbient_setPhase true state name current phase
  · rfl

theorem selectedUndo_setPhase
    (owner : Bool) (state : ExampleState) (name : Bool)
    (current : Fiber exampleCatalog)
    (phase : Phase (exampleCatalog.declaration current.component)) :
    selectedUndo owner (setPhase state name current phase) = selectedUndo owner state := by
  cases owner <;> rfl

theorem foreignPhaseCompatible (owner : Bool) :
    ForeignPhaseCompatibility (program owner) where
  execute_setPhase := by
    intro code state step foreignName foreignFiber foreignPhase reachable
      foreignPresent different executed
    cases code
    obtain ⟨ownerFiber, ownerPresent⟩ := IterationStep.owner_present step
    have ownerPresentMoved :
        (setPhase state foreignName foreignFiber foreignPhase).registry owner =
          some ownerFiber := by
      rw [setPhase_lookup_other state foreignName owner foreignFiber foreignPhase
        (Ne.symm different)]
      exact ownerPresent
    have known := successfulStep_executed owner state ownerFiber ownerPresent
    have stepEq : step = successfulStep owner state ownerFiber ownerPresent :=
      Except.ok.inj (executed.symm.trans known)
    subst step
    let movedStep := successfulStep owner
      (setPhase state foreignName foreignFiber foreignPhase) ownerFiber ownerPresentMoved
    have movedExecuted :
        executeOne dynamics (oracle owner) ()
            (setPhase state foreignName foreignFiber foreignPhase) = .ok movedStep :=
      successfulStep_executed owner
        (setPhase state foreignName foreignFiber foreignPhase) ownerFiber ownerPresentMoved
    refine ⟨movedStep, movedExecuted, ?_, ?_⟩
    · exact {
        undo_eq := by
          show (UndoCode.external
              (selectedUndo owner (setPhase state foreignName foreignFiber foreignPhase)) :
              UndoCode Signature) = UndoCode.external (selectedUndo owner state)
          rw [selectedUndo_setPhase]
        continuation := rfl
        kind := rfl
      }
    · change rawAfter owner (setPhase state foreignName foreignFiber foreignPhase) =
        setPhase (rawAfter owner state) foreignName foreignFiber foreignPhase
      exact rawAfter_setPhase owner state foreignName foreignFiber foreignPhase

theorem leftForeignPhaseCompatible : ForeignPhaseCompatibility leftProgram :=
  foreignPhaseCompatible false

theorem rightForeignPhaseCompatible : ForeignPhaseCompatibility rightProgram :=
  foreignPhaseCompatible true

end YieldSyntaxGap

/-! ## Executable positive Iter/Finish example -/

namespace Example

abbrev Signature := YieldSyntaxGap.Signature
abbrev exampleCatalog := YieldSyntaxGap.exampleCatalog
abbrev ExampleState := YieldSyntaxGap.ExampleState

def emptyView : CommittedView YieldSyntaxGap.declaration where
  provider declared := False.elim (by
    rcases declared with ⟨key, required⟩
    simp [YieldSyntaxGap.declaration] at required)

def reloadingFiber (birth : Nat) : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := birth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .reloading () [] emptyView

def origin : ExampleState where
  ambient := false
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty false (reloadingFiber 0)) true (reloadingFiber 1)

@[simp] theorem left_present : origin.registry false = some (reloadingFiber 0) := by
  simp [origin]

@[simp] theorem right_present : origin.registry true = some (reloadingFiber 1) := by
  simp [origin]

theorem origin_wellFormed : WellFormed origin := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [origin] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [origin] at lookup <;> subst fiber <;>
      simp [reloadingFiber] at parentEq
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [origin] at lookup <;> subst fiber <;>
      simp [reloadingFiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases leftFiber.component
    simp [YieldSyntaxGap.declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [YieldSyntaxGap.declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    rcases declared with ⟨key, required⟩
    simp [YieldSyntaxGap.declaration] at required

def nextCode (owner : Bool) : Option Unit := if owner then none else some ()

def result (owner : Bool) (state : ExampleState) :
    OrdinaryResult exampleCatalog Bool where
  after := state
  undo := .observe false
  next := nextCode owner

def runIterator (owner : Bool) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Bool) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.ordinary (result owner state))

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := YieldSyntaxGap.ambientSetoid
  runIterator := runIterator
  applyExternalUndo := YieldSyntaxGap.applyExternalUndo
  ordinary_recovers := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        rfl
  externalUndo_respects := by
    intro undo left right related
    cases undo with
    | restore ambient => rfl
    | observe tag => exact related
  ordinary_confined := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
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
          other_unchanged := by intros; rfl
          table_writes := by
            unfold WritesWithinProvision
            intros
            rfl
          nextBirth_eq := rfl
        }
  ordinary_preserves_wellFormed := by
    intro owner code state found runEq wf
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        exact wf
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.ordinary related rfl rfl)
  ReadEquivalent _ left right := left.ambient = right.ambient
  read_refl := by intros; rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.ordinary related rfl rfl)
  retire_respects := by
    intro name left right related
    exact YieldSyntaxGap.dynamics.retire_respects name related

def oracle (owner : Bool) : RegistrationOracle dynamics owner Unit where
  certify _ _ := .error ()

def program (owner : Bool) : Program dynamics where
  owner := owner
  RegistrationError := Unit
  oracle := oracle owner
  root := ()

abbrev leftProgram := program false
abbrev rightProgram := program true

theorem run_success
    (owner : Bool) (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry owner = some current) :
    dynamics.runIterator owner () state = .ok (.ordinary (result owner state)) := by
  simp [dynamics, runIterator, present]

def step
    (owner : Bool) (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry owner = some current) :
    IterationStep dynamics owner () state where
  after := state
  undo := .external (.observe false)
  next := nextCode owner
  source := .ordinary (result owner state) (run_success owner state current present)
  recovers := rfl
  preserves_wellFormed := fun wf ↦ wf

theorem step_executed
    (owner : Bool) (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry owner = some current) :
    executeOne dynamics (oracle owner) () state = .ok (step owner state current present) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success owner state current present)
  · rename_i found foundEq
    have resultEq : found = result owner state :=
      IteratorResult.ordinary.inj
        (Except.ok.inj (foundEq.symm.trans (run_success owner state current present)))
    subst found
    have proofEq : foundEq = run_success owner state current present := Subsingleton.elim _ _
    cases proofEq
    rfl
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success owner state current present)

theorem forward_apply (owner : Bool) (state : ExampleState) :
    forward (program owner) () state =
      match state.registry owner with
      | none => none
      | some _ => some state := by
  unfold forward
  simp only [program]
  cases lookup : state.registry owner with
  | none =>
      have raw : dynamics.runIterator owner () state = .error () := by
        simp [dynamics, runIterator, lookup]
      have failed : executeOne dynamics (oracle owner) () state = .error (.iterator ()) := by
        rw [executeOne.eq_def]
        split <;> simp_all
      rw [failed]
  | some current =>
      rw [step_executed owner state current lookup]
      rfl

theorem forward_success_eq
    (owner : Bool) (state moved : ExampleState)
    (transformed : forward (program owner) () state = some moved) : moved = state := by
  rw [forward_apply] at transformed
  cases lookup : state.registry owner with
  | none => simp [lookup] at transformed
  | some current =>
      simp [lookup] at transformed
      exact transformed.symm

theorem executed_inverse_identity
    {owner : Bool} {state : ExampleState}
    {currentStep : IterationStep dynamics owner () state}
    (executed : executeOne dynamics (oracle owner) () state = .ok currentStep) :
    total (dynamics.applyUndo currentStep.undo) =
      (Cordis.PartialTransformation.identity : PartialMap exampleCatalog Bool) := by
  obtain ⟨current, present⟩ := IterationStep.owner_present currentStep
  have known := step_executed owner state current present
  have stepEq : currentStep = step owner state current present :=
    Except.ok.inj (executed.symm.trans known)
  subst currentStep
  rfl

theorem forwards_commute (leftOwner rightOwner : Bool) :
    Cordis.PartialTransformation.Commutes
      (forward (program leftOwner) ()) (forward (program rightOwner) ()) := by
  intro state
  unfold Cordis.PartialTransformation.comp
  rw [forward_apply, forward_apply]
  cases leftLookup : state.registry leftOwner <;>
    cases rightLookup : state.registry rightOwner <;>
      simp [forward_apply, leftLookup, rightLookup]

theorem generator_commutes
    {leftMap rightMap : PartialMap exampleCatalog Bool}
    (leftGenerated : Generator leftProgram leftMap)
    (rightGenerated : Generator rightProgram rightMap) :
    Cordis.PartialTransformation.Commutes leftMap rightMap := by
  cases leftGenerated with
  | forward leftReachable =>
      cases rightGenerated with
      | forward rightReachable => exact forwards_commute false true
      | inverse rightReachable rightExecuted =>
          rw [executed_inverse_identity rightExecuted]
          exact YieldSyntaxGap.identity_commutes_left _
  | inverse leftReachable leftExecuted =>
      rw [executed_inverse_identity leftExecuted]
      cases rightGenerated with
      | forward rightReachable =>
          exact (YieldSyntaxGap.identity_commutes_left _).symm
      | inverse rightReachable rightExecuted =>
          rw [executed_inverse_identity rightExecuted]
          exact YieldSyntaxGap.identity_commutes_left _

theorem generator_yield_stable
    (owner foreignOwner : Bool) {map : PartialMap exampleCatalog Bool}
    (generated : Generator (program foreignOwner) map) : YieldStable (program owner) map := by
  intro code reachable seed currentStep moved executed transformed
  cases code
  cases generated with
  | forward foreignReachable =>
      have movedEq := forward_success_eq foreignOwner seed moved transformed
      subst moved
      exact ⟨currentStep, executed, YieldAgrees.refl currentStep⟩
  | inverse foreignReachable foreignExecuted =>
      rw [executed_inverse_identity foreignExecuted] at transformed
      have movedEq := Option.some.inj transformed
      subst moved
      exact ⟨currentStep, executed, YieldAgrees.refl currentStep⟩

theorem programs_independent : Independent leftProgram rightProgram :=
  Independent.of_generators generator_commutes
    (generator_yield_stable false true) (generator_yield_stable true false)

theorem lifecycle_stable_under_forward (owner foreignOwner : Bool) :
    LifecycleYieldStable (program owner) (forward (program foreignOwner) ()) := by
  intro code reachable seed currentStep moved executed transformed
  cases code
  have movedEq := forward_success_eq foreignOwner seed moved transformed
  subst moved
  exact ⟨currentStep, executed,
    Cordis.GlobalLandingTransposition.LifecycleYieldAgrees.refl currentStep⟩

theorem forwardLifecycleIndependent :
    ForwardLifecycleIndependent leftProgram rightProgram where
  independent := programs_independent
  left_under_right := by
    intro rightCode reachable
    cases rightCode
    exact lifecycle_stable_under_forward false true
  right_under_left := by
    intro leftCode reachable
    cases leftCode
    exact lifecycle_stable_under_forward true false

theorem foreignPhaseCompatible (owner : Bool) :
    ForeignPhaseCompatibility (program owner) where
  execute_setPhase := by
    intro code state currentStep foreignName foreignFiber foreignPhase reachable
      foreignPresent different executed
    cases code
    obtain ⟨ownerFiber, ownerPresent⟩ := IterationStep.owner_present currentStep
    have ownerPresentMoved :
        (setPhase state foreignName foreignFiber foreignPhase).registry owner =
          some ownerFiber := by
      rw [setPhase_lookup_other state foreignName owner foreignFiber foreignPhase
        (Ne.symm different)]
      exact ownerPresent
    have known := step_executed owner state ownerFiber ownerPresent
    have stepEq : currentStep = step owner state ownerFiber ownerPresent :=
      Except.ok.inj (executed.symm.trans known)
    subst currentStep
    let movedStep := step owner (setPhase state foreignName foreignFiber foreignPhase)
      ownerFiber ownerPresentMoved
    have movedExecuted :
        executeOne dynamics (oracle owner) ()
          (setPhase state foreignName foreignFiber foreignPhase) = .ok movedStep :=
      step_executed owner (setPhase state foreignName foreignFiber foreignPhase)
        ownerFiber ownerPresentMoved
    exact ⟨movedStep, movedExecuted, ⟨rfl, rfl, rfl⟩, rfl⟩

theorem leftCompatible : ForeignPhaseCompatibility leftProgram :=
  foreignPhaseCompatible false

theorem rightCompatible : ForeignPhaseCompatibility rightProgram :=
  foreignPhaseCompatible true

def leftStep : IterationStep dynamics leftProgram.owner () origin :=
  step false origin (reloadingFiber 0) left_present

def rightStep : IterationStep dynamics rightProgram.owner () origin :=
  step true origin (reloadingFiber 1) right_present

@[simp] theorem leftStep_executed :
    executeOne dynamics leftProgram.oracle () origin = .ok leftStep :=
  step_executed false origin (reloadingFiber 0) left_present

@[simp] theorem rightStep_executed :
    executeOne dynamics rightProgram.oracle () origin = .ok rightStep :=
  step_executed true origin (reloadingFiber 1) right_present

def leftLanding : Landing dynamics false () origin (reloadingFiber 0) where
  RegistrationError := Unit
  oracle := oracle false
  step := leftStep
  executed := leftStep_executed
  before_present := left_present
  afterFiber := reloadingFiber 0
  after_present := left_present
  component_eq := rfl
  phase_eq := rfl

def rightLanding : Landing dynamics true () origin (reloadingFiber 1) where
  RegistrationError := Unit
  oracle := oracle true
  step := rightStep
  executed := rightStep_executed
  before_present := right_present
  afterFiber := reloadingFiber 1
  after_present := right_present
  component_eq := rfl
  phase_eq := rfl

theorem left_target :
    targetView origin false (reloadingFiber 0) = some emptyView := by
  apply targetView_eq_of_isTarget origin_wellFormed
  exact {
    present := left_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [YieldSyntaxGap.declaration] at required
  }

theorem right_target :
    targetView origin true (reloadingFiber 1) = some emptyView := by
  apply targetView_eq_of_isTarget origin_wellFormed
  exact {
    present := right_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [YieldSyntaxGap.declaration] at required
  }

def leftActivation : ProgramAlignedLandingActivation leftProgram origin where
  fiber := reloadingFiber 0
  present := left_present
  code := ()
  undos := []
  committed := emptyView
  phase := rfl
  target := left_target
  landing := leftLanding
  program_witness := ⟨Reach.root, leftStep_executed⟩
  outcome := .iter () rfl

def rightActivation : ProgramAlignedLandingActivation rightProgram origin where
  fiber := reloadingFiber 1
  present := right_present
  code := ()
  undos := []
  committed := emptyView
  phase := rfl
  target := right_target
  landing := rightLanding
  program_witness := ⟨Reach.root, rightStep_executed⟩
  outcome := .finish rfl

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

noncomputable def diamond :
    LandingActivationDiamond (inertia := inertia) leftActivation rightActivation :=
  landing_activation_diamond origin_wellFormed (by decide) forwardLifecycleIndependent
    leftCompatible rightCompatible leftActivation rightActivation

def executableRulePair : Rule × Rule := (leftActivation.rule, rightActivation.rule)

theorem executableRulePair_eq : executableRulePair = (.iter, .finish) := rfl

end Example

/-! ## Common-source applicability is necessary -/

namespace ProviderFinishGap

open Cordis.GlobalRegistry.Example

abbrev Signature := Cordis.GlobalRegistry.Example.signature
abbrev exampleCatalog := Cordis.GlobalRegistry.Example.catalog
abbrev ExampleState := GlobalState exampleCatalog Nat

abbrev dynamics := Cordis.GlobalLifecycle.Example.dynamics
abbrev oracle := Cordis.GlobalLifecycle.Example.oracle
abbrev inertia := Cordis.GlobalLifecycle.Example.inertia

def consumerView : CommittedView consumerDecl where
  provider _ := 0

def activeBase : ExampleState where
  ambient := 0
  nextBirth := activeState.nextBirth
  registry := activeState.registry

theorem activeBase_wellFormed : WellFormed activeBase := by
  let wf := activeState_wellFormed
  exact {
    birth_bounded := wf.birth_bounded
    parent_present := wf.parent_present
    parent_older := wf.parent_older
    provisions_unique := wf.provisions_unique
    committed_provider_present := wf.committed_provider_present
    committed_provider_installed := wf.committed_provider_installed
  }

def activeWithConsumer : ExampleState := insertFiber activeBase 1 (some 0) .consumer

theorem activeWithConsumer_wellFormed : WellFormed activeWithConsumer := by
  apply preserve_insert activeBase 1 (by constructor; rfl) (some 0)
  · intro parent equal
    have parentEq : parent = 0 := Option.some.inj equal.symm
    subst parent
    exact ⟨activeProviderFiber, rfl⟩
  · simp [consumerDecl]
  · exact activeBase_wellFormed

def consumerFiber : Fiber exampleCatalog where
  component := .consumer
  parent := some 0
  birth := 1
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def providerReloadingFiber : Fiber exampleCatalog := {
  activeProviderFiber with phase := .reloading 0 [] emptyProviderView
}

def before : ExampleState :=
  setPhase activeWithConsumer 0 activeProviderFiber (.reloading 0 [] emptyProviderView)

@[simp] theorem before_provider_present :
    before.registry 0 = some providerReloadingFiber := rfl

@[simp] theorem before_consumer_present : before.registry 1 = some consumerFiber := rfl

theorem before_wellFormed : WellFormed before := by
  apply setPhase_installed_preserves
    (state := activeWithConsumer) (fiber := activeProviderFiber) (by rfl)
    (.reloading 0 [] emptyProviderView)
  · trivial
  · intro committed committedEq declared
    rcases declared with ⟨key, required⟩
    change key ∈ providerDecl.dependencies.keys at required
    simp [providerDecl] at required
  · exact activeWithConsumer_wellFormed

theorem before_provider_target :
    targetView before 0 providerReloadingFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget before_wellFormed
  exact {
    present := before_provider_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      change key ∈ providerDecl.dependencies.keys at required
      simp [providerDecl] at required
  }

theorem before_no_active_provider (key : Signature.Key) (name : Signature.Name) :
    ¬ActiveProvider before key name := by
  rintro ⟨found, lookup, active, value⟩
  by_cases zero : name = 0
  · subst name
    rw [before_provider_present] at lookup
    have foundEq := Option.some.inj lookup
    subst found
    simp [providerReloadingFiber, Fiber.Active, Phase.Active] at active
  · by_cases one : name = 1
    · subst name
      rw [before_consumer_present] at lookup
      have foundEq := Option.some.inj lookup
      subst found
      simp [consumerFiber, Fiber.Active, Phase.Active] at active
    · simp [before, activeWithConsumer, activeBase, activeState, Coeffect.setAt_other,
        zero, one] at lookup

theorem before_consumer_target_none : targetView before 1 consumerFiber = none := by
  classical
  simp only [targetView]
  split
  · rename_i existsTarget
    obtain ⟨view, target⟩ := existsTarget
    let declared : DeclaredKey consumerDecl := ⟨.counter, by simp [consumerDecl]⟩
    exact False.elim <| before_no_active_provider .counter (view.provider declared)
      (target.resolves_active declared)
  · rfl

def finalResult : OrdinaryResult exampleCatalog Nat where
  after := Cordis.GlobalLifecycle.Example.advance before
  undo := 0
  next := none

def finalStep : IterationStep dynamics 0 0 before where
  after := finalResult.after
  undo := .external finalResult.undo
  next := finalResult.next
  source := .ordinary finalResult rfl
  recovers := by
    change dynamics.equivalence.r
      (dynamics.applyExternalUndo 0 (Cordis.GlobalLifecycle.Example.advance before)) before
    rfl
  preserves_wellFormed := fun wf ↦ Cordis.GlobalLifecycle.Example.advance_preserves wf

theorem finalStep_executed : executeOne dynamics oracle 0 before = .ok finalStep := by
  rfl

def finalLanding : Landing dynamics 0 0 before providerReloadingFiber where
  RegistrationError := String
  oracle := oracle
  step := finalStep
  executed := finalStep_executed
  before_present := before_provider_present
  afterFiber := providerReloadingFiber
  after_present := before_provider_present
  component_eq := rfl
  phase_eq := rfl

def after : ExampleState :=
  setPhase finalStep.after 0 finalLanding.afterFiber
    (.active [finalStep.undo] emptyProviderView)

def providerFinish : Transition dynamics inertia before after :=
  .finish before 0 providerReloadingFiber before_provider_present 0 []
    emptyProviderView rfl before_provider_target finalLanding rfl

theorem after_wellFormed : WellFormed after :=
  providerFinish.preservesWellFormed before_wellFormed

def providerActiveFiber : Fiber exampleCatalog := {
  providerReloadingFiber with phase := .active [.external 0] emptyProviderView
}

@[simp] theorem after_provider_present : after.registry 0 = some providerActiveFiber := rfl

@[simp] theorem after_consumer_present : after.registry 1 = some consumerFiber := rfl

theorem after_consumer_target : targetView after 1 consumerFiber = some consumerView := by
  apply targetView_eq_of_isTarget after_wellFormed
  exact {
    present := after_consumer_present
    not_retired := rfl
    resolves_active := by
      intro declared
      refine ⟨providerActiveFiber, after_provider_present, ?_, ?_⟩
      · simp [providerActiveFiber, Fiber.Active, Phase.Active]
      · rcases declared with ⟨key, required⟩
        cases key <;>
          simp [providerActiveFiber, providerReloadingFiber, activeProviderFiber,
            providerTable]
  }

def consumerBeginAfter : ExampleState :=
  setPhase after 1 consumerFiber (.reloading 20 [] consumerView)

def consumerBegin : Transition dynamics inertia after consumerBeginAfter :=
  .begin after 1 consumerFiber after_consumer_present rfl consumerView after_consumer_target

theorem consumer_begin_not_available_at_predecessor :
    targetView before 1 consumerFiber ≠ some consumerView := by
  rw [before_consumer_target_none]
  intro impossible
  cases impossible

end ProviderFinishGap

/-! ## A bare landing does not determine fixed-program oracle provenance -/

namespace OracleProvenanceGap

open Cordis.GlobalRegistry.Example

abbrev Signature := Cordis.GlobalDynamics.Example.ExampleSig
abbrev exampleCatalog := Cordis.GlobalDynamics.Example.exampleCatalog
abbrev ExampleState := GlobalState exampleCatalog Nat
abbrev dynamics := Cordis.GlobalDynamics.Example.dynamics

def source : ExampleState := Cordis.GlobalDynamics.Example.afterOrdinary

def request : RegistrationRequest Signature :=
  Cordis.GlobalDynamics.Example.registrationRequest

def ownerFiber : Fiber exampleCatalog where
  component := .provider
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

@[simp] theorem source_owner_present : source.registry 0 = some ownerFiber := rfl

@[simp] theorem source_child_one_absent : source.registry 1 = none := rfl

@[simp] theorem source_child_two_absent : source.registry 2 = none := by
  simp [source, Cordis.GlobalDynamics.Example.afterOrdinary,
    Cordis.GlobalDynamics.Example.ordinaryAfter, Cordis.GlobalDynamics.Example.start,
    Cordis.GlobalRegistry.Example.withProvider, Cordis.GlobalRegistry.Example.initial,
    insertFiber]

theorem source_wellFormed : WellFormed source :=
  Cordis.GlobalDynamics.Example.afterOrdinary_wellFormed

def certifyAt (child : Nat) (state : ExampleState)
    (candidate : RegistrationRequest Signature) :
    Except Unit (RegistrationAdmission dynamics state 0 candidate) :=
  match candidate with
  | ⟨.provider, _⟩ => .error ()
  | ⟨.consumer, _⟩ =>
      match ownerPresent : state.registry 0 with
      | none => .error ()
      | some foundOwner =>
          match childFresh : state.registry child with
          | some _ => .error ()
          | none => .ok {
              child := child
              fresh := ⟨childFresh⟩
              ownerFiber := foundOwner
              owner_present := ownerPresent
              provision_fresh := by simp [consumerDecl]
              registration_recovers := by
                change (retireByName
                  (insertFiber state child (some 0) .consumer) child).ambient = state.ambient
                simp [retireByName, retireFiber]
                rfl
            }

def oracleAt (child : Nat) : RegistrationOracle dynamics 0 Unit where
  certify := certifyAt child

abbrev oracleOne := oracleAt 1
abbrev oracleTwo := oracleAt 2

def admissionOne : RegistrationAdmission dynamics source 0 request := {
  child := 1
  fresh := ⟨source_child_one_absent⟩
  ownerFiber := ownerFiber
  owner_present := source_owner_present
  provision_fresh := by
    simp [request, Cordis.GlobalDynamics.Example.registrationRequest, consumerDecl]
  registration_recovers := rfl
}

def admissionTwo : RegistrationAdmission dynamics source 0 request := {
  child := 2
  fresh := ⟨source_child_two_absent⟩
  ownerFiber := ownerFiber
  owner_present := source_owner_present
  provision_fresh := by
    simp [request, Cordis.GlobalDynamics.Example.registrationRequest, consumerDecl]
  registration_recovers := rfl
}

theorem admission_eq
    {before : ExampleState} {candidate : RegistrationRequest Signature}
    {left right : RegistrationAdmission dynamics before 0 candidate}
    (childEq : left.child = right.child)
    (ownerEq : left.ownerFiber = right.ownerFiber) : left = right := by
  rw [RegistrationAdmission.mk.injEq]
  exact ⟨childEq, ownerEq⟩

theorem raw_registration :
    dynamics.runIterator 0 1 source = .ok (.register request) := rfl

def registrationStep
    {before : ExampleState} {candidate : RegistrationRequest Signature}
    (admission : RegistrationAdmission dynamics before 0 candidate)
    (code : Signature.IteratorCode)
    (runEq : dynamics.runIterator 0 code before = .ok (.register candidate)) :
    IterationStep dynamics 0 code before where
  after := admission.after
  undo := admission.undo
  next := admission.next
  source := .registration candidate admission runEq
  recovers := admission.registration_recovers
  preserves_wellFormed := admission.after_wellFormed

theorem executeOne_registration_ok
    {Error : Type} (selectedOracle : RegistrationOracle dynamics 0 Error)
    (code : Signature.IteratorCode) (before : ExampleState)
    (candidate : RegistrationRequest Signature)
    (runEq : dynamics.runIterator 0 code before = .ok (.register candidate))
    (admission : RegistrationAdmission dynamics before 0 candidate)
    (accepted : selectedOracle.certify before candidate = .ok admission) :
    executeOne dynamics selectedOracle code before =
      .ok (registrationStep admission code runEq) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    have requestEq : found = candidate :=
      IteratorResult.register.inj (Except.ok.inj (foundEq.symm.trans runEq))
    subst found
    have runProofEq : foundEq = runEq := Subsingleton.elim _ _
    cases runProofEq
    split
    · rename_i foundError foundErrorEq
      cases foundErrorEq.symm.trans accepted
    · rename_i foundAdmission foundAdmissionEq
      have admissionEq : foundAdmission = admission :=
        Except.ok.inj (foundAdmissionEq.symm.trans accepted)
      subst foundAdmission
      have certificationProofEq : foundAdmissionEq = accepted := Subsingleton.elim _ _
      cases certificationProofEq
      rfl

def stepOne : IterationStep dynamics 0 1 source :=
  registrationStep admissionOne 1 raw_registration

def stepTwo : IterationStep dynamics 0 1 source :=
  registrationStep admissionTwo 1 raw_registration

theorem oracleOne_accepts : oracleOne.certify source request = .ok admissionOne := by
  change certifyAt 1 source request = .ok admissionOne
  unfold certifyAt
  simp only [request, Cordis.GlobalDynamics.Example.registrationRequest]
  split
  · rename_i ownerEq
    rw [source_owner_present] at ownerEq
    cases ownerEq
  · rename_i foundOwner ownerEq
    split
    · rename_i foundChild childEq
      rw [source_child_one_absent] at childEq
      cases childEq
    · apply congrArg Except.ok
      exact admission_eq rfl (Option.some.inj (ownerEq.symm.trans source_owner_present))

theorem oracleTwo_accepts : oracleTwo.certify source request = .ok admissionTwo := by
  change certifyAt 2 source request = .ok admissionTwo
  unfold certifyAt
  simp only [request, Cordis.GlobalDynamics.Example.registrationRequest]
  split
  · rename_i ownerEq
    rw [source_owner_present] at ownerEq
    cases ownerEq
  · rename_i foundOwner ownerEq
    split
    · rename_i foundChild childEq
      rw [source_child_two_absent] at childEq
      cases childEq
    · apply congrArg Except.ok
      exact admission_eq rfl (Option.some.inj (ownerEq.symm.trans source_owner_present))

theorem stepOne_executed : executeOne dynamics oracleOne 1 source = .ok stepOne :=
  executeOne_registration_ok oracleOne 1 source request raw_registration
    admissionOne oracleOne_accepts

theorem stepTwo_executed : executeOne dynamics oracleTwo 1 source = .ok stepTwo :=
  executeOne_registration_ok oracleTwo 1 source request raw_registration
    admissionTwo oracleTwo_accepts

def landingOne : Landing dynamics 0 1 source ownerFiber where
  RegistrationError := Unit
  oracle := oracleOne
  step := stepOne
  executed := stepOne_executed
  before_present := source_owner_present
  afterFiber := ownerFiber
  after_present := rfl
  component_eq := rfl
  phase_eq := rfl

def landingTwo : Landing dynamics 0 1 source ownerFiber where
  RegistrationError := Unit
  oracle := oracleTwo
  step := stepTwo
  executed := stepTwo_executed
  before_present := source_owner_present
  afterFiber := ownerFiber
  after_present := rfl
  component_eq := rfl
  phase_eq := rfl

def programOne : Program dynamics where
  owner := 0
  RegistrationError := Unit
  oracle := oracleOne
  root := 1

def programTwo : Program dynamics where
  owner := 0
  RegistrationError := Unit
  oracle := oracleTwo
  root := 1

theorem landingOne_program_aligned : LandingProgramWitness programOne landingOne where
  reachable := Reach.root
  program_executed := stepOne_executed

theorem landingTwo_program_aligned : LandingProgramWitness programTwo landingTwo where
  reachable := Reach.root
  program_executed := stepTwo_executed

theorem selected_children_differ : stepOne.undo ≠ stepTwo.undo := by
  intro equal
  cases equal

theorem landingTwo_not_aligned_with_programOne :
    ¬LandingProgramWitness programOne landingTwo := by
  exact no_program_witness_of_undo_ne landingOne_program_aligned
    (Ne.symm selected_children_differ)

theorem landingOne_not_aligned_with_programTwo :
    ¬LandingProgramWitness programTwo landingOne := by
  exact no_program_witness_of_undo_ne landingTwo_program_aligned
    selected_children_differ

end OracleProvenanceGap

end Cordis.GlobalLandingTransposition
