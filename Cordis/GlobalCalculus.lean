import Cordis.GlobalLifecycle

/-!
# Unified bounded global calculus

This module combines the three orchestration constructors from `GlobalRegistry` and the eight
lifecycle constructors from `GlobalLifecycle` into one exact-endpoint relation. Its public rule
alphabet has the paper's ten rule names: O-Insert, O-Retire, O-Remove, L-Begin, L-Iter,
L-Finish, L-Divert, L-Raise, L-Leave, and L-Unload. The two operational L-Divert alternatives
remain distinct witnesses but project to the single L-Divert name.

The calculus is still the bounded, sequential model established by the imported modules. In
particular, `RecoveryAdmission` remains the sole whole-accumulator temporal obligation, external
programs remain in `Dynamics`, registration-oracle rejection has no lifecycle edge, and this
module does not claim arbitrary-interleaving temporal composability or the paper's full Theorem 59.
-/

set_option autoImplicit false

namespace Cordis.GlobalCalculus

open Cordis.GlobalRegistry Cordis.GlobalDynamics

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Exact ten-name inventory -/

/-- The paper's ten global-calculus rule names. -/
inductive Rule where
  | oInsert
  | oRetire
  | oRemove
  | lBegin
  | lIter
  | lFinish
  | lDivert
  | lRaise
  | lLeave
  | lUnload
  deriving DecidableEq, Repr

def allRules : List Rule :=
  [.oInsert, .oRetire, .oRemove, .lBegin, .lIter, .lFinish, .lDivert, .lRaise,
    .lLeave, .lUnload]

theorem allRules_length : allRules.length = 10 := rfl

theorem allRules_nodup : allRules.Nodup := by decide

theorem allRules_complete (rule : Rule) : rule ∈ allRules := by
  cases rule <;> simp [allRules]

/-- Every paper step retains the acted-on name `n`; issuance policy is deliberately separate. -/
inductive Actor (Name : Type u) where
  | fiber (name : Name)
  deriving Repr

/-- The global state map run before any lifecycle owner-phase edit. -/
inductive StateMap where
  | identity
  | iterator
  | accumulatedRecovery
  deriving DecidableEq, Repr

def allStateMaps : List StateMap :=
  [.identity, .iterator, .accumulatedRecovery]

theorem allStateMaps_complete (stateMap : StateMap) : stateMap ∈ allStateMaps := by
  cases stateMap <;> simp [allStateMaps]

/-- The exact finite edit surface exposed by each step constructor. -/
inductive EditFootprint where
  | phaseOnly
  | iteratorThenPhase
  | recoveryThenInactive
  | insertEntry
  | retirementFlag
  | removeEntry
  deriving DecidableEq, Repr

def allEditFootprints : List EditFootprint :=
  [.phaseOnly, .iteratorThenPhase, .recoveryThenInactive, .insertEntry,
    .retirementFlag, .removeEntry]

theorem allEditFootprints_complete (edit : EditFootprint) : edit ∈ allEditFootprints := by
  cases edit <;> simp [allEditFootprints]

/-- Structural effect on the truth of the actor's installed-status predicate. -/
inductive InstallationEdit where
  | preservesStatus
  | installsExisting
  | uninstallsExisting
  deriving DecidableEq, Repr

/-- Whether a named actor currently has a registered fiber in an installed phase. -/
def InstalledAt (state : State catalog Ambient) (name : sig.Name) : Prop :=
  ∃ fiber, state.registry name = some fiber ∧ fiber.Installed

theorem installedAt_iff_of_lookup
    {state : State catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    (present : state.registry name = some fiber) : InstalledAt state name ↔ fiber.Installed := by
  constructor
  · rintro ⟨current, lookup, installed⟩
    rw [present] at lookup
    have current_eq : fiber = current := Option.some.inj lookup
    simpa [current_eq] using installed
  · intro installed
    exact ⟨fiber, present, installed⟩

theorem not_installedAt_of_absent
    {state : State catalog Ambient} {name : sig.Name}
    (absent : state.registry name = none) : ¬InstalledAt state name := by
  rintro ⟨fiber, lookup, installed⟩
  rw [absent] at lookup
  cases lookup

theorem installedAt_setPhase_owner
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) :
    InstalledAt (GlobalLifecycle.setPhase state name fiber phase) name ↔ phase.Installed := by
  simpa [Fiber.Installed] using
    (installedAt_iff_of_lookup
      (GlobalLifecycle.setPhase_lookup_same state name fiber phase))

private theorem transported_inactive_not_installed
    {left right : sig.ComponentId} (component_eq : left = right)
    (outcome : Option sig.Error) :
    ¬(component_eq.symm ▸
      Phase.inactive (decl := catalog.declaration right) outcome).Installed := by
  cases component_eq
  simp [Phase.Installed]

/-! ## Unified exact-endpoint step relation -/

/-- One global-calculus step, retaining the exact source relation as evidence. -/
inductive Step
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    State catalog Ambient → State catalog Ambient → Type (u + 1) where
  | orchestration
      {before after : State catalog Ambient}
      (step : OrchestrationStep before after) : Step dynamics inertia before after
  | lifecycle
      {before after : State catalog Ambient}
      (step : GlobalLifecycle.Transition dynamics inertia before after) :
      Step dynamics inertia before after

namespace Step

private def orchestrationRule
    {before after : State catalog Ambient} : OrchestrationStep before after → Rule
  | .insert .. => .oInsert
  | .retire .. => .oRetire
  | .remove .. => .oRemove

private def lifecycleRule : GlobalLifecycle.Rule → Rule
  | .begin => .lBegin
  | .iter => .lIter
  | .finish => .lFinish
  | .divertAbort => .lDivert
  | .divertLand => .lDivert
  | .raise => .lRaise
  | .leave => .lLeave
  | .unload => .lUnload

private def lifecycleOwner
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    GlobalLifecycle.Transition dynamics inertia before after → sig.Name
  | .begin _ owner .. => owner
  | .iter _ owner .. => owner
  | .finish _ owner .. => owner
  | .divertAbort _ owner .. => owner
  | .divertLand _ owner .. => owner
  | .raise _ owner .. => owner
  | .leave _ owner .. => owner
  | .unload _ owner .. => owner

private def orchestrationName
    {before after : State catalog Ambient} : OrchestrationStep before after → sig.Name
  | .insert _ name .. => name
  | .retire _ name .. => name
  | .remove _ name .. => name

private def orchestrationEdit
    {before after : State catalog Ambient} :
    OrchestrationStep before after → EditFootprint
  | .insert .. => .insertEntry
  | .retire .. => .retirementFlag
  | .remove .. => .removeEntry

def rule
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} : Step dynamics inertia before after → Rule
  | .orchestration step => orchestrationRule step
  | .lifecycle step => lifecycleRule step.rule

def actedName
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Step dynamics inertia before after → sig.Name
  | .orchestration step => orchestrationName step
  | .lifecycle step => lifecycleOwner step

def actor
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Actor sig.Name :=
  .fiber step.actedName

def stateMap
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} : Step dynamics inertia before after → StateMap
  | .orchestration _ => .identity
  | .lifecycle step =>
      match step.mapKind with
      | .identity => .identity
      | .iterator => .iterator
      | .accumulatedRecovery => .accumulatedRecovery

def editFootprint
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Step dynamics inertia before after → EditFootprint
  | .orchestration step => orchestrationEdit step
  | .lifecycle step =>
      match step.mapKind with
      | .identity => .phaseOnly
      | .iterator => .iteratorThenPhase
      | .accumulatedRecovery => .recoveryThenInactive

def installationEdit
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Step dynamics inertia before after → InstallationEdit
  | .orchestration _ => .preservesStatus
  | .lifecycle step =>
      match step.rule with
      | .begin => .installsExisting
      | .unload => .uninstallsExisting
      | _ => .preservesStatus

/-- Every combined step preserves the strengthened global registry invariant. -/
theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : WellFormed before → WellFormed after := by
  intro wf
  cases step with
  | orchestration step => exact step.preservesWellFormed wf
  | lifecycle step => exact step.preservesWellFormed wf

/-- The unified relation projects only to the exact ten-name inventory. -/
theorem rule_mem_inventory
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : step.rule ∈ allRules :=
  allRules_complete step.rule

/-- Both operational diversion alternatives project to the one paper rule name. -/
theorem lifecycle_divert_projection
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : GlobalLifecycle.Transition dynamics inertia before after) :
    (Step.lifecycle step).rule = .lDivert ↔
      step.rule = .divertAbort ∨ step.rule = .divertLand := by
  cases step <;>
    simp [rule, lifecycleRule, GlobalLifecycle.Transition.rule]

/-- The actor wrapper preserves the exact `r(n)` name projection. -/
theorem actor_exact
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.actor = .fiber step.actedName := rfl

/-- All three orchestration rules use the identity global map from Equation 51. -/
theorem orchestration_map_identity
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : OrchestrationStep before after) :
    (Step.orchestration step : Step dynamics inertia before after).stateMap = .identity := rfl

/-- Identity-map lookup is exact against the underlying edit footprint. -/
theorem identity_map_iff_footprint
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.stateMap = .identity ↔
      step.editFootprint = .phaseOnly ∨ step.editFootprint = .insertEntry ∨
      step.editFootprint = .retirementFlag ∨ step.editFootprint = .removeEntry := by
  cases step with
  | orchestration inner =>
      cases inner <;>
        simp [stateMap, editFootprint, orchestrationEdit]
  | lifecycle inner =>
      cases inner <;>
        simp [stateMap, editFootprint,
          GlobalLifecycle.Transition.mapKind]

/-- Iterator-map lookup is exact against the iterator-plus-phase footprint. -/
theorem iterator_map_iff_footprint
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.stateMap = .iterator ↔ step.editFootprint = .iteratorThenPhase := by
  cases step with
  | orchestration inner =>
      cases inner <;> simp [stateMap, editFootprint, orchestrationEdit]
  | lifecycle inner =>
      cases inner <;>
        simp [stateMap, editFootprint,
          GlobalLifecycle.Transition.mapKind]

/-- Whole-accumulator recovery is used exactly by L-Unload. -/
theorem recovery_map_iff
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.stateMap = .accumulatedRecovery ↔ step.rule = .lUnload := by
  cases step with
  | orchestration inner =>
      cases inner <;>
        simp [stateMap, rule, orchestrationRule]
  | lifecycle inner =>
      cases inner <;>
        simp [stateMap, rule, lifecycleRule, GlobalLifecycle.Transition.rule,
          GlobalLifecycle.Transition.mapKind]

/-- Iterator maps arise exactly from L-Iter, L-Finish, and landing L-Divert. -/
theorem iterator_map_implies_rule
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after)
    (iterator : step.stateMap = .iterator) :
    step.rule = .lIter ∨ step.rule = .lFinish ∨ step.rule = .lDivert := by
  cases step with
  | orchestration inner =>
      cases inner <;> simp [stateMap] at iterator
  | lifecycle inner =>
      cases inner <;>
        simp [stateMap, rule, lifecycleRule, GlobalLifecycle.Transition.rule,
          GlobalLifecycle.Transition.mapKind] at iterator ⊢

/-- Table-1 classifier lookup: only L-Begin and L-Unload request a status crossing. -/
theorem installation_change_iff
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.installationEdit ≠ .preservesStatus ↔
      step.rule = .lBegin ∨ step.rule = .lUnload := by
  cases step with
  | orchestration inner =>
      cases inner <;> simp [installationEdit, rule, orchestrationRule]
  | lifecycle inner =>
      cases inner <;>
        simp [installationEdit, rule, lifecycleRule, GlobalLifecycle.Transition.rule]

theorem installs_iff_begin
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.installationEdit = .installsExisting ↔ step.rule = .lBegin := by
  cases step with
  | orchestration inner =>
      cases inner <;> simp [installationEdit, rule, orchestrationRule]
  | lifecycle inner =>
      cases inner <;>
        simp [installationEdit, rule, lifecycleRule, GlobalLifecycle.Transition.rule]

theorem uninstalls_iff_unload
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.installationEdit = .uninstallsExisting ↔ step.rule = .lUnload := by
  cases step with
  | orchestration inner =>
      cases inner <;> simp [installationEdit, rule, orchestrationRule]
  | lifecycle inner =>
      cases inner <;>
        simp [installationEdit, rule, lifecycleRule, GlobalLifecycle.Transition.rule]

/-- Constructor-wise semantics of the installed-status classifier at the exact acted-on name. -/
theorem installation_semantics
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    match step.installationEdit with
    | .preservesStatus =>
        InstalledAt before step.actedName ↔ InstalledAt after step.actedName
    | .installsExisting =>
        ¬InstalledAt before step.actedName ∧ InstalledAt after step.actedName
    | .uninstallsExisting =>
        InstalledAt before step.actedName ∧ ¬InstalledAt after step.actedName := by
  cases step with
  | orchestration inner =>
      cases inner <;>
        simp_all [installationEdit, actedName, orchestrationName, InstalledAt,
          Fiber.Installed, Phase.Installed, Coeffect.Absent.lookup_eq,
          insertFiber, retireFiber, removeFiber]
      all_goals assumption
  | lifecycle inner =>
      cases inner
      case unload owner fiber present undos committed outcome phase notRelied admission =>
        change InstalledAt before owner ∧ ¬InstalledAt admission.after owner
        constructor
        · apply (installedAt_iff_of_lookup present).2
          change fiber.phase.Installed
          rw [phase]
          simp [Phase.Installed]
        · rw [admission.after_eq]
          intro installed
          have phaseInstalled :=
            (installedAt_setPhase_owner (dynamics.recover undos before) owner
              admission.recoveredFiber
              (admission.component_eq ▸ Phase.inactive outcome)).1 installed
          exact transported_inactive_not_installed admission.component_eq outcome phaseInstalled
      all_goals
        simp_all [installationEdit, actedName, lifecycleOwner, InstalledAt,
          Fiber.Installed, Phase.Installed, GlobalLifecycle.Transition.rule,
          GlobalLifecycle.setPhase]

/-- Every non-Begin/non-Unload constructor preserves the actual installed-status predicate. -/
theorem installedAt_preserved_unless_boundary
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after)
    (notBegin : step.rule ≠ .lBegin) (notUnload : step.rule ≠ .lUnload) :
    InstalledAt before step.actedName ↔ InstalledAt after step.actedName := by
  have preserves : step.installationEdit = .preservesStatus := by
    by_cases equal : step.installationEdit = .preservesStatus
    · exact equal
    · exact False.elim <| (step.installation_change_iff.1 equal).elim notBegin notUnload
  simpa [preserves] using step.installation_semantics

theorem begin_installs_actor
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) (beginRule : step.rule = .lBegin) :
    ¬InstalledAt before step.actedName ∧ InstalledAt after step.actedName := by
  have installs : step.installationEdit = .installsExisting :=
    step.installs_iff_begin.2 beginRule
  simpa [installs] using step.installation_semantics

theorem unload_uninstalls_actor
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) (unloadRule : step.rule = .lUnload) :
    InstalledAt before step.actedName ∧ ¬InstalledAt after step.actedName := by
  have uninstalls : step.installationEdit = .uninstallsExisting :=
    step.uninstalls_iff_unload.2 unloadRule
  simpa [uninstalls] using step.installation_semantics

/-- Actual installed-status change can therefore occur only at L-Begin or L-Unload. -/
theorem installedAt_change_only_boundary
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after)
    (changed : ¬(InstalledAt before step.actedName ↔
      InstalledAt after step.actedName)) :
    step.rule = .lBegin ∨ step.rule = .lUnload := by
  by_cases beginRule : step.rule = .lBegin
  · exact .inl beginRule
  · by_cases unloadRule : step.rule = .lUnload
    · exact .inr unloadRule
    · exact False.elim <| changed
        (step.installedAt_preserved_unless_boundary beginRule unloadRule)

end Step

/-! ## Exact finite traces and bounded empty-registry origin -/

inductive Trace
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    State catalog Ambient → State catalog Ambient → Type (u + 1) where
  | nil (state : State catalog Ambient) : Trace dynamics inertia state state
  | cons
      {before middle after : State catalog Ambient}
      (head : Step dynamics inertia before middle)
      (tail : Trace dynamics inertia middle after) : Trace dynamics inertia before after

namespace Trace

def rules
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} : Trace dynamics inertia before after → List Rule
  | .nil _ => []
  | .cons head tail => head.rule :: tail.rules

def actors
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Trace dynamics inertia before after → List (Actor sig.Name)
  | .nil _ => []
  | .cons head tail => head.actor :: tail.actors

def stateMaps
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Trace dynamics inertia before after → List StateMap
  | .nil _ => []
  | .cons head tail => head.stateMap :: tail.stateMaps

def editFootprints
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Trace dynamics inertia before after → List EditFootprint
  | .nil _ => []
  | .cons head tail => head.editFootprint :: tail.editFootprints

theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : Trace dynamics inertia before after) : WellFormed before → WellFormed after := by
  intro wf
  induction trace with
  | nil => exact wf
  | cons head tail ih => exact ih (head.preservesWellFormed wf)

end Trace

/-- Definition 53's bounded initial condition: the finite registry starts empty. -/
def EmptyRegistry (state : State catalog Ambient) : Prop :=
  ∀ name, state.registry name = none

/-- A proof-carrying exact trace whose chosen initial state has an empty registry. -/
structure FromEmpty
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    (final : State catalog Ambient) where
  initial : State catalog Ambient
  empty : EmptyRegistry initial
  initial_wellFormed : WellFormed initial
  trace : Trace dynamics inertia initial final

namespace FromEmpty

theorem final_wellFormed
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {final : State catalog Ambient}
    (execution : FromEmpty dynamics inertia final) : WellFormed final :=
  execution.trace.preservesWellFormed execution.initial_wellFormed

end FromEmpty

/-! ## Unified heterogeneous trace from and back to an empty registry -/

namespace Example

abbrev ExampleSig := GlobalLifecycle.Example.ExampleSig
abbrev exampleCatalog := GlobalLifecycle.Example.exampleCatalog
abbrev ExampleState := State exampleCatalog Nat

def emptyStart : ExampleState where
  ambient := 3
  nextBirth := 0
  registry := Coeffect.empty

theorem emptyStart_empty : EmptyRegistry emptyStart := by
  intro name
  rfl

theorem emptyStart_wellFormed : WellFormed emptyStart := by
  constructor <;> intros <;> simp [emptyStart, Coeffect.empty] at *

def insertTransition :
    OrchestrationStep emptyStart GlobalLifecycle.Example.start :=
  .insert emptyStart 0 (by constructor; rfl) none (by simp)
    GlobalRegistry.Example.Component.provider (by
      intro existing existingFiber key lookup
      simp [emptyStart, Coeffect.empty] at lookup)

def insertStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      emptyStart GlobalLifecycle.Example.start :=
  .orchestration insertTransition

def beginStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.start GlobalLifecycle.Example.beginState :=
  .lifecycle GlobalLifecycle.Example.beginTransition

def iterStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.beginState GlobalLifecycle.Example.iterState :=
  .lifecycle GlobalLifecycle.Example.iterTransition

def finishStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.iterState GlobalLifecycle.Example.finishState :=
  .lifecycle GlobalLifecycle.Example.finishTransition

def retireStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.finishState GlobalLifecycle.Example.retiredState :=
  .orchestration GlobalLifecycle.Example.retireTransition

def leaveStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.retiredState GlobalLifecycle.Example.leaveState :=
  .lifecycle GlobalLifecycle.Example.leaveTransition

def unloadStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.leaveState GlobalLifecycle.Example.unloadedState :=
  .lifecycle GlobalLifecycle.Example.unloadTransition

def inactiveFiber : Fiber exampleCatalog := {
  GlobalLifecycle.Example.unloadingFiber with phase := .inactive none
}

theorem unloaded_present :
    GlobalLifecycle.Example.unloadedState.registry 0 = some inactiveFiber := rfl

theorem unloaded_lookup_other (name : Nat) (different : name ≠ 0) :
    GlobalLifecycle.Example.unloadedState.registry name = none := by
  simp [GlobalLifecycle.Example.unloadedState, GlobalLifecycle.Example.recoveredState,
    GlobalLifecycle.Example.dynamics, Dynamics.recover, Dynamics.applyUndo,
    GlobalLifecycle.Example.applyExternalUndo, GlobalLifecycle.Example.leaveState,
    GlobalLifecycle.setPhase, Coeffect.setAt_other, different,
    GlobalLifecycle.Example.retiredState, retireFiber,
    GlobalLifecycle.Example.finishState, GlobalLifecycle.Example.finalStep,
    GlobalLifecycle.Example.finalResult, GlobalLifecycle.Example.advance,
    GlobalLifecycle.Example.iterState, GlobalLifecycle.Example.firstStep,
    GlobalLifecycle.Example.firstResult, GlobalLifecycle.Example.beginState,
    GlobalLifecycle.Example.start, GlobalDynamics.Example.start,
    GlobalRegistry.Example.withProvider, GlobalRegistry.Example.initial,
    insertFiber, Coeffect.empty]

def removedState : ExampleState :=
  removeFiber GlobalLifecycle.Example.unloadedState 0

def removeTransition :
    OrchestrationStep GlobalLifecycle.Example.unloadedState removedState :=
  .remove GlobalLifecycle.Example.unloadedState 0 inactiveFiber unloaded_present rfl
    (by simp [inactiveFiber, Fiber.Installed, Phase.Installed]) (by
      intro child childFiber lookup
      by_cases same : child = 0
      · subst child
        rw [unloaded_present] at lookup
        have fiber_eq : inactiveFiber = childFiber := Option.some.inj lookup
        subst childFiber
        simp [inactiveFiber, GlobalLifecycle.Example.unloadingFiber,
          GlobalLifecycle.Example.retiredFiber, GlobalLifecycle.Example.activeFiber,
          GlobalLifecycle.Example.iterFiber, GlobalLifecycle.Example.beginFiber,
          GlobalLifecycle.Example.inactiveProvider]
      · rw [unloaded_lookup_other child same] at lookup
        cases lookup)

def removeStep :
    Step GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      GlobalLifecycle.Example.unloadedState removedState :=
  .orchestration removeTransition

def unifiedTrace :
    Trace GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia
      emptyStart removedState :=
  .cons insertStep <| .cons beginStep <| .cons iterStep <| .cons finishStep <|
    .cons retireStep <| .cons leaveStep <| .cons unloadStep <|
      .cons removeStep (.nil _)

def execution :
    FromEmpty GlobalLifecycle.Example.dynamics GlobalLifecycle.Example.inertia removedState where
  initial := emptyStart
  empty := emptyStart_empty
  initial_wellFormed := emptyStart_wellFormed
  trace := unifiedTrace

theorem unifiedTrace_wellFormed : WellFormed removedState :=
  unifiedTrace.preservesWellFormed emptyStart_wellFormed

theorem execution_endpoint_wellFormed : WellFormed removedState :=
  execution.final_wellFormed

theorem removedState_empty : EmptyRegistry removedState := by
  intro name
  by_cases same : name = 0
  · subst name
    exact removeFiber_lookup_same GlobalLifecycle.Example.unloadedState 0
  · change (removeFiber GlobalLifecycle.Example.unloadedState 0).registry name = none
    rw [removeFiber_lookup_other GlobalLifecycle.Example.unloadedState 0 name same]
    exact unloaded_lookup_other name same

/-- Exact projection of the unified trace into the ten-name paper rule alphabet. -/
theorem unified_rule_projection :
    unifiedTrace.rules =
      [.oInsert, .lBegin, .lIter, .lFinish, .oRetire, .lLeave, .lUnload, .oRemove] :=
  rfl

theorem unified_actor_projection :
    unifiedTrace.actors =
      [.fiber 0, .fiber 0, .fiber 0, .fiber 0, .fiber 0,
        .fiber 0, .fiber 0, .fiber 0] := rfl

theorem unified_stateMap_projection :
    unifiedTrace.stateMaps =
      [.identity, .identity, .iterator, .iterator, .identity, .identity,
        .accumulatedRecovery, .identity] := rfl

theorem unified_edit_projection :
    unifiedTrace.editFootprints =
      [.insertEntry, .phaseOnly, .iteratorThenPhase, .iteratorThenPhase,
        .retirementFlag, .phaseOnly, .recoveryThenInactive, .removeEntry] := rfl

/-- The trace begins and ends with an empty registry after exact ambient recovery. -/
theorem unified_endpoint_exact :
    EmptyRegistry removedState ∧ removedState.ambient = emptyStart.ambient := by
  exact ⟨removedState_empty, rfl⟩

end Example

end Cordis.GlobalCalculus
