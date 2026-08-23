import Cordis.GlobalPaperRelation
import Cordis.GlobalNameTraceAction

/-!
# Name-renamed paper-visible endpoint relation

This module connects the executable structural name action to the paper-facing
birth-erased observations.  The relation compares a left state at `n` with a
right state at `action.name n`: active-context values are transported by the
dependent value action, while paper fiber controls are reindexed by the name
permutation and mapped through the phase action.

The main theorem is reflexive at an acted endpoint.  A trace endpoint theorem
then combines it with the existing exact trace well-formedness proof.  This is
an observation bridge, not an unconditional lifecycle bisimulation: the
primitive dynamics, registration oracle, recovery, and inertia equivariance
obligations remain those of `GlobalNameLifecycle`.
-/

set_option autoImplicit false

namespace Cordis.GlobalNamePaperRelation

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalNameAction Cordis.GlobalNameLifecycle
open Cordis.GlobalCalculus Cordis.GlobalNameTraceAction Cordis.GlobalTraceRewrite

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-- The paper control transported through a structural name action. -/
def actPaperFiberControl
    (action : NameAction sig Ambient)
    (control : PaperFiberControl catalog) : PaperFiberControl catalog where
  component := control.component
  parent := control.parent.map action.name
  retired := control.retired
  phase := actPhase action control.phase

/-- Look up a left paper control at the name corresponding to a right name. -/
def actPaperControlAt
    (action : NameAction sig Ambient)
    (state : State catalog Ambient) (name : sig.Name) :
    Option (PaperFiberControl catalog) :=
  (paperControlAt state (action.name.symm name)).map (actPaperFiberControl action)

theorem actPaperControlAt_apply
    (action : NameAction sig Ambient)
    (state : State catalog Ambient) (name : sig.Name) :
    actPaperControlAt action state (action.name name) =
      (paperControlAt state name).map (actPaperFiberControl action) := by
  simp [actPaperControlAt]

/-- A relation at renamed names, retaining the paper's active-context/control split. -/
def NameActionPaperRelated
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    (left right : State catalog Ambient) : Prop :=
  ContextRelated values (actTable action (activeContext left)) (activeContext right) ∧
    ∀ name, actPaperControlAt action left (action.name name) =
      paperControlAt right (action.name name)

theorem activeValue_act_iff
    (action : NameAction sig Ambient)
    (state : State catalog Ambient) (key : sig.Key) (value : sig.Value key) :
    ActiveValue (actState action state) key (action.value key value) ↔
      ActiveValue state key value := by
  constructor
  · rintro ⟨actedName, actedFiber, actedLookup, actedActive, actedValue⟩
    have lookup := originalFiber_of_actRegistry_lookup action state.registry actedLookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ := lookup
    subst actedFiber
    refine ⟨action.name.symm actedName, originalFiber, originalLookup, ?_, ?_⟩
    · exact (actPhase_active_iff action originalFiber.phase).1
        (by simpa [Fiber.Active] using actedActive)
    · change (originalFiber.table key).map (action.value key) =
        some (action.value key value) at actedValue
      cases table : originalFiber.table key with
      | none => simp [table] at actedValue
      | some oldValue =>
          have valueEq : oldValue = value := (action.value key).injective (by
            simpa [table] using actedValue)
          simp [valueEq]
  · rintro ⟨originalName, originalFiber, originalLookup, originalActive, originalValue⟩
    refine ⟨action.name originalName, actFiber action originalFiber, ?_, ?_, ?_⟩
    · change actRegistry action state.registry (action.name originalName) =
        some (actFiber action originalFiber)
      rw [actRegistry_lookup_apply, originalLookup]
      simp
    · simpa [Fiber.Active] using
        ((actPhase_active_iff action originalFiber.phase).2 originalActive)
    · change (originalFiber.table key).map (action.value key) =
        some (action.value key value)
      rw [originalValue]
      rfl

theorem activeContext_act_eq
    (action : NameAction sig Ambient)
    {state : State catalog Ambient} (stateWf : WellFormed state) :
    activeContext (actState action state) = actTable action (activeContext state) := by
  apply Coeffect.Context.ext
  intro key
  cases source : activeContext state key with
  | none =>
      have noSource : ¬∃ value, ActiveValue state key value := by
        rintro ⟨value, present⟩
        have equal := (activeContext_value_iff stateWf).2 present
        rw [source] at equal
        cases equal
      have noActed : ¬∃ value, ActiveValue (actState action state) key value := by
        rintro ⟨value, present⟩
        let original := (action.value key).symm value
        have mapped : action.value key original = value := by
          exact Equiv.apply_symm_apply (action.value key) value
        apply noSource
        exact ⟨original, (activeValue_act_iff action state key original).1
          (mapped ▸ present)⟩
      have targetEq : activeContext (actState action state) key = none := by
        cases target : activeContext (actState action state) key with
        | none => rfl
        | some value =>
            exact False.elim (noActed ⟨value, (activeContext_value_iff
              (wellFormed_act action stateWf)).1 target⟩)
      simp [actTable, source, targetEq]
  | some value =>
      have sourceActive := (activeContext_value_iff stateWf).1 (by rw [source])
      have targetActive : ActiveValue (actState action state) key
          (action.value key value) :=
        (activeValue_act_iff action state key value).2 sourceActive
      have targetEq := (activeContext_value_iff (wellFormed_act action stateWf)).2
        targetActive
      simp [actTable, source, targetEq]

theorem nameActionPaperRelated_actState
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {state : State catalog Ambient} (stateWf : WellFormed state) :
    NameActionPaperRelated action values state (actState action state) := by
  refine ⟨?_, ?_⟩
  · rw [activeContext_act_eq action stateWf]
    exact contextRelated_refl values _
  · intro name
    cases lookup : state.registry name with
    | none =>
        simp [actPaperControlAt, actState, actRegistry, paperControlAt, lookup]
    | some fiber =>
        simp [actPaperControlAt, actState, actRegistry, paperControlAt, lookup,
          actPaperFiberControl, paperFiberControl]

theorem nameActionPaperRelated_context
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {state : State catalog Ambient} (stateWf : WellFormed state) :
    ContextRelated values (actTable action (activeContext state))
      (activeContext (actState action state)) :=
  (nameActionPaperRelated_actState action values stateWf).1

theorem nameActionPaperRelated_control
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {state : State catalog Ambient} (stateWf : WellFormed state) (name : sig.Name) :
    actPaperControlAt action state (action.name name) =
      paperControlAt (actState action state) (action.name name) :=
  (nameActionPaperRelated_actState action values stateWf).2 name

theorem nameActionPaperRelated_trace_endpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    NameActionPaperRelated action values after (actState action after) :=
  nameActionPaperRelated_actState action values (trace.preservesWellFormed beforeWf)

/-! ## Exact non-activation assignments without a lifecycle transport premise -/

structure NonActivationTracePaperEndpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) where
  acted : GlobalCalculus.Trace dynamics inertia
    (actState action before) (actState action after)
  acted_eq : acted = actTrace assumptions beforeWf trace
  actedAssignment : TraceProgramAssignment dynamics inertia acted
  paperRelated : NameActionPaperRelated action values after (actState action after)

noncomputable def nonActivationTracePaperEndpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) :
    NonActivationTracePaperEndpoint action values assumptions beforeWf trace evidence
      assignment :=
  { acted := actTrace assumptions beforeWf trace
    acted_eq := rfl
    actedAssignment := actNonactivationTraceAssignment assumptions beforeWf evidence assignment
    paperRelated := nameActionPaperRelated_actState action values
      (trace.preservesWellFormed beforeWf) }

theorem nonActivationTracePaperEndpoint_acted_eq
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) :
    let endpoint :=
      nonActivationTracePaperEndpoint action values assumptions beforeWf trace evidence assignment
    endpoint.acted =
      actTrace assumptions beforeWf trace := rfl

/-! ## Exact acted traces with paper-visible endpoint evidence -/

structure AssignedTracePaperEndpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (assignment : TraceProgramAssignment dynamics inertia trace)
    (activationTransport : ActivationAssignmentTransport assumptions) where
  acted : AssignedForwardTrace assumptions beforeWf trace assignment activationTransport
  paperRelated : NameActionPaperRelated action values after (actState action after)

noncomputable def assignedTracePaperEndpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (assignment : TraceProgramAssignment dynamics inertia trace)
    (activationTransport : ActivationAssignmentTransport assumptions) :
    AssignedTracePaperEndpoint action values assumptions beforeWf trace assignment
      activationTransport :=
  { acted := assignedForwardTrace assumptions beforeWf trace assignment activationTransport
    paperRelated := nameActionPaperRelated_actState action values
      (trace.preservesWellFormed beforeWf) }

theorem assignedTracePaperEndpoint_acted_eq
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (assignment : TraceProgramAssignment dynamics inertia trace)
    (activationTransport : ActivationAssignmentTransport assumptions) :
    (assignedTracePaperEndpoint action values assumptions beforeWf trace assignment
      activationTransport).acted.acted = actTrace assumptions beforeWf trace := rfl

/-! ## A nonidentity endpoint witness -/

namespace Example

open Cordis.GlobalNameAction.Example

def exactSetoid {α : Type u} : Setoid α where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

def values : ValueSetoids Signature where
  relation
    | .flag => exactSetoid
    | .token => exactSetoid

theorem actedRaise_related :
    NameActionPaperRelated swapAction values
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState
      (actState swapAction GlobalNameLifecycle.NonidentityRaiseExample.raiseState) :=
  nameActionPaperRelated_actState swapAction values
    GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed

abbrev raiseDynamics := GlobalNameLifecycle.NonidentityRaiseExample.dynamics
abbrev raiseInertia := GlobalNameLifecycle.NonidentityRaiseExample.inertia
abbrev raiseAssumptions := GlobalNameLifecycle.NonidentityRaiseExample.assumptions
abbrev raiseState := GlobalNameLifecycle.NonidentityRaiseExample.raiseState
abbrev raiseAfter := GlobalNameLifecycle.NonidentityRaiseExample.raiseAfter
abbrev raiseTransition := GlobalNameLifecycle.NonidentityRaiseExample.raiseTransition

def raiseStep : GlobalCalculus.Step raiseDynamics raiseInertia raiseState raiseAfter :=
  .lifecycle raiseTransition

def raiseTrace : GlobalCalculus.Trace raiseDynamics raiseInertia raiseState raiseAfter :=
  .cons raiseStep (.nil raiseAfter)

theorem raiseStep_not_activation : ¬IsProgramActivationRule raiseStep.rule := by
  intro evidence
  cases evidence

def raiseTraceEvidence : NonActivationTrace raiseTrace :=
  .cons raiseStep_not_activation (.nil raiseAfter)

def raiseTraceAssignment : TraceProgramAssignment raiseDynamics raiseInertia raiseTrace :=
  .cons (StepProgramAssignment.ofNotActivation raiseStep raiseStep_not_activation) (.nil _)

noncomputable def actedRaiseTrace :
    NonActivationTracePaperEndpoint swapAction values raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed
      raiseTrace raiseTraceEvidence raiseTraceAssignment :=
  nonActivationTracePaperEndpoint swapAction values raiseAssumptions
    GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed
    raiseTrace raiseTraceEvidence raiseTraceAssignment

theorem actedRaiseTrace_related :
    NameActionPaperRelated swapAction values raiseAfter (actState swapAction raiseAfter) :=
  actedRaiseTrace.paperRelated

theorem actedRaiseTrace_rules : actedRaiseTrace.acted.rules = raiseTrace.rules := by
  change (actTrace raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace).rules =
    raiseTrace.rules
  exact actTrace_rules raiseAssumptions
    GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace

end Example

end Cordis.GlobalNamePaperRelation
