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

@[simp]
theorem actPaperFiberControl_trans
    (first second : NameAction sig Ambient)
    (control : PaperFiberControl catalog) :
    actPaperFiberControl (first.trans second) control =
      actPaperFiberControl second (actPaperFiberControl first control) := by
  cases control with
  | mk component parent retired phase =>
      cases parent with
      | none =>
          change PaperFiberControl.mk component none retired
              (actPhase (first.trans second) phase) =
            PaperFiberControl.mk component none retired
              (actPhase second (actPhase first phase))
          rw [actPhase_trans]
      | some parent =>
          change PaperFiberControl.mk component
              (some ((first.trans second).name parent)) retired
              (actPhase (first.trans second) phase) =
            PaperFiberControl.mk component (some (second.name (first.name parent))) retired
              (actPhase second (actPhase first phase))
          rw [actPhase_trans]
          rfl

@[simp]
theorem actPaperFiberControl_symm_apply
    (action : NameAction sig Ambient)
    (control : PaperFiberControl catalog) :
    actPaperFiberControl action.symm (actPaperFiberControl action control) = control := by
  cases control with
  | mk component parent retired phase =>
      cases parent with
      | none =>
          change PaperFiberControl.mk component none retired
              (actPhase action.symm (actPhase action phase)) =
            PaperFiberControl.mk component none retired phase
          rw [actPhase_symm_apply]
      | some parent =>
          change PaperFiberControl.mk component
              (some (action.name.symm (action.name parent))) retired
              (actPhase action.symm (actPhase action phase)) =
            PaperFiberControl.mk component (some parent) retired phase
          rw [actPhase_symm_apply]
          simp

@[simp]
theorem actPaperFiberControl_refl
    (control : PaperFiberControl catalog) :
    actPaperFiberControl (NameAction.refl sig Ambient) control = control := by
  cases control with
  | mk component parent retired phase =>
      cases parent with
      | none =>
          change PaperFiberControl.mk component none retired
              (actPhase (NameAction.refl sig Ambient) phase) =
            PaperFiberControl.mk component none retired phase
          exact congrArg (fun nextPhase =>
            PaperFiberControl.mk component none retired nextPhase)
            (actPhase_refl phase)
      | some parent =>
          change PaperFiberControl.mk component (some parent) retired
              (actPhase (NameAction.refl sig Ambient) phase) =
            PaperFiberControl.mk component (some parent) retired phase
          exact congrArg (fun nextPhase =>
            PaperFiberControl.mk component (some parent) retired nextPhase)
            (actPhase_refl phase)

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

/-! ## Closure under certified value actions -/

/-- The dependent value action preserves the paper's per-key value setoids. -/
def ValueActionEquiv
    (action : NameAction sig Ambient) (values : ValueSetoids sig) : Prop :=
  ∀ (key : sig.Key) (left right : sig.Value key),
    (values.relation key).r left right ↔
      (values.relation key).r (action.value key left) (action.value key right)

theorem valueActionEquiv_symm
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    (invariant : ValueActionEquiv action values) :
    ValueActionEquiv action.symm values := by
  intro key left right
  let leftOriginal := (action.value key).symm left
  let rightOriginal := (action.value key).symm right
  have original := invariant key leftOriginal rightOriginal
  constructor
  · intro related
    have related' : (values.relation key).r
        ((action.value key) leftOriginal) ((action.value key) rightOriginal) := by
      simpa [leftOriginal, rightOriginal, Equiv.symm] using related
    have mapped := original.mpr related'
    simpa [leftOriginal, rightOriginal, Equiv.symm] using mapped
  · intro related
    have mapped := original.mp related
    simpa [leftOriginal, rightOriginal, Equiv.symm] using mapped

theorem valueActionEquiv_refl
    (values : ValueSetoids sig) :
    ValueActionEquiv (NameAction.refl sig Ambient) values := by
  intro key left right
  simp

theorem valueActionEquiv_trans
    (first second : NameAction sig Ambient) (values : ValueSetoids sig)
    (firstInvariant : ValueActionEquiv first values)
    (secondInvariant : ValueActionEquiv second values) :
    ValueActionEquiv (first.trans second) values := by
  intro key left right
  constructor
  · intro related
    have firstRelated := (firstInvariant key left right).mp related
    exact (secondInvariant key (first.value key left) (first.value key right)).mp
      firstRelated
  · intro related
    have secondRelated :=
      (secondInvariant key (first.value key left) (first.value key right)).mpr related
    exact (firstInvariant key left right).mpr secondRelated

theorem contextRelated_actTable
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    (invariant : ValueActionEquiv action values)
    {left right : Coeffect.Context sig.Key sig.Value}
    (related : ContextRelated values left right) :
    ContextRelated values (actTable action left) (actTable action right) := by
  intro key
  rw [actTable_lookup, actTable_lookup]
  cases hleft : left key with
  | none =>
      cases hright : right key with
      | none =>
          change OptionRelated (values.relation key) none none
          exact OptionRelated.refl (values.relation key) none
      | some rightVal =>
          have relatedKey := related key
          rw [hleft, hright] at relatedKey
          cases relatedKey
  | some leftVal =>
      cases hright : right key with
      | none =>
          have relatedKey := related key
          rw [hleft, hright] at relatedKey
          cases relatedKey
      | some rightVal =>
          have relatedKey := related key
          rw [hleft, hright] at relatedKey
          change (values.relation key).r (action.value key leftVal)
            (action.value key rightVal)
          exact (invariant key leftVal rightVal).mp relatedKey

theorem controlAt_trans_apply
    (first second : NameAction sig Ambient)
    (state : State catalog Ambient) (name : sig.Name) :
    actPaperControlAt (first.trans second) state ((first.trans second).name name) =
      (actPaperControlAt first state (first.name name)).map
        (actPaperFiberControl second) := by
  simp only [actPaperControlAt, NameAction.trans_name_symm_apply,
    Option.map_map]
  cases lookup : paperControlAt state name with
  | none => simp [lookup]
  | some control =>
      simp [lookup, actPaperFiberControl_trans]

theorem controlAt_symm_apply
    (action : NameAction sig Ambient)
    (state : State catalog Ambient) (name : sig.Name) :
    actPaperControlAt action.symm state (action.symm.name name) =
      (paperControlAt state name).map (actPaperFiberControl action.symm) := by
  simp [actPaperControlAt]

theorem nameActionPaperRelated_trans
    (first second : NameAction sig Ambient) (values : ValueSetoids sig)
    (secondInvariant : ValueActionEquiv second values)
    {left middle right : State catalog Ambient}
    (firstRelated : NameActionPaperRelated first values left middle)
    (secondRelated : NameActionPaperRelated second values middle right) :
    NameActionPaperRelated (first.trans second) values left right := by
  refine ⟨?_, ?_⟩
  · rw [actTable_trans]
    exact contextRelated_trans
      (contextRelated_actTable second values secondInvariant firstRelated.1)
      secondRelated.1
  · intro name
    calc
      actPaperControlAt (first.trans second) left ((first.trans second).name name) =
          (actPaperControlAt first left (first.name name)).map
            (actPaperFiberControl second) :=
        controlAt_trans_apply first second left name
      _ = (paperControlAt middle (first.name name)).map
            (actPaperFiberControl second) := by rw [firstRelated.2 name]
      _ = actPaperControlAt second middle (second.name (first.name name)) := by
        symm
        exact actPaperControlAt_apply second middle (first.name name)
      _ = paperControlAt right (second.name (first.name name)) :=
        secondRelated.2 (first.name name)

theorem controlAt_apply_symm
    (action : NameAction sig Ambient)
    (state : State catalog Ambient) (name : sig.Name) :
    (actPaperControlAt action state (action.name name)).map
        (actPaperFiberControl action.symm) =
      paperControlAt state name := by
  rw [actPaperControlAt_apply]
  simp [Function.comp_def]

theorem nameActionPaperRelated_symm
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    (invariant : ValueActionEquiv action values)
    {left right : State catalog Ambient}
    (related : NameActionPaperRelated action values left right) :
    NameActionPaperRelated action.symm values right left := by
  refine ⟨?_, ?_⟩
  · have swapped := contextRelated_symm related.1
    have inverseInvariant := valueActionEquiv_symm action values invariant
    have mapped := contextRelated_actTable action.symm values inverseInvariant swapped
    simpa [actTable_symm_apply] using mapped
  · intro name
    calc
      actPaperControlAt action.symm right (action.symm.name name) =
          (paperControlAt right name).map (actPaperFiberControl action.symm) :=
        controlAt_symm_apply action right name
      _ = (actPaperControlAt action left name).map
            (actPaperFiberControl action.symm) := by
        have h := congrArg (Option.map (actPaperFiberControl action.symm))
          (related.2 (action.symm.name name))
        simpa using h.symm
      _ = paperControlAt left (action.symm.name name) := by
        simpa using controlAt_apply_symm action left (action.symm.name name)

theorem nameActionPaperRelated_refl
    (values : ValueSetoids sig) (state : State catalog Ambient) :
    NameActionPaperRelated (NameAction.refl sig Ambient) values state state := by
  refine ⟨?_, ?_⟩
  · simpa [actTable_refl] using contextRelated_refl values (activeContext state)
  · intro name
    change (paperControlAt state name).map
        (actPaperFiberControl (NameAction.refl sig Ambient)) = paperControlAt state name
    cases lookup : state.registry name with
    | none => simp [paperControlAt, NameAction.refl, Equiv.refl, lookup]
    | some fiber =>
        have paperLookup : paperControlAt state name = some (paperFiberControl fiber) := by
          simp [paperControlAt, lookup]
        rw [paperLookup]
        exact congrArg some (actPaperFiberControl_refl (sig := sig) (Ambient := Ambient)
          (paperFiberControl fiber))

theorem nameActionPaperRelated_symm_symm
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    (invariant : ValueActionEquiv action values)
    {left right : State catalog Ambient}
    (related : NameActionPaperRelated action values left right) :
    NameActionPaperRelated action.symm.symm values left right := by
  have inverseInvariant := valueActionEquiv_symm action values invariant
  have twice := nameActionPaperRelated_symm action.symm values inverseInvariant
    (nameActionPaperRelated_symm action values invariant related)
  simpa [NameAction.symm] using twice

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

theorem nameActionPaperRelated_actState_trans
    (first second : NameAction sig Ambient) (values : ValueSetoids sig)
    (secondInvariant : ValueActionEquiv second values)
    {state : State catalog Ambient} (stateWf : WellFormed state) :
    NameActionPaperRelated (first.trans second) values state
      (actState (first.trans second) state) := by
  rw [actState_trans]
  exact nameActionPaperRelated_trans first second values secondInvariant
    (nameActionPaperRelated_actState first values stateWf)
    (nameActionPaperRelated_actState second values (wellFormed_act first stateWf))

theorem nameActionPaperRelated_actState_symm
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    (invariant : ValueActionEquiv action values)
    {state : State catalog Ambient} (stateWf : WellFormed state) :
    NameActionPaperRelated action.symm values (actState action state) state := by
  exact nameActionPaperRelated_symm action values invariant
    (nameActionPaperRelated_actState action values stateWf)

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

def transportNonActivationTrace
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {middle middle' after : State catalog Ambient}
    (eq : middle = middle')
    (trace : GlobalCalculus.Trace dynamics inertia middle' after)
    (evidence : NonActivationTrace trace) :
    NonActivationTrace (eq ▸ trace) := by
  cases eq
  exact evidence

structure BackwardNonActivationTraceAction
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before actedAfter : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia (actState action before) actedAfter)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) where
  originalAfter : State catalog Ambient
  original : GlobalCalculus.Trace dynamics inertia before originalAfter
  endpoint_eq : actState action originalAfter = actedAfter
  originalAfter_wellFormed : WellFormed originalAfter
  originalAssignment : TraceProgramAssignment dynamics inertia original

noncomputable def unactNonActivationTraceAssignment
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before actedAfter : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia (actState action before) actedAfter)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) :
    BackwardNonActivationTraceAction assumptions beforeWf trace evidence assignment :=
  @GlobalCalculus.Trace.rec sig catalog Ambient dynamics inertia
    (fun source target trace =>
      ∀ (original : State catalog Ambient)
        (sourceEq : actState action original = source)
        (originalWf : WellFormed original)
        (evidence : NonActivationTrace (sourceEq.symm ▸ trace))
        (assignment : TraceProgramAssignment dynamics inertia (sourceEq.symm ▸ trace)),
        BackwardNonActivationTraceAction (before := original) (actedAfter := target)
          assumptions originalWf (sourceEq.symm ▸ trace) evidence assignment)
    (fun state original sourceEq originalWf evidence assignment => by
      cases sourceEq
      cases evidence
      cases assignment
      exact {
        originalAfter := original
        original := .nil original
        endpoint_eq := rfl
        originalAfter_wellFormed := originalWf
        originalAssignment := .nil original })
    (fun {source middle target} head tail ih original sourceEq originalWf evidence assignment => by
      cases sourceEq
      cases evidence with
      | cons headEvidence tailEvidence =>
          cases assignment with
          | cons headAssignment tailAssignment =>
              let headResult := unactUnifiedStep assumptions originalWf head
              have actedMiddleWf : WellFormed middle :=
                head.preservesWellFormed (wellFormed_act action originalWf)
              have originalMiddleWf : WellFormed headResult.originalAfter := by
                rw [← wellFormed_act_iff action headResult.originalAfter]
                rw [headResult.endpoint_eq]
                exact actedMiddleWf
              have originalNotActivation :
                  ¬IsProgramActivationRule headResult.original.rule := by
                intro originalActivation
                apply headEvidence
                rw [← headResult.same_rule]
                exact originalActivation
              have tailEvidence' :
                  NonActivationTrace (headResult.endpoint_eq ▸ tail) := by
                exact @transportNonActivationTrace sig catalog Ambient dynamics inertia
                  (actState action headResult.originalAfter) middle target
                  headResult.endpoint_eq tail tailEvidence
              have tailAssignment' := @transportTraceAssignment sig catalog Ambient
                dynamics inertia (actState action headResult.originalAfter) middle target
                headResult.endpoint_eq tail tailAssignment
              let tailResult := ih headResult.originalAfter headResult.endpoint_eq
                originalMiddleWf tailEvidence' tailAssignment'
              exact {
                originalAfter := tailResult.originalAfter
                original := .cons headResult.original tailResult.original
                endpoint_eq := tailResult.endpoint_eq
                originalAfter_wellFormed := tailResult.originalAfter_wellFormed
                originalAssignment := .cons
                  (StepProgramAssignment.ofNotActivation _ originalNotActivation)
                  tailResult.originalAssignment })
    (actState action before) actedAfter trace before rfl beforeWf evidence assignment

structure BackwardNonActivationTracePaperEndpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before actedAfter : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia (actState action before) actedAfter)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) where
  backward : BackwardNonActivationTraceAction assumptions beforeWf trace evidence assignment
  paperRelated : NameActionPaperRelated action values backward.originalAfter
    (actState action backward.originalAfter)

noncomputable def backwardNonActivationTracePaperEndpoint
    (action : NameAction sig Ambient) (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before actedAfter : State catalog Ambient} (beforeWf : WellFormed before)
    (trace : GlobalCalculus.Trace dynamics inertia (actState action before) actedAfter)
    (evidence : NonActivationTrace trace)
    (assignment : TraceProgramAssignment dynamics inertia trace) :
    BackwardNonActivationTracePaperEndpoint action values assumptions beforeWf trace evidence
      assignment :=
  let backward := unactNonActivationTraceAssignment assumptions beforeWf trace evidence assignment
  { backward := backward
    paperRelated := nameActionPaperRelated_actState action values
      backward.originalAfter_wellFormed }

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

def actedRaiseTraceEvidence : NonActivationTrace
    (actTrace raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace) :=
  .cons (by
    intro evidence
    apply raiseStep_not_activation
    rw [← actStep_rule raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseStep]
    exact evidence) (.nil _)

noncomputable def actedRaiseTraceAssignment : TraceProgramAssignment raiseDynamics raiseInertia
    (actTrace raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace) :=
  actNonactivationTraceAssignment raiseAssumptions
    GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTraceEvidence
    raiseTraceAssignment

noncomputable def unactedRaiseTrace :
    BackwardNonActivationTracePaperEndpoint swapAction values raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed
      (actTrace raiseAssumptions
        GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace)
      actedRaiseTraceEvidence actedRaiseTraceAssignment :=
  backwardNonActivationTracePaperEndpoint swapAction values raiseAssumptions
    GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed
    (actTrace raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace)
    actedRaiseTraceEvidence actedRaiseTraceAssignment

theorem actedRaiseTrace_related :
    NameActionPaperRelated swapAction values raiseAfter (actState swapAction raiseAfter) :=
  actedRaiseTrace.paperRelated

theorem actedRaiseTrace_rules : actedRaiseTrace.acted.rules = raiseTrace.rules := by
  change (actTrace raiseAssumptions
      GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace).rules =
    raiseTrace.rules
  exact actTrace_rules raiseAssumptions
    GlobalNameLifecycle.NonidentityRaiseExample.raiseState_wellFormed raiseTrace

theorem unactedRaiseTrace_related :
    NameActionPaperRelated swapAction values
      unactedRaiseTrace.backward.originalAfter
      (actState swapAction unactedRaiseTrace.backward.originalAfter) :=
  unactedRaiseTrace.paperRelated

theorem unactedRaiseTrace_endpoint :
    actState swapAction unactedRaiseTrace.backward.originalAfter =
      actState swapAction raiseAfter :=
  unactedRaiseTrace.backward.endpoint_eq

end Example

end Cordis.GlobalNamePaperRelation
