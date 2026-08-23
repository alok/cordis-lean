import Cordis.GlobalPaperTraceSimulation

/-!
# Non-reflexive birth-erased lifecycle replay

This module supplies a concrete lifecycle replay that is genuinely non-reflexive in the
allocator state.  The peer starts from the existing leave/unload example with only `nextBirth`
shifted by one; registry fibers, phases, tables, ambient data, and recovery codes are unchanged.
The paper-visible relation therefore relates the two endpoints while exact state equality does
not.  Both leave and unload are rebuilt at the shifted indices, and the resulting assigned replay
retains exact dependent transitions, well-formed endpoints, rule/actor projections, and a
transported `TraceProgramAssignment`.

This is a concrete trace-local witness, not a global lifecycle bisimulation.  It does not weaken
the existing clock-sensitive countermodel or claim that arbitrary related states admit matching
lifecycle transitions.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperShiftedLifecycle

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation Cordis.GlobalPaperTraceSimulation
open Cordis.GlobalRegistry.Example

universe u

abbrev Signature := GlobalLifecycle.Example.ExampleSig
abbrev Catalog := GlobalLifecycle.Example.exampleCatalog
abbrev State := GlobalLifecycle.Example.ExampleState
abbrev dynamics := GlobalLifecycle.Example.dynamics
abbrev inertia := GlobalLifecycle.Example.inertia
abbrev values := Cordis.GlobalRuleInvariance.HeterogeneousExample.values

/-! ## The allocator-only peer -/

def shift (state : State) : State := { state with nextBirth := state.nextBirth + 1 }

theorem shift_wellFormed {state : State} (wf : WellFormed state) : WellFormed (shift state) := by
  constructor
  · intro name fiber lookup
    exact Nat.lt_trans (wf.birth_bounded name fiber lookup) (Nat.lt_succ_self _)
  · exact wf.parent_present
  · exact wf.parent_older
  · exact wf.provisions_unique
  · exact wf.committed_provider_present
  · exact wf.committed_provider_installed

theorem shift_related (state : State) :
    BirthErasedRuleRelated values state (shift state) := by
  constructor
  · exact contextRelated_refl values (activeContext state)
  · intro name
    rfl

abbrev retiredState := GlobalLifecycle.Example.retiredState
abbrev retiredFiber := GlobalLifecycle.Example.retiredFiber
abbrev leaveTransition := GlobalLifecycle.Example.leaveTransition
abbrev leaveState := GlobalLifecycle.Example.leaveState
abbrev unloadTransition := GlobalLifecycle.Example.unloadTransition
abbrev unloadedState := GlobalLifecycle.Example.unloadedState

def shiftedRetiredState : State := shift retiredState
def shiftedLeaveState : State := shift leaveState
def shiftedUnloadedState : State := shift unloadedState

theorem shiftedRetired_wellFormed : WellFormed shiftedRetiredState :=
  shift_wellFormed GlobalLifecycle.Example.retiredState_wellFormed

theorem shiftedRetired_present :
    shiftedRetiredState.registry 0 = some retiredFiber := by
  rfl

theorem shiftedRetired_related :
    BirthErasedRuleRelated values retiredState shiftedRetiredState :=
  shift_related retiredState

theorem shiftedRetired_ne_source : shiftedRetiredState ≠ retiredState := by
  intro equality
  have clocks := congrArg GlobalState.nextBirth equality
  simp [shiftedRetiredState, shift, retiredState] at clocks

/-! ## Shifted leave and unload transitions -/

def shiftedLeaveTransition : Transition dynamics inertia shiftedRetiredState shiftedLeaveState :=
  .leave shiftedRetiredState 0 retiredFiber shiftedRetired_present
    [.external 0, .external 0] emptyProviderView rfl
    (by
      have target : targetView shiftedRetiredState 0 retiredFiber = none :=
        targetView_none_of_retired rfl
      simp [target])

theorem shiftedLeave_wellFormed : WellFormed shiftedLeaveState :=
  shiftedLeaveTransition.preservesWellFormed shiftedRetired_wellFormed

theorem shiftedLeave_related :
    BirthErasedRuleRelated values leaveState shiftedLeaveState :=
  shift_related leaveState

theorem shiftedLeave_not_activation :
    ¬IsProgramActivationRule (Step.lifecycle shiftedLeaveTransition).rule := by
  intro impossible
  change IsProgramActivationRule (.lLeave) at impossible
  exact impossible

def shiftedUnloadTransition :
    Transition dynamics inertia shiftedLeaveState shiftedUnloadedState :=
  .unload shiftedLeaveState 0 GlobalLifecycle.Example.unloadingFiber
    (by rfl) [.external 0, .external 0] emptyProviderView none rfl
    (by exact GlobalLifecycle.Example.leave_notRelied)
    {
      before_present := by rfl
      recoveredFiber := GlobalLifecycle.Example.unloadingFiber
      recovered_present := by rfl
      component_eq := rfl
      after := shiftedUnloadedState
      after_eq := rfl
      preserves_wellFormed := by
        intro _
        exact shift_wellFormed GlobalLifecycle.Example.unloadedState_wellFormed
    }

theorem shiftedUnload_wellFormed : WellFormed shiftedUnloadedState :=
  shiftedUnloadTransition.preservesWellFormed shiftedLeave_wellFormed

theorem shiftedUnload_related :
    BirthErasedRuleRelated values unloadedState shiftedUnloadedState :=
  shift_related unloadedState

theorem shiftedUnload_not_activation :
    ¬IsProgramActivationRule (Step.lifecycle shiftedUnloadTransition).rule := by
  intro impossible
  change IsProgramActivationRule (.lUnload) at impossible
  exact impossible

/-! ## Assigned trace replay -/

def sourceTrace : GlobalCalculus.Trace dynamics inertia retiredState unloadedState :=
  .cons (.lifecycle leaveTransition) (.cons (.lifecycle unloadTransition) (.nil _))

def shadowTrace :
    GlobalCalculus.Trace dynamics inertia shiftedRetiredState shiftedUnloadedState :=
  .cons (.lifecycle shiftedLeaveTransition)
    (.cons (.lifecycle shiftedUnloadTransition) (.nil _))

def sourceAssignment : TraceProgramAssignment dynamics inertia sourceTrace :=
  .cons (StepProgramAssignment.ofNonactivationLifecycle leaveTransition
    GlobalPaperTraceSimulation.PositiveLifecycle.leave_not_activation) <|
    .cons (StepProgramAssignment.ofNonactivationLifecycle unloadTransition
      GlobalPaperTraceSimulation.PositiveLifecycle.unload_not_activation) (.nil _)

def shiftedLeaveMatch :
    ForwardAssignedStepMatch values dynamics inertia (shadowBefore := shiftedRetiredState)
      (.lifecycle leaveTransition) where
  shadowAfter := shiftedLeaveState
  matched := .lifecycle shiftedLeaveTransition
  same_detailedRule := by
    change DetailedRule.lifecycle .leave = DetailedRule.lifecycle .leave
    rfl
  same_actor := by
    change Actor.fiber 0 = Actor.fiber 0
    rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.leaveState_wellFormed
  shadowAfter_wellFormed := shiftedLeave_wellFormed
  successors_related := shiftedLeave_related
  transportAssignment := fun _ => StepProgramAssignment.ofNonactivationLifecycle
    shiftedLeaveTransition shiftedLeave_not_activation

def shiftedUnloadMatch :
    ForwardAssignedStepMatch values dynamics inertia (shadowBefore := shiftedLeaveState)
      (.lifecycle unloadTransition) where
  shadowAfter := shiftedUnloadedState
  matched := .lifecycle shiftedUnloadTransition
  same_detailedRule := by
    change DetailedRule.lifecycle .unload = DetailedRule.lifecycle .unload
    rfl
  same_actor := by
    change Actor.fiber 0 = Actor.fiber 0
    rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.unloadedState_wellFormed
  shadowAfter_wellFormed := shiftedUnload_wellFormed
  successors_related := shiftedUnload_related
  transportAssignment := fun _ => StepProgramAssignment.ofNonactivationLifecycle
    shiftedUnloadTransition shiftedUnload_not_activation

def evidence : ForwardAssignedTraceEvidence values dynamics inertia sourceTrace shadowTrace := by
  exact .cons shiftedLeaveMatch (.cons shiftedUnloadMatch .nil)

noncomputable def replay :
    ForwardPaperTraceReplay values sourceTrace shiftedRetiredState :=
  ForwardAssignedTraceEvidence.replay evidence
    GlobalLifecycle.Example.retiredState_wellFormed shiftedRetired_wellFormed
    shiftedRetired_related sourceAssignment

theorem replay_endpoint : replay.result.shadowAfter = shiftedUnloadedState := by
  change shiftedUnloadedState = shiftedUnloadedState
  rfl

theorem replay_final_related :
    BirthErasedRuleRelated values unloadedState replay.result.shadowAfter := by
  simpa [replay_endpoint] using replay.final_related

theorem replay_rules : replay.result.shadow.rules = sourceTrace.rules :=
  replay.rules_eq

theorem replay_actors : replay.result.shadow.actors = sourceTrace.actors :=
  replay.actors_eq

noncomputable def replayAssignment :
    TraceProgramAssignment dynamics inertia replay.result.shadow :=
  replay.result.certificate.transportAssignment sourceAssignment

theorem replay_assignment :
    replayAssignment = replay.result.certificate.transportAssignment sourceAssignment := rfl

def executableClockPair : Nat × Nat :=
  (retiredState.nextBirth, shiftedRetiredState.nextBirth)

theorem executableClockPair_eq : executableClockPair = (1, 2) := by
  decide

def executableRules : List DetailedRule := [.lifecycle .leave, .lifecycle .unload]

theorem executableRules_eq : executableRules = detailedRules sourceTrace := by
  rfl

def executableActors : List Signature.Name := [0, 0]

theorem executableActors_eq : executableActors = sourceTrace.actors.map
    (fun actor => match actor with | .fiber name => name) := by
  rfl

end Cordis.GlobalPaperShiftedLifecycle
