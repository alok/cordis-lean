import Cordis.GlobalPaperFullLifecycleReplay
import Cordis.GlobalPaperShiftedLifecycle

/-!
# Non-reflexive full assigned lifecycle replay

This module instantiates the relation-aware trace simulator on the complete six-step lifecycle
fixture.  The shadow states are obtained by shifting the allocator clock in
`GlobalPaperShiftedLifecycle`; birth/clock fields are intentionally outside the paper-visible
relation, while every source occurrence still gets an exact assigned shadow step.

The resulting certificate is stronger than the reflexive full-path witness: it replays
L-Begin, L-Iter, L-Finish, O-Retire, L-Leave, and L-Unload into a genuinely distinct peer
endpoint.  It remains a finite concrete trace certificate, not a proof of global lifecycle
bisimulation, paper Lemma 71/72, or Theorem 73.  In particular, the peer assignments are
constructed occurrence-by-occurrence rather than inferred from the relation alone.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperShiftedFullLifecycle

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalActivationTransposition
open Cordis.GlobalLandingTransposition
open Cordis.GlobalPaperRelation Cordis.GlobalPaperTraceSimulation
open Cordis.GlobalRelations Cordis.GlobalDeletion
open Cordis.GlobalRegistry.Example

namespace Example

abbrev Dynamics := GlobalLifecycle.Example.dynamics
abbrev Inertia := GlobalLifecycle.Example.inertia
abbrev State := GlobalLifecycle.Example.ExampleState
abbrev Catalog := GlobalLifecycle.Example.exampleCatalog
abbrev Sig := GlobalLifecycle.Example.ExampleSig
abbrev Values := GlobalPaperShiftedLifecycle.values

abbrev sourceStart := GlobalLifecycle.Example.start
abbrev sourceBegin := GlobalLifecycle.Example.beginState
abbrev sourceIter := GlobalLifecycle.Example.iterState
abbrev sourceFinish := GlobalLifecycle.Example.finishState
abbrev sourceRetired := GlobalLifecycle.Example.retiredState
abbrev sourceLeave := GlobalLifecycle.Example.leaveState
abbrev sourceUnloaded := GlobalLifecycle.Example.unloadedState

abbrev inactiveProvider := GlobalLifecycle.Example.inactiveProvider
abbrev beginFiber := GlobalLifecycle.Example.beginFiber
abbrev iterFiber := GlobalLifecycle.Example.iterFiber
abbrev activeFiber := GlobalLifecycle.Example.activeFiber
abbrev retiredFiber := GlobalLifecycle.Example.retiredFiber
abbrev unloadingFiber := GlobalLifecycle.Example.unloadingFiber

abbrev shift := GlobalPaperShiftedLifecycle.shift

theorem shiftWf {s : State} (wf : WellFormed s) : WellFormed (shift s) :=
  GlobalPaperShiftedLifecycle.shift_wellFormed wf

theorem shiftRelated (s : State) : BirthErasedRuleRelated Values s (shift s) :=
  GlobalPaperShiftedLifecycle.shift_related s

def shiftedStart : State := shift sourceStart
def shiftedBegin : State := shift sourceBegin
def shiftedIter : State := shift sourceIter
def shiftedFinish : State := shift sourceFinish
def shiftedRetired : State := shift sourceRetired
def shiftedLeave : State := shift sourceLeave
def shiftedUnloaded : State := shift sourceUnloaded

theorem shiftedStart_wf : WellFormed shiftedStart :=
  shiftWf GlobalLifecycle.Example.start_wellFormed
theorem shiftedBegin_wf : WellFormed shiftedBegin :=
  shiftWf GlobalLifecycle.Example.beginState_wellFormed
theorem shiftedIter_wf : WellFormed shiftedIter :=
  shiftWf GlobalLifecycle.Example.iterState_wellFormed
theorem shiftedFinish_wf : WellFormed shiftedFinish :=
  shiftWf GlobalLifecycle.Example.finishState_wellFormed
theorem shiftedRetired_wf : WellFormed shiftedRetired :=
  shiftWf GlobalLifecycle.Example.retiredState_wellFormed
theorem shiftedLeave_wf : WellFormed shiftedLeave :=
  shiftWf GlobalLifecycle.Example.leaveState_wellFormed
theorem shiftedUnloaded_wf : WellFormed shiftedUnloaded :=
  shiftWf GlobalLifecycle.Example.unloadedState_wellFormed

theorem shiftedStart_related : BirthErasedRuleRelated Values sourceStart shiftedStart :=
  shiftRelated sourceStart
theorem shiftedBegin_related : BirthErasedRuleRelated Values sourceBegin shiftedBegin :=
  shiftRelated sourceBegin
theorem shiftedIter_related : BirthErasedRuleRelated Values sourceIter shiftedIter :=
  shiftRelated sourceIter
theorem shiftedFinish_related : BirthErasedRuleRelated Values sourceFinish shiftedFinish :=
  shiftRelated sourceFinish
theorem shiftedRetired_related : BirthErasedRuleRelated Values sourceRetired shiftedRetired :=
  shiftRelated sourceRetired
theorem shiftedLeave_related : BirthErasedRuleRelated Values sourceLeave shiftedLeave :=
  shiftRelated sourceLeave
theorem shiftedUnloaded_related : BirthErasedRuleRelated Values sourceUnloaded shiftedUnloaded :=
  shiftRelated sourceUnloaded

theorem shiftedStart_present : shiftedStart.registry 0 = some inactiveProvider := by
  change sourceStart.registry 0 = some inactiveProvider
  exact GlobalLifecycle.Example.start_present

theorem shiftedBegin_present : shiftedBegin.registry 0 = some beginFiber := by
  change sourceBegin.registry 0 = some beginFiber
  exact GlobalLifecycle.Example.begin_present

theorem shiftedIter_present : shiftedIter.registry 0 = some iterFiber := by
  change sourceIter.registry 0 = some iterFiber
  exact GlobalLifecycle.Example.iter_present

theorem shiftedFinish_present : shiftedFinish.registry 0 = some activeFiber := by
  change sourceFinish.registry 0 = some activeFiber
  exact GlobalLifecycle.Example.finish_present

theorem shiftedRetired_present : shiftedRetired.registry 0 = some retiredFiber := by
  change sourceRetired.registry 0 = some retiredFiber
  exact GlobalLifecycle.Example.retired_present

theorem shiftedLeave_present : shiftedLeave.registry 0 = some unloadingFiber := by
  change sourceLeave.registry 0 = some unloadingFiber
  exact GlobalLifecycle.Example.leave_present

theorem shiftedStart_target :
    targetView shiftedStart 0 inactiveProvider = some emptyProviderView := by
  apply targetView_eq_of_isTarget shiftedStart_wf
  exact {
    present := shiftedStart_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

def shiftedBeginTransition : Transition Dynamics Inertia shiftedStart shiftedBegin :=
  .begin shiftedStart 0 inactiveProvider shiftedStart_present rfl emptyProviderView
    shiftedStart_target

def shiftedBeginFiber : Fiber Catalog := {
  inactiveProvider with phase := .reloading 10 [] emptyProviderView
}

theorem shiftedBeginFiber_eq : shiftedBeginFiber = beginFiber := by
  rfl

theorem shiftedBegin_target :
    targetView shiftedBegin 0 beginFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget shiftedBegin_wf
  exact {
    present := shiftedBegin_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

def shiftedFirstResult : OrdinaryResult Catalog Nat where
  after := GlobalLifecycle.Example.advance shiftedBegin
  undo := 0
  next := some 0

def shiftedFirstStep : IterationStep Dynamics 0 10 shiftedBegin where
  after := shiftedFirstResult.after
  undo := .external shiftedFirstResult.undo
  next := shiftedFirstResult.next
  source := .ordinary shiftedFirstResult (by rfl)
  recovers := by
    change (GlobalLifecycle.Example.applyExternalUndo 0
      (GlobalLifecycle.Example.advance shiftedBegin)).ambient =
      shiftedBegin.ambient
    rfl
  preserves_wellFormed := fun wf => GlobalLifecycle.Example.advance_preserves wf

theorem shiftedFirst_executed :
    executeOne Dynamics (GlobalLifecycle.Example.oracle) 10 shiftedBegin =
      .ok shiftedFirstStep := by
  rfl

def shiftedFirstLanding : Landing Dynamics 0 10 shiftedBegin beginFiber where
  RegistrationError := String
  oracle := GlobalLifecycle.Example.oracle
  step := shiftedFirstStep
  executed := shiftedFirst_executed
  before_present := shiftedBegin_present
  afterFiber := beginFiber
  after_present := by rfl
  component_eq := rfl
  phase_eq := rfl

def shiftedIterState : State :=
  setPhase shiftedFirstStep.after 0 shiftedFirstLanding.afterFiber
    (.reloading 0 [shiftedFirstStep.undo] emptyProviderView)

theorem shiftedIterState_eq : shiftedIterState = shiftedIter := by
  rfl

theorem shiftedIter_target :
    targetView shiftedIterState 0 iterFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget shiftedIter_wf
  exact {
    present := shiftedIter_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

def shiftedIterTransition : Transition Dynamics Inertia shiftedBegin shiftedIterState :=
  .iter shiftedBegin 0 beginFiber shiftedBegin_present 10 [] emptyProviderView rfl
    shiftedBegin_target shiftedFirstLanding 0 rfl

def shiftedFinalResult : OrdinaryResult Catalog Nat where
  after := GlobalLifecycle.Example.advance shiftedIterState
  undo := 0
  next := none

def shiftedFinalStep : IterationStep Dynamics 0 0 shiftedIterState where
  after := shiftedFinalResult.after
  undo := .external shiftedFinalResult.undo
  next := shiftedFinalResult.next
  source := .ordinary shiftedFinalResult (by rfl)
  recovers := by
    change (GlobalLifecycle.Example.applyExternalUndo 0
      (GlobalLifecycle.Example.advance shiftedIterState)).ambient =
      shiftedIterState.ambient
    rfl
  preserves_wellFormed := fun wf => GlobalLifecycle.Example.advance_preserves wf

theorem shiftedFinal_executed :
    executeOne Dynamics (GlobalLifecycle.Example.oracle) 0 shiftedIterState =
      .ok shiftedFinalStep := by
  rfl

def shiftedFinalLanding : Landing Dynamics 0 0 shiftedIterState iterFiber where
  RegistrationError := String
  oracle := GlobalLifecycle.Example.oracle
  step := shiftedFinalStep
  executed := shiftedFinal_executed
  before_present := shiftedIter_present
  afterFiber := iterFiber
  after_present := by rfl
  component_eq := rfl
  phase_eq := rfl

def shiftedFinishTransition : Transition Dynamics Inertia shiftedIterState shiftedFinish :=
  .finish shiftedIterState 0 iterFiber shiftedIter_present 0 [.external 0]
    emptyProviderView rfl shiftedIter_target shiftedFinalLanding rfl

def shiftedRetireTransition : OrchestrationStep shiftedFinish shiftedRetired :=
  .retire shiftedFinish 0 activeFiber shiftedFinish_present

abbrev shiftedLeaveTransition : Transition Dynamics Inertia shiftedRetired shiftedLeave :=
  GlobalPaperShiftedLifecycle.shiftedLeaveTransition

abbrev shiftedUnloadTransition : Transition Dynamics Inertia shiftedLeave shiftedUnloaded :=
  GlobalPaperShiftedLifecycle.shiftedUnloadTransition

abbrev program := GlobalPaperFullLifecycleReplay.Example.program

def shiftedBeginActivation : ProgramActivation program shiftedStart := .begin inactiveProvider {
  present := shiftedStart_present
  committed := emptyProviderView
  entry := rfl
  target := shiftedStart_target
} rfl

def shiftedFirstAligned : ProgramAlignedLandingActivation program shiftedBegin where
  fiber := beginFiber
  present := shiftedBegin_present
  code := 10
  undos := []
  committed := emptyProviderView
  phase := rfl
  target := shiftedBegin_target
  landing := shiftedFirstLanding
  program_witness := ⟨.root, shiftedFirst_executed⟩
  outcome := .iter 0 rfl

def shiftedFirstActivation : ProgramActivation program shiftedBegin :=
  .landing shiftedFirstAligned

def shiftedFinalAligned : ProgramAlignedLandingActivation program shiftedIterState where
  fiber := iterFiber
  present := shiftedIter_present
  code := 0
  undos := [.external 0]
  committed := emptyProviderView
  phase := rfl
  target := shiftedIter_target
  landing := shiftedFinalLanding
  program_witness := ⟨.next .root shiftedFirst_executed rfl, shiftedFinal_executed⟩
  outcome := .finish rfl

def shiftedFinalActivation : ProgramActivation program shiftedIterState :=
  .landing shiftedFinalAligned

def shiftedBeginAssignment : StepProgramAssignment
    (Step.lifecycle shiftedBeginTransition) := by
  exact StepProgramAssignment.ofActivation shiftedBeginActivation

def shiftedIterAssignment : StepProgramAssignment
    (Step.lifecycle shiftedIterTransition) := by
  exact StepProgramAssignment.ofActivation shiftedFirstActivation

def shiftedFinishAssignment : StepProgramAssignment
    (Step.lifecycle shiftedFinishTransition) := by
  exact StepProgramAssignment.ofActivation shiftedFinalActivation

def shiftedRetireAssignment : StepProgramAssignment
    (Step.orchestration (dynamics := Dynamics) (inertia := Inertia)
      shiftedRetireTransition) :=
  StepProgramAssignment.ofOrchestration shiftedRetireTransition

def shiftedLeaveAssignment : StepProgramAssignment
    (Step.lifecycle shiftedLeaveTransition) :=
  StepProgramAssignment.ofNonactivationLifecycle shiftedLeaveTransition (by
    intro h
    change IsProgramActivationRule (Step.lifecycle shiftedLeaveTransition).rule at h
    exact h)

def shiftedUnloadAssignment : StepProgramAssignment
    (Step.lifecycle shiftedUnloadTransition) :=
  StepProgramAssignment.ofNonactivationLifecycle shiftedUnloadTransition (by
    intro h
    change IsProgramActivationRule (Step.lifecycle shiftedUnloadTransition).rule at h
    exact h)

def shiftedTrace : GlobalCalculus.Trace Dynamics Inertia shiftedStart shiftedUnloaded :=
  .cons (.lifecycle shiftedBeginTransition)
    (.cons (.lifecycle shiftedIterTransition)
      (.cons (.lifecycle shiftedFinishTransition)
        (.cons (.orchestration shiftedRetireTransition)
          (.cons (.lifecycle shiftedLeaveTransition)
            (.cons (.lifecycle shiftedUnloadTransition) (.nil _))))))

def shiftedAssignment : TraceProgramAssignment Dynamics Inertia shiftedTrace :=
  .cons shiftedBeginAssignment
    (.cons shiftedIterAssignment
      (.cons shiftedFinishAssignment
        (.cons shiftedRetireAssignment
          (.cons shiftedLeaveAssignment (.cons shiftedUnloadAssignment (.nil _))))))

def sourceTrace := GlobalPaperFullLifecycleReplay.Example.fullTrace
def sourceAssignment := GlobalPaperFullLifecycleReplay.Example.fullAssignment

def beginMatch : ForwardAssignedStepMatch Values Dynamics Inertia
    (shadowBefore := shiftedStart) (.lifecycle GlobalLifecycle.Example.beginTransition) where
  shadowAfter := shiftedBegin
  matched := .lifecycle shiftedBeginTransition
  same_detailedRule := rfl
  same_actor := rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.beginState_wellFormed
  shadowAfter_wellFormed := shiftedBegin_wf
  successors_related := shiftedBegin_related
  transportAssignment := fun _ => shiftedBeginAssignment

def iterMatch : ForwardAssignedStepMatch Values Dynamics Inertia
    (shadowBefore := shiftedBegin) (.lifecycle GlobalLifecycle.Example.iterTransition) where
  shadowAfter := shiftedIter
  matched := .lifecycle shiftedIterTransition
  same_detailedRule := rfl
  same_actor := rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.iterState_wellFormed
  shadowAfter_wellFormed := shiftedIter_wf
  successors_related := shiftedIter_related
  transportAssignment := fun _ => shiftedIterAssignment

def finishMatch : ForwardAssignedStepMatch Values Dynamics Inertia
    (shadowBefore := shiftedIter) (.lifecycle GlobalLifecycle.Example.finishTransition) where
  shadowAfter := shiftedFinish
  matched := .lifecycle shiftedFinishTransition
  same_detailedRule := rfl
  same_actor := rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.finishState_wellFormed
  shadowAfter_wellFormed := shiftedFinish_wf
  successors_related := shiftedFinish_related
  transportAssignment := fun _ => shiftedFinishAssignment

def retireMatch : ForwardAssignedStepMatch Values Dynamics Inertia
    (shadowBefore := shiftedFinish)
    (.orchestration GlobalLifecycle.Example.retireTransition) where
  shadowAfter := shiftedRetired
  matched := .orchestration shiftedRetireTransition
  same_detailedRule := rfl
  same_actor := rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.retiredState_wellFormed
  shadowAfter_wellFormed := shiftedRetired_wf
  successors_related := shiftedRetired_related
  transportAssignment := fun _ => shiftedRetireAssignment

def leaveMatch : ForwardAssignedStepMatch Values Dynamics Inertia
    (shadowBefore := shiftedRetired) (.lifecycle GlobalLifecycle.Example.leaveTransition) where
  shadowAfter := shiftedLeave
  matched := .lifecycle shiftedLeaveTransition
  same_detailedRule := rfl
  same_actor := rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.leaveState_wellFormed
  shadowAfter_wellFormed := shiftedLeave_wf
  successors_related := shiftedLeave_related
  transportAssignment := fun _ => shiftedLeaveAssignment

def unloadMatch : ForwardAssignedStepMatch Values Dynamics Inertia
    (shadowBefore := shiftedLeave) (.lifecycle GlobalLifecycle.Example.unloadTransition) where
  shadowAfter := shiftedUnloaded
  matched := .lifecycle shiftedUnloadTransition
  same_detailedRule := rfl
  same_actor := rfl
  sourceAfter_wellFormed := GlobalLifecycle.Example.unloadedState_wellFormed
  shadowAfter_wellFormed := shiftedUnloaded_wf
  successors_related := shiftedUnloaded_related
  transportAssignment := fun _ => shiftedUnloadAssignment

def evidence : ForwardAssignedTraceEvidence Values Dynamics Inertia sourceTrace shiftedTrace :=
  .cons beginMatch
    (.cons iterMatch
      (.cons finishMatch
        (.cons retireMatch
          (.cons leaveMatch (.cons unloadMatch .nil)))))

noncomputable def replay : ForwardPaperTraceReplay Values sourceTrace shiftedStart :=
  ForwardAssignedTraceEvidence.replay evidence
    GlobalLifecycle.Example.start_wellFormed shiftedStart_wf shiftedStart_related sourceAssignment

noncomputable def replayAssignment :
    TraceProgramAssignment Dynamics Inertia replay.result.shadow :=
  replay.result.certificate.transportAssignment sourceAssignment

theorem replay_endpoint : replay.result.shadowAfter = shiftedUnloaded := by
  change shiftedUnloaded = shiftedUnloaded
  rfl

theorem replay_final_related :
    BirthErasedRuleRelated Values GlobalLifecycle.Example.unloadedState
      replay.result.shadowAfter := by
  simpa [replay_endpoint] using replay.final_related

theorem replay_shadow_wellFormed : WellFormed replay.result.shadowAfter :=
  replay.shadowAfter_wellFormed

theorem replay_rules : replay.result.shadow.rules = sourceTrace.rules := replay.rules_eq

theorem replay_actors : replay.result.shadow.actors = sourceTrace.actors := replay.actors_eq

theorem replay_decisions : replay.result.certificate.decisions =
    List.replicate (GlobalTraceFacts.Trace.records sourceTrace).length
      ReplayDecision.keep := by
  rfl

theorem replay_assignment_matches_constructed :
    replayAssignment = shiftedAssignment := by
  rfl

def executableClockPair : Nat × Nat :=
  (sourceStart.nextBirth, shiftedStart.nextBirth)

theorem executableClockPair_eq : executableClockPair = (1, 2) := by
  decide

theorem shiftedStart_ne_source : shiftedStart ≠ sourceStart := by
  intro equality
  have clocks := congrArg GlobalState.nextBirth equality
  change 2 = 1 at clocks
  cases clocks

def executableRules : List DetailedRule := [
  .lifecycle .begin, .lifecycle .iter, .lifecycle .finish,
  .orchestration .retire, .lifecycle .leave, .lifecycle .unload]

def executableActors : List Sig.Name := [0, 0, 0, 0, 0, 0]

def executableGlobalRules : List GlobalCalculus.Rule := [
  .lBegin, .lIter, .lFinish, .oRetire, .lLeave, .lUnload]

theorem shiftedTrace_rules : detailedRules shiftedTrace = executableRules := by
  rfl

theorem shiftedTrace_global_rules : shiftedTrace.rules = executableGlobalRules := by
  rfl

theorem shiftedTrace_actors : shiftedTrace.actors.map (fun actor => match actor with
    | .fiber name => name) = executableActors := by
  rfl

end Example
end Cordis.GlobalPaperShiftedFullLifecycle
