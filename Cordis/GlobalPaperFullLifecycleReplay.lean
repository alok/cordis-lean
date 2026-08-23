import Cordis.GlobalPaperTraceSimulation
import Cordis.GlobalLifecycle

/-!
# Assigned full lifecycle trace

This module packages the existing heterogeneous lifecycle example as one complete dependent
trace: L-Begin, L-Iter, L-Finish, O-Retire, L-Leave, and L-Unload.  The first three records carry
actual fixed-program activation assignments; the orchestration and terminal lifecycle records
carry explicit non-activation assignments.  An all-keep `DeletionReplay` then replays that exact
trace against itself, retaining the relation, well-formedness, detailed rule ledger, actor
ledger, decision list, and transported assignment.

This is a concrete full-path certificate, not a global lifecycle bisimulation.  It does not infer
program provenance from arbitrary transitions, prove relation-aware matching for an unrelated
peer state, or close paper Lemmas 71/72/Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperFullLifecycleReplay

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalIteratorIndependence Cordis.GlobalActivationTransposition
open Cordis.GlobalPaperRelation Cordis.GlobalPaperTraceSimulation
open Cordis.GlobalRelations Cordis.GlobalLandingTransposition
open Cordis.GlobalDeletion

namespace Example

abbrev dynamics := GlobalLifecycle.Example.dynamics
abbrev inertia := GlobalLifecycle.Example.inertia
abbrev state := GlobalLifecycle.Example.ExampleState
abbrev catalog := GlobalLifecycle.Example.exampleCatalog
abbrev sig := GlobalLifecycle.Example.ExampleSig

abbrev start := GlobalLifecycle.Example.start
abbrev beginState := GlobalLifecycle.Example.beginState
abbrev iterState := GlobalLifecycle.Example.iterState
abbrev finishState := GlobalLifecycle.Example.finishState
abbrev retiredState := GlobalLifecycle.Example.retiredState
abbrev leaveState := GlobalLifecycle.Example.leaveState
abbrev unloadedState := GlobalLifecycle.Example.unloadedState

abbrev inactiveProvider := GlobalLifecycle.Example.inactiveProvider
abbrev beginFiber := GlobalLifecycle.Example.beginFiber
abbrev iterFiber := GlobalLifecycle.Example.iterFiber
abbrev activeFiber := GlobalLifecycle.Example.activeFiber
abbrev retiredFiber := GlobalLifecycle.Example.retiredFiber
abbrev unloadingFiber := GlobalLifecycle.Example.unloadingFiber

abbrev beginTransition := GlobalLifecycle.Example.beginTransition
abbrev iterTransition := GlobalLifecycle.Example.iterTransition
abbrev finishTransition := GlobalLifecycle.Example.finishTransition
abbrev retireTransition := GlobalLifecycle.Example.retireTransition
abbrev leaveTransition := GlobalLifecycle.Example.leaveTransition
abbrev unloadTransition := GlobalLifecycle.Example.unloadTransition

def values : ValueSetoids sig where
  relation _ := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

/-! ## Fixed-program activation assignments -/

def program : Program dynamics where
  owner := 0
  RegistrationError := String
  oracle := GlobalLifecycle.Example.oracle
  root := 10

def beginActivation : ProgramActivation program start := .begin inactiveProvider {
  present := GlobalLifecycle.Example.start_present
  committed := Cordis.GlobalRegistry.Example.emptyProviderView
  entry := rfl
  target := GlobalLifecycle.Example.start_target
} rfl

def firstLanding : Landing dynamics 0 10 beginState beginFiber :=
  GlobalLifecycle.Example.firstLanding

def firstAligned : ProgramAlignedLandingActivation program beginState where
  fiber := beginFiber
  present := GlobalLifecycle.Example.begin_present
  code := 10
  undos := []
  committed := Cordis.GlobalRegistry.Example.emptyProviderView
  phase := rfl
  target := GlobalLifecycle.Example.begin_target
  landing := firstLanding
  program_witness := ⟨.root, GlobalLifecycle.Example.firstStep_executed⟩
  outcome := .iter 0 rfl

def firstActivation : ProgramActivation program beginState := .landing firstAligned

def finalLanding : Landing dynamics 0 0 iterState iterFiber := GlobalLifecycle.Example.finalLanding

def finalAligned : ProgramAlignedLandingActivation program iterState where
  fiber := iterFiber
  present := GlobalLifecycle.Example.iter_present
  code := 0
  undos := [.external 0]
  committed := Cordis.GlobalRegistry.Example.emptyProviderView
  phase := rfl
  target := GlobalLifecycle.Example.iter_target
  landing := finalLanding
  program_witness := ⟨.next .root GlobalLifecycle.Example.firstStep_executed rfl,
    GlobalLifecycle.Example.finalStep_executed⟩
  outcome := .finish rfl

def finalActivation : ProgramActivation program iterState := .landing finalAligned

def beginAssignment : StepProgramAssignment (Step.lifecycle beginTransition) :=
  StepProgramAssignment.ofActivation beginActivation

def iterAssignment : StepProgramAssignment (Step.lifecycle iterTransition) :=
  StepProgramAssignment.ofActivation firstActivation

def finishAssignment : StepProgramAssignment (Step.lifecycle finishTransition) :=
  StepProgramAssignment.ofActivation finalActivation

def retireAssignment : StepProgramAssignment
    (Step.orchestration (dynamics := dynamics) (inertia := inertia) retireTransition) :=
  StepProgramAssignment.ofOrchestration retireTransition

def leaveAssignment : StepProgramAssignment (Step.lifecycle leaveTransition) :=
  StepProgramAssignment.ofNonactivationLifecycle leaveTransition (by
    intro h
    change IsProgramActivationRule .lLeave at h
    exact h)

def unloadAssignment : StepProgramAssignment (Step.lifecycle unloadTransition) :=
  StepProgramAssignment.ofNonactivationLifecycle unloadTransition (by
    intro h
    change IsProgramActivationRule .lUnload at h
    exact h)

/-! ## Complete source trace and assignment -/

def fullTrace : GlobalCalculus.Trace dynamics inertia start unloadedState :=
  .cons (.lifecycle beginTransition)
    (.cons (.lifecycle iterTransition)
      (.cons (.lifecycle finishTransition)
        (.cons (.orchestration retireTransition)
          (.cons (.lifecycle leaveTransition)
            (.cons (.lifecycle unloadTransition) (.nil _))))))

def fullAssignment : TraceProgramAssignment dynamics inertia fullTrace :=
  .cons beginAssignment
    (.cons iterAssignment
      (.cons finishAssignment
        (.cons retireAssignment
          (.cons leaveAssignment (.cons unloadAssignment (.nil _))))))

/-! ## Exact all-keep replay -/

noncomputable def fullCertificate :
    DeletionReplay (BirthErasedRuleRelated values) (fun _ => False) fullTrace fullTrace := by
  exact .keep (birthErasedRuleRelated_refl values start)
    (ForwardAssignedStepMatch.refl values (.lifecycle beginTransition)
      GlobalLifecycle.Example.start_wellFormed).toRetainedStep <|
    .keep (birthErasedRuleRelated_refl values beginState)
      (ForwardAssignedStepMatch.refl values (.lifecycle iterTransition)
        GlobalLifecycle.Example.beginState_wellFormed).toRetainedStep <|
      .keep (birthErasedRuleRelated_refl values iterState)
        (ForwardAssignedStepMatch.refl values (.lifecycle finishTransition)
          GlobalLifecycle.Example.iterState_wellFormed).toRetainedStep <|
        .keep (birthErasedRuleRelated_refl values finishState)
          (ForwardAssignedStepMatch.refl values (.orchestration retireTransition)
            GlobalLifecycle.Example.finishState_wellFormed).toRetainedStep <|
          .keep (birthErasedRuleRelated_refl values retiredState)
            (ForwardAssignedStepMatch.refl values (.lifecycle leaveTransition)
              GlobalLifecycle.Example.retiredState_wellFormed).toRetainedStep <|
            .keep (birthErasedRuleRelated_refl values leaveState)
              (ForwardAssignedStepMatch.refl values (.lifecycle unloadTransition)
                GlobalLifecycle.Example.leaveState_wellFormed).toRetainedStep <|
              .nil (birthErasedRuleRelated_refl values unloadedState)

noncomputable def replay : ForwardPaperTraceReplay values fullTrace start where
  result := {
    shadowAfter := unloadedState
    shadow := fullTrace
    certificate := fullCertificate
  }
  sourceAfter_wellFormed := GlobalLifecycle.Example.unloadedState_wellFormed
  shadowAfter_wellFormed := GlobalLifecycle.Example.unloadedState_wellFormed
  detailedRules_eq := rfl

noncomputable def replayAssignment :
    TraceProgramAssignment dynamics inertia replay.result.shadow :=
  replay.result.certificate.transportAssignment fullAssignment

def executableRules : List DetailedRule := [
  .lifecycle .begin, .lifecycle .iter, .lifecycle .finish,
  .orchestration .retire, .lifecycle .leave, .lifecycle .unload]

def executableActors : List sig.Name := [0, 0, 0, 0, 0, 0]

def executableGlobalRules : List GlobalCalculus.Rule := [
  .lBegin, .lIter, .lFinish, .oRetire, .lLeave, .lUnload]

theorem fullTrace_rules : detailedRules fullTrace = executableRules := by
  rfl

theorem fullTrace_global_rules : fullTrace.rules = executableGlobalRules := by
  rfl

theorem fullTrace_actors : fullTrace.actors.map (fun actor => match actor with
    | .fiber name => name) = executableActors := by
  rfl

theorem replay_endpoint : replay.result.shadowAfter = unloadedState := by
  rfl

theorem replay_final_related :
    BirthErasedRuleRelated values unloadedState replay.result.shadowAfter := by
  simpa [replay_endpoint] using replay.final_related

theorem replay_wellFormed : WellFormed replay.result.shadowAfter :=
  replay.shadowAfter_wellFormed

theorem replay_rules : replay.result.shadow.rules = fullTrace.rules :=
  replay.rules_eq

theorem replay_actors : replay.result.shadow.actors = fullTrace.actors :=
  replay.actors_eq

theorem replay_decisions :
    replay.result.certificate.decisions =
      [.keep, .keep, .keep, .keep, .keep, .keep] := by
  rfl

theorem replay_decisions_length :
    replay.result.certificate.decisions.length = 6 := by
  decide

theorem replay_assignment_exact :
    replayAssignment = replay.result.certificate.transportAssignment fullAssignment := rfl

def executableSummary : Prop :=
  detailedRules fullTrace = executableRules ∧
    fullTrace.rules = executableGlobalRules ∧
    fullTrace.actors.map (fun actor => match actor with | .fiber name => name) =
      executableActors ∧
    replay.result.certificate.decisions =
      [.keep, .keep, .keep, .keep, .keep, .keep]

theorem executable_summary : executableSummary := by
  exact ⟨fullTrace_rules, fullTrace_global_rules, fullTrace_actors, replay_decisions⟩

end Example

end Cordis.GlobalPaperFullLifecycleReplay
