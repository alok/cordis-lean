import Cordis.GlobalPaperRelation

/-!
# Birth-erased assigned trace simulation

This module lifts the paper-visible birth-erased relation from local steps to finite intrinsic
traces. Orchestration matching is inherited from `GlobalPaperRelation`; lifecycle matching remains
an explicit assigned-simulation frontier. The trace theorem is therefore conditional, but its
suffix replay and assignment transport are constructed rather than assumed.

The exact lifecycle rule tag retains the distinction between L-DivertAbort and L-DivertLand,
which the public ten-name calculus projects to the same `lDivert` constructor. The related-window
rewrite also replays the old suffix from a merely related endpoint; it never casts an indexed
suffix across a relation proof.

This is an all-keep finite trace layer. It does not prove lifecycle simulation from base dynamics,
deletion, normalization, termination, confluence, Lemma 72, or Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceSimulation

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts
open Cordis.GlobalRelations Cordis.GlobalVestigial
open Cordis.GlobalDeletion Cordis.GlobalTraceRewrite
open Cordis.GlobalPaperRelation

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Exact rule tags -/

inductive DetailedRule where
  | orchestration : OrchestrationKind -> DetailedRule
  | lifecycle : GlobalLifecycle.Rule -> DetailedRule
deriving DecidableEq, Repr

def DetailedRule.global : DetailedRule -> GlobalCalculus.Rule
  | .orchestration .insert => .oInsert
  | .orchestration .retire => .oRetire
  | .orchestration .remove => .oRemove
  | .lifecycle .begin => .lBegin
  | .lifecycle .iter => .lIter
  | .lifecycle .finish => .lFinish
  | .lifecycle .divertAbort => .lDivert
  | .lifecycle .divertLand => .lDivert
  | .lifecycle .raise => .lRaise
  | .lifecycle .leave => .lLeave
  | .lifecycle .unload => .lUnload

def detailedRule
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Step dynamics inertia before after -> DetailedRule
  | .orchestration step => .orchestration (orchestrationKind step)
  | .lifecycle transition => .lifecycle transition.rule

theorem detailedRule_global
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    (detailedRule step).global = step.rule := by
  cases step with
  | orchestration step =>
      rw [Cordis.GlobalNameLifecycle.orchestrationStep_global_rule]
      cases step <;> rfl
  | lifecycle transition =>
      rw [Cordis.GlobalNameLifecycle.lifecycleStep_global_rule]
      cases transition <;> rfl

def detailedRules
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Trace dynamics inertia before after -> List DetailedRule
  | .nil _ => []
  | .cons head tail => detailedRule head :: detailedRules tail

theorem detailedRules_append
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : Trace dynamics inertia start middle)
    (right : Trace dynamics inertia middle finish) :
    detailedRules (Cordis.GlobalTraceFacts.Trace.append left right) =
      detailedRules left ++ detailedRules right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp [Cordis.GlobalTraceFacts.Trace.append, detailedRules, ih]

/-! ## Local assigned step matches -/

structure ForwardAssignedStepMatch
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  matched : Step dynamics inertia shadowBefore shadowAfter
  same_detailedRule : detailedRule matched = detailedRule source
  same_actor : matched.actor = source.actor
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed shadowAfter
  successors_related :
    BirthErasedRuleRelated values sourceAfter shadowAfter
  transportAssignment : StepProgramAssignment source -> StepProgramAssignment matched

def ForwardAssignedStepMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    {source : Step dynamics inertia sourceBefore sourceAfter}
    (matched : ForwardAssignedStepMatch values dynamics inertia
      (shadowBefore := shadowBefore) source) :
    RetainedStep (shadowBefore := shadowBefore) source where
  shadowAfter := matched.shadowAfter
  replay := matched.matched
  same_rule := by
    rw [← detailedRule_global matched.matched, ← detailedRule_global source,
      matched.same_detailedRule]
  same_actor := matched.same_actor
  transportAssignment := matched.transportAssignment

structure BackwardAssignedStepMatch
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  matched : Step dynamics inertia shadowBefore shadowAfter
  same_detailedRule : detailedRule matched = detailedRule source
  same_actor : matched.actor = source.actor
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed shadowAfter
  successors_related :
    BirthErasedRuleRelated values shadowAfter sourceAfter
  transportAssignment : StepProgramAssignment source -> StepProgramAssignment matched

def BackwardAssignedStepMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    {source : Step dynamics inertia sourceBefore sourceAfter}
    (matched : BackwardAssignedStepMatch values dynamics inertia
      (shadowBefore := shadowBefore) source) :
    RetainedStep (shadowBefore := shadowBefore) source where
  shadowAfter := matched.shadowAfter
  replay := matched.matched
  same_rule := by
    rw [← detailedRule_global matched.matched, ← detailedRule_global source,
      matched.same_detailedRule]
  same_actor := matched.same_actor
  transportAssignment := matched.transportAssignment

/-! ## Constructor-specific matching -/

noncomputable def matchOrchestrationStepForward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore) (shadowWf : WellFormed shadowBefore)
    (related : BirthErasedRuleRelated values sourceBefore shadowBefore)
    (step : OrchestrationStep sourceBefore sourceAfter) :
    ForwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore)
      (.orchestration step) := by
  let result := matchOrchestrationForward (dynamics := dynamics) (inertia := inertia)
    sourceWf shadowWf related step
  exact {
    shadowAfter := result.rightAfter
    matched := .orchestration result.matched
    same_detailedRule := congrArg DetailedRule.orchestration result.same_kind
    same_actor := result.toRetainedStep.same_actor
    sourceAfter_wellFormed := result.leftAfter_wellFormed
    shadowAfter_wellFormed := result.rightAfter_wellFormed
    successors_related := result.successors_related
    transportAssignment := fun _ => StepProgramAssignment.ofOrchestration result.matched
  }

noncomputable def matchOrchestrationStepBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (shadowWf : WellFormed shadowBefore) (sourceWf : WellFormed sourceBefore)
    (related : BirthErasedRuleRelated values shadowBefore sourceBefore)
    (step : OrchestrationStep sourceBefore sourceAfter) :
    BackwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore)
      (.orchestration step) := by
  let result := matchOrchestrationBackward (dynamics := dynamics) (inertia := inertia)
    shadowWf sourceWf related step
  exact {
    shadowAfter := result.leftAfter
    matched := .orchestration result.matched
    same_detailedRule := congrArg DetailedRule.orchestration result.same_kind
    same_actor := result.toRetainedStep.same_actor
    sourceAfter_wellFormed := result.rightAfter_wellFormed
    shadowAfter_wellFormed := result.leftAfter_wellFormed
    successors_related := result.successors_related
    transportAssignment := fun _ => StepProgramAssignment.ofOrchestration result.matched
  }

noncomputable def matchLifecycleStepForward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (lifecycle : BirthErasedLifecycleAssignedSimulation values dynamics inertia)
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore) (shadowWf : WellFormed shadowBefore)
    (related : BirthErasedRuleRelated values sourceBefore shadowBefore)
    (transition : Transition dynamics inertia sourceBefore sourceAfter) :
    ForwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore)
      (.lifecycle transition) := by
  let result := lifecycle.forward sourceWf shadowWf related transition
  exact {
    shadowAfter := result.rightAfter
    matched := .lifecycle result.matched
    same_detailedRule := congrArg DetailedRule.lifecycle result.same_lifecycle_rule
    same_actor := result.same_actor
    sourceAfter_wellFormed := result.leftAfter_wellFormed
    shadowAfter_wellFormed := result.rightAfter_wellFormed
    successors_related := result.successors_related
    transportAssignment := result.transportAssignment
  }

noncomputable def matchLifecycleStepBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (lifecycle : BirthErasedLifecycleAssignedSimulation values dynamics inertia)
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (shadowWf : WellFormed shadowBefore) (sourceWf : WellFormed sourceBefore)
    (related : BirthErasedRuleRelated values shadowBefore sourceBefore)
    (transition : Transition dynamics inertia sourceBefore sourceAfter) :
    BackwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore)
      (.lifecycle transition) := by
  let result := lifecycle.backward shadowWf sourceWf related transition
  exact {
    shadowAfter := result.leftAfter
    matched := .lifecycle result.matched
    same_detailedRule := congrArg DetailedRule.lifecycle result.same_lifecycle_rule
    same_actor := result.same_actor
    sourceAfter_wellFormed := result.rightAfter_wellFormed
    shadowAfter_wellFormed := result.leftAfter_wellFormed
    successors_related := result.successors_related
    transportAssignment := result.transportAssignment
  }

noncomputable def matchStepForward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (lifecycle : BirthErasedLifecycleAssignedSimulation values dynamics inertia)
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore) (shadowWf : WellFormed shadowBefore)
    (related : BirthErasedRuleRelated values sourceBefore shadowBefore)
    (source : Step dynamics inertia sourceBefore sourceAfter) :
    ForwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore) source := by
  cases source with
  | orchestration step =>
      exact matchOrchestrationStepForward sourceWf shadowWf related step
  | lifecycle transition =>
      exact matchLifecycleStepForward lifecycle sourceWf shadowWf related transition

noncomputable def matchStepBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (lifecycle : BirthErasedLifecycleAssignedSimulation values dynamics inertia)
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (shadowWf : WellFormed shadowBefore) (sourceWf : WellFormed sourceBefore)
    (related : BirthErasedRuleRelated values shadowBefore sourceBefore)
    (source : Step dynamics inertia sourceBefore sourceAfter) :
    BackwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore) source := by
  cases source with
  | orchestration step =>
      exact matchOrchestrationStepBackward shadowWf sourceWf related step
  | lifecycle transition =>
      exact matchLifecycleStepBackward lifecycle shadowWf sourceWf related transition

structure ForwardAssignedStepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : forall {sourceBefore shadowBefore sourceAfter : State catalog Ambient},
    WellFormed sourceBefore ->
    WellFormed shadowBefore ->
    BirthErasedRuleRelated values sourceBefore shadowBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      ForwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore) source

structure AssignedStepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    extends ForwardAssignedStepSimulation values dynamics inertia where
  backward : forall {shadowBefore sourceBefore sourceAfter : State catalog Ambient},
    WellFormed shadowBefore ->
    WellFormed sourceBefore ->
    BirthErasedRuleRelated values shadowBefore sourceBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      BackwardAssignedStepMatch values dynamics inertia (shadowBefore := shadowBefore) source

noncomputable def ForwardAssignedStepSimulation.ofLifecycle
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (lifecycle : BirthErasedLifecycleAssignedSimulation values dynamics inertia) :
    ForwardAssignedStepSimulation values dynamics inertia where
  forward := matchStepForward lifecycle

noncomputable def AssignedStepSimulation.ofLifecycle
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (lifecycle : BirthErasedLifecycleAssignedSimulation values dynamics inertia) :
    AssignedStepSimulation values dynamics inertia where
  forward := matchStepForward lifecycle
  backward := matchStepBackward lifecycle

end Cordis.GlobalPaperTraceSimulation
