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
    GlobalCalculus.Trace dynamics inertia before after -> List DetailedRule
  | .nil _ => []
  | .cons head tail => detailedRule head :: detailedRules tail

theorem detailedRules_append
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : GlobalCalculus.Trace dynamics inertia start middle)
    (right : GlobalCalculus.Trace dynamics inertia middle finish) :
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

/-! ## Structural all-keep replay -/

theorem replay_rules_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient -> State catalog Ambient -> Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related (fun _ => False) source shadow) :
    shadow.rules = source.rules := by
  induction replay with
  | nil => rfl
  | keep related retained tail ih =>
      simp only [GlobalCalculus.Trace.rules]
      rw [retained.same_rule, ih]
  | drop related impossible tail ih => exact False.elim impossible

theorem replay_actors_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient -> State catalog Ambient -> Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related (fun _ => False) source shadow) :
    shadow.actors = source.actors := by
  induction replay with
  | nil => rfl
  | keep related retained tail ih =>
      simp only [GlobalCalculus.Trace.actors]
      rw [retained.same_actor, ih]
  | drop related impossible tail ih => exact False.elim impossible

structure ForwardPaperTraceReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter : State catalog Ambient}
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (shadowBefore : State catalog Ambient) where
  result :
    DeletionResult (BirthErasedRuleRelated values) (fun _ => False)
      source shadowBefore
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed result.shadowAfter
  detailedRules_eq : detailedRules result.shadow = detailedRules source

noncomputable def ForwardAssignedStepSimulation.replayTrace
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : ForwardAssignedStepSimulation values dynamics inertia)
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore) (shadowWf : WellFormed shadowBefore)
    (related : BirthErasedRuleRelated values sourceBefore shadowBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter) :
    ForwardPaperTraceReplay values source shadowBefore := by
  induction source generalizing shadowBefore with
  | nil sourceBefore =>
      exact {
        result := {
          shadowAfter := shadowBefore
          shadow := .nil shadowBefore
          certificate := .nil related
        }
        sourceAfter_wellFormed := sourceWf
        shadowAfter_wellFormed := shadowWf
        detailedRules_eq := rfl
      }
  | @cons sourceBefore sourceMiddle sourceAfter head tail ih =>
      let headMatch := simulation.forward sourceWf shadowWf related head
      let tailResult := ih headMatch.sourceAfter_wellFormed
        headMatch.shadowAfter_wellFormed headMatch.successors_related
      exact {
        result := {
          shadowAfter := tailResult.result.shadowAfter
          shadow := .cons headMatch.matched tailResult.result.shadow
          certificate := .keep related headMatch.toRetainedStep
            tailResult.result.certificate
        }
        sourceAfter_wellFormed := tailResult.sourceAfter_wellFormed
        shadowAfter_wellFormed := tailResult.shadowAfter_wellFormed
        detailedRules_eq := by
          simp only [detailedRules]
          rw [headMatch.same_detailedRule, tailResult.detailedRules_eq]
      }

namespace ForwardPaperTraceReplay

theorem final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : ForwardPaperTraceReplay values source shadowBefore) :
    BirthErasedRuleRelated values sourceAfter replay.result.shadowAfter :=
  replay.result.certificate.final_related

noncomputable def transportAssignment
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : ForwardPaperTraceReplay values source shadowBefore)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceProgramAssignment dynamics inertia replay.result.shadow :=
  replay.result.certificate.transportAssignment assignment

theorem rules_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : ForwardPaperTraceReplay values source shadowBefore) :
    replay.result.shadow.rules = source.rules :=
  replay_rules_eq replay.result.certificate

theorem actors_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : ForwardPaperTraceReplay values source shadowBefore) :
    replay.result.shadow.actors = source.actors :=
  replay_actors_eq replay.result.certificate

end ForwardPaperTraceReplay

/-! ## Related assigned adjacent swaps -/

structure RelatedAssignedAdjacentSwap
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (normal : StepPair dynamics inertia before after) where
  swappedAfter : State catalog Ambient
  swapped : StepPair dynamics inertia before swappedAfter
  first_detailedRule : detailedRule swapped.first = detailedRule normal.second
  second_detailedRule : detailedRule swapped.second = detailedRule normal.first
  first_actor : swapped.first.actor = normal.second.actor
  second_actor : swapped.second.actor = normal.first.actor
  endpoints_related : BirthErasedRuleRelated values after swappedAfter
  swappedFirstAssignment : StepProgramAssignment swapped.first
  swappedSecondAssignment : StepProgramAssignment swapped.second

namespace RelatedAssignedAdjacentSwap

noncomputable def ofExact
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {normal : StepPair dynamics inertia before after}
    (swap : AssignedAdjacentSwap normal)
    (firstDetailed : detailedRule swap.swapped.first = detailedRule normal.second)
    (secondDetailed : detailedRule swap.swapped.second = detailedRule normal.first) :
    RelatedAssignedAdjacentSwap values normal where
  swappedAfter := after
  swapped := swap.swapped
  first_detailedRule := firstDetailed
  second_detailedRule := secondDetailed
  first_actor := swap.first_actor
  second_actor := swap.second_actor
  endpoints_related := birthErasedRuleRelated_refl values after
  swappedFirstAssignment := swap.swappedFirstAssignment
  swappedSecondAssignment := swap.swappedSecondAssignment

theorem first_rule
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {normal : StepPair dynamics inertia before after}
    (swap : RelatedAssignedAdjacentSwap values normal) :
    swap.swapped.first.rule = normal.second.rule := by
  rw [← detailedRule_global swap.swapped.first, ← detailedRule_global normal.second,
    swap.first_detailedRule]

theorem second_rule
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {normal : StepPair dynamics inertia before after}
    (swap : RelatedAssignedAdjacentSwap values normal) :
    swap.swapped.second.rule = normal.first.rule := by
  rw [← detailedRule_global swap.swapped.second, ← detailedRule_global normal.first,
    swap.second_detailedRule]

end RelatedAssignedAdjacentSwap

structure RelatedAdjacentRewrite
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair) where
  suffixReplay : ForwardPaperTraceReplay values occurrence.afterTrace swap.swappedAfter

namespace RelatedAdjacentRewrite

def trace
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : RelatedAdjacentRewrite values occurrence swap) :
    GlobalCalculus.Trace dynamics inertia initial result.suffixReplay.result.shadowAfter :=
  GlobalTraceFacts.Trace.append occurrence.beforeTrace
    (.cons swap.swapped.first
      (.cons swap.swapped.second result.suffixReplay.result.shadow))

theorem final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : RelatedAdjacentRewrite values occurrence swap) :
    BirthErasedRuleRelated values final result.suffixReplay.result.shadowAfter :=
  result.suffixReplay.result.certificate.final_related

theorem final_wellFormed
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : RelatedAdjacentRewrite values occurrence swap) :
    WellFormed result.suffixReplay.result.shadowAfter :=
  result.suffixReplay.shadowAfter_wellFormed

noncomputable def assignment
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (assigned : AssignedAdjacentOccurrence occurrence)
    (result : RelatedAdjacentRewrite values occurrence swap) :
    TraceProgramAssignment dynamics inertia (result.trace) := by
  let suffixAssignment := result.suffixReplay.result.certificate.transportAssignment
    assigned.afterAssignment
  let windowAndSuffix : TraceProgramAssignment dynamics inertia
      (.cons swap.swapped.first
        (.cons swap.swapped.second result.suffixReplay.result.shadow)) :=
    .cons swap.swappedFirstAssignment
      (.cons swap.swappedSecondAssignment suffixAssignment)
  exact TraceProgramAssignment.append assigned.beforeAssignment windowAndSuffix

theorem detailedRules_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : RelatedAdjacentRewrite values occurrence swap) :
    (detailedRules result.trace).Perm (detailedRules source) := by
  rw [trace, detailedRules_append]
  simp only [detailedRules]
  rw [result.suffixReplay.detailedRules_eq, swap.first_detailedRule,
    swap.second_detailedRule]
  have sourceDetailed := congrArg detailedRules occurrence.decomposition
  rw [sourceDetailed, detailedRules_append]
  simp only [detailedRules]
  exact List.Perm.append_left (detailedRules occurrence.beforeTrace)
    (List.Perm.swap (detailedRule occurrence.pair.first)
      (detailedRule occurrence.pair.second) (detailedRules occurrence.afterTrace))

theorem rules_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : RelatedAdjacentRewrite values occurrence swap) :
    result.trace.rules.Perm source.rules := by
  rw [trace, GlobalTraceRewrite.Trace.rules_append]
  simp only [GlobalCalculus.Trace.rules]
  rw [replay_rules_eq result.suffixReplay.result.certificate,
    RelatedAssignedAdjacentSwap.first_rule swap,
    RelatedAssignedAdjacentSwap.second_rule swap,
    occurrence.original_rules]
  exact List.Perm.append_left occurrence.beforeTrace.rules
    (List.Perm.swap occurrence.pair.first.rule occurrence.pair.second.rule
      occurrence.afterTrace.rules)

theorem actors_perm
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : RelatedAdjacentRewrite values occurrence swap) :
    result.trace.actors.Perm source.actors := by
  rw [trace, GlobalTraceRewrite.Trace.actors_append]
  simp only [GlobalCalculus.Trace.actors]
  rw [replay_actors_eq result.suffixReplay.result.certificate,
    swap.first_actor, swap.second_actor, occurrence.original_actors]
  exact List.Perm.append_left occurrence.beforeTrace.actors
    (List.Perm.swap occurrence.pair.first.actor occurrence.pair.second.actor
      occurrence.afterTrace.actors)

end RelatedAdjacentRewrite

noncomputable def ForwardAssignedStepSimulation.rewriteAdjacent
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : ForwardAssignedStepSimulation values dynamics inertia)
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    (initialWf : WellFormed initial)
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair) :
    RelatedAdjacentRewrite values occurrence swap := by
  have windowStartWf := occurrence.beforeTrace.preservesWellFormed initialWf
  have normalEndWf := occurrence.pair.trace.preservesWellFormed windowStartWf
  have swappedEndWf := swap.swapped.trace.preservesWellFormed windowStartWf
  exact {
    suffixReplay := simulation.replayTrace normalEndWf swappedEndWf
      swap.endpoints_related occurrence.afterTrace
  }

/-! ## Lifecycle frontier is not automatic -/

namespace ClockGap

open Cordis.GlobalPaperRelation.ClockLifecycleGap
open Cordis.GlobalProgress.RegistrationRejectionGap

theorem no_shifted_detailedDivertAbort :
    ¬∃ after, ∃ step : Step dynamics clockInertia shifted after,
      detailedRule step = .lifecycle .divertAbort := by
  rintro ⟨after, step, exactRule⟩
  cases step with
  | orchestration orchestration => cases exactRule
  | lifecycle transition =>
      have transitionRule : transition.rule = .divertAbort :=
        DetailedRule.lifecycle.inj exactRule
      exact no_shifted_divertAbort ⟨after, transition, transitionRule⟩

theorem no_forward_step_simulation :
    ¬Nonempty (ForwardAssignedStepSimulation values dynamics clockInertia) := by
  rintro ⟨simulation⟩
  let matched := simulation.forward changed_wellFormed shifted_wellFormed
    sources_related (Step.lifecycle originalAbort)
  apply no_shifted_detailedDivertAbort
  refine ⟨matched.shadowAfter, matched.matched, ?_⟩
  exact matched.same_detailedRule

end ClockGap

/-! ## Concrete orchestration replay -/

namespace PositiveOrchestration

open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap
open Cordis.GlobalPaperRelation.BirthGap

abbrev Signature := Cordis.GlobalRegistry.Example.signature

def sourceTrace
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    GlobalCalculus.Trace dynamics inertia normal
      (retireFiber normal 1 normalOneFiber) :=
  .cons (.orchestration retireOne) (.nil _)

/-! A closed, executable tag projection for the concrete positive source occurrence. -/

def executableDetailedRules : List DetailedRule :=
  [.orchestration .retire]

def executableActorNames : List Signature.Name := [1]

theorem executableDetailedRules_eq_source
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    executableDetailedRules = detailedRules (sourceTrace dynamics inertia) := by
  rfl

theorem executableActorNames_eq_source
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    executableActorNames = (sourceTrace dynamics inertia).actors.map
      (fun actor => match actor with | .fiber name => name) := by
  rfl

noncomputable def replay
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    DeletionResult (BirthErasedRuleRelated exactValues) (fun _ => False)
      (sourceTrace dynamics inertia) swapped := by
  let retained := retainedRetire dynamics inertia
  exact {
    shadowAfter := retained.shadowAfter
    shadow := .cons retained.replay (.nil _)
    certificate := .keep birth_erased_related retained
      (.nil (matchedRetire dynamics inertia).successors_related)
  }

def sourceAssignment
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    TraceProgramAssignment dynamics inertia (sourceTrace dynamics inertia) :=
  .cons (StepProgramAssignment.ofOrchestration retireOne) (.nil _)

noncomputable def shadowAssignment
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    TraceProgramAssignment dynamics inertia (replay dynamics inertia).shadow :=
  (replay dynamics inertia).certificate.transportAssignment
    (sourceAssignment dynamics inertia)

theorem final_related
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    BirthErasedRuleRelated exactValues
      (retireFiber normal 1 normalOneFiber)
      (replay dynamics inertia).shadowAfter :=
  (replay dynamics inertia).certificate.final_related

theorem rules_eq
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    (replay dynamics inertia).shadow.rules =
      (sourceTrace dynamics inertia).rules :=
  replay_rules_eq (replay dynamics inertia).certificate

theorem actors_eq
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    (replay dynamics inertia).shadow.actors =
      (sourceTrace dynamics inertia).actors :=
  replay_actors_eq (replay dynamics inertia).certificate

theorem detailedRules_eq
    (dynamics : Dynamics Signature exampleCatalog Unit)
    (inertia : InertiaPolicy dynamics) :
    detailedRules (replay dynamics inertia).shadow =
      detailedRules (sourceTrace dynamics inertia) := by
  rfl

end PositiveOrchestration

end Cordis.GlobalPaperTraceSimulation
