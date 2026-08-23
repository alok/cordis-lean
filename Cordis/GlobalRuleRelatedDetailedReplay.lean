import Cordis.GlobalRuleRelatedTraceReplay
import Cordis.GlobalPaperTraceSimulation

/-!
# Exact replay with constructor-sensitive lifecycle tags

`GlobalRuleRelatedTraceReplay` preserves the public ten-rule `GlobalCalculus.Rule` alphabet.
That alphabet intentionally identifies L-DivertAbort and L-DivertLand, so global rule equality
alone cannot justify a detailed paper trace replay. This module adds the smallest extra field:
`ForwardDetailedStepMatch.same_detailedRule`.

Given exact `RuleRelated` endpoint matching, detailed-tag preservation, and dependent assignment
transport, the recursive theorem constructs the birth-erased `ForwardPaperTraceReplay` package.
The relation is weakened only at the output boundary; the stored shadow steps and assignments
remain exact. The `DetailedAssignedStepSimulation` contract and `replayBackward` provide the
same guarantee in the reverse orientation. No lifecycle tag equality is inferred from the coarse
ten-rule projection.
-/

set_option autoImplicit false

namespace Cordis.GlobalRuleRelatedDetailedReplay

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation Cordis.GlobalDeletion
open Cordis.GlobalRuleRelatedTraceReplay
open Cordis.GlobalPaperTraceSimulation

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

structure ForwardDetailedStepMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  base : ForwardStepMatch values (shadowBefore := shadowBefore) source
  same_detailedRule : detailedRule base.matched = detailedRule source

structure DetailedForwardStepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : ∀ {sourceBefore shadowBefore sourceAfter : State catalog Ambient},
    WellFormed sourceBefore ->
    WellFormed shadowBefore ->
    RuleRelated values sourceBefore shadowBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      ForwardDetailedStepMatch values (shadowBefore := shadowBefore) source

noncomputable def ForwardDetailedStepMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    {source : Step dynamics inertia sourceBefore sourceAfter}
    (matched : ForwardDetailedStepMatch values (shadowBefore := shadowBefore) source) :
    RetainedStep (shadowBefore := shadowBefore) source :=
  matched.base.toRetainedStep

noncomputable def DetailedForwardStepSimulation.replay
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : DetailedForwardStepSimulation values dynamics inertia)
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore)
    (shadowWf : WellFormed shadowBefore)
    (related : RuleRelated values sourceBefore shadowBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    ForwardPaperTraceReplay values source shadowBefore := by
  induction source generalizing shadowBefore with
  | nil sourceBefore =>
      exact {
        result := {
          shadowAfter := shadowBefore
          shadow := .nil shadowBefore
          certificate := .nil (birthErased_of_ruleRelated related)
        }
        sourceAfter_wellFormed := sourceWf
        shadowAfter_wellFormed := shadowWf
        detailedRules_eq := rfl
      }
  | @cons sourceBefore sourceMiddle sourceAfter head tail ih =>
      cases assignment with
      | cons headAssignment tailAssignment =>
          let headMatch := simulation.forward sourceWf shadowWf related head
          let tailReplay := ih headMatch.base.sourceAfter_wellFormed
            headMatch.base.shadowAfter_wellFormed
            headMatch.base.successors_related tailAssignment
          exact {
            result := {
              shadowAfter := tailReplay.result.shadowAfter
              shadow := .cons headMatch.base.matched tailReplay.result.shadow
              certificate := .keep (birthErased_of_ruleRelated related)
                headMatch.toRetainedStep tailReplay.result.certificate
            }
            sourceAfter_wellFormed := tailReplay.sourceAfter_wellFormed
            shadowAfter_wellFormed := tailReplay.shadowAfter_wellFormed
            detailedRules_eq := by
              simp only [detailedRules]
              rw [headMatch.same_detailedRule, tailReplay.detailedRules_eq]
          }

/-! ## Backward exact replay with constructor-sensitive tags -/

structure BackwardDetailedStepMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  base : BackwardStepMatch values (shadowBefore := shadowBefore) source
  same_detailedRule : detailedRule base.matched = detailedRule source

noncomputable def BackwardDetailedStepMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    {source : Step dynamics inertia sourceBefore sourceAfter}
    (matched : BackwardDetailedStepMatch values (shadowBefore := shadowBefore) source) :
    RetainedStep (shadowBefore := shadowBefore) source :=
  matched.base.toRetainedStep

structure DetailedAssignedStepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : ∀ {sourceBefore shadowBefore sourceAfter : State catalog Ambient},
    WellFormed sourceBefore ->
    WellFormed shadowBefore ->
    RuleRelated values sourceBefore shadowBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      ForwardDetailedStepMatch values (shadowBefore := shadowBefore) source
  backward : ∀ {shadowBefore sourceBefore sourceAfter : State catalog Ambient},
    WellFormed shadowBefore ->
    WellFormed sourceBefore ->
    RuleRelated values shadowBefore sourceBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      BackwardDetailedStepMatch values (shadowBefore := shadowBefore) source

def DetailedAssignedStepSimulation.forwardOnly
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : DetailedAssignedStepSimulation values dynamics inertia) :
    DetailedForwardStepSimulation values dynamics inertia where
  forward := simulation.forward

noncomputable def DetailedAssignedStepSimulation.replayForward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : DetailedAssignedStepSimulation values dynamics inertia)
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore)
    (shadowWf : WellFormed shadowBefore)
    (related : RuleRelated values sourceBefore shadowBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    ForwardPaperTraceReplay values source shadowBefore :=
  simulation.forwardOnly.replay sourceWf shadowWf related source assignment

noncomputable def DetailedAssignedStepSimulation.replayBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : DetailedAssignedStepSimulation values dynamics inertia)
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore)
    (shadowWf : WellFormed shadowBefore)
    (related : RuleRelated values shadowBefore sourceBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    BackwardPaperTraceReplay values source shadowBefore := by
  induction source generalizing shadowBefore with
  | nil sourceBefore =>
      exact {
        result := {
          shadowAfter := shadowBefore
          shadow := .nil shadowBefore
          certificate := .nil (birthErased_of_ruleRelated related)
        }
        sourceAfter_wellFormed := sourceWf
        shadowAfter_wellFormed := shadowWf
        detailedRules_eq := rfl
      }
  | @cons sourceBefore sourceMiddle sourceAfter head tail ih =>
      cases assignment with
      | cons headAssignment tailAssignment =>
          let headMatch := simulation.backward shadowWf sourceWf related head
          let tailReplay := ih headMatch.base.sourceAfter_wellFormed
            headMatch.base.shadowAfter_wellFormed
            headMatch.base.successors_related tailAssignment
          exact {
            result := {
              shadowAfter := tailReplay.result.shadowAfter
              shadow := .cons headMatch.base.matched tailReplay.result.shadow
              certificate := .keep (Related := fun source shadow =>
                  BirthErasedRuleRelated values shadow source) (MayDrop := fun _ => False)
                (birthErased_of_ruleRelated related)
                headMatch.toRetainedStep tailReplay.result.certificate
            }
            sourceAfter_wellFormed := tailReplay.sourceAfter_wellFormed
            shadowAfter_wellFormed := tailReplay.shadowAfter_wellFormed
            detailedRules_eq := by
              simp only [detailedRules]
              rw [headMatch.same_detailedRule, tailReplay.detailedRules_eq]
          }

def executableSummary : List String := [
  "exact-rule-related-input",
  "detailed-lifecycle-tag-preservation",
  "birth-erased-paper-replay-output",
  "backward-detailed-replay-contract"
]

end Cordis.GlobalRuleRelatedDetailedReplay
