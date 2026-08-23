import Cordis.GlobalRuleRelatedTraceReplay
import Cordis.GlobalLifecycleBisimulation

/-!
# Conditional lifecycle bisimulation to exact replay

`GlobalLifecycleBisimulation` supplies a well-formed, bidirectional matching certificate for
the unified ten-rule calculus. `GlobalRuleRelatedTraceReplay` consumes a local match whose
endpoint assignment transport is explicit. This module is the narrow adapter between them:
the conditional bisimulation is reusable, but it does not manufacture dependent program
assignments. `BisimulationAssignmentTransport` is therefore a visible proof obligation.

The adapter preserves the source boundary. It does not claim that arbitrary `Dynamics` respect
`RuleRelated`, and it does not infer assignment transport from equal rule names or actors.
Once the caller supplies that transport, the existing exact all-keep replay induction applies
without any endpoint casts or allocator erasure.
-/

set_option autoImplicit false

namespace Cordis.GlobalRuleRelatedTraceReplay

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation Cordis.GlobalDeletion

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

/-! ## The one additional dependent proof obligation -/

structure BisimulationAssignmentTransport
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (bisim : GlobalLifecycleBisimulation.WellFormedRuleBisimulation
      values dynamics inertia) where
  forward : ∀ {left right leftAfter : State catalog Ambient},
    (leftWf : WellFormed left) ->
    (rightWf : WellFormed right) ->
    (related : RuleRelated values left right) ->
    (step : Step dynamics inertia left leftAfter) ->
      StepProgramAssignment step ->
        StepProgramAssignment (bisim.forward leftWf rightWf related step).matched
  backward : ∀ {left right rightAfter : State catalog Ambient},
    (leftWf : WellFormed left) ->
    (rightWf : WellFormed right) ->
    (related : RuleRelated values left right) ->
    (step : Step dynamics inertia right rightAfter) ->
      StepProgramAssignment step ->
        StepProgramAssignment (bisim.backward leftWf rightWf related step).matched

theorem actor_eq_of_actedName_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    {source : Step dynamics inertia leftBefore leftAfter}
    {matched : Step dynamics inertia rightBefore rightAfter}
    (same : matched.actedName = source.actedName) :
    matched.actor = source.actor := by
  simpa [Step.actor] using same

/-! ## Adapter and replay theorem -/

noncomputable def StepSimulation.ofWellFormedBisimulation
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (bisim : GlobalLifecycleBisimulation.WellFormedRuleBisimulation
      values dynamics inertia)
    (transport : BisimulationAssignmentTransport values dynamics inertia bisim) :
    StepSimulation values dynamics inertia where
  forward := fun sourceWf shadowWf related source =>
    let base := bisim.forward sourceWf shadowWf related source
    {
      shadowAfter := base.rightAfter
      matched := base.matched
      same_rule := base.same_rule
      same_actor := actor_eq_of_actedName_eq base.same_actor
      sourceAfter_wellFormed := base.leftAfter_wellFormed
      shadowAfter_wellFormed := base.rightAfter_wellFormed
      successors_related := base.successors_related
      transportAssignment := transport.forward sourceWf shadowWf related source
    }
  backward := fun shadowWf sourceWf related source =>
    let base := bisim.backward shadowWf sourceWf related source
    {
      shadowAfter := base.leftAfter
      matched := base.matched
      same_rule := base.same_rule
      same_actor := actor_eq_of_actedName_eq base.same_actor
      sourceAfter_wellFormed := base.rightAfter_wellFormed
      shadowAfter_wellFormed := base.leftAfter_wellFormed
      successors_related := base.successors_related
      transportAssignment := transport.backward shadowWf sourceWf related source
    }

noncomputable def replayFromWellFormedBisimulation
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (bisim : GlobalLifecycleBisimulation.WellFormedRuleBisimulation
      values dynamics inertia)
    (transport : BisimulationAssignmentTransport values dynamics inertia bisim)
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore)
    (shadowWf : WellFormed shadowBefore)
    (related : RuleRelated values sourceBefore shadowBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceReplay values source shadowBefore :=
  (StepSimulation.ofWellFormedBisimulation bisim transport).replay
    sourceWf shadowWf related source assignment

def executableSummary : List String := [
  "well-formed-rule-bisimulation",
  "explicit-assignment-transport",
  "exact-rule-related-replay-adapter"
]

end Cordis.GlobalRuleRelatedTraceReplay
