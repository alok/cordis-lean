import Cordis.GlobalPaperTraceSimulation
import Cordis.GlobalPaperNonReflexiveRewrite

/-!
# Backward birth-erased assigned trace rewriting

This module mirrors the forward related-endpoint rewrite.  Given an adjacent source window and
a swapped window whose endpoint is only birth-erased related, it replays the original suffix from
the swapped endpoint using the backward assigned simulator.  The output therefore has the
relation in the opposite orientation, a transported dependent assignment, and the same detailed
rule/actor permutations as the forward construction.

The construction remains conditional: lifecycle matching is supplied through
`AssignedStepSimulation`, while the concrete witness below uses only the proved orchestration
matcher.  It does not claim a global lifecycle bisimulation, deletion theorem, normalization,
confluence, Lemma 72, or Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceBackwardRewrite

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceSimulation

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## The mirrored relation-aware rewrite certificate -/

structure BackwardRelatedAdjacentRewrite
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair) where
  suffixReplay : BackwardPaperTraceReplay values occurrence.afterTrace swap.swappedAfter

namespace BackwardRelatedAdjacentRewrite

def trace
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
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
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
    BirthErasedRuleRelated values result.suffixReplay.result.shadowAfter final :=
  result.suffixReplay.result.certificate.final_related

theorem final_wellFormed
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    {occurrence : AdjacentOccurrence source}
    {swap : RelatedAssignedAdjacentSwap values occurrence.pair}
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
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
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
    TraceProgramAssignment dynamics inertia (trace result) := by
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
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
    (detailedRules (trace result)).Perm (detailedRules source) := by
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
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
    (trace result).rules.Perm source.rules := by
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
    (result : BackwardRelatedAdjacentRewrite values occurrence swap) :
    (trace result).actors.Perm source.actors := by
  rw [trace, GlobalTraceRewrite.Trace.actors_append]
  simp only [GlobalCalculus.Trace.actors]
  rw [replay_actors_eq result.suffixReplay.result.certificate,
    swap.first_actor, swap.second_actor, occurrence.original_actors]
  exact List.Perm.append_left occurrence.beforeTrace.actors
    (List.Perm.swap occurrence.pair.first.actor occurrence.pair.second.actor
      occurrence.afterTrace.actors)

end BackwardRelatedAdjacentRewrite

/-! ## Generic construction from the bidirectional assigned simulator -/

noncomputable def AssignedStepSimulation.rewriteAdjacentBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : AssignedStepSimulation values dynamics inertia)
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    (initialWf : WellFormed initial)
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair) :
    BackwardRelatedAdjacentRewrite values occurrence swap := by
  have windowStartWf := occurrence.beforeTrace.preservesWellFormed initialWf
  have normalEndWf := occurrence.pair.trace.preservesWellFormed windowStartWf
  have swappedEndWf := swap.swapped.trace.preservesWellFormed windowStartWf
  exact {
    suffixReplay := simulation.replayTraceBackward normalEndWf swappedEndWf
      (birthErasedRuleRelated_symm swap.endpoints_related) occurrence.afterTrace
  }

noncomputable def BackwardOrchestrationStepSimulation.rewriteAdjacentBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : BackwardOrchestrationStepSimulation values dynamics inertia)
    {initial final : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia initial final}
    (initialWf : WellFormed initial)
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair)
    (afterAll : AllOrchestrationTrace occurrence.afterTrace) :
    BackwardRelatedAdjacentRewrite values occurrence swap := by
  have windowStartWf := occurrence.beforeTrace.preservesWellFormed initialWf
  have normalEndWf := occurrence.pair.trace.preservesWellFormed windowStartWf
  have swappedEndWf := swap.swapped.trace.preservesWellFormed windowStartWf
  exact {
    suffixReplay := simulation.replayTrace normalEndWf swappedEndWf
      (birthErasedRuleRelated_symm swap.endpoints_related) afterAll
  }

/-! ## Concrete non-reflexive backward suffix witness -/

namespace Example

open Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite
open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap
open Cordis.GlobalPaperRelation.BirthGap

noncomputable def result
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    BackwardRelatedAdjacentRewrite exactValues
      (occurrence dynamics inertia) (swap dynamics inertia) :=
  BackwardOrchestrationStepSimulation.rewriteAdjacentBackward
    (BackwardOrchestrationStepSimulation.ofPaperRelation exactValues dynamics inertia)
    (initial := Source) (final := sourceFinal)
    (source := sourceTrace dynamics inertia)
    Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.source_wellFormed
      (occurrence dynamics inertia) (swap dynamics inertia)
    (.cons retireOne (.nil sourceFinal) (.nil sourceFinal))

noncomputable def assignment
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    TraceProgramAssignment dynamics inertia
      (BackwardRelatedAdjacentRewrite.trace (result dynamics inertia)) :=
  BackwardRelatedAdjacentRewrite.assignment
    (assignedOccurrence dynamics inertia) (result dynamics inertia)

theorem final_related
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    BirthErasedRuleRelated exactValues
      (result dynamics inertia).suffixReplay.result.shadowAfter sourceFinal :=
  (result dynamics inertia).final_related

theorem final_wellFormed
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    WellFormed (result dynamics inertia).suffixReplay.result.shadowAfter :=
  (result dynamics inertia).final_wellFormed

theorem assignment_exact
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    assignment dynamics inertia =
      BackwardRelatedAdjacentRewrite.assignment
        (assignedOccurrence dynamics inertia) (result dynamics inertia) :=
  rfl

def executableRules : List GlobalCalculus.Rule :=
  [.oInsert, .oInsert, .oRetire]

def executableActors : List
    Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature.Name := [2, 1, 1]

theorem source_rules
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    (sourceTrace dynamics inertia).rules = executableRules := by
  rfl

theorem backward_rules_perm
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    (result dynamics inertia).trace.rules.Perm (sourceTrace dynamics inertia).rules :=
  (result dynamics inertia).rules_perm

theorem backward_actors
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    (result dynamics inertia).trace.actors.map (fun actor => match actor with
      | .fiber name => name) = executableActors := by
  simp only [BackwardRelatedAdjacentRewrite.trace,
    GlobalTraceRewrite.Trace.actors_append]
  simp only [GlobalCalculus.Trace.actors]
  simp only [List.map_append, List.map_cons]
  have suffixActors := replay_actors_eq
    (result dynamics inertia).suffixReplay.result.certificate
  have suffixActorsMapped := congrArg
    (List.map (fun actor => match actor with | .fiber name => name)) suffixActors
  rw [suffixActorsMapped]
  rfl

theorem backward_actors_perm
    (dynamics : Cordis.GlobalDynamics.Dynamics
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Signature
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Catalog
      Cordis.GlobalPaperNonReflexiveRewrite.BirthGapRewrite.Ambient)
    (inertia : Cordis.GlobalLifecycle.InertiaPolicy dynamics) :
    (result dynamics inertia).trace.actors.Perm (sourceTrace dynamics inertia).actors :=
  (result dynamics inertia).actors_perm

end Example

end Cordis.GlobalPaperTraceBackwardRewrite
