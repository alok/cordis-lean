import Cordis.GlobalPaperTraceSimulation

/-!
# Concrete non-reflexive related-endpoint trace rewriting

This module instantiates the relation-aware adjacent-window API with the allocator-order gap
already present in `GlobalPaperRelation.BirthGap`. The two insertions have a common predecessor,
but opposite orders allocate different birth ranks. Their endpoints are therefore related by the
birth-erased paper relation while remaining distinct and failing the current exact `RuleRelated`
relation. A trailing `O-Retire` is then replayed from the merely related swapped endpoint by the
orchestration simulator.

The witness is deliberately finite and occurrence-indexed. It proves an actual related-window
rewrite, endpoint well-formedness, transported assignments, and rule/actor permutations. It does
not infer lifecycle simulation, a global normalization strategy, episode deletion, Lemma 72, or
Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperNonReflexiveRewrite

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts
open Cordis.GlobalRelations Cordis.GlobalVestigial
open Cordis.GlobalDeletion Cordis.GlobalTraceRewrite
open Cordis.GlobalPaperRelation Cordis.GlobalPaperTraceSimulation

namespace BirthGapRewrite

open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap
open Cordis.GlobalPaperRelation.BirthGap

abbrev Signature := Cordis.GlobalRegistry.Example.signature
abbrev Catalog := Cordis.GlobalRegistry.Example.catalog
abbrev Ambient := Unit

def normalPair
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    StepPair dynamics inertia Source normal where
  middle := registered
  first := .orchestration registerChild
  second := .orchestration normalInsert

def swappedPair
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    StepPair dynamics inertia Source swapped where
  middle := swappedFirst
  first := .orchestration swappedFirstInsert
  second := .orchestration swappedSecondInsert

def sourceFinal : ExampleState := retireFiber normal 1 normalOneFiber

def sourceTrace
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    GlobalCalculus.Trace dynamics inertia Source sourceFinal :=
  .cons (.orchestration registerChild)
    (.cons (.orchestration normalInsert)
      (.cons (.orchestration retireOne) (.nil sourceFinal)))

def occurrence
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    AdjacentOccurrence (sourceTrace dynamics inertia) where
  windowStart := Source
  windowEnd := normal
  beforeTrace := .nil Source
  pair := normalPair dynamics inertia
  afterTrace := .cons (.orchestration retireOne) (.nil sourceFinal)
  decomposition := by rfl

def assignedOccurrence
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    AssignedAdjacentOccurrence (occurrence dynamics inertia) where
  beforeAssignment := .nil Source
  firstAssignment := .ofOrchestration registerChild
  secondAssignment := .ofOrchestration normalInsert
  afterAssignment := .cons (.ofOrchestration retireOne) (.nil sourceFinal)

def swap
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    RelatedAssignedAdjacentSwap exactValues (normalPair dynamics inertia) where
  swappedAfter := swapped
  swapped := swappedPair dynamics inertia
  first_detailedRule := by rfl
  second_detailedRule := by rfl
  first_actor := by rfl
  second_actor := by rfl
  endpoints_related := birth_erased_related
  swappedFirstAssignment := .ofOrchestration swappedFirstInsert
  swappedSecondAssignment := .ofOrchestration swappedSecondInsert

theorem source_endpoint_not_swapped_endpoint
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    normal ≠ (swap dynamics inertia).swappedAfter := by
  exact registration_insert_birth_order_differs

theorem source_endpoint_not_current_rule_related
    (dynamics : Dynamics Signature Catalog Ambient) (inertia : InertiaPolicy dynamics) :
    ¬RuleRelated exactValues normal (swap dynamics inertia).swappedAfter := by
  exact birth_order_not_ruleRelated

theorem source_and_swapped_are_paper_related
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    BirthErasedRuleRelated exactValues normal (swap dynamics inertia).swappedAfter := by
  exact birth_erased_related

noncomputable def result
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    RelatedAdjacentRewrite exactValues
      (occurrence dynamics inertia) (swap dynamics inertia) := {
  suffixReplay :=
    (ForwardOrchestrationStepSimulation.ofPaperRelation exactValues dynamics inertia).replayTrace
      normal_wellFormed swapped_wellFormed birth_erased_related
      (.cons retireOne (.nil sourceFinal) (.nil sourceFinal))
}

theorem result_final_related
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    BirthErasedRuleRelated exactValues sourceFinal
      (result dynamics inertia).suffixReplay.result.shadowAfter := by
  exact (result dynamics inertia).final_related

theorem result_final_wellFormed
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    WellFormed (result dynamics inertia).suffixReplay.result.shadowAfter := by
  exact (result dynamics inertia).final_wellFormed

noncomputable def result_assignment
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    TraceProgramAssignment dynamics inertia (result dynamics inertia).trace :=
  (result dynamics inertia).assignment (assignedOccurrence dynamics inertia)

theorem result_assignment_exists
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    Nonempty (TraceProgramAssignment dynamics inertia (result dynamics inertia).trace) :=
  ⟨result_assignment dynamics inertia⟩

theorem result_rules_perm
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    (result dynamics inertia).trace.rules.Perm (sourceTrace dynamics inertia).rules := by
  exact (result dynamics inertia).rules_perm

theorem result_actors_perm
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    (result dynamics inertia).trace.actors.Perm (sourceTrace dynamics inertia).actors := by
  exact (result dynamics inertia).actors_perm

def executableSourceRules : List GlobalCalculus.Rule :=
  [.oInsert, .oInsert, .oRetire]

def executableSourceActors : List Signature.Name := [1, 2, 1]

theorem source_trace_rules
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    (sourceTrace dynamics inertia).rules = executableSourceRules := by
  rfl

theorem source_trace_actors
    (dynamics : Dynamics Signature Catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    (sourceTrace dynamics inertia).actors.map (fun actor => match actor with
      | .fiber name => name) = executableSourceActors := by
  rfl

end BirthGapRewrite

end Cordis.GlobalPaperNonReflexiveRewrite
