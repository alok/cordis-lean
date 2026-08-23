import Cordis.GlobalPaperTraceSimulation
import Cordis.GlobalActivationTransposition

/-!
# Assigned birth-erased landing transposition

This module connects the concrete fixed-program Iter/Finish landing diamond to the
birth-erased assigned trace layer.  The source and shadow windows are exact dependent
`GlobalCalculus.Trace` values with one Iter and one Finish occurrence in opposite order;
their `TraceProgramAssignment`s are reconstructed from the actual program activations,
not inferred from rule tags.  The endpoint is exact in this witness, so the relation
certificate is reflexive, while the rule and actor ledgers are proved to be swapped.

This is a positive trace-local landing witness.  It does not derive the global lifecycle
simulation frontier, episode provenance, or paper Lemma 71/72/Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperLandingReplay

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceRewrite
open Cordis.GlobalActivationTransposition
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceSimulation

namespace Example

namespace LandingPair

abbrev dynamics := Cordis.GlobalActivationTransposition.Example.LandingPair.dynamics
abbrev inertia := Cordis.GlobalActivationTransposition.Example.LandingPair.inertia
abbrev leftProgram := Cordis.GlobalActivationTransposition.Example.LandingPair.leftProgram
abbrev rightProgram := Cordis.GlobalActivationTransposition.Example.LandingPair.rightProgram
abbrev origin := Cordis.GlobalActivationTransposition.Example.LandingPair.origin
abbrev left := Cordis.GlobalActivationTransposition.Example.LandingPair.left
abbrev right := Cordis.GlobalActivationTransposition.Example.LandingPair.right
abbrev laws := Cordis.GlobalActivationTransposition.Example.LandingPair.laws
noncomputable abbrev diamond := Cordis.GlobalActivationTransposition.Example.LandingPair.diamond

noncomputable def values : ValueSetoids Cordis.GlobalLandingTransposition.Example.Signature where
  relation _ := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

noncomputable def normalPair : StepPair dynamics inertia origin
    diamond.rightAfterLeft.after where
  middle := left.after
  first := ProgramActivation.globalStep (inertia := inertia) left
  second := ProgramActivation.globalStep (inertia := inertia) diamond.rightAfterLeft

noncomputable def leftOccurrence : ProgramOccurrence normalPair.first :=
  ProgramOccurrence.ofActivation left

noncomputable def rightOccurrence : ProgramOccurrence normalPair.second :=
  ProgramOccurrence.ofActivation diamond.rightAfterLeft

noncomputable def assignedSwap : AssignedAdjacentSwap normalPair := by
  exact transposeActivationPair normalPair leftOccurrence rightOccurrence right
    Cordis.GlobalLandingTransposition.Example.origin_wellFormed (by decide) laws

noncomputable def sourceTrace : Cordis.GlobalCalculus.Trace dynamics inertia origin
    diamond.rightAfterLeft.after := normalPair.trace

noncomputable def occurrence : AdjacentOccurrence sourceTrace where
  windowStart := origin
  windowEnd := diamond.rightAfterLeft.after
  beforeTrace := .nil origin
  pair := normalPair
  afterTrace := .nil diamond.rightAfterLeft.after
  decomposition := rfl

noncomputable def assignedOccurrence : AssignedAdjacentOccurrence occurrence where
  beforeAssignment := .nil origin
  firstAssignment := StepProgramAssignment.ofActivation left
  secondAssignment := StepProgramAssignment.ofActivation diamond.rightAfterLeft
  afterAssignment := .nil diamond.rightAfterLeft.after

private theorem detailedRule_lIter
    {before after : GlobalRegistry.GlobalState
      Cordis.GlobalLandingTransposition.Example.exampleCatalog Bool}
    (step : GlobalCalculus.Step dynamics inertia before after)
    (h : step.rule = GlobalCalculus.Rule.lIter) :
    detailedRule step = DetailedRule.lifecycle GlobalLifecycle.Rule.iter := by
  cases step with
  | orchestration step =>
      cases step <;> cases h
  | lifecycle transition =>
      have h' : Cordis.GlobalNameLifecycle.globalRuleOfLifecycleRule transition.rule =
          GlobalCalculus.Rule.lIter := by
        simpa using h
      cases transition <;>
        simp_all [Cordis.GlobalNameLifecycle.globalRuleOfLifecycleRule,
          GlobalLifecycle.Transition.rule, detailedRule]

private theorem detailedRule_lFinish
    {before after : GlobalRegistry.GlobalState
      Cordis.GlobalLandingTransposition.Example.exampleCatalog Bool}
    (step : GlobalCalculus.Step dynamics inertia before after)
    (h : step.rule = GlobalCalculus.Rule.lFinish) :
    detailedRule step = DetailedRule.lifecycle GlobalLifecycle.Rule.finish := by
  cases step with
  | orchestration step =>
      cases step <;> cases h
  | lifecycle transition =>
      have h' : Cordis.GlobalNameLifecycle.globalRuleOfLifecycleRule transition.rule =
          GlobalCalculus.Rule.lFinish := by
        simpa using h
      cases transition <;>
        simp_all [Cordis.GlobalNameLifecycle.globalRuleOfLifecycleRule,
          GlobalLifecycle.Transition.rule, detailedRule]

noncomputable def relatedSwap : RelatedAssignedAdjacentSwap values normalPair :=
  RelatedAssignedAdjacentSwap.ofExact assignedSwap
    (by
      calc
        detailedRule assignedSwap.swapped.first = DetailedRule.lifecycle .finish :=
          detailedRule_lFinish assignedSwap.swapped.first (by
            rw [assignedSwap.first_rule]
            rfl)
        _ = detailedRule normalPair.second := by rfl)
    (by
      calc
        detailedRule assignedSwap.swapped.second = DetailedRule.lifecycle .iter :=
          detailedRule_lIter assignedSwap.swapped.second (by
            rw [assignedSwap.second_rule]
            rfl)
        _ = detailedRule normalPair.first := by rfl)

noncomputable def rewritten : RelatedAdjacentRewrite values occurrence relatedSwap where
  suffixReplay := {
    result := {
      shadowAfter := diamond.rightAfterLeft.after
      shadow := .nil diamond.rightAfterLeft.after
      certificate := .nil
        (birthErasedRuleRelated_refl values diamond.rightAfterLeft.after)
    }
    sourceAfter_wellFormed := by
      have leftWf : WellFormed left.after :=
        (ProgramActivation.globalStep (inertia := inertia) left).preservesWellFormed
          Cordis.GlobalLandingTransposition.Example.origin_wellFormed
      exact (ProgramActivation.globalStep (inertia := inertia)
        diamond.rightAfterLeft).preservesWellFormed leftWf
    shadowAfter_wellFormed := by
      have leftWf : WellFormed left.after :=
        (ProgramActivation.globalStep (inertia := inertia) left).preservesWellFormed
          Cordis.GlobalLandingTransposition.Example.origin_wellFormed
      exact (ProgramActivation.globalStep (inertia := inertia)
        diamond.rightAfterLeft).preservesWellFormed leftWf
    detailedRules_eq := rfl
  }

noncomputable def rewrittenAssignment :
    TraceProgramAssignment dynamics inertia rewritten.trace :=
  RelatedAdjacentRewrite.assignment assignedOccurrence rewritten

theorem source_rules : sourceTrace.rules = [GlobalCalculus.Rule.lIter, .lFinish] := by
  rfl

theorem rewritten_rules : rewritten.trace.rules = [.lFinish, .lIter] := by
  change [relatedSwap.swapped.first.rule, relatedSwap.swapped.second.rule] =
    [GlobalCalculus.Rule.lFinish, .lIter]
  rw [RelatedAssignedAdjacentSwap.first_rule relatedSwap,
    RelatedAssignedAdjacentSwap.second_rule relatedSwap]
  rfl

theorem source_actors : sourceTrace.actors =
    [GlobalCalculus.Actor.fiber false, .fiber true] := by
  rfl

theorem rewritten_actors : rewritten.trace.actors =
    [GlobalCalculus.Actor.fiber true, .fiber false] := by
  change [relatedSwap.swapped.first.actor, relatedSwap.swapped.second.actor] =
    [GlobalCalculus.Actor.fiber true, .fiber false]
  rw [relatedSwap.first_actor, relatedSwap.second_actor]
  rfl

theorem endpoint_related :
    BirthErasedRuleRelated values diamond.rightAfterLeft.after
      rewritten.suffixReplay.result.shadowAfter :=
  RelatedAdjacentRewrite.final_related rewritten

theorem endpoint_wellFormed :
    WellFormed rewritten.suffixReplay.result.shadowAfter :=
  RelatedAdjacentRewrite.final_wellFormed rewritten

theorem assignment_exact :
    rewrittenAssignment = RelatedAdjacentRewrite.assignment assignedOccurrence rewritten :=
  rfl

def executableSummary : Prop :=
  sourceTrace.rules = [GlobalCalculus.Rule.lIter, .lFinish] ∧
    rewritten.trace.rules = [GlobalCalculus.Rule.lFinish, .lIter] ∧
    sourceTrace.actors = [GlobalCalculus.Actor.fiber false, .fiber true] ∧
    rewritten.trace.actors = [GlobalCalculus.Actor.fiber true, .fiber false]

theorem executable_summary : executableSummary := by
  exact ⟨source_rules, rewritten_rules, source_actors, rewritten_actors⟩

end LandingPair

end Example

end Cordis.GlobalPaperLandingReplay
