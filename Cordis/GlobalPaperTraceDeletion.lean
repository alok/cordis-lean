import Cordis.GlobalPaperTraceSimulation

/-!
# Birth-erased assigned deletion replay

This module connects the paper-visible directional deletion theorem to the richer exact trace
surface. `GlobalPaperRelation` already proves a safe orchestration suffix can be replayed after a
finite family of entries has been removed. The present layer packages that replay with its complete
`TraceProgramAssignment`, exact detailed-rule and actor projections, and an executable keep/drop
decision list.

The source trace is intentionally restricted to the safe orchestration language. This is a real
trace-level deletion result, but it is not the paper's closing-episode deletion theorem: lifecycle
suffix transport, registration/retirement provenance, lifetime-indexed no-redraw, normalization,
termination, and confluence remain explicit boundaries.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperTraceDeletion

open Cordis.GlobalRegistry Cordis.GlobalDynamics
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalVestigial Cordis.GlobalDeletion
open Cordis.GlobalRelations Cordis.GlobalPaperRelation Cordis.GlobalPaperTraceSimulation

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Orchestration-only trace evidence -/

def IsOrchestrationStep
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Prop :=
  ∃ orchestration : OrchestrationStep before after, step = .orchestration orchestration

inductive AllOrchestration
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics} :
    {before after : State catalog Ambient} →
      GlobalCalculus.Trace dynamics inertia before after → Prop where
  | nil (state : State catalog Ambient) :
      AllOrchestration (.nil state)
  | cons
      {before middle after : State catalog Ambient}
      (step : OrchestrationStep before middle)
      (tail : GlobalCalculus.Trace dynamics inertia middle after)
      (tailAll : AllOrchestration tail) :
      AllOrchestration (.cons (.orchestration step) tail)

theorem allOrchestration_safe
    {names : List sig.Name}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (safe : SafeNamesOrchestrationTrace names dynamics inertia trace) :
    AllOrchestration trace := by
  induction safe with
  | nil state => exact .nil state
  | cons step tail stepSafe tailSafe ih => exact .cons step tail ih

theorem detailedRule_eq_of_orchestration
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after shadowBefore shadowAfter : State catalog Ambient}
    {shadow : Step dynamics inertia shadowBefore shadowAfter}
    (sourceOrchestration : OrchestrationStep before after)
    (ruleEq : shadow.rule =
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) sourceOrchestration).rule) :
    detailedRule shadow = .orchestration (orchestrationKind sourceOrchestration) := by
  cases sourceOrchestration with
  | insert name fresh parent parentPresent component provisionFresh =>
      cases shadow with
      | orchestration shadowStep =>
          cases shadowStep <;>
            simp_all [detailedRule, orchestrationKind,
              GlobalNameLifecycle.globalRuleOfOrchestrationKind]
      | lifecycle transition => cases transition <;> cases ruleEq
  | retire name fiber present =>
      cases shadow with
      | orchestration shadowStep =>
          cases shadowStep <;>
            simp_all [detailedRule, orchestrationKind,
              GlobalNameLifecycle.globalRuleOfOrchestrationKind]
      | lifecycle transition => cases transition <;> cases ruleEq
  | remove name fiber present retired inactive childless =>
      cases shadow with
      | orchestration shadowStep =>
          cases shadowStep <;>
            simp_all [detailedRule, orchestrationKind,
              GlobalNameLifecycle.globalRuleOfOrchestrationKind]
      | lifecycle transition => cases transition <;> cases ruleEq

theorem replay_detailedRules_eq
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related (fun _ => False) source shadow)
    (sourceAll : AllOrchestration source) :
    detailedRules shadow = detailedRules source := by
  induction replay with
  | nil related => rfl
  | keep related retained tail ih =>
      cases sourceAll with
      | cons sourceOrchestration sourceTail sourceTailAll =>
          simp only [detailedRules]
          rw [detailedRule_eq_of_orchestration sourceOrchestration retained.same_rule]
          exact congrArg
            (List.cons (DetailedRule.orchestration (orchestrationKind sourceOrchestration)))
            (ih sourceTailAll)
  | drop related impossible tail ih =>
      exact False.elim impossible

theorem replay_decisions_allKeep
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related (fun _ => False) source shadow) :
    replay.decisions = List.replicate (GlobalTraceFacts.Trace.records source).length
      ReplayDecision.keep := by
  induction replay with
  | nil related => rfl
  | keep related retained tail ih =>
      simp [DeletionReplay.decisions, GlobalTraceFacts.Trace.records,
        List.replicate_succ, ih]
  | drop related impossible tail ih => exact False.elim impossible

/-! ## Assigned directional deletion result -/

structure AssignedDeletedTraceReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    (family : VestigialNames before names)
    (source : GlobalCalculus.Trace dynamics inertia before after) where
  replay : ForwardDeletedTraceReplay values family source
  sourceAssignment : TraceProgramAssignment dynamics inertia source
  shadowAssignment : TraceProgramAssignment dynamics inertia replay.shadow
  assignment_eq : shadowAssignment = replay.transportAssignment sourceAssignment
  sourceOrchestration : AllOrchestration source
  detailedRules_eq : detailedRules replay.shadow = detailedRules source

noncomputable def replaySafeVestigialTraceAssigned
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (beforeWf : WellFormed before)
    (safe : SafeNamesOrchestrationTrace names dynamics inertia source)
    (sourceAssignment : TraceProgramAssignment dynamics inertia source) :
    AssignedDeletedTraceReplay values family source := by
  let replay := replaySafeVestigialTrace values beforeWf family safe
  let shadowAssignment := replay.transportAssignment sourceAssignment
  have sourceOrchestration := allOrchestration_safe safe
  exact {
    replay := replay
    sourceAssignment := sourceAssignment
    shadowAssignment := shadowAssignment
    assignment_eq := rfl
    sourceOrchestration := sourceOrchestration
    detailedRules_eq := replay_detailedRules_eq replay.certificate sourceOrchestration
  }

namespace AssignedDeletedTraceReplay

theorem final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (replay : AssignedDeletedTraceReplay values family source) :
    DeletionRelated values (fun name => name ∈ names)
      after (removeNames after names) :=
  replay.replay.final_related

theorem rules_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (replay : AssignedDeletedTraceReplay values family source) :
    replay.replay.shadow.rules = source.rules :=
  replay_rules_eq replay.replay.certificate

theorem actors_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (replay : AssignedDeletedTraceReplay values family source) :
    replay.replay.shadow.actors = source.actors :=
  replay_actors_eq replay.replay.certificate

theorem decisions_allKeep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (replay : AssignedDeletedTraceReplay values family source) :
    replay.replay.certificate.decisions =
      List.replicate (GlobalTraceFacts.Trace.records source).length ReplayDecision.keep :=
  replay_decisions_allKeep replay.replay.certificate

end AssignedDeletedTraceReplay

/-! ## Concrete executable projection -/

namespace Example

open Cordis.GlobalPaperRelation.DirectedReplayExample
open Cordis.GlobalDeletion.Positive

abbrev values := Cordis.GlobalPaperRelation.DirectedReplayExample.values

noncomputable def replay :
    AssignedDeletedTraceReplay values family sourceTrace :=
  replaySafeVestigialTraceAssigned values retired_wellFormed namesSafe sourceAssignment

def executableDetailedRules : List DetailedRule := [.orchestration .retire]

def executableActorNames : List Nat := [0]

def executableDecisions : List ReplayDecision := [.keep]

theorem executableDetailedRules_eq :
    detailedRules replay.replay.shadow = executableDetailedRules := by
  calc
    detailedRules replay.replay.shadow = detailedRules sourceTrace := replay.detailedRules_eq
    _ = executableDetailedRules := by
      rfl

theorem executableActorNames_eq :
    replay.replay.shadow.actors.map (fun actor => match actor with
      | .fiber name => name) = executableActorNames := by
  have actorsEq : replay.replay.shadow.actors = sourceTrace.actors :=
    replay_actors_eq replay.replay.certificate
  rw [actorsEq]
  rfl

theorem executableDecisions_eq :
    replay.replay.certificate.decisions = executableDecisions := by
  rfl

end Example

end Cordis.GlobalPaperTraceDeletion
