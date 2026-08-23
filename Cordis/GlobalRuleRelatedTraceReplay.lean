import Cordis.GlobalPaperFullLifecycleReplay

/-!
# Exact `RuleRelated` trace replay with dependent assignments

`GlobalPaperTraceSimulation` supplies a finite all-keep replay for the birth-erased relation. This
module adds the corresponding exact bridge for the stricter `GlobalRelations.RuleRelated` relation.
The local match certificate is deliberately explicit: it carries the matched endpoint, exact rule
and actor equations, endpoint well-formedness, successor `RuleRelated`, and transport of the
dependent `StepProgramAssignment`. Consequently the trace theorem is a genuine construction from
occurrence-indexed local evidence, not an inference that arbitrary lifecycle dynamics respect the
paper relation.

The reflexive instance is unconditional and gives an executable smoke witness. A non-reflexive
caller must provide the local matching certificate (or an equivalent external bisimulation plus
assignment transport). This module does not claim paper Lemmas 55, 71, 72, or Theorem 73, and it
does not erase allocator birth/clock fields.
-/

set_option autoImplicit false

namespace Cordis.GlobalRuleRelatedTraceReplay

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation Cordis.GlobalDeletion
open Cordis.GlobalPaperFullLifecycleReplay

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Exact local matches -/

structure ForwardStepMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  matched : Step dynamics inertia shadowBefore shadowAfter
  same_rule : matched.rule = source.rule
  same_actor : matched.actor = source.actor
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed shadowAfter
  successors_related : RuleRelated values sourceAfter shadowAfter
  transportAssignment : StepProgramAssignment source -> StepProgramAssignment matched

def ForwardStepMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    {source : Step dynamics inertia sourceBefore sourceAfter}
    (matched : ForwardStepMatch values (shadowBefore := shadowBefore) source) :
    RetainedStep (shadowBefore := shadowBefore) source where
  shadowAfter := matched.shadowAfter
  replay := matched.matched
  same_rule := matched.same_rule
  same_actor := matched.same_actor
  transportAssignment := matched.transportAssignment

structure BackwardStepMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  matched : Step dynamics inertia shadowBefore shadowAfter
  same_rule : matched.rule = source.rule
  same_actor : matched.actor = source.actor
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed shadowAfter
  successors_related : RuleRelated values shadowAfter sourceAfter
  transportAssignment : StepProgramAssignment source -> StepProgramAssignment matched

def BackwardStepMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    {source : Step dynamics inertia sourceBefore sourceAfter}
    (matched : BackwardStepMatch values (shadowBefore := shadowBefore) source) :
    RetainedStep (shadowBefore := shadowBefore) source where
  shadowAfter := matched.shadowAfter
  replay := matched.matched
  same_rule := matched.same_rule
  same_actor := matched.same_actor
  transportAssignment := matched.transportAssignment

structure StepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : forall {sourceBefore shadowBefore sourceAfter : State catalog Ambient},
    WellFormed sourceBefore ->
    WellFormed shadowBefore ->
    RuleRelated values sourceBefore shadowBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      ForwardStepMatch values (shadowBefore := shadowBefore) source
  backward : forall {shadowBefore sourceBefore sourceAfter : State catalog Ambient},
    WellFormed shadowBefore ->
    WellFormed sourceBefore ->
    RuleRelated values shadowBefore sourceBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      BackwardStepMatch values (shadowBefore := shadowBefore) source

/-! ## The exact all-keep trace package -/

structure TraceReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter : State catalog Ambient}
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (shadowBefore : State catalog Ambient) where
  result :
    DeletionResult (RuleRelated values) (fun _ => False) source shadowBefore
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed result.shadowAfter

noncomputable def StepSimulation.replay
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (simulation : StepSimulation values dynamics inertia)
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore)
    (shadowWf : WellFormed shadowBefore)
    (related : RuleRelated values sourceBefore shadowBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceReplay values source shadowBefore := by
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
      }
  | @cons sourceBefore sourceMiddle sourceAfter head tail ih =>
      cases assignment with
      | cons headAssignment tailAssignment =>
          let headMatch := simulation.forward sourceWf shadowWf related head
          let tailReplay := ih headMatch.sourceAfter_wellFormed
            headMatch.shadowAfter_wellFormed headMatch.successors_related tailAssignment
          exact {
            result := {
              shadowAfter := tailReplay.result.shadowAfter
              shadow := .cons headMatch.matched tailReplay.result.shadow
              certificate := .keep related headMatch.toRetainedStep
                tailReplay.result.certificate
            }
            sourceAfter_wellFormed := tailReplay.sourceAfter_wellFormed
            shadowAfter_wellFormed := tailReplay.shadowAfter_wellFormed
          }

namespace TraceReplay

theorem final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : TraceReplay values source shadowBefore) :
    RuleRelated values sourceAfter replay.result.shadowAfter :=
  replay.result.certificate.final_related

noncomputable def transportAssignment
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : TraceReplay values source shadowBefore)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceProgramAssignment dynamics inertia replay.result.shadow :=
  replay.result.certificate.transportAssignment assignment

theorem rules_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : TraceReplay values source shadowBefore) :
    replay.result.shadow.rules = source.rules := by
  exact Cordis.GlobalPaperTraceSimulation.replay_rules_eq replay.result.certificate

theorem actors_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : TraceReplay values source shadowBefore) :
    replay.result.shadow.actors = source.actors := by
  exact Cordis.GlobalPaperTraceSimulation.replay_actors_eq replay.result.certificate

theorem final_birthErased_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    (replay : TraceReplay values source shadowBefore) :
    BirthErasedRuleRelated values sourceAfter replay.result.shadowAfter :=
  birthErased_of_ruleRelated replay.final_related

end TraceReplay

/-! ## Diagonal witness and the existing complete-path smoke trace -/

noncomputable def diagonalReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter : State catalog Ambient}
    (sourceWf : WellFormed sourceBefore)
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceReplay values source sourceBefore := by
  induction source with
  | nil sourceBefore =>
      exact {
        result := {
          shadowAfter := sourceBefore
          shadow := .nil sourceBefore
          certificate := .nil (ruleRelated_refl values sourceBefore)
        }
        sourceAfter_wellFormed := sourceWf
        shadowAfter_wellFormed := sourceWf
      }
  | @cons sourceBefore sourceMiddle sourceAfter head tail ih =>
      cases assignment with
      | cons headAssignment tailAssignment =>
          let headWf := head.preservesWellFormed sourceWf
          let tailReplay := ih headWf tailAssignment
          exact {
            result := {
              shadowAfter := tailReplay.result.shadowAfter
              shadow := .cons head tailReplay.result.shadow
              certificate := .keep (ruleRelated_refl values sourceBefore)
                {
                  shadowAfter := sourceMiddle
                  replay := head
                  same_rule := rfl
                  same_actor := rfl
                  transportAssignment := id
                }
                tailReplay.result.certificate
            }
            sourceAfter_wellFormed := tailReplay.sourceAfter_wellFormed
            shadowAfter_wellFormed := tailReplay.shadowAfter_wellFormed
          }

namespace Example

abbrev values := GlobalPaperFullLifecycleReplay.Example.values
abbrev dynamics := GlobalPaperFullLifecycleReplay.Example.dynamics
abbrev inertia := GlobalPaperFullLifecycleReplay.Example.inertia
abbrev state := GlobalPaperFullLifecycleReplay.Example.state
abbrev source := GlobalPaperFullLifecycleReplay.Example.fullTrace
abbrev assignment := GlobalPaperFullLifecycleReplay.Example.fullAssignment
abbrev start := GlobalPaperFullLifecycleReplay.Example.start

noncomputable def reflexiveReplay :
    TraceReplay values source start :=
  diagonalReplay values Cordis.GlobalLifecycle.Example.start_wellFormed source assignment

theorem reflexive_final_related :
    RuleRelated values GlobalPaperFullLifecycleReplay.Example.unloadedState
      reflexiveReplay.result.shadowAfter :=
  reflexiveReplay.final_related

theorem reflexive_rules : reflexiveReplay.result.shadow.rules = source.rules :=
  reflexiveReplay.rules_eq

theorem reflexive_actors : reflexiveReplay.result.shadow.actors = source.actors :=
  reflexiveReplay.actors_eq

noncomputable def reflexiveAssignment :
    TraceProgramAssignment dynamics inertia reflexiveReplay.result.shadow :=
  reflexiveReplay.transportAssignment assignment

theorem reflexive_assignment_exists : Nonempty (TraceProgramAssignment dynamics inertia
    reflexiveReplay.result.shadow) :=
  ⟨reflexiveAssignment⟩

def executableSummary : List String := [
  "exact-rule-related-replay",
  "six-step-assignment-preserving-diagonal",
  "rule-related-final-endpoint",
  "dependent-assignment-transport"
]

end Example

end Cordis.GlobalRuleRelatedTraceReplay
