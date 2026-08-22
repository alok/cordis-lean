import Cordis.GlobalProgressAssignment
import Cordis.GlobalPaperTraceSimulation

/-!
# Assigned progress-run paper replay

This module composes the finite progress runner's explicit program-assignment certificate with
the birth-erased assigned-trace simulator.  The runner owns the source trace, endpoint, stop
reason, and assignment; the simulator owns the relation-aware peer replay.  Keeping those roles
separate avoids inferring lifecycle provenance from `Dynamics` while still exposing one package a
caller can carry through a paper-visible replay.

The result is conditional: a `ForwardAssignedStepSimulation` is still supplied by the caller.
This is not a lifecycle bisimulation theorem, and it does not turn a progress authority into a
normalizer, maximal execution, or deployed-runtime equivalence.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperProgressReplay

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalProgressRun Cordis.GlobalProgressAssignment
open Cordis.GlobalTraceRewrite
open Cordis.GlobalRelations Cordis.GlobalPaperRelation
open Cordis.GlobalPaperTraceSimulation

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

structure ReplayedProgressRun
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    (run : AssignedProgressRunResult dynamics inertia initial fuel)
    (shadow : State catalog Ambient) where
  replay : ForwardPaperTraceReplay values run.base.trace shadow
  sourceAssignment : TraceProgramAssignment dynamics inertia run.base.trace := run.assignment
  shadowAssignment : TraceProgramAssignment dynamics inertia replay.result.shadow :=
    replay.result.certificate.transportAssignment sourceAssignment
  assignment_eq : shadowAssignment =
    replay.result.certificate.transportAssignment sourceAssignment

noncomputable def replayRun
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    (run : AssignedProgressRunResult dynamics inertia initial fuel)
    (simulation : ForwardAssignedStepSimulation values dynamics inertia)
    (initialWellFormed : WellFormed initial)
    {shadow : State catalog Ambient}
    (shadowWellFormed : WellFormed shadow)
    (related : BirthErasedRuleRelated values initial shadow) :
    ReplayedProgressRun values run shadow := by
  let replay := simulation.replayTrace initialWellFormed shadowWellFormed related run.base.trace
  exact {
    replay := replay
    sourceAssignment := run.assignment
    shadowAssignment := replay.result.certificate.transportAssignment run.assignment
    assignment_eq := rfl
  }

namespace ReplayedProgressRun

theorem source_endpoint_wellFormed
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (_result : ReplayedProgressRun values run shadow) :
    WellFormed run.base.final :=
  run.base.final_wellFormed

theorem source_length_le
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (_result : ReplayedProgressRun values run shadow) :
    progressTraceLength run.base.trace ≤ fuel :=
  run.base.length_le

theorem source_stop
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (_result : ReplayedProgressRun values run shadow) :
    Quiescent run.base.final ∨
      (¬Quiescent run.base.final ∧ progressTraceLength run.base.trace = fuel) :=
  run.base.stop

theorem shadow_endpoint_wellFormed
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (result : ReplayedProgressRun values run shadow) :
    WellFormed result.replay.result.shadowAfter :=
  result.replay.shadowAfter_wellFormed

theorem final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (result : ReplayedProgressRun values run shadow) :
    BirthErasedRuleRelated values run.base.final result.replay.result.shadowAfter :=
  result.replay.final_related

theorem assignment_transport_exact
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (result : ReplayedProgressRun values run shadow) :
    result.shadowAssignment =
      result.replay.result.certificate.transportAssignment result.sourceAssignment := by
  exact result.assignment_eq

theorem detailed_rules_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (result : ReplayedProgressRun values run shadow) :
    detailedRules result.replay.result.shadow = detailedRules run.base.trace :=
  result.replay.detailedRules_eq

theorem rules_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (result : ReplayedProgressRun values run shadow) :
    result.replay.result.shadow.rules = run.base.trace.rules :=
  result.replay.rules_eq

theorem actors_eq
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    {fuel : Nat}
    {run : AssignedProgressRunResult dynamics inertia initial fuel}
    {shadow : State catalog Ambient}
    (result : ReplayedProgressRun values run shadow) :
    result.replay.result.shadow.actors = run.base.trace.actors :=
  result.replay.actors_eq

end ReplayedProgressRun

/-! ## Executable zero-fuel bridge -/

namespace Example

abbrev Signature := Cordis.GlobalActivationTransposition.Example.BeginPairs.Signature
abbrev dynamics := Cordis.GlobalProgressRun.Example.dynamics
abbrev inertia := Cordis.GlobalProgressRun.Example.inertia
abbrev state := Cordis.GlobalProgressRun.Example.state

def values : ValueSetoids Signature where
  relation _ := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

def assignedZero : AssignedProgressRunResult dynamics inertia state 0 where
  base := Cordis.GlobalProgressRun.Example.zeroFuelResult
  assignment := .nil state

def zeroReplay : ForwardPaperTraceReplay values assignedZero.base.trace state where
  result := {
    shadowAfter := state
    shadow := .nil state
    certificate := .nil (birthErasedRuleRelated_refl values state)
  }
  sourceAfter_wellFormed := Cordis.GlobalProgressRun.Example.zeroFuelResult.final_wellFormed
  shadowAfter_wellFormed := Cordis.GlobalProgressRun.Example.zeroFuelResult.final_wellFormed
  detailedRules_eq := rfl

noncomputable def replayed : ReplayedProgressRun values assignedZero state where
  replay := zeroReplay
  sourceAssignment := assignedZero.assignment
  shadowAssignment := zeroReplay.result.certificate.transportAssignment assignedZero.assignment
  assignment_eq := rfl

theorem executable_fuel : progressTraceLength assignedZero.base.trace = 0 := by
  rfl

theorem executable_stop :
    ¬Quiescent assignedZero.base.final ∧ progressTraceLength assignedZero.base.trace = 0 := by
  exact ⟨Cordis.GlobalProgressRun.Example.zeroFuelResult_not_quiescent,
    Cordis.GlobalProgressRun.Example.zeroFuelResult_length⟩

theorem executable_replay_related :
    BirthErasedRuleRelated values assignedZero.base.final replayed.replay.result.shadowAfter :=
  replayed.final_related

theorem executable_assignment :
    replayed.shadowAssignment =
      replayed.replay.result.certificate.transportAssignment replayed.sourceAssignment :=
  replayed.assignment_transport_exact

end Example

end Cordis.GlobalPaperProgressReplay
