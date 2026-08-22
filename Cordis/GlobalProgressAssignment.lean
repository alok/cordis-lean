import Cordis.GlobalProgressRun
import Cordis.GlobalTraceRewrite

/-!
# Trace-wide program assignments for finite progress runs

`GlobalProgressRun` constructs a finite lifecycle trace under a supplied progress authority and
strict potential, but its result intentionally stops at the intrinsic trace.  This module adds the
smallest explicit provenance bridge: callers supply a `StepProgramAssignment` for every lifecycle
transition, and the runner reconstructs the complete `TraceProgramAssignment` one trace constructor
at a time.

The assignment authority is deliberately external.  A raw `Transition` does not determine a fixed
program, root, reachable code, registration oracle, or landing witness.  This module therefore does
not infer any of those facts, and it does not claim trace-wide assignment from `Dynamics`,
`WellFormed`, or `GlobalProgress` alone.  Orchestration steps, if encountered by the generic trace
builder, receive their canonical non-activation assignments automatically.

The resulting certificate is useful to the paper trace-simulation layers: an assigned progress run
can be consumed by `TraceProgramAssignment.headOccurrence`, `GlobalPaperTraceSimulation`, or a
caller-owned lifecycle replay contract without erasing the exact runner endpoint.
-/

set_option autoImplicit false

namespace Cordis.GlobalProgressAssignment

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalProgress Cordis.GlobalProgressRun
open Cordis.GlobalTraceRewrite

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Assignment authority and generic trace reconstruction -/

structure AssignedProgressAuthority
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) extends ProgressAuthority dynamics inertia where
  /-- Fixed-program/oracle provenance for each lifecycle transition selected by the runner. -/
  stepAssignment : ∀ {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after),
    StepProgramAssignment (Step.lifecycle transition)

noncomputable def assignTrace
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    {before after : State catalog Ambient} :
    (trace : GlobalCalculus.Trace dynamics inertia before after) →
      TraceProgramAssignment dynamics inertia trace
  | .nil state => .nil state
  | .cons head tail =>
      match head with
      | .orchestration orchestration =>
          .cons (StepProgramAssignment.ofOrchestration orchestration)
            (assignTrace authority tail)
      | .lifecycle transition =>
          .cons (authority.stepAssignment transition) (assignTrace authority tail)

theorem assignTrace_nil
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    (state : State catalog Ambient) :
    assignTrace authority (.nil state) = .nil state := rfl

theorem assignTrace_orchestration_cons
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    {before middle after : State catalog Ambient}
    (step : OrchestrationStep before middle)
    (tail : GlobalCalculus.Trace dynamics inertia middle after) :
    assignTrace authority (.cons (.orchestration step) tail) =
      .cons (StepProgramAssignment.ofOrchestration step) (assignTrace authority tail) := rfl

theorem assignTrace_lifecycle_cons
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    {before middle after : State catalog Ambient}
    (transition : Transition dynamics inertia before middle)
    (tail : GlobalCalculus.Trace dynamics inertia middle after) :
    assignTrace authority (.cons (.lifecycle transition) tail) =
      .cons (authority.stepAssignment transition) (assignTrace authority tail) := rfl

/-! ## Assigned runner result -/

structure AssignedProgressRunResult
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (fuel : Nat) where
  base : ProgressRunResult dynamics inertia initial fuel
  assignment : TraceProgramAssignment dynamics inertia base.trace

noncomputable def runFuel
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    (fuel : Nat)
    (initial : State catalog Ambient)
    (initialWellFormed : WellFormed initial) :
    AssignedProgressRunResult dynamics inertia initial fuel := by
  let base := GlobalProgressRun.runFuel authority.toProgressAuthority fuel initial initialWellFormed
  exact {
    base := base
    assignment := assignTrace authority base.trace
  }

theorem runFuel_final_wellFormed
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    (fuel : Nat)
    (initial : State catalog Ambient)
    (initialWellFormed : WellFormed initial) :
    WellFormed (runFuel authority fuel initial initialWellFormed).base.final := by
  exact (runFuel authority fuel initial initialWellFormed).base.final_wellFormed

theorem runFuel_length_le
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    (fuel : Nat)
    (initial : State catalog Ambient)
    (initialWellFormed : WellFormed initial) :
    progressTraceLength (runFuel authority fuel initial initialWellFormed).base.trace ≤ fuel := by
  exact (runFuel authority fuel initial initialWellFormed).base.length_le

/-! The standard progress result can always be recovered by projection. -/

def erase
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient} {fuel : Nat}
    (result : AssignedProgressRunResult dynamics inertia initial fuel) :
    ProgressRunResult dynamics inertia initial fuel :=
  result.base

theorem erase_runFuel
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : AssignedProgressAuthority dynamics inertia)
    (fuel : Nat)
    (initial : State catalog Ambient)
    (initialWellFormed : WellFormed initial) :
    erase (runFuel authority fuel initial initialWellFormed) =
      GlobalProgressRun.runFuel authority.toProgressAuthority fuel initial initialWellFormed := rfl

/-! ## Strict-potential assigned certificate -/

structure Certificate
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  authority : AssignedProgressAuthority dynamics inertia
  potential : StepPotential dynamics inertia
  initialWellFormed : WellFormed initial

noncomputable def certifiedRun
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    AssignedProgressRunResult dynamics inertia initial (certificate.potential.value initial) :=
  runFuel certificate.authority (certificate.potential.value initial) initial
    certificate.initialWellFormed

def eraseCertificate
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    GlobalProgressRun.Certificate dynamics inertia initial where
  authority := certificate.authority.toProgressAuthority
  potential := certificate.potential
  initial_wellFormed := certificate.initialWellFormed

theorem certifiedRun_quiescent
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    Quiescent (certifiedRun certificate).base.final := by
  change Quiescent (GlobalProgressRun.certifiedRun (eraseCertificate certificate)).final
  exact GlobalProgressRun.certifiedRun_quiescent (eraseCertificate certificate)

theorem certifiedRun_length_le_initial_potential
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    progressTraceLength (certifiedRun certificate).base.trace ≤
      certificate.potential.value initial := by
  exact (certifiedRun certificate).base.length_le

/-! ## Small executable assignment witness -/

namespace Example

open Cordis.GlobalActivationTransposition.Example.BeginPairs
open Cordis.GlobalProgress.BeginExample

abbrev state := beginOrigin
abbrev dynamics := Cordis.GlobalActivationTransposition.Example.BeginPairs.dynamics
abbrev inertia := Cordis.GlobalActivationTransposition.Example.BeginPairs.inertia

def beginTrace :
    GlobalCalculus.Trace dynamics inertia state beginLeft.after :=
  .cons (.lifecycle explicitTransition) (.nil _)

def beginAssignment : TraceProgramAssignment dynamics inertia beginTrace := by
  exact .cons (StepProgramAssignment.ofActivation beginLeft) (.nil _)

theorem beginAssignment_head_is_activation :
    ∃ occurrence : ProgramOccurrence (.lifecycle explicitTransition),
      occurrence.program.owner = false := by
  exact ⟨beginAssignment.headOccurrence trivial, rfl⟩

def beginProjection : List GlobalCalculus.Rule := beginTrace.rules

theorem beginProjection_eq : beginProjection = [.lBegin] := by
  rfl

end Example

end Cordis.GlobalProgressAssignment
