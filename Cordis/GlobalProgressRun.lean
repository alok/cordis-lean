import Cordis.GlobalProgressTermination

/-!
# Certified finite global progress runs

`GlobalProgress` proves that a well-formed non-quiescent state has some lifecycle
edge when the occurrence-local execution, recovery, precedence, and committed-provider
authorities are supplied. `GlobalProgressTermination` proves a generic strict-potential
bound for an already-given finite trace. This module connects those two facts with an
exact dependent runner.

`ProgressAuthority` supplies the state-local laws again at every well-formed endpoint;
`StepPotential` supplies a strict natural-valued decrease for every exact unified step.
The runner chooses an actual lifecycle transition from `lifecycle_progress`, appends it
to an intrinsic `GlobalCalculus.Trace`, and recursively carries the endpoint proof. With
finite fuel it returns either a quiescent endpoint or a non-quiescent endpoint whose
trace has consumed all fuel. If the fuel is the initial potential, the latter branch is
impossible, so the run is quiescent.

This is a conditional finite progress layer. It does not derive a potential, target-turn
accounting, finite-name freshness, fairness, trace-wide program assignment, maximal
termination, support, confluence, or the paper's unrestricted Theorem 66.
-/

set_option autoImplicit false

namespace Cordis.GlobalProgressRun

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalProgress

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Authorities and exact trace length -/

structure ProgressAuthority
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  laws : ∀ state : State catalog Ambient, WellFormed state →
    LocalProgressLaws dynamics state

structure StepPotential
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  value : State catalog Ambient → Nat
  decreases : ∀ {before after},
    Step dynamics inertia before after → value after < value before

def progressTraceLength
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    GlobalCalculus.Trace dynamics inertia before after → Nat
  | .nil _ => 0
  | .cons _ tail => progressTraceLength tail + 1

theorem traceLength_append
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : GlobalCalculus.Trace dynamics inertia start middle)
    (right : GlobalCalculus.Trace dynamics inertia middle finish) :
    progressTraceLength (GlobalTraceFacts.Trace.append left right) =
      progressTraceLength left + progressTraceLength right := by
  induction left with
  | nil => simp [GlobalTraceFacts.Trace.append, progressTraceLength]
  | cons head tail ih =>
      simp only [GlobalTraceFacts.Trace.append, progressTraceLength]
      rw [ih]
      omega

theorem trace_budget
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (potential : StepPotential dynamics inertia)
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    progressTraceLength trace + potential.value after ≤ potential.value before := by
  induction trace with
  | nil => simp [progressTraceLength]
  | cons head tail ih =>
      have decrease := potential.decreases head
      calc
        progressTraceLength (.cons head tail) + potential.value _ =
            (progressTraceLength tail + potential.value _) + 1 := by
              simp [progressTraceLength, Nat.add_assoc, Nat.add_comm]
        _ ≤ potential.value _ + 1 := Nat.add_le_add_right ih 1
        _ ≤ potential.value _ := by
          simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt decrease

/-! ## The finite dependent runner -/

structure ProgressRunResult
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient)
    (fuel : Nat) where
  final : State catalog Ambient
  trace : GlobalCalculus.Trace dynamics inertia initial final
  final_wellFormed : WellFormed final
  length_le : progressTraceLength trace ≤ fuel
  stop : Quiescent final ∨
    (¬Quiescent final ∧ progressTraceLength trace = fuel)

noncomputable def chooseApplicable
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : ProgressAuthority dynamics inertia)
    {state : State catalog Ambient}
    (wf : WellFormed state)
    (notQuiet : ¬Quiescent state) :
    Sigma fun after => Transition dynamics inertia state after := by
  let applicable := lifecycle_progress (inertia := inertia) wf
    (authority.laws state wf) notQuiet
  let after := Classical.choose applicable
  have witness : Nonempty (Transition dynamics inertia state after) :=
    Classical.choose_spec applicable
  exact ⟨after, Classical.choice witness⟩

noncomputable def runFuel
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (authority : ProgressAuthority dynamics inertia) :
    (fuel : Nat) →
      (initial : State catalog Ambient) →
      WellFormed initial →
      ProgressRunResult dynamics inertia initial fuel
  | 0, initial, wf => by
      by_cases quiet : Quiescent initial
      · exact {
          final := initial
          trace := .nil initial
          final_wellFormed := wf
          length_le := by simp [progressTraceLength]
          stop := Or.inl quiet
        }
      · exact {
          final := initial
          trace := .nil initial
          final_wellFormed := wf
          length_le := by simp [progressTraceLength]
          stop := Or.inr ⟨quiet, rfl⟩
        }
  | fuel + 1, initial, wf => by
      by_cases quiet : Quiescent initial
      · exact {
          final := initial
          trace := .nil initial
          final_wellFormed := wf
          length_le := by simp [progressTraceLength]
          stop := Or.inl quiet
        }
      · let chosen := chooseApplicable authority wf quiet
        let nextWf := chosen.2.preservesWellFormed wf
        let tail := runFuel authority fuel chosen.1 nextWf
        exact {
          final := tail.final
          trace := .cons (.lifecycle chosen.2) tail.trace
          final_wellFormed := tail.final_wellFormed
          length_le := by
            change progressTraceLength tail.trace + 1 ≤ fuel + 1
            exact Nat.add_le_add_right tail.length_le 1
          stop := by
            cases tail.stop with
            | inl tailQuiet => exact Or.inl tailQuiet
            | inr tailExhausted =>
                exact Or.inr ⟨tailExhausted.1, by
                  change progressTraceLength tail.trace + 1 = fuel + 1
                  rw [tailExhausted.2]
                ⟩
        }

/-! ## Strict-potential completion -/

structure Certificate
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (initial : State catalog Ambient) where
  authority : ProgressAuthority dynamics inertia
  potential : StepPotential dynamics inertia
  initial_wellFormed : WellFormed initial

noncomputable def certifiedRun
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    ProgressRunResult dynamics inertia initial (certificate.potential.value initial) :=
  runFuel certificate.authority (certificate.potential.value initial) initial
    certificate.initial_wellFormed

theorem certifiedRun_quiescent
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    Quiescent (certifiedRun certificate).final := by
  let result := certifiedRun certificate
  cases result.stop with
  | inl quiet => exact quiet
  | inr exhausted =>
      have budget := trace_budget certificate.potential result.trace
      have finalZero : certificate.potential.value result.final = 0 := by
        omega
      have applicable := lifecycle_progress (inertia := inertia) result.final_wellFormed
        (certificate.authority.laws result.final result.final_wellFormed)
        exhausted.1
      obtain ⟨after, ⟨transition⟩⟩ := applicable
      have decrease := certificate.potential.decreases (.lifecycle transition)
      have impossible := decrease
      simp [finalZero] at impossible

theorem certifiedRun_length_le_initial_potential
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {initial : State catalog Ambient}
    (certificate : Certificate dynamics inertia initial) :
    progressTraceLength (certifiedRun certificate).trace ≤
      certificate.potential.value initial :=
  (certifiedRun certificate).length_le

/-! ## An explicit zero-fuel boundary witness -/

namespace Example

open Cordis.GlobalActivationTransposition.Example.BeginPairs

abbrev state := beginOrigin
abbrev dynamics := Cordis.GlobalActivationTransposition.Example.BeginPairs.dynamics
abbrev inertia := Cordis.GlobalActivationTransposition.Example.BeginPairs.inertia

def zeroFuelResult :
    ProgressRunResult dynamics inertia state 0 := {
  final := state
  trace := .nil state
  final_wellFormed :=
    Cordis.GlobalActivationTransposition.Example.BeginPairs.beginOrigin_wellFormed
  length_le := by simp [progressTraceLength]
  stop := Or.inr ⟨Cordis.GlobalProgress.BeginExample.not_quiescent, rfl⟩
}

theorem zeroFuelResult_length : progressTraceLength zeroFuelResult.trace = 0 := by
  rfl

theorem zeroFuelResult_not_quiescent : ¬Quiescent zeroFuelResult.final := by
  cases zeroFuelResult.stop with
  | inl quiet => exact False.elim (Cordis.GlobalProgress.BeginExample.not_quiescent quiet)
  | inr exhausted => exact exhausted.1

end Example

end Cordis.GlobalProgressRun
