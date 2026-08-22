import Cordis.GlobalProgress

/-!
# Conditional quantitative progress

`GlobalProgress` proves a state-local no-deadlock result: under explicit precedence,
readiness, recovery, and provider-soundness authorities, a non-quiescent state has
some applicable lifecycle edge.  That theorem does not by itself bound a trace or
exclude a later cycle.  This module adds the smallest proof-carrying quantitative
layer needed for those conclusions: a supplied strict natural-valued potential.

The `StrictPotential` record is intentionally an authority, not a derived fact about
the current CORDIS calculus.  Given it, every exact finite trace has a telescoping
budget inequality, and an initial budget of `K + 4` gives the corresponding finite
bound.  The lifecycle wrapper applies the generic theorem to the exact dependent
`GlobalLifecycle.Trace`.  The small executable example is a kernel witness for the
arithmetic and is not presented as the paper's full Theorem 66: no target-turn
finiteness, maximal-execution termination, fairness, support, program assignment, or
confluence theorem is claimed here.
-/

set_option autoImplicit false

namespace Cordis.GlobalProgressTermination

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalProgress

universe u v

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

/-! ## Generic exact traces and a strict potential -/

variable {S : Type u}

/-! An endpoint-indexed finite execution for an arbitrary proof-carrying edge. -/
inductive FiniteTrace (edge : S → S → Type v) : S → S → Type (max u v) where
  | nil (state : S) : FiniteTrace edge state state
  | cons {before middle after : S}
      (head : edge before middle)
      (tail : FiniteTrace edge middle after) :
      FiniteTrace edge before after

namespace FiniteTrace

def length {edge : S → S → Type v} {before after : S} :
    FiniteTrace edge before after → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

structure StrictPotential (edge : S → S → Type v) where
  value : S → Nat
  decreases : ∀ {before after}, edge before after → value after < value before

theorem budget
    {edge : S → S → Type v} (potential : StrictPotential edge)
    {before after : S} (trace : FiniteTrace edge before after) :
    trace.length + potential.value after ≤ potential.value before := by
  induction trace with
  | nil => simp [length]
  | cons head tail ih =>
      have edgeDecrease := potential.decreases head
      calc
        (FiniteTrace.cons head tail).length + potential.value _ =
            (tail.length + potential.value _) + 1 := by
              simp [length, Nat.add_assoc, Nat.add_comm]
        _ ≤ potential.value _ + 1 := Nat.add_le_add_right ih 1
        _ ≤ potential.value _ := by
          simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt edgeDecrease

theorem length_le
    {edge : S → S → Type v} (potential : StrictPotential edge)
    {before after : S} (trace : FiniteTrace edge before after) :
    trace.length ≤ potential.value before := by
  have bound := FiniteTrace.budget potential trace
  omega

theorem endpoint_strict_of_nonempty
    {edge : S → S → Type v} (potential : StrictPotential edge)
    {before after : S} (trace : FiniteTrace edge before after)
    (nonempty : 0 < trace.length) :
    potential.value after < potential.value before := by
  have bound := FiniteTrace.budget potential trace
  omega

theorem no_nonempty_cycle
    {edge : S → S → Type v} (potential : StrictPotential edge)
    {state : S} (trace : FiniteTrace edge state state) :
    trace.length = 0 := by
  have bound := FiniteTrace.budget potential trace
  omega

end FiniteTrace

/-! ## A paper-shaped `K + 4` certificate, kept explicitly conditional -/

structure KPlusFourCertificate
    {dynamics : Dynamics sig catalog Ambient}
    (inertia : InertiaPolicy dynamics)
    (initial : Cordis.GlobalLifecycle.State catalog Ambient) (K : Nat) where
  potential : FiniteTrace.StrictPotential
    (fun before after => Transition dynamics inertia before after)
  initial_wellFormed : WellFormed initial
  initial_bound : potential.value initial ≤ K + 4

namespace KPlusFourCertificate

def traceToFinite
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : Cordis.GlobalLifecycle.State catalog Ambient} :
    Trace dynamics inertia before after →
      FiniteTrace (fun left right => Transition dynamics inertia left right) before after
  | .nil state => .nil state
  | .cons head tail => .cons head (traceToFinite tail)

def traceLength
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : Cordis.GlobalLifecycle.State catalog Ambient}
    (trace : Trace dynamics inertia before after) : Nat :=
  (traceToFinite trace).length

theorem trace_budget
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {K : Nat}
    {initial final : Cordis.GlobalLifecycle.State catalog Ambient} (certificate :
      KPlusFourCertificate inertia initial K)
    (trace : Trace dynamics inertia initial final) :
    traceLength trace + certificate.potential.value final ≤
      certificate.potential.value initial := by
  exact FiniteTrace.budget certificate.potential (traceToFinite trace)

theorem trace_length_le_initial
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {K : Nat}
    {initial final : Cordis.GlobalLifecycle.State catalog Ambient} (certificate :
      KPlusFourCertificate inertia initial K)
    (trace : Trace dynamics inertia initial final) :
    traceLength trace ≤ certificate.potential.value initial := by
  exact FiniteTrace.length_le certificate.potential (traceToFinite trace)

theorem trace_length_le_k_plus_four
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {K : Nat}
    {initial final : Cordis.GlobalLifecycle.State catalog Ambient} (certificate :
      KPlusFourCertificate inertia initial K)
    (trace : Trace dynamics inertia initial final) :
    traceLength trace ≤ K + 4 := by
  exact Nat.le_trans (certificate.trace_length_le_initial trace)
    certificate.initial_bound

theorem final_wellFormed
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {K : Nat}
    {initial final : Cordis.GlobalLifecycle.State catalog Ambient} (certificate :
      KPlusFourCertificate inertia initial K)
    (trace : Trace dynamics inertia initial final) : WellFormed final :=
  trace.preservesWellFormed certificate.initial_wellFormed

theorem no_nonempty_cycle
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {K : Nat}
    {initial : Cordis.GlobalLifecycle.State catalog Ambient} (certificate :
      KPlusFourCertificate inertia initial K)
    (trace : Trace dynamics inertia initial initial) :
    traceLength trace = 0 := by
  exact FiniteTrace.no_nonempty_cycle certificate.potential (traceToFinite trace)

end KPlusFourCertificate

/-! ## Executable arithmetic witness -/

namespace Example

inductive State where
  | start
  | middle
  | done
  deriving DecidableEq, Repr

inductive Edge : State → State → Type where
  | startToMiddle : Edge .start .middle
  | middleToDone : Edge .middle .done

def potential : FiniteTrace.StrictPotential Edge where
  value
    | .start => 2
    | .middle => 1
    | .done => 0
  decreases := by
    intro before after edge
    cases edge <;> decide

def trace : FiniteTrace Edge State.start State.done :=
  .cons .startToMiddle (.cons .middleToDone (.nil State.done))

def executableLength : Nat := trace.length

theorem executableLength_eq : executableLength = 2 := by
  simp [executableLength, trace, FiniteTrace.length]

theorem executableBudget : executableLength + potential.value .done ≤
    potential.value .start := by
  exact FiniteTrace.budget potential trace

theorem executableBound : executableLength ≤ 2 := by
  simpa [executableLength, potential] using FiniteTrace.length_le potential trace

theorem executableEndpoint : potential.value .done < potential.value .start := by
  exact FiniteTrace.endpoint_strict_of_nonempty potential trace (by decide)

end Example

end Cordis.GlobalProgressTermination
