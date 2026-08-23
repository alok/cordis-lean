import Cordis.DeepSeekExternalGenericRound

/-!
# Finite proof-carrying external conversations

`DeepSeekExternalGenericRound` proves one process-backed dispatch.  This module lifts that
boundary to a finite, dependent script: a later round may be chosen from the exact accepted
runner state and the proof-carrying dispatch produced by an earlier round.  The script is
fuel-indexed, so exhaustion is represented rather than silently treated as success.

`RoundPlan` contains a heterogeneous `ToolSpec`, and therefore lives above the executable
`IO` universe.  The returned `Trace` deliberately erases those heterogeneous payloads from
data while retaining an existential `external` certificate in `Prop` for every edge.  This is
the API boundary: a caller can prove that each edge came from a configured observation and
accepted dispatch, while the executable result remains usable by `IO` and downstream tests.

The module does not claim process identity, sandboxing, authentication, exactly-once effects,
cleanup, persistence, provider obedience, or deployed DeepSeek Harness equivalence.  A failed
or uncertified process is retained as an explicit stop classification.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekExternalGenericConversation

open Cordis
open Cordis.GenericHarness
open Cordis.DeepSeekExternalToolProcess
open Cordis.DeepSeekExternalGenericRound

universe u

/-! ## Dependent scripts -/

structure RoundPlan
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    (state : GenericHarness.Runner cfg (.step turn step [])) where
  spec : ToolSpec Model Capability
  binding : ProcessBinding spec
  invocation : ToolSpec.Invocation spec
  certify : ∀ observed : ObservedResult binding invocation,
    observed.process.exitCode = 0 → Option (ObservedDispatch state observed)

/-- A finite script.  Its continuation receives the exact accepted observation and dispatch. -/
inductive Script
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat} :
    (state : GenericHarness.Runner cfg (.step turn step [])) → Type (u + 2) where
  | stop {state : GenericHarness.Runner cfg (.step turn step [])}
      (plan : RoundPlan state) : Script state
  | continue {state : GenericHarness.Runner cfg (.step turn step [])}
      (plan : RoundPlan state)
      (next : ∀ (observed : ObservedResult plan.binding plan.invocation),
        ∀ (dispatch : ObservedDispatch state observed),
        Script dispatch.result.runnerResult.runner) : Script state

/-! ## Executable trace with proof-only heterogeneous provenance -/

/-- One accepted external edge, with its heterogeneous source retained only in `Prop`. -/
structure ExternalStep
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    (before after : GenericHarness.Runner cfg (.step turn step [])) where
  result : GenericHarness.Runner.DispatchResult before
  result_eq : result.runner = after
  external :
    ∃ (spec : ToolSpec Model Capability)
      (binding : ProcessBinding spec)
      (invocation : ToolSpec.Invocation spec)
      (observed : ObservedResult binding invocation),
        ∃ dispatch : ObservedDispatch before observed,
          dispatch.result.runnerResult = result

def ExternalStep.ofObserved
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    {state : GenericHarness.Runner cfg (.step turn step [])}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (dispatch : ObservedDispatch state observed) :
    ExternalStep state dispatch.result.runnerResult.runner where
  result := dispatch.result.runnerResult
  result_eq := rfl
  external := ⟨spec, binding, invocation, observed, dispatch, rfl⟩

inductive Trace
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat} :
    (initial : GenericHarness.Runner cfg (.step turn step [])) →
    (final : GenericHarness.Runner cfg (.step turn step [])) → Type u where
  | nil (state : GenericHarness.Runner cfg (.step turn step [])) : Trace state state
  | cons
      {initial middle final : GenericHarness.Runner cfg (.step turn step [])}
      (head : ExternalStep initial middle)
      (tail : Trace middle final) :
      Trace initial final

namespace Trace

def length
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    {initial final : GenericHarness.Runner cfg (.step turn step [])} :
    Trace initial final → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

theorem length_cons
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    {initial middle final : GenericHarness.Runner cfg (.step turn step [])}
    (head : ExternalStep initial middle)
    (tail : Trace middle final) :
    length (.cons head tail) = length tail + 1 :=
  rfl

end Trace

/-! ## Stopping and execution -/

inductive StopKind where
  | completed
  | fuelExhausted
  | uncertified
deriving DecidableEq, Repr

structure RunResult
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    (initial final : GenericHarness.Runner cfg (.step turn step [])) where
  trace : Trace initial final
  stop : StopKind
  stopProcess : Option ProcessObservation

def runAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    (fuel : Nat)
    {state : GenericHarness.Runner cfg (.step turn step [])}
    (script : Script state) :
    IO (Except ObservationError
      (Sigma fun final : GenericHarness.Runner cfg (.step turn step []) =>
        RunResult state final)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨state, {
        trace := .nil state
        stop := .fuelExhausted
        stopProcess := none
      }⟩)
  | fuel + 1 =>
      match script with
      | .stop plan =>
          match ← observeAndDispatch state
              (binding := plan.binding) (invocation := plan.invocation)
              plan.certify with
          | .error error => pure (.error error)
          | .ok ⟨observed, none⟩ =>
              pure (.ok ⟨state, {
                trace := .nil state
                stop := .uncertified
                stopProcess := some observed.process
              }⟩)
          | .ok ⟨_, some dispatch⟩ =>
              let head := ExternalStep.ofObserved dispatch
              pure (.ok ⟨dispatch.result.runnerResult.runner, {
                trace := .cons head (.nil dispatch.result.runnerResult.runner)
                stop := .completed
                stopProcess := none
              }⟩)
      | .continue plan next =>
          match ← observeAndDispatch state
              (binding := plan.binding) (invocation := plan.invocation)
              plan.certify with
          | .error error => pure (.error error)
          | .ok ⟨observed, none⟩ =>
              pure (.ok ⟨state, {
                trace := .nil state
                stop := .uncertified
                stopProcess := some observed.process
              }⟩)
          | .ok ⟨observed, some dispatch⟩ =>
              let head := ExternalStep.ofObserved dispatch
              match ← runAux fuel (next observed dispatch) with
              | .error error => pure (.error error)
              | .ok ⟨final, tail⟩ =>
                  pure (.ok ⟨final, {
                    trace := .cons head tail.trace
                    stop := tail.stop
                    stopProcess := tail.stopProcess
                  }⟩)
termination_by fuel

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {turn step : Nat}
    (fuel : Nat)
    {state : GenericHarness.Runner cfg (.step turn step [])}
    (script : Script state) :
    IO (Except ObservationError
      (Sigma fun final : GenericHarness.Runner cfg (.step turn step []) =>
        RunResult state final)) :=
  runAux fuel script

/-! ## Concrete two-round fixtures -/

def counterReadStopPlan : RoundPlan DeepSeekExternalGenericRound.counterReadRunner where
  spec := Cordis.Examples.Counter.readSpec
  binding := DeepSeekExternalGenericRound.counterReadBinding
  invocation := DeepSeekExternalGenericRound.counterReadInvocation
  certify := DeepSeekExternalGenericRound.counterReadCertifyAndDispatch

def counterReadStopScript : Script DeepSeekExternalGenericRound.counterReadRunner :=
  .stop counterReadStopPlan

def counterReadStopRun := run 1 counterReadStopScript

def uncertifiedCounterRead
    {state : GenericHarness.Runner Harness.counterConfig (.step 0 0 [])}
    (observed : ObservedResult
      DeepSeekExternalGenericRound.counterReadFailBinding
      DeepSeekExternalGenericRound.counterReadInvocation)
    (_exit_zero : observed.process.exitCode = 0) :
    Option (ObservedDispatch state observed) :=
  none

def counterReadFailPlan
    {state : GenericHarness.Runner Harness.counterConfig (.step 0 0 [])} :
    RoundPlan state where
  spec := Cordis.Examples.Counter.readSpec
  binding := DeepSeekExternalGenericRound.counterReadFailBinding
  invocation := DeepSeekExternalGenericRound.counterReadInvocation
  certify := uncertifiedCounterRead

def counterReadContinueScript : Script DeepSeekExternalGenericRound.counterReadRunner :=
  .continue counterReadStopPlan (fun _ dispatch =>
    .stop (counterReadFailPlan (state := dispatch.result.runnerResult.runner)))

def counterReadContinueRun := run 2 counterReadContinueScript

end Cordis.DeepSeekExternalGenericConversation
