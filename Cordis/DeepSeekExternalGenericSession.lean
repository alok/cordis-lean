import Cordis.DeepSeekExternalGenericConversation

/-!
# Session-indexed external conversation execution

This module threads the proof-carrying external conversation runner through the rich CORDIS
session state.  A script is indexed by the exact generic runner, the rich session, and the
projection equality connecting the runner log to the session's protocol events.  An accepted
external dispatch therefore appends its typed tool-call/tool-result events exactly once, while
the reused generic Trace retains the heterogeneous process certificate for each accepted edge.

Fuel exhaustion, uncertified observations, and observation errors retain the current rich-session
prefix.  The runner deliberately remains finite and oracle/certification driven: this does not
claim process identity, sandboxing, exactly-once effects, persistence, authentication, deployed
DeepSeek Harness equivalence, or a total protocol implementation.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekExternalGenericSession

open Cordis
open Cordis.GenericHarness
open Cordis.GenericSessionHarness
open Cordis.DeepSeekExternalToolProcess
open Cordis.DeepSeekExternalGenericRound
open Cordis.DeepSeekExternalGenericConversation

universe u

def attachedSession
    {Model Capability : Type u}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat}
    (runner : GenericHarness.Runner cfg.core (.step turn step []))
    (session : Session.Session Session.noExtensions)
    (aligned : Session.protocolProjection session.events = runner.log)
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (dispatch : ObservedDispatch runner observed) :
    Session.Session Session.noExtensions :=
  (GenericSessionHarness.RunnerState.attachCompletedDispatch
    runner session aligned dispatch.result.runnerResult).session

theorem attachedProjection
    {Model Capability : Type u}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat}
    (runner : GenericHarness.Runner cfg.core (.step turn step []))
    (session : Session.Session Session.noExtensions)
    (aligned : Session.protocolProjection session.events = runner.log)
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (dispatch : ObservedDispatch runner observed) :
    Session.protocolProjection (attachedSession runner session aligned dispatch).events =
      dispatch.result.runnerResult.runner.log :=
  (GenericSessionHarness.RunnerState.attachCompletedDispatch
    runner session aligned dispatch.result.runnerResult).projection_eq

structure SessionRoundPlan
    {Model Capability : Type u}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat}
    (runner : GenericHarness.Runner cfg.core (.step turn step [])) where
  spec : ToolSpec Model Capability
  binding : ProcessBinding spec
  invocation : ToolSpec.Invocation spec
  certify : ∀ observed : ObservedResult binding invocation,
    observed.process.exitCode = 0 → Option (ObservedDispatch runner observed)

inductive SessionScript
    {Model Capability : Type u}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat} :
    (runner : GenericHarness.Runner cfg.core (.step turn step [])) →
    (session : Session.Session Session.noExtensions) →
    (aligned : Session.protocolProjection session.events = runner.log) →
    Type (u + 2) where
  | stop
      {runner : GenericHarness.Runner cfg.core (.step turn step [])}
      {session : Session.Session Session.noExtensions}
      {aligned : Session.protocolProjection session.events = runner.log}
      (plan : SessionRoundPlan runner) : SessionScript runner session aligned
  | continue
      {runner : GenericHarness.Runner cfg.core (.step turn step [])}
      {session : Session.Session Session.noExtensions}
      {aligned : Session.protocolProjection session.events = runner.log}
      (plan : SessionRoundPlan runner)
      (next : ∀ (observed : ObservedResult plan.binding plan.invocation)
        (dispatch : ObservedDispatch runner observed),
        SessionScript dispatch.result.runnerResult.runner
          (attachedSession runner session aligned dispatch)
          (attachedProjection runner session aligned dispatch)) :
      SessionScript runner session aligned

structure SessionRunResult
    {Model Capability : Type u}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat}
    (initialRunner : GenericHarness.Runner cfg.core (.step turn step []))
    (initialSession : Session.Session Session.noExtensions)
    (finalRunner : GenericHarness.Runner cfg.core (.step turn step []))
    (finalSession : Session.Session Session.noExtensions) where
  initialProjection : Session.protocolProjection initialSession.events = initialRunner.log
  finalProjection : Session.protocolProjection finalSession.events = finalRunner.log
  trace : Cordis.DeepSeekExternalGenericConversation.Trace initialRunner finalRunner
  stop : StopKind
  stopProcess : Option ProcessObservation
  stopError : Option ObservationError

def runAux
    {Model Capability : Type}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat}
    (fuel : Nat)
    {runner : GenericHarness.Runner cfg.core (.step turn step [])}
    {session : Session.Session Session.noExtensions}
    {aligned : Session.protocolProjection session.events = runner.log}
    (script : SessionScript runner session aligned) :
    IO (Sigma fun finalRunner : GenericHarness.Runner cfg.core (.step turn step []) =>
      Sigma fun finalSession : Session.Session Session.noExtensions =>
        SessionRunResult runner session finalRunner finalSession) := do
  match fuel with
  | 0 =>
      pure ⟨runner, ⟨session, {
        initialProjection := aligned
        finalProjection := aligned
        trace := Cordis.DeepSeekExternalGenericConversation.Trace.nil runner
        stop := .fuelExhausted
        stopProcess := none
        stopError := none
      }⟩⟩
  | fuel + 1 =>
      match script with
      | .stop plan =>
          match ← observeAndDispatch runner
              (binding := plan.binding) (invocation := plan.invocation)
              plan.certify with
          | .error error =>
              pure ⟨runner, ⟨session, {
                initialProjection := aligned
                finalProjection := aligned
                trace := Cordis.DeepSeekExternalGenericConversation.Trace.nil runner
                stop := .observationError
                stopProcess := none
                stopError := some error
              }⟩⟩
          | .ok ⟨observed, none⟩ =>
              pure ⟨runner, ⟨session, {
                initialProjection := aligned
                finalProjection := aligned
                trace := Cordis.DeepSeekExternalGenericConversation.Trace.nil runner
                stop := .uncertified
                stopProcess := some observed.process
                stopError := none
              }⟩⟩
          | .ok ⟨observed, some dispatch⟩ =>
              let finalSession := attachedSession runner session aligned dispatch
              let finalProjection := attachedProjection runner session aligned dispatch
              let head : ExternalStep runner dispatch.result.runnerResult.runner :=
                .ofObserved dispatch
              pure ⟨dispatch.result.runnerResult.runner, ⟨finalSession, {
                initialProjection := aligned
                finalProjection := finalProjection
                trace := Cordis.DeepSeekExternalGenericConversation.Trace.cons head
                  (Cordis.DeepSeekExternalGenericConversation.Trace.nil _)
                stop := .completed
                stopProcess := none
                stopError := none
              }⟩⟩
      | .continue plan next =>
          match ← observeAndDispatch runner
              (binding := plan.binding) (invocation := plan.invocation)
              plan.certify with
          | .error error =>
              pure ⟨runner, ⟨session, {
                initialProjection := aligned
                finalProjection := aligned
                trace := Cordis.DeepSeekExternalGenericConversation.Trace.nil runner
                stop := .observationError
                stopProcess := none
                stopError := some error
              }⟩⟩
          | .ok ⟨observed, none⟩ =>
              pure ⟨runner, ⟨session, {
                initialProjection := aligned
                finalProjection := aligned
                trace := Cordis.DeepSeekExternalGenericConversation.Trace.nil runner
                stop := .uncertified
                stopProcess := some observed.process
                stopError := none
              }⟩⟩
          | .ok ⟨observed, some dispatch⟩ =>
              let head : ExternalStep runner dispatch.result.runnerResult.runner :=
                .ofObserved dispatch
              let captured ← runAux fuel (next observed dispatch)
              match captured with
              | ⟨finalRunner, ⟨finalSession, tail⟩⟩ =>
                  pure ⟨finalRunner, ⟨finalSession, {
                    initialProjection := aligned
                    finalProjection := tail.finalProjection
                    trace := Cordis.DeepSeekExternalGenericConversation.Trace.cons head tail.trace
                    stop := tail.stop
                    stopProcess := tail.stopProcess
                    stopError := tail.stopError
                  }⟩⟩
termination_by fuel

def run
    {Model Capability : Type}
    {cfg : GenericSessionHarness.SessionConfig Model Capability}
    {turn step : Nat}
    (fuel : Nat)
    {runner : GenericHarness.Runner cfg.core (.step turn step [])}
    {session : Session.Session Session.noExtensions}
    {aligned : Session.protocolProjection session.events = runner.log}
    (script : SessionScript runner session aligned) :=
  runAux fuel script

def counterSessionConfig : GenericSessionHarness.SessionConfig Nat
    Cordis.Examples.Counter.Capability := {
  core := Harness.counterConfig
  requestHeader := {
    provider := "external-process"
    model := "proof-carrying"
    system := none
    toolSchemas := []
  }
  userPrompt := ""
  assistantPrompt := ""
}

def counterSessionStopPlan : SessionRoundPlan (cfg := counterSessionConfig)
    DeepSeekExternalGenericRound.counterReadRunner where
  spec := Cordis.Examples.Counter.readSpec
  binding := DeepSeekExternalGenericRound.counterReadBinding
  invocation := DeepSeekExternalGenericRound.counterReadInvocation
  certify := DeepSeekExternalGenericRound.counterReadCertifyAndDispatch

def counterSessionStopScript :
    SessionScript (cfg := counterSessionConfig)
      DeepSeekExternalGenericRound.counterReadRunner
      DeepSeekExternalGenericRound.counterReadSession
      DeepSeekExternalGenericRound.counterReadSession_aligned :=
  .stop counterSessionStopPlan

def counterSessionStopRun :=
  run (cfg := counterSessionConfig) 1 counterSessionStopScript

def counterSessionMalformedCertify
    {runner : GenericHarness.Runner Harness.counterConfig (.step 0 0 [])}
    (observed : ObservedResult
      DeepSeekExternalGenericConversation.counterReadMalformedBinding
      DeepSeekExternalGenericRound.counterReadInvocation)
    (_exit_zero : observed.process.exitCode = 0) :
    Option (ObservedDispatch runner observed) :=
  none

def counterSessionMalformedPlan
    {runner : GenericHarness.Runner Harness.counterConfig (.step 0 0 [])} :
    SessionRoundPlan (cfg := counterSessionConfig) runner where
  spec := Cordis.Examples.Counter.readSpec
  binding := DeepSeekExternalGenericConversation.counterReadMalformedBinding
  invocation := DeepSeekExternalGenericRound.counterReadInvocation
  certify := counterSessionMalformedCertify

def counterSessionErrorScript :
    SessionScript (cfg := counterSessionConfig)
      DeepSeekExternalGenericRound.counterReadRunner
      DeepSeekExternalGenericRound.counterReadSession
      DeepSeekExternalGenericRound.counterReadSession_aligned :=
  .continue counterSessionStopPlan (fun _ dispatch =>
    .stop (counterSessionMalformedPlan (runner := dispatch.result.runnerResult.runner)))

def counterSessionErrorRun :=
  run (cfg := counterSessionConfig) 2 counterSessionErrorScript

end Cordis.DeepSeekExternalGenericSession
