import Cordis.DeepSeekExternalToolProcess
import Cordis.DeepSeekExternalToolRound
import Cordis.GenericSessionHarness
import Cordis.Harness

/-!
# External completion into the generic typed runner

This module is the explicit adapter between the process-backed observation boundary and the
generic CORDIS runner.  An external result does not replace provider execution by fiat: the
caller supplies a `CompletionBridge` containing the generic completion, the exact
`View.execute = completion` equation, and the model-successor equation.  The generic runner then
constructs its ordinary `CallEvidence.completed` and `RecordChain`; the rich-session bridge can
attach the resulting call/result events without dispatching a second time.

The bridge is deliberately a proof obligation.  It is the seam where a real process-backed
adapter must establish that its typed output corresponds to the configured generic catalog.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekExternalGenericRound

open Cordis
open Cordis.GenericHarness
open Cordis.GenericSessionHarness
open Cordis.DeepSeekExternalToolProcess

universe u

structure CompletionBridge
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (accepted : AcceptedResult observed)
    (call : cfg.Call) where
  completion : cfg.Completion call
  before_eq : invocation.before = call.request.before
  after_eq : accepted.after = GenericHarness.completionAfter call.request.before completion
  execution : cfg.view.execute call = completion

structure ExternalDispatchResult
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (accepted : AcceptedResult observed)
    {turn step : Nat}
    (state : GenericHarness.Runner cfg (.step turn step [])) where
  raw : RawCall
  call : cfg.Call
  bridge : CompletionBridge accepted call
  runnerResult : GenericHarness.Runner.DispatchResult state

def dispatchAccepted
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (accepted : AcceptedResult observed)
    {turn step : Nat}
    (state : GenericHarness.Runner cfg (.step turn step []))
    (raw : RawCall)
    (call : cfg.Call)
    (bridge : CompletionBridge accepted call)
    (validation : cfg.validate state.model raw = .ok call)
    (allowed : cfg.decide state.model raw call = .allow)
    (issued : LeasePool)
    (issuance : state.leases.issue { value := state.nextCall } = some issued)
    {remaining : LeasePool}
    (consumption : issued.consume { value := state.nextCall } = some remaining)
    (policy : SubjectPolicyTrace
      (Completed := cfg.Completion)
      (Rejected := cfg.PolicyRejected)
      (.proposed { value := state.nextCall } call issued)
      (.settled { value := state.nextCall } call remaining (.completed bridge.completion))) :
    ExternalDispatchResult accepted state :=
  {
    raw
    call
    bridge
    runnerResult := GenericHarness.Runner.dispatchCompleted state raw call validation allowed
      issued issuance consumption bridge.completion bridge.execution policy
  }

def attach
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    {accepted : AcceptedResult observed}
    {turn step : Nat}
    {state : GenericHarness.Runner cfg (.step turn step [])}
    (result : ExternalDispatchResult accepted state)
    (session : Session.Session Session.noExtensions)
    (aligned : Session.protocolProjection session.events = state.log) :
    GenericSessionHarness.RunnerState {
      core := cfg
      requestHeader := {
        provider := "external-process"
        model := "proof-carrying"
        system := none
        toolSchemas := []
      }
      userPrompt := ""
      assistantPrompt := ""
    } :=
  GenericSessionHarness.RunnerState.attachCompletedDispatch state session aligned
    result.runnerResult

/-! ## Concrete read-process bridge over the existing counter catalog -/

def counterReadBinding : ProcessBinding Cordis.Examples.Counter.readSpec where
  resultCodec := fun input => Cordis.Examples.Counter.wire.resultCodec .read input
  config := fun _ => {
    command := "sh"
    args := #["-c", "printf '%s' '[true,7]'"]
    stdin := ""
  }

def counterReadCall : Harness.counterConfig.Call :=
  Cordis.Examples.Counter.readCall 7

def counterReadInvocation : ToolSpec.Invocation Cordis.Examples.Counter.readSpec :=
  counterReadCall.request

theorem counterReadValidation :
    Harness.counterConfig.validate 7 Cordis.Examples.Counter.rawRead =
      .ok counterReadCall := by
  exact Cordis.Examples.Counter.validateRaw_read 7

def counterReadCompletion
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    (accepted : AcceptedResult observed) :
    Harness.counterConfig.Completion counterReadCall :=
  .ok { value := accepted.certified }

def counterReadSurface : DeepSeekExternalToolRound.SurfaceCodec
    (spec := Cordis.Examples.Counter.readSpec) where
  render := fun _ result =>
    match result with
    | .ok value =>
      let typedValue : Nat := value
      toString typedValue
    | .error error => error
  isError := fun _ result =>
    match result with
    | .ok _ => false
    | .error _ => true

end Cordis.DeepSeekExternalGenericRound
