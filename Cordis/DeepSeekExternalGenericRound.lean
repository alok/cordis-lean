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
  invocation_before_eq : invocation.before = state.model
  accepted_after_eq : accepted.after = GenericHarness.completionAfter state.model bridge.completion
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
    (invocation_before_eq : invocation.before = state.model)
    (accepted_after_eq :
      accepted.after = GenericHarness.completionAfter state.model bridge.completion)
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
    invocation_before_eq
    accepted_after_eq
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

/-! ## Reusable process-to-runner handoff -/

/-- An accepted observation together with its proof-carrying generic dispatch. -/
structure ObservedDispatch
    {Model Capability : Type u}
    {cfg : GenericHarness.Config Model Capability}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {turn step : Nat}
    (state : GenericHarness.Runner cfg (.step turn step []))
    (observed : ObservedResult binding invocation) where
  accepted : AcceptedResult observed
  result : ExternalDispatchResult accepted state

/--
Observe one configured process and, when a caller can prove acceptance, dispatch it into the
generic runner.  The `none` branch is deliberately not an error: it covers a nonzero process
exit or an observation for which the caller cannot establish the tool postcondition.  The
observation remains in the returned sigma value, so a caller can inspect the exact stdout,
stderr, exit code, JSON, and typed result before choosing a policy-level rejection.
-/
def observeAndDispatch
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {turn step : Nat}
    (state : GenericHarness.Runner cfg (.step turn step []))
    (certify : ∀ observed : ObservedResult binding invocation,
      observed.process.exitCode = 0 → Option (ObservedDispatch state observed)) :
    IO (Except ObservationError
      (Sigma fun observed : ObservedResult binding invocation =>
        Option (ObservedDispatch state observed))) := do
  match ← observe binding invocation with
  | .error error => pure (.error error)
  | .ok observed =>
      if exit_zero : observed.process.exitCode = 0 then
        match certify observed exit_zero with
        | none => pure (.ok ⟨observed, none⟩)
        | some dispatch => pure (.ok ⟨observed, some dispatch⟩)
      else
        pure (.ok ⟨observed, none⟩)

/-! ## Concrete read-process bridge over the existing counter catalog -/

def counterReadBinding : ProcessBinding Cordis.Examples.Counter.readSpec where
  resultCodec := fun input => Cordis.Examples.Counter.wire.resultCodec .read input
  config := fun _ => {
    command := "sh"
    args := #["-c", "printf '%s' '[true,7]'"]
    stdin := ""
  }

def counterReadFailBinding : ProcessBinding Cordis.Examples.Counter.readSpec where
  resultCodec := fun input => Cordis.Examples.Counter.wire.resultCodec .read input
  config := fun _ => {
    command := "sh"
    args := #["-c", "printf '%s' '[true,7]'; exit 7"]
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

theorem counterReadResult_eq
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    {value : Cordis.Examples.Counter.readSpec.Output counterReadInvocation.input}
    (result_eq : observed.result = .ok value)
    (value_eq : (show Nat from value) = 7) :
    observed.result = .ok (7 : Nat) := by
  rw [result_eq]
  congr

theorem noAccepted_of_nonzero
    {Model Capability : Type u}
    {spec : ToolSpec Model Capability}
    {binding : ProcessBinding spec}
    {invocation : ToolSpec.Invocation spec}
    {observed : ObservedResult binding invocation}
    (nonzero : observed.process.exitCode ≠ 0) :
    ¬ Nonempty (AcceptedResult observed) := by
  intro existsAccepted
  rcases existsAccepted with ⟨accepted⟩
  exact nonzero accepted.exitCode_eq_zero

def counterReadCompletion
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    (accepted : AcceptedResult observed) :
    Harness.counterConfig.Completion counterReadCall :=
  .ok { value := accepted.certified }

theorem counterReadExecution_of_eq
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    (accepted : AcceptedResult observed)
    (result_eq : observed.result = .ok (7 : Nat))
    (after_eq : accepted.after = 7) :
    Harness.counterConfig.view.execute counterReadCall = counterReadCompletion accepted := by
  cases observed with
  | mk config config_eq process json result parsed decoded =>
      cases accepted with
      | mk exitCode_eq after postcondition =>
          cases result_eq
          cases after_eq
          rfl

def counterReadRunner : GenericHarness.Runner Harness.counterConfig (.step 0 0 []) :=
  ((GenericHarness.Runner.initial Harness.counterConfig 7).beginTurn).beginStep

def counterReadIssued : LeasePool :=
  { available := [{ value := 0 }], unique := by simp }

theorem counterReadIssuance :
    counterReadRunner.leases.issue { value := counterReadRunner.nextCall } =
      some counterReadIssued := by
  rfl

theorem counterReadConsumption :
    counterReadIssued.consume { value := counterReadRunner.nextCall } = some .empty := by
  rfl

def counterReadBridge
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    (accepted : AcceptedResult observed)
    (result_eq : observed.result = .ok (7 : Nat))
    (after_eq : accepted.after = 7) :
    CompletionBridge accepted counterReadCall where
  completion := counterReadCompletion accepted
  before_eq := rfl
  after_eq := by
    rfl
  execution := counterReadExecution_of_eq accepted result_eq after_eq

def counterReadPolicy
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    {accepted : AcceptedResult observed}
    (bridge : CompletionBridge accepted counterReadCall) :
    SubjectPolicyTrace
      (Completed := Harness.counterConfig.Completion)
      (Rejected := Harness.counterConfig.PolicyRejected)
      (.proposed { value := counterReadRunner.nextCall } counterReadCall counterReadIssued)
      (.settled { value := counterReadRunner.nextCall } counterReadCall .empty
        (.completed bridge.completion)) :=
  .cons (.decide _ _ _ .allow)
    (.cons (.dispatch (by exact counterReadConsumption))
      (.cons (.settle bridge.completion) (.nil _)))

def counterReadDispatch
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    (accepted : AcceptedResult observed)
    (result_eq : observed.result = .ok (7 : Nat))
    (after_eq : accepted.after = 7) :
    ExternalDispatchResult accepted counterReadRunner :=
  let bridge := counterReadBridge accepted result_eq after_eq
  {
    raw := Cordis.Examples.Counter.rawRead
    call := counterReadCall
    bridge
    invocation_before_eq := by rfl
    accepted_after_eq := by rfl
    runnerResult := (dispatchAccepted accepted counterReadRunner
      Cordis.Examples.Counter.rawRead counterReadCall bridge
      (by rfl) (by rfl)
      counterReadValidation (by rfl)
      counterReadIssued counterReadIssuance counterReadConsumption
      (counterReadPolicy bridge)).runnerResult
  }

def counterReadCertifyAndDispatch
    (observed : ObservedResult counterReadBinding counterReadInvocation)
    (exit_zero : observed.process.exitCode = 0) :
    Option (ObservedDispatch counterReadRunner observed) :=
  match result_eq : observed.result with
  | .error _ => none
  | .ok value =>
      if value_eq : (show Nat from value) = 7 then
        have result_eq' : observed.result = .ok (7 : Nat) := by
          rw [result_eq, value_eq]
        let post : Cordis.Examples.Counter.readSpec.post
            counterReadInvocation.input counterReadInvocation.before observed.result 7 := by
          rw [result_eq']
          simp [Cordis.Examples.Counter.readSpec, counterReadInvocation,
            counterReadCall, Cordis.Examples.Counter.readCall]
        let accepted := accept exit_zero 7 post
        some {
          accepted
          result := counterReadDispatch accepted result_eq' rfl
        }
      else
        none

def counterReadFailCertify
    (observed : ObservedResult counterReadFailBinding counterReadInvocation)
    (_exit_zero : observed.process.exitCode = 0) :
    Option (ObservedDispatch counterReadRunner observed) :=
  none

def counterReadSession : Session.Session Session.noExtensions :=
  let empty := Session.Session.empty Session.noExtensions
  let withTurn := empty.appendLogOnly .turnStart { turn := 0 }
  withTurn.appendLogOnly .stepStart { turn := 0, step := 0 }

theorem counterReadSession_aligned :
    Session.protocolProjection counterReadSession.events = counterReadRunner.log := by
  rfl

def counterReadAttached
    {observed : ObservedResult counterReadBinding counterReadInvocation}
    (accepted : AcceptedResult observed)
    (result_eq : observed.result = .ok (7 : Nat))
    (after_eq : accepted.after = 7) :
    GenericSessionHarness.RunnerState {
      core := Harness.counterConfig
      requestHeader := {
        provider := "external-process"
        model := "proof-carrying"
        system := none
        toolSchemas := []
      }
      userPrompt := ""
      assistantPrompt := ""
    } :=
  attach (counterReadDispatch accepted result_eq after_eq)
    counterReadSession counterReadSession_aligned

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
