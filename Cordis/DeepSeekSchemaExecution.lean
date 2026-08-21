import Cordis.DeepSeekGenericBridge
import Cordis.DeepSeekHarness

/-!
# Certified DeepSeek call execution

`DeepSeekGenericBridge` composes provider-schema and generic admission but
stops before dispatch. This module adds a separate pure execution adapter: a
call must first carry both certificates, then the existing generic policy must
allow it, and only then may the committed `View` execute the dependent call.

The adapter deliberately does not replace `DeepSeekHarness.executeFunctionCall`.
The latter remains the compatibility path for raw provider calls; this module
is the stricter schema-aware path. It proves neither provider obedience nor
call-ID authenticity, and it does not turn a pure provider view into a live
external tool process.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaExecution

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

universe u

/-- Failures after the provider/schema and generic admission boundary. -/
inductive ExecutionError where
  | admission (error : BridgeError)
  | policy (decision : Decision) (reason : String)
  | provider (message : String)
deriving BEq, DecidableEq, Repr

/-- A call that passed schema admission, policy, and dependent execution. -/
structure ExecutedCall
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (raw : FunctionCall)
    (before : Model)
    (call : cfg.Call) where
  checked : SchemaCheckedCall binding raw before call
  reply : Reply call
  policy : cfg.decide before {
      name := raw.name
      arguments := checked.provider.arguments.json
    } call = .allow
  execution : cfg.view.execute call = .ok reply

/-- Execute only after composing provider and generic admission certificates. -/
def executeCertifiedCall
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (raw : FunctionCall) :
    Except ExecutionError
      (Sigma fun call : cfg.Call => ExecutedCall binding raw before call) :=
  match validateAndAdmit binding before raw with
  | .error error => .error (.admission error)
  | .ok ⟨call, checked⟩ =>
      let genericRaw : RawCall := {
        name := raw.name
        arguments := checked.provider.arguments.json
      }
      match decisionEvidence : cfg.decide before genericRaw call with
      | .reject decision _ reason =>
          .error (.policy decision (cfg.renderPolicyRejected call reason))
      | .allow =>
          match executionEvidence : cfg.view.execute call with
          | .error message => .error (.provider message)
          | .ok reply =>
              .ok ⟨call, {
                checked
                reply
                policy := decisionEvidence
                execution := executionEvidence
              }⟩

theorem ExecutedCall.generic_tool_eq
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : ExecutedCall binding raw before call) :
    call.op = binding.genericTool :=
  validateAndAdmit_generic_tool_eq binding executed.checked

/-! ## Executable success and rejection fixtures -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example

def weatherExecuted
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    Except ExecutionError
      (Sigma fun call : weatherConfig.Call =>
        ExecutedCall (weatherBinding certificate)
          DeepSeekToolAdmission.weatherCall 0 call) :=
  executeCertifiedCall (weatherBinding certificate) 0
    DeepSeekToolAdmission.weatherCall

def weatherExecutionAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match weatherExecuted certificate with
      | .error _ => false
      | .ok ⟨_, _⟩ => true

end Example

end Cordis.DeepSeekSchemaExecution
