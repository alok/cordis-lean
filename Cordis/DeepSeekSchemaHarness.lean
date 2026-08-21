import Cordis.DeepSeekSchemaExecution

/-!
# Schema-certified calls on the existing session surface

`DeepSeekSchemaExecution` proves that a provider function call passed both
schema admission and the generic dependent policy/view. This module is the
small transport boundary after that proof: it reifies the successful call as
the existing `DeepSeekHarness.ExecutedTool`, and therefore reuses the already
certified tool-result encoder and session append operation.

The conversion is deliberately proof-preserving rather than a second
executor. The provider certificate is retained in `SchemaExecutedTool`, while
`toExecutedTool` exposes the exact parsed JSON, generic validation, policy, and
dependent reply expected by `DeepSeekHarness`. No claim is made about remote
provider obedience, call-ID authenticity, persistence, or deployed-session
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaHarness

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekSchemaExecution
open Cordis.DeepSeekToolAdmission
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-- A successful schema-certified execution with its provider proof retained. -/
structure SchemaExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (raw : FunctionCall)
    (before : Model)
    (call : cfg.Call) where
  executed : ExecutedCall binding raw before call

/-- Reify a schema-certified execution in the existing generic harness record. -/
def SchemaExecutedTool.toExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : SchemaExecutedTool binding raw before call) :
    DeepSeekHarness.ExecutedTool cfg :=
  {
    raw := raw
    before := before
    parsed := executed.executed.checked.provider.arguments.json
    parsed_eq := executed.executed.checked.provider.arguments.parsed_eq
    call := call
    validation := executed.executed.checked.validation
    reply := executed.executed.reply
    policy := executed.executed.policy
    execution := executed.executed.execution
  }

theorem SchemaExecutedTool.toExecutedTool_parsed
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : SchemaExecutedTool binding raw before call) :
    executed.toExecutedTool.parsed =
      executed.executed.checked.provider.arguments.json :=
  rfl

theorem SchemaExecutedTool.toExecutedTool_provider_validation
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : SchemaExecutedTool binding raw before call) :
    executed.toExecutedTool.validation = executed.executed.checked.validation :=
  rfl

theorem SchemaExecutedTool.toExecutedTool_generic_tool_eq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : SchemaExecutedTool binding raw before call) :
    call.op = binding.genericTool :=
  executed.executed.generic_tool_eq

/-- Run the schema-aware executor and retain its provider certificate. -/
def executeCertifiedFunctionCall
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (raw : FunctionCall) :
    Except ExecutionError
      (Sigma fun call : cfg.Call => SchemaExecutedTool binding raw before call) :=
  match executeCertifiedCall binding before raw with
  | .error error => .error error
  | .ok ⟨call, executed⟩ =>
      .ok ⟨call, { executed := executed }⟩

theorem executeCertifiedFunctionCall_toExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    {before : Model}
    {raw : FunctionCall}
    {call : cfg.Call}
    (executed : SchemaExecutedTool binding raw before call) :
    executed.toExecutedTool.call = call :=
  rfl

/-- Append one certified result through the existing exact session operation. -/
def appendCertifiedToolResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.Session Session.noExtensions :=
  DeepSeekHarness.appendExecutedToolResult session turn step callId assistantSeq
    executed.toExecutedTool assistantSeqEarlier

theorem appendCertifiedToolResult_messages
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendCertifiedToolResult session turn step callId assistantSeq executed
      assistantSeqEarlier).messages =
      session.messages ++ [.toolResult callId
        (DeepSeekHarness.executedToolResultContent executed.toExecutedTool)
        (DeepSeekHarness.executedToolResultIsError executed.toExecutedTool)] := by
  exact DeepSeekHarness.appendExecutedToolResult_messages session turn step callId assistantSeq
    executed.toExecutedTool assistantSeqEarlier

theorem appendCertifiedToolResult_protocolProjection
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.protocolProjection
        (appendCertifiedToolResult session turn step callId assistantSeq executed
          assistantSeqEarlier).events =
      Session.protocolProjection session.events ++ [.toolResult turn step callId] := by
  exact DeepSeekHarness.appendExecutedToolResult_protocolProjection session turn step callId
    assistantSeq executed.toExecutedTool assistantSeqEarlier

theorem appendCertifiedToolResult_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendCertifiedToolResult session turn step callId assistantSeq executed
      assistantSeqEarlier).nextSeq = session.nextSeq + 1 := by
  exact DeepSeekHarness.appendExecutedToolResult_nextSeq session turn step callId assistantSeq
    executed.toExecutedTool assistantSeqEarlier

/-- Lift one schema-certified result into the existing conversation runner. -/
def appendCertifiedToolResultToRunner
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (runner : DeepSeekHarness.ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    DeepSeekHarness.ConversationRunner :=
  DeepSeekHarness.ConversationRunner.appendToolResults runner baseCall assistantSeq
    [executed.toExecutedTool] assistantSeqEarlier

theorem appendCertifiedToolResultToRunner_messages
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (runner : DeepSeekHarness.ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendCertifiedToolResultToRunner runner baseCall assistantSeq executed
      assistantSeqEarlier).session.messages =
      runner.session.messages ++
        DeepSeekHarness.executedToolMessages baseCall [executed.toExecutedTool] := by
  exact DeepSeekHarness.ConversationRunner.appendToolResults_session_messages runner baseCall
    assistantSeq [executed.toExecutedTool] assistantSeqEarlier

theorem appendCertifiedToolResultToRunner_nextCall
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (runner : DeepSeekHarness.ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executed : SchemaExecutedTool binding raw before call)
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendCertifiedToolResultToRunner runner baseCall assistantSeq executed
      assistantSeqEarlier).nextCall = runner.nextCall :=
  rfl

/-! ## Concrete bridge evidence -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example

def weatherSchemaExecuted
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    Except ExecutionError
      (Sigma fun call : weatherConfig.Call =>
        SchemaExecutedTool (weatherBinding certificate)
          DeepSeekToolAdmission.weatherCall 0 call) :=
  executeCertifiedFunctionCall (weatherBinding certificate) 0
    DeepSeekToolAdmission.weatherCall

def weatherAppended : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match weatherSchemaExecuted certificate with
      | .error _ => false
      | .ok ⟨_, executed⟩ =>
          let session := appendCertifiedToolResult
            DeepSeekHarness.counterSession 1 0 { value := 0 } 0 executed (by
              decide)
          session.nextSeq == DeepSeekHarness.counterSession.nextSeq + 1

def counterRunner : DeepSeekHarness.ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def weatherRunnerAppended : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match weatherSchemaExecuted certificate with
      | .error _ => false
      | .ok ⟨_, executed⟩ =>
          let runner := appendCertifiedToolResultToRunner counterRunner 0 0 executed (by
            decide)
          runner.session.nextSeq == counterRunner.session.nextSeq + 1

end Example

end Cordis.DeepSeekSchemaHarness
