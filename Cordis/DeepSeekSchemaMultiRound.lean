import Cordis.DeepSeekSchemaRound

/-!
# A schema-certified multi-call response round

`DeepSeekSchemaRound` proves the smallest schema-aware assistant response: one accepted
function call. This module lifts the same dependent boundary to a nonempty list of calls for
one explicit `SchemaToolBinding`. Every call is checked against the same provider schema and
generic catalog operation, while the model passed to the next call is the certified successor of
the preceding call.

The binding is intentionally homogeneous. A heterogeneous provider registry, name-based lookup
among multiple schema certificates, remote transport, provider call-ID authentication, and
deployed Harness equivalence remain separate boundaries. The useful guarantee here is narrower
and executable: no raw call enters the batch, no call is skipped after a failure, and the exact
list of certified executions is what is appended to the typed runner.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaMultiRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaExecution
open Cordis.DeepSeekSchemaHarness
open Cordis.DeepSeekToolAdmission
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-! ## Nonempty accepted call lists -/

structure AcceptedToolCalls (body : String) where
  accepted : AcceptedApiResponse body
  calls : List FunctionCall
  calls_eq : accepted.validated.response.choices.head.message.toolCalls = calls
  nonempty : calls ≠ []

inductive SchemaBatchError where
  | response (error : ApiSessionError)
  | noToolCalls
  | execution (index : Nat) (error : ExecutionError)
deriving BEq, DecidableEq, Repr

/-- Preserve the accepted response while rejecting the empty tool-call shape. -/
def acceptToolCalls (body : String) :
    Except SchemaBatchError (AcceptedToolCalls body) :=
  match acceptResponse body with
  | .error error => .error (.response error)
  | .ok accepted =>
      match callList : accepted.validated.response.choices.head.message.toolCalls with
      | [] => .error .noToolCalls
      | head :: tail => .ok {
          accepted
          calls := head :: tail
          calls_eq := callList
          nonempty := by simp
        }

/-! ## Dependent execution traces -/

structure AnySchemaExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool) where
  raw : FunctionCall
  before : Model
  call : cfg.Call
  executed : SchemaExecutedTool binding raw before call
  execution_eq :
    executeCertifiedFunctionCall binding before raw =
      .ok ⟨call, executed⟩

namespace AnySchemaExecutedTool

def after
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    (executed : AnySchemaExecutedTool binding) : Model :=
  executed.executed.executed.reply.value.after

def toExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    (executed : AnySchemaExecutedTool binding) : DeepSeekHarness.ExecutedTool cfg :=
  executed.executed.toExecutedTool

end AnySchemaExecutedTool

structure SchemaExecutionBatch
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (calls : List FunctionCall) where
  finalModel : Model
  executions : List (AnySchemaExecutedTool binding)
  length_eq : executions.length = calls.length

def executeSchemaCallsAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (index : Nat) :
    (calls : List FunctionCall) ->
      Except SchemaBatchError (SchemaExecutionBatch binding before calls)
  | [] => .ok {
      finalModel := before
      executions := []
      length_eq := rfl
    }
  | raw :: rest =>
      match execution_eq : executeCertifiedFunctionCall binding before raw with
      | .error error => .error (.execution index error)
      | .ok ⟨call, executed⟩ =>
          let head : AnySchemaExecutedTool binding := {
            raw
            before
            call
            executed
            execution_eq
          }
          match executeSchemaCallsAux binding head.after (index + 1) rest with
          | .error error => .error error
          | .ok suffix => .ok {
              finalModel := suffix.finalModel
              executions := head :: suffix.executions
              length_eq := by
                simp only [List.length_cons]
                rw [suffix.length_eq]
            }

def executeSchemaCalls
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (calls : List FunctionCall) :
    Except SchemaBatchError (SchemaExecutionBatch binding before calls) :=
  executeSchemaCallsAux binding before 0 calls

theorem executeSchemaCalls_empty
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (before : Model) :
    executeSchemaCalls binding before [] = .ok {
      finalModel := before
      executions := []
      length_eq := rfl
    } := by
  rfl

/-! ## Runner append -/

def toExecutedTools
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool} :
    List (AnySchemaExecutedTool binding) -> List (DeepSeekHarness.ExecutedTool cfg)
  | [] => []
  | executed :: rest => executed.toExecutedTool :: toExecutedTools rest

@[simp] theorem toExecutedTools_length
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    (executions : List (AnySchemaExecutedTool binding)) :
    (toExecutedTools executions).length = executions.length := by
  induction executions with
  | nil => rfl
  | cons head tail inductionHypothesis => simp [toExecutedTools, inductionHypothesis]

def appendSchemaToolResultsToRunner
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (AnySchemaExecutedTool binding))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    ConversationRunner :=
  ConversationRunner.appendToolResults runner baseCall assistantSeq
    (toExecutedTools executions) assistantSeqEarlier

theorem appendSchemaToolResultsToRunner_session_messages
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (AnySchemaExecutedTool binding))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendSchemaToolResultsToRunner runner baseCall assistantSeq executions
      assistantSeqEarlier).session.messages =
      runner.session.messages ++ DeepSeekHarness.executedToolMessages baseCall
        (toExecutedTools executions) := by
  exact ConversationRunner.appendToolResults_session_messages runner baseCall assistantSeq
    (toExecutedTools executions) assistantSeqEarlier

theorem appendSchemaToolResultsToRunner_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (AnySchemaExecutedTool binding))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendSchemaToolResultsToRunner runner baseCall assistantSeq executions
      assistantSeqEarlier).session.nextSeq =
      runner.session.nextSeq + executions.length := by
  change (DeepSeekHarness.appendExecutedToolResults runner.session runner.turn runner.step
      baseCall assistantSeq (toExecutedTools executions) assistantSeqEarlier).nextSeq = _
  rw [DeepSeekHarness.appendExecutedToolResults_nextSeq]
  rw [toExecutedTools_length]

/-! ## Complete schema-aware multi-call round -/

structure SchemaMultiRoundResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (runner : ConversationRunner)
    (before : Model)
    {body : String}
    (accepted : AcceptedToolCalls body)
    (batch : SchemaExecutionBatch binding before accepted.calls) where
  assistantRunner : ConversationRunner
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq
  assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq
  finalRunner : ConversationRunner
  finalRunner_eq :
    finalRunner = appendSchemaToolResultsToRunner assistantRunner runner.nextCall
      assistantSeq batch.executions assistantSeqEarlier

def executeSchemaMultiRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (runner : ConversationRunner)
    (binding : SchemaToolBinding cfg tool)
    (before : Model)
    (body : String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except SchemaBatchError
      (Sigma fun accepted : AcceptedToolCalls body =>
        Sigma fun batch : SchemaExecutionBatch binding before accepted.calls =>
          SchemaMultiRoundResult binding runner before accepted batch) :=
  match acceptToolCalls body with
  | .error error => .error error
  | .ok accepted =>
      let assistantSeq := runner.session.nextSeq
      let assistantRunner := ConversationRunner.appendAcceptedApi runner accepted.accepted
        sourceEventSeqs sourcesNodup sourcesEarlier
      have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
        rw [ConversationRunner.appendAcceptedApi_nextSeq]
        exact Nat.lt_succ_self _
      match executeSchemaCalls binding before accepted.calls with
      | .error error => .error error
      | .ok batch =>
          let finalRunner := appendSchemaToolResultsToRunner assistantRunner runner.nextCall
            assistantSeq batch.executions assistantSeqEarlier
          .ok ⟨accepted, ⟨batch, {
            assistantRunner
            assistantSeq
            assistantSeq_eq := by
              change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
              rw [ConversationRunner.appendAcceptedApi_nextSeq]
            assistantSeqEarlier
            finalRunner
            finalRunner_eq := rfl
          }⟩⟩

theorem SchemaMultiRoundResult.finalRunner_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {runner : ConversationRunner}
    {before : Model}
    {body : String}
    {accepted : AcceptedToolCalls body}
    {batch : SchemaExecutionBatch binding before accepted.calls}
    (result : SchemaMultiRoundResult binding runner before accepted batch) :
    result.finalRunner.session.nextSeq =
      result.assistantRunner.session.nextSeq + batch.executions.length := by
  rw [result.finalRunner_eq]
  exact appendSchemaToolResultsToRunner_nextSeq result.assistantRunner runner.nextCall
    result.assistantSeq batch.executions result.assistantSeqEarlier

theorem SchemaMultiRoundResult.finalRunner_nextSeq_calls
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {runner : ConversationRunner}
    {before : Model}
    {body : String}
    {accepted : AcceptedToolCalls body}
    {batch : SchemaExecutionBatch binding before accepted.calls}
    (result : SchemaMultiRoundResult binding runner before accepted batch) :
    result.finalRunner.session.nextSeq =
      result.assistantRunner.session.nextSeq + accepted.calls.length := by
  rw [result.finalRunner_nextSeq, batch.length_eq]

/-! ## Executable two-call fixture -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example

def twoWeatherResponseJson (secondName secondArguments : String) : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-two-weather"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("finish_reason", .str "tool_calls"),
    ("message", .mkObj [
      ("role", .str "assistant"),
      ("content", .str "I will check both cities."),
      ("reasoning_content", .str "The user asked for two weather checks."),
      ("tool_calls", .arr #[
        .mkObj [
          ("id", .str "call-weather-0"),
          ("type", .str "function"),
          ("function", .mkObj [
            ("name", .str "get_weather"),
            ("arguments", .str "{\"city\":\"San Francisco\"}")
          ])
        ],
        .mkObj [
          ("id", .str "call-weather-1"),
          ("type", .str "function"),
          ("function", .mkObj [
            ("name", .str secondName),
            ("arguments", .str secondArguments)
          ])
        ]
      ])
    ])
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 20)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 20)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 40))
  ])
]

def twoWeatherResponseBody : String :=
  Lean.Json.compress (twoWeatherResponseJson "get_weather" "{\"city\":\"New York\"}")

def wrongSecondNameResponseBody : String :=
  Lean.Json.compress (twoWeatherResponseJson "unknown_weather" "{\"city\":\"New York\"}")

def twoWeatherRound
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    Except SchemaBatchError
      (Sigma fun accepted : AcceptedToolCalls twoWeatherResponseBody =>
        Sigma fun batch : SchemaExecutionBatch (weatherBinding certificate) 0 accepted.calls =>
          SchemaMultiRoundResult (weatherBinding certificate)
            DeepSeekSchemaHarness.Example.counterRunner 0 accepted batch) :=
  executeSchemaMultiRound DeepSeekSchemaHarness.Example.counterRunner
    (weatherBinding certificate) 0 twoWeatherResponseBody [] (by simp) (by simp)

def twoWeatherRoundAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match twoWeatherRound certificate with
      | .error _ => false
      | .ok ⟨_, ⟨batch, _⟩⟩ => batch.executions.length == 2

def twoWeatherRoundFinalNextSeq : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match twoWeatherRound certificate with
      | .error _ => false
      | .ok ⟨_, ⟨batch, result⟩⟩ =>
          result.finalRunner.session.nextSeq ==
            DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3 &&
            batch.finalModel == 0

def wrongSecondNameRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match acceptToolCalls wrongSecondNameResponseBody with
      | .error _ => false
      | .ok accepted =>
          match executeSchemaCalls (weatherBinding certificate) 0 accepted.calls with
          | .error (.execution 1 _) => true
          | .error _ => false
          | .ok _ => false

end Example

end Cordis.DeepSeekSchemaMultiRound
