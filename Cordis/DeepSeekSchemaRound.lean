import Cordis.DeepSeekSchemaHarness

/-!
# A schema-certified complete-body round

`DeepSeekHarness.executeConversationRound` intentionally keeps its raw tool-call
compatibility path. This module adds the source-honest schema-aware alternative
for the smallest useful response shape: one accepted assistant choice carrying
exactly one function call. The response certificate, singleton-call witness,
schema/generic/policy/execution certificate, and runner endpoint are all
retained in one dependent result.

The restriction is structural, not an accidental runtime convention. Empty and
multi-call assistant payloads receive typed errors, while the accepted fixture
uses the real `DeepSeekApi.exampleResponseBody`. No claim is made about
provider obedience, remote call-ID authenticity, multi-tool dispatch, live
transport, persistence, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekSchemaExecution
open Cordis.DeepSeekSchemaHarness
open Cordis.DeepSeekToolAdmission
open Cordis.DeepSeekToolSchema
open Cordis.DeepSeekHarness
open Cordis.GenericHarness

/-- The accepted response has exactly one provider function call. -/
structure AcceptedSingleToolCall (body : String) where
  accepted : AcceptedApiResponse body
  raw : FunctionCall
  toolCalls_eq : accepted.validated.response.choices.head.message.toolCalls = [raw]

inductive SingleToolError where
  | noToolCall
  | multipleToolCalls (count : Nat)
deriving BEq, DecidableEq, Repr

/-- Extract the singleton tool-call witness without dropping the response proof. -/
def singleToolCall {body : String} (accepted : AcceptedApiResponse body) :
    Except SingleToolError (AcceptedSingleToolCall body) :=
  match calls : accepted.validated.response.choices.head.message.toolCalls with
  | [] => .error .noToolCall
  | [raw] => .ok { accepted, raw, toolCalls_eq := calls }
  | _ :: _ :: rest => .error (.multipleToolCalls (rest.length + 2))

inductive SchemaRoundError where
  | response (error : ApiSessionError)
  | toolShape (error : SingleToolError)
  | execution (error : ExecutionError)
deriving BEq, DecidableEq, Repr

def acceptSingleToolCall (body : String) :
    Except SchemaRoundError (AcceptedSingleToolCall body) :=
  match acceptResponse body with
  | .error error => .error (.response error)
  | .ok accepted =>
      match singleToolCall accepted with
      | .error error => .error (.toolShape error)
      | .ok single => .ok single

/-- One schema-aware round after the assistant response has been accepted. -/
structure SchemaRoundResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    (binding : SchemaToolBinding cfg tool)
    (runner : ConversationRunner)
    (before : Model)
    {body : String}
    (single : AcceptedSingleToolCall body)
    (call : cfg.Call) where
  assistantRunner : ConversationRunner
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq
  assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq
  executed : SchemaExecutedTool binding single.raw before call
  execution_eq :
    executeCertifiedFunctionCall binding before single.raw =
      .ok ⟨call, executed⟩
  finalRunner : ConversationRunner
  finalRunner_eq :
    finalRunner = appendCertifiedToolResultToRunner assistantRunner runner.nextCall
      assistantSeq executed assistantSeqEarlier

/-- Execute one accepted singleton-tool response through the schema-aware path. -/
def executeSchemaRound
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
    Except SchemaRoundError
      (Sigma fun single : AcceptedSingleToolCall body =>
        Sigma fun call : cfg.Call =>
          SchemaRoundResult binding runner before single call) :=
  match acceptSingleToolCall body with
  | .error error => .error error
  | .ok single =>
      let assistantSeq := runner.session.nextSeq
      let assistantRunner := ConversationRunner.appendAcceptedApi runner single.accepted
        sourceEventSeqs sourcesNodup sourcesEarlier
      have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
        rw [ConversationRunner.appendAcceptedApi_nextSeq]
        exact Nat.lt_succ_self _
      match execution_eq : executeCertifiedFunctionCall binding before single.raw with
      | .error error => .error (.execution error)
      | .ok ⟨call, executed⟩ =>
          let finalRunner := appendCertifiedToolResultToRunner assistantRunner
            runner.nextCall assistantSeq executed assistantSeqEarlier
          .ok ⟨single, ⟨call, {
            assistantRunner
            assistantSeq
            assistantSeq_eq := by
              change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
              rw [ConversationRunner.appendAcceptedApi_nextSeq]
            assistantSeqEarlier
            executed
            execution_eq := execution_eq
            finalRunner
            finalRunner_eq := rfl
          }⟩⟩

theorem SchemaRoundResult.finalRunner_nextCall
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {tool : ToolDefinition}
    {binding : SchemaToolBinding cfg tool}
    {runner : ConversationRunner}
    {before : Model}
    {body : String}
    {single : AcceptedSingleToolCall body}
    {call : cfg.Call}
    (result : SchemaRoundResult binding runner before single call) :
    result.finalRunner.nextCall = result.assistantRunner.nextCall := by
  rw [result.finalRunner_eq]
  exact appendCertifiedToolResultToRunner_nextCall result.assistantRunner runner.nextCall
    result.assistantSeq result.executed result.assistantSeqEarlier

/-! ## Executable response-round evidence -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example

def weatherRound
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    Except SchemaRoundError
      (Sigma fun single : AcceptedSingleToolCall DeepSeekApi.exampleResponseBody =>
        Sigma fun call : weatherConfig.Call =>
          SchemaRoundResult (weatherBinding certificate)
            DeepSeekSchemaHarness.Example.counterRunner 0 single call) :=
  executeSchemaRound DeepSeekSchemaHarness.Example.counterRunner
    (weatherBinding certificate) 0 DeepSeekApi.exampleResponseBody [] (by simp) (by simp)

def weatherRoundAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match weatherRound certificate with
      | .error _ => false
      | .ok ⟨_, ⟨_, _⟩⟩ => true

def weatherRoundFinalNextSeq : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => false
  | .ok certificate =>
      match weatherRound certificate with
      | .error _ => false
      | .ok ⟨_, ⟨_, result⟩⟩ =>
          result.finalRunner.session.nextSeq ==
            DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 2

def emptyResponseRejected : Bool :=
  match acceptSingleToolCall DeepSeekHarness.counterFinalResponseBody with
  | .error (.response _) => false
  | .error (.toolShape .noToolCall) => true
  | .error _ => false
  | .ok _ => false

end Example

end Cordis.DeepSeekSchemaRound
