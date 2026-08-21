import Cordis.DeepSeekSchemaRegistry

/-!
# Transport-backed heterogeneous schema conversation round

`DeepSeekSchemaRegistry` executes a validated response body against a dependent registry. This
module closes the adjacent request boundary: a registry-derived `RequestSource` carries the exact
tool declarations, `buildTypedCompleteRequestPlan` enforces terminal mode, and the explicit
`Transport` returns a validated response before the registry round is admitted. The result keeps
the wire response, accepted call list, heterogeneous execution batch, and exact runner endpoint
together.

The bridge is intentionally one complete-body round. It does not claim remote credentials,
provider obedience, call-ID authenticity, persistence, retries, asynchronous delivery, external
tool effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaMultiRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekToolSchema

/-! ## Registry-derived request source -/

def registryToolDefinitions
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) : List ToolDefinition :=
  registry.entries.map (fun entry => entry.tool)

structure RegistryRequestSource
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) where
  source : RequestSource
  tools_eq : source.tools = registryToolDefinitions registry

theorem RegistryRequestSource.source_tools
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry) :
    request.source.tools = registryToolDefinitions registry :=
  request.tools_eq

/-! ## Response/error packaging -/

inductive SchemaConversationError where
  | request (error : RequestError)
  | client (error : ClientError)
  | response (error : ApiSessionError)
  | noToolCalls
  | execution (error : RegistryExecutionError)
deriving BEq, DecidableEq, Repr

structure SchemaRegistryConversationResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    {body : String}
    (accepted : AcceptedToolCalls body)
    (batch : RegistryExecutionBatch cfg before accepted.calls) where
  accepted : AcceptedToolCalls body
  batch : RegistryExecutionBatch cfg before accepted.calls
  plan : TypedRequestPlan .complete
  response : ValidatedResponse body
  round : SchemaRegistryRoundResult registry runner before accepted batch

theorem SchemaRegistryConversationResult.finalRunner_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {runner : ConversationRunner}
    {before : Model}
    {body : String}
    {accepted : AcceptedToolCalls body}
    {batch : RegistryExecutionBatch cfg before accepted.calls}
    (result : SchemaRegistryConversationResult registry runner before accepted batch) :
    result.round.finalRunner.session.nextSeq =
      result.round.assistantRunner.session.nextSeq + result.batch.executions.length := by
  exact SchemaRegistryRoundResult.finalRunner_nextSeq result.round

/-! ## Complete-body request/transport composition -/

def executeSchemaRegistryConversationRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaConversationError
      (Sigma fun body : String =>
        Sigma fun accepted : AcceptedToolCalls body =>
          Sigma fun batch : RegistryExecutionBatch cfg before accepted.calls =>
            SchemaRegistryConversationResult registry runner before accepted batch)) := do
  match buildTypedCompleteRequestPlan baseUrl apiKey request.source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeComplete transport plan with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, response⟩ =>
          match executeSchemaRegistryRound runner registry before body sourceEventSeqs
              sourcesNodup sourcesEarlier with
          | .error (.response error) => pure (.error (.response error))
          | .error .noToolCalls => pure (.error .noToolCalls)
          | .error (.execution error) => pure (.error (.execution error))
          | .ok ⟨accepted, ⟨batch, round⟩⟩ =>
              pure (.ok ⟨body, ⟨accepted, ⟨batch, {
                accepted
                batch
                plan
                response
                round
              }⟩⟩⟩)

/-! ## Executable transport-backed heterogeneous fixture -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example
open Cordis.DeepSeekSchemaRegistry.Example

def dualRequestSource
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    RegistryRequestSource (dualRegistryEntries weatherCertificate clockCertificate) where
  source := {
    model := "deepseek-reasoner"
    system := some "Use the certified weather and clock tools."
    tools := [DeepSeekApi.exampleTool, clockTool]
    toolChoice := some .auto
  }
  tools_eq := by rfl

def dualTransport : Transport where
  send _request := pure <| .ok {
    status := 200
    body := dualResponseBody
  }

def dualConversationRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaConversationError
      (Sigma fun body : String =>
        Sigma fun accepted : AcceptedToolCalls body =>
          Sigma fun batch : RegistryExecutionBatch dualConfig 0 accepted.calls =>
            SchemaRegistryConversationResult
              (dualRegistryEntries weatherCertificate clockCertificate)
              DeepSeekSchemaHarness.Example.counterRunner 0 accepted batch)) :=
  executeSchemaRegistryConversationRound dualTransport "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    0 DeepSeekSchemaHarness.Example.counterRunner [] (by simp) (by simp)

end Example

end Cordis.DeepSeekSchemaConversation
