import Cordis.DeepSeekApiBytes
import Cordis.DeepSeekSchemaConversation

/-!
# Byte-backed heterogeneous schema conversation round

This module composes the byte-level DeepSeek API boundary with the dependent heterogeneous schema
registry. A successful result retains the exact request plan, exact request bytes, exact response
bytes, UTF-8 decoding certificate, typed response certificate, accepted calls, heterogeneous
execution batch, and runner endpoint in one dependent result.

The transport is injected and the response is a deterministic fixture in the examples. This does
not claim remote reachability, credentials, provider obedience, call-ID authenticity, retries,
cancellation, persistence, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaConversationBytes

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiBytes
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaMultiRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaHarness
open Cordis.DeepSeekToolSchema

/-! ## Typed plans retain their exact byte request -/

def ByteRequestPlan.ofTypedPlan
    {mode : RequestMode} (plan : TypedRequestPlan mode) : ByteRequestPlan :=
  {
    plan := plan.requestPlan
    bodyBytes := plan.request.body.toUTF8
    bodyBytes_eq := rfl
  }

theorem ByteRequestPlan.ofTypedPlan_plan
    {mode : RequestMode} (plan : TypedRequestPlan mode) :
    (ByteRequestPlan.ofTypedPlan plan).plan = plan.requestPlan :=
  rfl

theorem ByteRequestPlan.ofTypedPlan_bodyBytes
    {mode : RequestMode} (plan : TypedRequestPlan mode) :
    (ByteRequestPlan.ofTypedPlan plan).bodyBytes = plan.request.body.toUTF8 :=
  rfl

structure PreparedByteRequest
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (baseUrl : String)
    (key : ApiKey)
    (runner : ConversationRunner) where
  plan : TypedRequestPlan .complete
  build_eq : buildTypedCompleteRequestPlan baseUrl key request.source runner.session = .ok plan
  bytes : ByteRequestPlan
  bytes_plan_eq : bytes.plan = plan.requestPlan
  bytes_body_eq : bytes.bodyBytes = plan.request.body.toUTF8

namespace PreparedByteRequest

theorem complete_mode
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner}
    (prepared : PreparedByteRequest request baseUrl key runner) :
    prepared.plan.source.stream = false :=
  prepared.plan.complete_source_stream

theorem bytes_are_plan
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner}
    (prepared : PreparedByteRequest request baseUrl key runner) :
    prepared.bytes.plan = prepared.plan.requestPlan :=
  prepared.bytes_plan_eq

theorem bytes_are_utf8_body
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner}
    (prepared : PreparedByteRequest request baseUrl key runner) :
    prepared.bytes.bodyBytes = prepared.plan.request.body.toUTF8 :=
  prepared.bytes_body_eq

end PreparedByteRequest

/-! ## Dependent byte-backed result -/

inductive ConversationBytesError where
  | request (error : RequestError)
  | client (error : DeepSeekApiBytes.ClientError)
  | round (error : RegistryRoundError)

structure ConversationBytesResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (baseUrl : String)
    (key : ApiKey)
    (runner : ConversationRunner)
    (before : Model)
    {body : ByteArray}
    (validated : ValidatedResponseBytes body)
    (accepted : AcceptedToolCalls validated.text)
    (batch : RegistryExecutionBatch cfg before accepted.calls) where
  prepared : PreparedByteRequest request baseUrl key runner
  response : ValidatedResponseBytes body
  response_eq : response = validated
  round : SchemaRegistryRoundResult registry runner before accepted batch

namespace ConversationBytesResult

theorem finalRunner_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner} {before : Model}
    {body : ByteArray}
    {validated : ValidatedResponseBytes body}
    {accepted : AcceptedToolCalls validated.text}
    {batch : RegistryExecutionBatch cfg before accepted.calls}
    (result : ConversationBytesResult request baseUrl key runner before validated accepted batch) :
    result.round.finalRunner.session.nextSeq =
      result.round.assistantRunner.session.nextSeq + batch.executions.length :=
  SchemaRegistryRoundResult.finalRunner_nextSeq result.round

theorem response_is_validated
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {baseUrl : String} {key : ApiKey} {runner : ConversationRunner} {before : Model}
    {body : ByteArray}
    {validated : ValidatedResponseBytes body}
    {accepted : AcceptedToolCalls validated.text}
    {batch : RegistryExecutionBatch cfg before accepted.calls}
    (result : ConversationBytesResult request baseUrl key runner before validated accepted batch) :
    result.response = validated :=
  result.response_eq

end ConversationBytesResult

/-! ## Byte transport composition -/

def executeSchemaRegistryConversationRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (transport : DeepSeekApiBytes.Transport)
    (baseUrl : String)
    (key : ApiKey)
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except (ConversationBytesError)
      (Sigma fun body : ByteArray =>
        Sigma fun validated : ValidatedResponseBytes body =>
            Sigma fun accepted : AcceptedToolCalls validated.text =>
              Sigma fun batch : RegistryExecutionBatch cfg before accepted.calls =>
              ConversationBytesResult request baseUrl key runner before validated accepted
                batch)) := do
  match built : buildTypedCompleteRequestPlan baseUrl key request.source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      let bytes := ByteRequestPlan.ofTypedPlan plan
      match ← DeepSeekApiBytes.execute transport bytes with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, validated⟩ =>
          match executeSchemaRegistryRound runner registry before validated.text sourceEventSeqs
              sourcesNodup sourcesEarlier with
          | .error error => pure (.error (.round error))
          | .ok ⟨accepted, ⟨batch, round⟩⟩ =>
              pure (.ok ⟨body, ⟨validated, ⟨accepted, ⟨batch, {
                prepared := {
                  plan
                  build_eq := built
                  bytes
                  bytes_plan_eq := rfl
                  bytes_body_eq := rfl
                }
                response := validated
                response_eq := rfl
                round
              }⟩⟩⟩⟩)

/-! ## Executable heterogeneous byte fixture -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaRegistry.Example

def dualByteTransport : DeepSeekApiBytes.Transport where
  send _request := pure <| .ok {
    status := 200
    body := dualResponseBody.toUTF8
  }

def dualByteConversationRoundWithTransport
    (transport : DeepSeekApiBytes.Transport)
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except ConversationBytesError
      (Sigma fun body : ByteArray =>
        Sigma fun validated : ValidatedResponseBytes body =>
          Sigma fun accepted : AcceptedToolCalls validated.text =>
            Sigma fun batch : RegistryExecutionBatch dualConfig 0 accepted.calls =>
              ConversationBytesResult
                (dualRequestSource weatherCertificate clockCertificate)
                "https://fixture.invalid"
                { value := "fixture-key" }
                DeepSeekSchemaHarness.Example.counterRunner
                0 validated accepted batch)) :=
  executeSchemaRegistryConversationRound transport "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    0 DeepSeekSchemaHarness.Example.counterRunner [] (by simp) (by simp)

def dualByteConversationRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :=
  dualByteConversationRoundWithTransport dualByteTransport weatherCertificate clockCertificate

def dualByteRoundAccepted : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← dualByteConversationRound weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok ⟨body, ⟨validated, ⟨accepted, ⟨batch, result⟩⟩⟩⟩ =>
          pure (body = dualResponseBody.toUTF8 &&
            validated.text == dualResponseBody &&
            accepted.calls.length = 2 &&
            batch.executions.length = 2 &&
            batch.finalModel = 0 &&
            result.round.finalRunner.session.nextSeq =
              DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3)
  | _, _ => pure false

def invalidStatusTransport : DeepSeekApiBytes.Transport where
  send _request := pure <| .ok {
    status := 503
    body := dualResponseBody.toUTF8
  }

def invalidStatusRejected : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← dualByteConversationRoundWithTransport invalidStatusTransport
          weatherCertificate clockCertificate with
      | .error (.client (.httpStatus 503 _)) => pure true
      | _ => pure false
  | _, _ => pure false

end Example

end Cordis.DeepSeekSchemaConversationBytes
