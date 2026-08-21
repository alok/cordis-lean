import Cordis.DeepSeekSchemaStreamConversation

/-!
# Process-backed heterogeneous schema provenance

DeepSeekSchemaStreamConversation already proves a complete-body streamed round for a
dependent registry. This module retains one more boundary that the loop intentionally hides: the
exact certified registry-derived request plan used by the process, alongside the validated body,
the typed schema step, and its runner endpoint. The process, request, and registry execution
failures remain distinct.

This is still a local complete-body adapter. It does not claim provider schema obedience,
credential authenticity, incremental reader semantics, cancellation, persistence, external tool
trust, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessProcessSchema

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekToolSchema

/-! ## Registry-derived request provenance -/

structure PreparedRegistryStreamingRequest
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (runner : ConversationRunner) where
  plan : TypedRequestPlan .streaming
  build_eq :
    CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
      (registryCertifiedRequestSource request) runner.session = .ok plan

namespace PreparedRegistryStreamingRequest

theorem build_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner) :
    CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
      (registryCertifiedRequestSource request) runner.session = .ok prepared.plan :=
  prepared.build_eq

theorem source_stream
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedRegistryStreamingRequest

def prepareRegistryStreamingRequest
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (runner : ConversationRunner) :
    Except RequestError
      (PreparedRegistryStreamingRequest registry baseUrl apiKey request runner) :=
  match built : CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
      (registryCertifiedRequestSource request) runner.session with
  | .error error => .error error
  | .ok plan => .ok { plan, build_eq := built }

/-! ## Process-backed schema step -/

def processedStep
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {runner : ConversationRunner}
    {before : Model}
    {body : String} :
    SchemaStreamConversationStep registry runner before body → ProcessedResponse body
  | .terminal result => result.processed
  | .tools result => result.processed

structure SchemaProcessRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry}
    {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq)
    (body : String) where
  processed : ProcessedResponse body
  step : SchemaStreamConversationStep registry runner before body
  processed_eq : processedStep step = processed

namespace SchemaProcessRound

theorem plan_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (_round : SchemaProcessRound prepared before sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    prepared.plan.source.stream = true :=
  prepared.source_stream

theorem processed_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String} (round : SchemaProcessRound prepared before sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    processedStep round.step = round.processed :=
  round.processed_eq

end SchemaProcessRound

inductive SchemaProcessError where
  | request (error : RequestError)
  | client (error : SessionClientError)
  | execution (error : RegistryExecutionError)
deriving DecidableEq, Repr

def executePreparedSchemaRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (config : ProcessConfig)
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaProcessError
      (Sigma fun body : String =>
        SchemaProcessRound prepared before sourceEventSeqs sourcesNodup sourcesEarlier body)) := do
  match ← executeTypedStreamingWith finishMulti config prepared.plan with
  | .error error => pure (.error (.client error))
  | .ok ⟨body, processed⟩ =>
      let calls := finishedFunctionCalls processed.finished
      if noToolCalls : calls = [] then
        pure (.ok ⟨body, {
          processed
          step := .terminal { processed, noToolCalls }
          processed_eq := rfl
        }⟩)
      else
        let assistantSeq := runner.session.nextSeq
        let assistantRunner := ConversationRunner.appendFinished runner processed.finished
          sourceEventSeqs sourcesNodup sourcesEarlier
        have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
          rw [ConversationRunner.appendFinished_nextSeq]
          exact Nat.lt_succ_self _
        match batchResult : executeSchemaRegistryCalls registry before calls with
        | .error error => pure (.error (.execution error))
        | .ok batch =>
            let finalRunner := appendSchemaRegistryResultsToRunner assistantRunner
              runner.nextCall assistantSeq batch.executions assistantSeqEarlier
            pure (.ok ⟨body, {
              processed
              step := .tools {
                processed
                calls
                batch
                assistantRunner
                runner := finalRunner
                finalModel := batch.finalModel
                assistantSeq
                assistantSeq_eq := by
                  rw [ConversationRunner.appendFinished_nextSeq]
                finalRunner_nextSeq := by
                  change (appendSchemaRegistryResultsToRunner assistantRunner runner.nextCall
                    assistantSeq batch.executions assistantSeqEarlier).session.nextSeq = _
                  rw [appendSchemaRegistryResultsToRunner_nextSeq]
                  rw [ConversationRunner.appendFinished_nextSeq]
                  simp [batch.length_eq]
              }
              processed_eq := rfl
            }⟩)

def executeRegistrySchemaRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
          runner =>
        Sigma fun body : String =>
          SchemaProcessRound prepared before sourceEventSeqs sourcesNodup sourcesEarlier
            body)) := do
  match prepareRegistryStreamingRequest baseUrl apiKey request runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← executePreparedSchemaRound config prepared before sourceEventSeqs sourcesNodup
          sourcesEarlier with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ => pure (.ok ⟨prepared, ⟨body, round⟩⟩)

/-! ## Executable registry/process fixtures -/

namespace Example

open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekSchemaHarness.Example

def dualToolStreamProvenanceRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest
          (dualRegistryEntries weatherCertificate clockCertificate)
          "https://fixture.invalid" { value := "fixture-key" }
          (dualRequestSource weatherCertificate clockCertificate)
          DeepSeekSchemaHarness.Example.counterRunner =>
        Sigma fun body : String => SchemaProcessRound prepared 0 [] (by simp) (by simp) body)) := do
  executeRegistrySchemaRound dualToolStreamProcess "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    0 DeepSeekSchemaHarness.Example.counterRunner [] (by simp) (by simp)

def textProvenanceRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest
          (dualRegistryEntries weatherCertificate clockCertificate)
          "https://fixture.invalid" { value := "fixture-key" }
          (dualRequestSource weatherCertificate clockCertificate)
          DeepSeekSchemaHarness.Example.counterRunner =>
        Sigma fun body : String => SchemaProcessRound prepared 0 [] (by simp) (by simp) body)) := do
  executeRegistrySchemaRound DeepSeekCurlSession.fixtureTextProcess "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    0 DeepSeekSchemaHarness.Example.counterRunner [] (by simp) (by simp)

end Example

end Cordis.DeepSeekHarnessProcessSchema
