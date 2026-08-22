import Cordis.DeepSeekHarnessProcessSchema
import Cordis.DeepSeekSchemaStreamPrefixConversation

/-!
# Process-backed prefix schema provenance

`DeepSeekSchemaStreamPrefixConversation` already carries a line-oriented prefix state, a
caller-controlled stop policy, and the heterogeneous registry through a completed `[DONE]` body.
This adapter retains the exact registry-derived `TypedRequestPlan` alongside that prefix result,
including fuel-exhausted and cancelled results. The plan is therefore not silently lost at the
incremental process boundary.

The slice is intentionally narrow. It does not claim byte framing, blocked-read interruption,
reconnects, provider-complete assembly, provider schema obedience, credential authenticity,
persistence, external tool trust, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessProcessSchemaPrefix

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessProcessSchema
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSchemaStreamPrefixConversation
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamIncremental
open Cordis.DeepSeekToolSchema

structure PreparedSchemaPrefixRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
    (policy : LinePolicy)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) where
  outcome : SchemaPrefixRoundOutcome registry policy runner before

namespace PreparedSchemaPrefixRound

theorem plan_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner}
    {policy : LinePolicy} {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    (_round : PreparedSchemaPrefixRound prepared policy before sourceEventSeqs sourcesNodup
      sourcesEarlier) :
    prepared.plan.source.stream = true :=
  prepared.source_stream

theorem body_eq_source
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner}
    {policy : LinePolicy} {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    (_round : PreparedSchemaPrefixRound prepared policy before sourceEventSeqs sourcesNodup
      sourcesEarlier) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  PreparedRegistryStreamingRequest.body_eq_source prepared

end PreparedSchemaPrefixRound

def executePreparedSchemaPrefixRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry} {runner : ConversationRunner}
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaPrefixConversationError
      (PreparedSchemaPrefixRound prepared policy before sourceEventSeqs sourcesNodup
        sourcesEarlier)) := do
  match ← executeSchemaStreamPrefixRound policy maxReads config baseUrl apiKey request
      before runner sourceEventSeqs sourcesNodup sourcesEarlier with
  | .error error => pure (.error error)
  | .ok outcome => pure (.ok { outcome })

def executeRegistrySchemaPrefixRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaPrefixConversationError
      (Sigma fun prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
          runner =>
        PreparedSchemaPrefixRound prepared policy before sourceEventSeqs sourcesNodup
          sourcesEarlier)) := do
  match prepareRegistryStreamingRequest baseUrl apiKey request runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← executePreparedSchemaPrefixRound policy maxReads config prepared before
          sourceEventSeqs sourcesNodup sourcesEarlier with
      | .error error => pure (.error error)
      | .ok round => pure (.ok ⟨prepared, round⟩)

/-! ## Executable prefix provenance fixtures -/

namespace Example

open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekSchemaHarness.Example

def dualToolPrefixProvenanceRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (Sigma fun prepared : PreparedRegistryStreamingRequest
          (dualRegistryEntries weatherCertificate clockCertificate)
          "https://fixture.invalid" { value := "fixture-key" }
          (dualRequestSource weatherCertificate clockCertificate)
          DeepSeekSchemaHarness.Example.counterRunner =>
        PreparedSchemaPrefixRound prepared (LinePolicy.never) 0 [] (by simp) (by simp))) := do
  executeRegistrySchemaPrefixRound (LinePolicy.never) 64 dualToolStreamProcess
    "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    0 DeepSeekSchemaHarness.Example.counterRunner [] (by simp) (by simp)

def dualToolPrefixCancelled
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (Sigma fun prepared : PreparedRegistryStreamingRequest
          (dualRegistryEntries weatherCertificate clockCertificate)
          "https://fixture.invalid" { value := "fixture-key" }
          (dualRequestSource weatherCertificate clockCertificate)
          DeepSeekSchemaHarness.Example.counterRunner =>
        PreparedSchemaPrefixRound prepared (LinePolicy.atLine 1 "cancelled:prefix") 0 []
          (by simp) (by simp))) := do
  executeRegistrySchemaPrefixRound (LinePolicy.atLine 1 "cancelled:prefix") 64
    dualToolStreamProcess "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    0 DeepSeekSchemaHarness.Example.counterRunner [] (by simp) (by simp)

end Example

end Cordis.DeepSeekHarnessProcessSchemaPrefix
