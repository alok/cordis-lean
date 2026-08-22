import Cordis.DeepSeekHarnessEventText
import Cordis.DeepSeekHarnessProcessSchema

/-!
# Event-restored heterogeneous schema process

`DeepSeekHarnessEventText` restores a supported current-Harness event log to an exact
`ConversationRunner`, while `DeepSeekHarnessProcessSchema` keeps a heterogeneous registry request
and its process-backed schema step dependent.  This module is the small composition boundary
between them: the restored archive/session certificate remains attached to the exact prepared
registry plan and the exact process/schema round.

The adapter is intentionally one-shot and local.  It does not claim complete event-union
coverage, provider schema obedience, credential authenticity, byte framing, persistence,
cancellation, external tool effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventProcessSchema

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekHarnessProcessSchema
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaConversationLoop
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.SessionRefinement
open Cordis.DeepSeekToolSchema

/-! ## The attached dependent round -/

structure EventSchemaProcessRound
    {sourceText : String}
    (restored : RestoredTextRunner sourceText)
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (request : RegistryRequestSource registry)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq)
    (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner)
    (body : String) where
  round : SchemaProcessRound prepared before sourceEventSeqs sourcesNodup sourcesEarlier body
  restored_session_eq :
    restored.restored.runner.session = restored.validated.validated.final.session
  archive_raw_eq :
    restored.restored.log.archive.events.map SessionEventArchive.ArchivedEvent.raw =
      restored.validated.parsed.lines

namespace EventSchemaProcessRound

theorem plan_source_stream
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner}
    {body : String}
    (round : EventSchemaProcessRound restored registry request before sourceEventSeqs
      sourcesNodup sourcesEarlier prepared body) :
    prepared.plan.source.stream = true :=
  Cordis.DeepSeekHarnessProcessSchema.SchemaProcessRound.plan_exact round.round

theorem plan_body_eq_source
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner}
    {body : String}
    (_round : EventSchemaProcessRound restored registry request before sourceEventSeqs
      sourcesNodup sourcesEarlier prepared body) :
    prepared.plan.request.body = Lean.Json.compress prepared.plan.source.toJson :=
  PreparedRegistryStreamingRequest.body_eq_source prepared

theorem request_build_eq_validated_session
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner}
    {body : String}
    (round : EventSchemaProcessRound restored registry request before sourceEventSeqs
      sourcesNodup sourcesEarlier prepared body) :
    CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
        (registryCertifiedRequestSource request)
        restored.validated.validated.final.session = .ok prepared.plan := by
  rw [← round.restored_session_eq]
  exact prepared.build_eq

theorem processed_exact
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner}
    {body : String}
    (round : EventSchemaProcessRound restored registry request before sourceEventSeqs
      sourcesNodup sourcesEarlier prepared body) :
    processedStep round.round.step = round.round.processed :=
  Cordis.DeepSeekHarnessProcessSchema.SchemaProcessRound.processed_exact round.round

theorem archive_raw_eq_source
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner}
    {body : String}
    (_round : EventSchemaProcessRound restored registry request before sourceEventSeqs
      sourcesNodup sourcesEarlier prepared body) :
    restored.restored.log.archive.events.map SessionEventArchive.ArchivedEvent.raw =
      restored.validated.parsed.lines :=
  restored.archive_raw_eq_lines

theorem source_projection_exact
    {sourceText : String}
    {restored : RestoredTextRunner sourceText}
    {baseUrl : String} {apiKey : ApiKey}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {request : RegistryRequestSource registry}
    {before : Model} {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq}
    {prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
      restored.restored.runner}
    {body : String}
    (_round : EventSchemaProcessRound restored registry request before sourceEventSeqs
      sourcesNodup sourcesEarlier prepared body) :
    Session.protocolProjection restored.validated.validated.final.session.events =
      restored.validated.validated.sequence.protocolTrace.erase :=
  ValidatedJsonLog.projection_exact restored.validated.validated

end EventSchemaProcessRound

/-! ## Restored text and byte entry points -/

inductive EventSchemaProcessError where
  | text (error : TextArchiveError)
  | process (error : SchemaProcessError)
deriving DecidableEq, Repr

def executeRestoredSchemaRound
    (config : ProcessConfig)
    {sourceText : String}
    (restored : RestoredTextRunner sourceText)
    (baseUrl : String)
    (apiKey : ApiKey)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.runner.session.nextSeq) :
    IO (Except EventSchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
          restored.restored.runner =>
        Sigma fun body : String =>
          EventSchemaProcessRound restored registry request before sourceEventSeqs sourcesNodup
            sourcesEarlier prepared body)) := do
  match ← executeRegistrySchemaRound config baseUrl apiKey request before
      restored.restored.runner sourceEventSeqs sourcesNodup sourcesEarlier with
  | .error error => pure (.error (.process error))
  | .ok ⟨prepared, ⟨body, round⟩⟩ =>
      pure (.ok ⟨prepared, ⟨body, {
        round
        restored_session_eq := restored.session_eq
        archive_raw_eq := restored.archive_raw_eq_lines
      }⟩⟩)

def executeRestoredBytesSchemaRound
    (config : ProcessConfig)
    {bytes : ByteArray}
    (restored : RestoredBytesRunner bytes)
    (baseUrl : String)
    (apiKey : ApiKey)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ eventSeq ∈ sourceEventSeqs,
      eventSeq < restored.restored.restored.runner.session.nextSeq) :
    IO (Except EventSchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request
          restored.restored.restored.runner =>
        Sigma fun body : String =>
          EventSchemaProcessRound restored.restored registry request before sourceEventSeqs
            sourcesNodup sourcesEarlier prepared body)) :=
  executeRestoredSchemaRound config restored.restored baseUrl apiKey request before sourceEventSeqs
    sourcesNodup sourcesEarlier

namespace Example

open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekSchemaHarness.Example

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    {sourceText : String} (restored : RestoredTextRunner sourceText) :
    ∀ eventSeq ∈ ([] : List Nat),
      eventSeq < restored.restored.runner.session.nextSeq := by
  simp

def toolTextDualSchemaRoundFromRestored
    (restored : RestoredTextRunner DeepSeekHarnessEventText.toolTextSource)
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except EventSchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest
          (dualRegistryEntries weatherCertificate clockCertificate)
          "https://fixture.invalid" { value := "fixture-key" }
          (dualRequestSource weatherCertificate clockCertificate) restored.restored.runner =>
        Sigma fun body : String =>
          EventSchemaProcessRound restored
            (dualRegistryEntries weatherCertificate clockCertificate)
            (dualRequestSource weatherCertificate clockCertificate) 0 [] (by simp) (by simp)
            prepared body)) :=
  executeRestoredSchemaRound (registry := dualRegistryEntries weatherCertificate clockCertificate)
    dualToolStreamProcess restored "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate) 0 [] (by simp)
    (emptySourcesEarlier restored)

def toolTextDualSchemaRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except (TextArchiveError ⊕ EventSchemaProcessError)
      (Sigma fun restored : RestoredTextRunner DeepSeekHarnessEventText.toolTextSource =>
        Sigma fun prepared : PreparedRegistryStreamingRequest
            (dualRegistryEntries weatherCertificate clockCertificate)
            "https://fixture.invalid" { value := "fixture-key" }
            (dualRequestSource weatherCertificate clockCertificate) restored.restored.runner =>
          Sigma fun body : String =>
            EventSchemaProcessRound restored
              (dualRegistryEntries weatherCertificate clockCertificate)
              (dualRequestSource weatherCertificate clockCertificate) 0 [] (by simp) (by
                simp) prepared body)) := do
  match DeepSeekHarnessEventText.toolTextRestored with
  | .error error => pure (.error (.inl error))
  | .ok restored =>
      match ← toolTextDualSchemaRoundFromRestored restored weatherCertificate clockCertificate with
      | .error error => pure (.error (.inr error))
      | .ok ⟨prepared, ⟨body, round⟩⟩ =>
          pure (.ok ⟨restored, ⟨prepared, ⟨body, round⟩⟩⟩)

end Example

end Cordis.DeepSeekHarnessEventProcessSchema
