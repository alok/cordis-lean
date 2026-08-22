import Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
import Cordis.DeepSeekHarnessEventProcessSchema
import Cordis.DeepSeekSchemaRegistry
import Cordis.DeepSeekToolSchema

/-!
# Current-event file restore into heterogeneous schema processing

This module composes the supported current-Harness event archive with the dependent
weather/clock schema process.  The event JSONL fixture is written to a temporary file,
read back through the byte/UTF-8/JSONL certificate, and only then used as the index of
the registry-derived request plan and schema-dispatched process step.

The result keeps the file bytes, restored archive/session, prepared streaming plan,
complete response body, heterogeneous tool step, and final dependent runner endpoint
together.  It does not claim provider obedience, credential authenticity, durable file
storage, byte framing, cancellation, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventFileProcessSchema

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
open Cordis.DeepSeekHarnessEventProcessSchema
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekHarnessProcessSchema
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekToolSchema

abbrev SourceBytes : ByteArray :=
  DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes

abbrev FileRestored :=
  DeepSeekHarnessEventFileStreamRetryCancellation.FileRestored

abbrev FixtureBaseUrl : String := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def executeFileRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition Example.clockTool)
    (file : FileRestored) :
    IO (Except EventSchemaProcessError
      (Sigma fun prepared : PreparedRegistryStreamingRequest
          (Example.dualRegistryEntries weatherCertificate clockCertificate)
          FixtureBaseUrl FixtureApiKey
          (Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
            weatherCertificate clockCertificate)
          file.restored.restored.restored.runner =>
        Sigma fun body : String =>
          EventSchemaProcessRound file.restored.restored
            (Example.dualRegistryEntries weatherCertificate clockCertificate)
            (Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
              weatherCertificate clockCertificate)
            0 [] (by simp) (by simp) prepared body)) :=
  executeRestoredSchemaRound (cfg := Example.dualConfig)
    (registry := Example.dualRegistryEntries weatherCertificate clockCertificate)
    dualToolStreamProcess file.restored.restored FixtureBaseUrl FixtureApiKey
    (Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
      weatherCertificate clockCertificate) 0 [] (by simp) (by simp)

structure FileSchemaProcessRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition Example.clockTool) where
  file : FileRestored
  prepared : PreparedRegistryStreamingRequest
      (Example.dualRegistryEntries weatherCertificate clockCertificate)
      FixtureBaseUrl FixtureApiKey
      (Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
        weatherCertificate clockCertificate)
      file.restored.restored.restored.runner
  body : String
  round : EventSchemaProcessRound file.restored.restored
      (Example.dualRegistryEntries weatherCertificate clockCertificate)
      (Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
        weatherCertificate clockCertificate)
      0 [] (by simp) (by simp) prepared body

inductive EndToEndError where
  | file (error : FileReadError)
  | weather (error : ToolSchemaError)
  | clock (error : ToolSchemaError)
  | process (error : EventSchemaProcessError)
deriving Repr

abbrev FixtureResult :=
  Sigma fun weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool =>
    Sigma fun clockCertificate : ValidatedToolDefinition Example.clockTool =>
      FileSchemaProcessRun weatherCertificate clockCertificate

def runFixture : IO (Except EndToEndError FixtureResult) := do
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => pure (.error (.weather error))
  | .ok weatherCertificate =>
      match Example.clockToolCertificate with
      | .error error => pure (.error (.clock error))
      | .ok clockCertificate =>
          match ← restoreFile with
          | .error error => pure (.error (.file error))
          | .ok file =>
              match ← executeFileRound weatherCertificate clockCertificate file with
              | .error error => pure (.error (.process error))
              | .ok ⟨prepared, ⟨body, round⟩⟩ =>
                  pure (.ok ⟨weatherCertificate, ⟨clockCertificate, {
                    file
                    prepared
                    body
                    round
                  }⟩⟩)

theorem file_bytes_eq_source
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    run.file.bytes = SourceBytes :=
  run.file.bytes_eq_source

theorem restored_session_eq_event_archive
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    run.file.restored.restored.restored.runner.session =
      run.file.restored.restored.validated.validated.final.session :=
  RestoredTextRunner.session_eq run.file.restored.restored

theorem plan_source_stream
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    run.prepared.plan.source.stream = true :=
  EventSchemaProcessRound.plan_source_stream run.round

theorem plan_body_eq_source
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    run.prepared.plan.request.body =
      Lean.Json.compress run.prepared.plan.source.toJson :=
  EventSchemaProcessRound.plan_body_eq_source run.round

theorem request_build_eq_validated_session
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    CertifiedRequestSource.buildTypedStreamingRequestPlan FixtureBaseUrl FixtureApiKey
        (registryCertifiedRequestSource
          (Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
            weatherCertificate clockCertificate))
        run.file.restored.restored.validated.validated.final.session =
      .ok run.prepared.plan :=
  EventSchemaProcessRound.request_build_eq_validated_session run.round

theorem processed_exact
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    processedStep run.round.round.step = run.round.round.processed :=
  EventSchemaProcessRound.processed_exact run.round

theorem archive_raw_eq_source
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    run.file.restored.restored.restored.log.archive.events.map
          SessionEventArchive.ArchivedEvent.raw =
      run.file.restored.restored.validated.parsed.lines :=
  EventSchemaProcessRound.archive_raw_eq_source run.round

theorem source_projection_exact
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) :
    Session.protocolProjection run.file.restored.restored.validated.validated.final.session.events =
      run.file.restored.restored.validated.validated.sequence.protocolTrace.erase :=
  EventSchemaProcessRound.source_projection_exact run.round

structure Summary where
  sourceBytes : Nat
  readBytes : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  toolCount : Nat
  registryTools : Nat
  streaming : Bool
  finalModel : Nat
  toolStep : Bool
deriving BEq, DecidableEq, Repr

def summaryForRun
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSchemaProcessRun weatherCertificate clockCertificate) : Summary :=
  match run.round.round.step with
  | .terminal _ => {
      sourceBytes := SourceBytes.size
      readBytes := run.file.bytes.size
      initialNextSeq := run.file.restored.restored.restored.runner.session.nextSeq
      finalNextSeq := 0
      toolCount := 0
      registryTools := run.prepared.plan.source.tools.length
      streaming := run.prepared.plan.source.stream
      finalModel := 0
      toolStep := false
    }
  | .tools result => {
      sourceBytes := SourceBytes.size
      readBytes := run.file.bytes.size
      initialNextSeq := run.file.restored.restored.restored.runner.session.nextSeq
      finalNextSeq := result.runner.session.nextSeq
      toolCount := result.calls.length
      registryTools := run.prepared.plan.source.tools.length
      streaming := run.prepared.plan.source.stream
      finalModel := result.finalModel
      toolStep := true
    }

def expectedSummary : Summary := {
  sourceBytes := SourceBytes.size
  readBytes := SourceBytes.size
  initialNextSeq := 8
  finalNextSeq := 11
  toolCount := 2
  registryTools := 2
  streaming := true
  finalModel := 0
  toolStep := true
}

def summaryMatches (value : Summary) : Bool := value == expectedSummary

def runSummary : IO (Except EndToEndError Summary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok ⟨_, ⟨_, run⟩⟩ => pure (.ok (summaryForRun run))

end Cordis.DeepSeekHarnessEventFileProcessSchema
