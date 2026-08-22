import Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
import Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation
import Cordis.DeepSeekSchemaRegistry
import Cordis.DeepSeekToolSchema

/-!
# Current-event file restore into loopback heterogeneous SSE

This module composes the supported current-Harness event archive with the real loopback
HTTP/SSE byte-prefix conversation.  The temporary-file restore supplies the initial
`ConversationRunner`; the local server then emits a heterogeneous weather/clock tool
round followed by a terminal streamed response.  The result retains the file bytes,
archive/session equality, scoped registry, request-indexed byte evidence, dependent
tool execution, and final session endpoint together.

The fixture is deliberately local and finite.  It does not claim provider obedience,
credential authenticity, durable storage, blocked-read cancellation, reconnects,
external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventFileLocalSseSchema

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekHarnessLocalSse
open Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation
open Cordis.DeepSeekProcessScopedRequestBytePrefixConversation
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekToolSchema

abbrev SourceBytes : ByteArray :=
  DeepSeekHarnessEventFileStreamRetryCancellation.SourceBytes

abbrev FileRestored :=
  DeepSeekHarnessEventFileStreamRetryCancellation.FileRestored

abbrev FileSession (file : FileRestored) : Session.Session Session.noExtensions :=
  file.restored.restored.restored.runner.session

abbrev Source
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition Example.clockTool) :
    Cordis.DeepSeekHarness.RequestSource :=
  let source := Cordis.DeepSeekSchemaConversation.Example.dualRequestSource
    weatherCertificate clockCertificate |>.source
  { source with model := "deterministic-counter" }

abbrev Registry
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition Example.clockTool) :
    ScopedRegistry Example.dualConfig :=
  Cordis.DeepSeekScopedRegistry.Example.scopedRegistry weatherCertificate clockCertificate

abbrev Key : ApiKey := { value := "fixture-key" }

structure FileSseSchemaRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition Example.clockTool) where
  file : FileRestored
  loopback : LocalConversationResult
    (Registry weatherCertificate clockCertificate)
    Cordis.DeepSeekScopedRegistry.Example.approvalPolicy Key
    (Source weatherCertificate clockCertificate)
    0 (FileSession file)
  outcome : ConversationResult
    (Registry weatherCertificate clockCertificate)
    Cordis.DeepSeekScopedRegistry.Example.approvalPolicy
    (Cordis.DeepSeekHarnessLocalSse.localBaseUrl loopback.port) Key
    (Source weatherCertificate clockCertificate)
  outcome_eq : loopback.outcome = .ok outcome

inductive EndToEndError where
  | file (error : FileReadError)
  | conversation
  | certificate
deriving Repr

def runFileRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition Example.clockTool)
    (file : FileRestored) :
    IO (Except EndToEndError (FileSseSchemaRun weatherCertificate clockCertificate)) := do
  let registry := Registry weatherCertificate clockCertificate
  let source := Source weatherCertificate clockCertificate
  match ← runWithKey registry Cordis.DeepSeekScopedRegistry.Example.approvalPolicy Key source 0
      file.restored.restored.restored.runner.session 2 2 4096 1 with
  | .error _ => pure (.error .conversation)
  | .ok loopback =>
      match outcome_eq : loopback.outcome with
      | .error _ => pure (.error .conversation)
      | .ok outcome => pure (.ok { file, loopback, outcome, outcome_eq })

def runFixture : IO (Except EndToEndError
    (Sigma fun weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool =>
      Sigma fun clockCertificate : ValidatedToolDefinition Example.clockTool =>
        FileSseSchemaRun weatherCertificate clockCertificate)) := do
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error _ => pure (.error .certificate)
  | .ok weatherCertificate =>
      match Example.clockToolCertificate with
      | .error _ => pure (.error .certificate)
      | .ok clockCertificate =>
          match ← restoreFile with
          | .error error => pure (.error (.file error))
          | .ok file =>
              match ← runFileRound weatherCertificate clockCertificate file with
              | .error error => pure (.error error)
              | .ok run => pure (.ok ⟨weatherCertificate, ⟨clockCertificate, run⟩⟩)

theorem file_bytes_eq_source
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSseSchemaRun weatherCertificate clockCertificate) :
    run.file.bytes = SourceBytes :=
  run.file.bytes_eq_source

theorem restored_session_eq_event_archive
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSseSchemaRun weatherCertificate clockCertificate) :
    FileSession run.file =
      run.file.restored.restored.validated.validated.final.session :=
  RestoredTextRunner.session_eq run.file.restored.restored

theorem server_exited_successfully
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSseSchemaRun weatherCertificate clockCertificate) :
    run.loopback.serverExit = 0 :=
  run.loopback.server_exit_eq

theorem server_requests_match
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSseSchemaRun weatherCertificate clockCertificate)
    {expected : Nat}
    (requests_eq : run.loopback.requests = expected)
    (valid_eq : run.loopback.validRequests = expected) :
    run.loopback.requests = run.loopback.validRequests :=
  LocalConversationResult.server_requests_are_valid run.loopback requests_eq valid_eq

theorem successful_outcome
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSseSchemaRun weatherCertificate clockCertificate) :
    run.loopback.outcome = .ok run.outcome :=
  run.outcome_eq

structure Summary where
  sourceBytes : Nat
  readBytes : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  requests : Nat
  validRequests : Nat
  rounds : Nat
  allByteComplete : Bool
  distinctBodies : Bool
  manyFirstChunks : Bool
  finalModel : Nat
  completed : Bool
  prefixStopped : Bool
deriving BEq, DecidableEq, Repr

def summaryForRun
    {weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool}
    {clockCertificate : ValidatedToolDefinition Example.clockTool}
    (run : FileSseSchemaRun weatherCertificate clockCertificate) : Summary :=
  {
    sourceBytes := SourceBytes.size
    readBytes := run.file.bytes.size
    initialNextSeq := (FileSession run.file).nextSeq
    finalNextSeq := run.outcome.session.nextSeq
    requests := run.loopback.requests
    validRequests := run.loopback.validRequests
    rounds := run.outcome.rounds.length
    allByteComplete :=
      Cordis.DeepSeekProcessScopedRequestBytePrefixConversation.RoundWitness.allByteComplete
        run.outcome.rounds
    distinctBodies :=
      Cordis.DeepSeekProcessScopedRequestBytePrefixConversation.RoundWitness.firstTwoBodiesDistinct
        run.outcome.rounds
    manyFirstChunks :=
      Cordis.DeepSeekProcessScopedRequestBytePrefixConversation.RoundWitness.firstHasManyByteChunks
        run.outcome.rounds
    finalModel := run.outcome.finalModel
    completed :=
      !ConversationStop.isFuelExhausted run.outcome.stop &&
      !ConversationStop.isPrefixFuelExhausted run.outcome.stop
    prefixStopped :=
      ConversationStop.isPrefixFuelExhausted run.outcome.stop
  }

def expectedSummary : Summary :=
  {
    sourceBytes := SourceBytes.size
    readBytes := SourceBytes.size
    initialNextSeq := 8
    finalNextSeq := 12
    requests := 2
    validRequests := 2
    rounds := 2
    allByteComplete := true
    distinctBodies := true
    manyFirstChunks := true
    finalModel := 0
    completed := true
    prefixStopped := false
  }

def summaryMatches (value : Summary) : Bool := value == expectedSummary

def runSummary : IO (Except EndToEndError Summary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok ⟨_, ⟨_, run⟩⟩ => pure (.ok (summaryForRun run))

end Cordis.DeepSeekHarnessEventFileLocalSseSchema
