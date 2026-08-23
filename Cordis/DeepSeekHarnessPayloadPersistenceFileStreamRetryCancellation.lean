import Cordis.DeepSeekHarnessPayloadPersistence
import Cordis.DeepSeekHarnessPayloadPersistenceStreamRetryCancellation
import Cordis.HarnessPersistenceIO
import Cordis.TextRefinement

/-!
# File-backed payload-preserving process cancellation

This module composes the lossless payload ledger with a real temporary-file read and the
process-backed pre-round cancellation prefix.  The file is written from the canonical persisted
JSONL fixture, read back as bytes through `DurableIO.FileBackend`, validated as JSONL, enriched with
payload rows, and only then used as the initial index of the dependent cancellation trace.

The result retains the exact source/read-byte equality, restored session, payload ledger, typed
timeout prefix, and final runner/model endpoint.  The temporary file is deleted when the fixture
returns; this does not claim fsync, stable media, crash recovery, blocked-read interruption,
process cleanup, provider authenticity, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadPersistenceFileStreamRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessPayloadPersistence
open Cordis.DeepSeekHarnessPayloadPersistenceStreamRetryCancellation
open Cordis.DeepSeekHarnessPersistence
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryCancellation
open Cordis.DeepSeekStreamHarnessRetryConversation
open Cordis.HarnessPersistenceIO
open Cordis.HarnessPersistenceRefinement
open Cordis.SessionPayloadArchive
open Cordis.TextRefinement

/-! ## Fixed source and dependent file read -/

abbrev SourceRows : List Lean.Json := DeepSeekHarnessPersistence.persistedToolInput
abbrev SourceText : String := TextRefinement.renderJsonLines SourceRows
abbrev SourceBytes : ByteArray := SourceText.toUTF8

abbrev FixtureCancellation :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureCancellation
abbrev FixtureRetry :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureRetry
abbrev FixtureConfig :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureConfig
abbrev FixtureSource :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureSource
abbrev FixtureProcess :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureProcess
abbrev FixtureBaseUrl :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureBaseUrl
abbrev FixtureApiKey :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.FixtureApiKey
abbrev EmptySources :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.emptySourceEventSeqs

theorem emptySources_nodup : EmptySources.Nodup := by
  exact DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.emptySourceEventSeqs_nodup

theorem emptySources_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ EmptySources, source < current.session.nextSeq := by
  exact DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.emptySourceEventSeqs_earlier

inductive FileReadError where
  | io (message : String)
  | mismatch (expected actual : Nat)
  | certificateMismatch (expected actual : Nat)
  | store (error : HarnessPersistenceIO.StoreError)
  | payload (error : DeepSeekHarnessPayloadPersistence.PayloadError)
deriving Repr

structure FileRestored where
  bytes : ByteArray
  bytes_eq_source : bytes = SourceBytes
  read : HarnessPersistenceIO.ReadCertificate
  restored : ReadRestoredRunner
  restored_read_eq : restored.read = read
  read_bytes_eq_file : DurableIO.toByteArray read.bytes = bytes

theorem restoreRead_read
    (read : HarnessPersistenceIO.ReadCertificate)
    (turn step : Nat)
    {restored : ReadRestoredRunner}
    (h : restoreRead read turn step = .ok restored) :
    restored.read = read := by
  unfold Cordis.DeepSeekHarnessPayloadPersistence.restoreRead at h
  split at h <;> try contradiction
  next payload hp =>
    injection h with hrest
    cases hrest
    rfl

def restoreFile : IO (Except FileReadError FileRestored) :=
  IO.FS.withTempFile fun _ path => do
    try
      IO.FS.writeBinFile path SourceBytes
      let bytes ← IO.FS.readBinFile path
      if same : bytes = SourceBytes then
        match ← HarnessPersistenceIO.readValidated (DurableIO.FileBackend.mk path).backend with
        | .error error => pure (.error (.store error))
        | .ok read =>
            if readSame : DurableIO.toByteArray read.bytes = bytes then
              match restoredEq : restoreRead read 1 1 with
              | .error error => pure (.error (.payload error))
              | .ok restored =>
                  pure (.ok {
                    bytes
                    bytes_eq_source := same
                    read
                    restored
                    restored_read_eq := restoreRead_read read 1 1 restoredEq
                    read_bytes_eq_file := readSame
                  })
            else
              pure (.error (.certificateMismatch SourceBytes.size read.bytes.length))
      else
        pure (.error (.mismatch SourceBytes.size bytes.size))
    catch error =>
      pure (.error (.io error.toString))

/-! ## File-backed cancellation result -/

inductive EndToEndError where
  | file (error : FileReadError)
  | retry (error : ConversationError FixtureRetry)

structure FilePayloadCancellationRun where
  file : FileRestored
  finalRunner : ConversationRunner
  finalModel : Nat
  cancellation : RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
    FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
    emptySources_nodup emptySources_earlier file.restored.restored.runner 0 finalRunner finalModel

def runRestoredWithFinish
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (file : FileRestored) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
            FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
            emptySources_nodup emptySources_earlier
            file.restored.restored.runner 0 finalRunner finalModel)) :=
  DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.runRestoredWithFinish
    finish file.restored

def runRestored (file : FileRestored) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
            FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
            emptySources_nodup emptySources_earlier
            file.restored.restored.runner 0 finalRunner finalModel)) :=
  runRestoredWithFinish finishMulti file

def runFixtureWithFinish
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body)) :
    IO (Except EndToEndError FilePayloadCancellationRun) := do
  match ← restoreFile with
  | .error error => pure (.error (.file error))
  | .ok file =>
      match ← runRestoredWithFinish finish file with
      | .error error => pure (.error (.retry error))
      | .ok ⟨finalRunner, ⟨finalModel, cancellation⟩⟩ =>
          pure (.ok { file, finalRunner, finalModel, cancellation })

def runFixture : IO (Except EndToEndError FilePayloadCancellationRun) :=
  runFixtureWithFinish finishMulti

/-! ## Exact file, session, and payload projections -/

theorem file_bytes_eq_source (run : FilePayloadCancellationRun) :
    run.file.bytes = SourceBytes :=
  run.file.bytes_eq_source

theorem read_bytes_eq_source (run : FilePayloadCancellationRun) :
    DurableIO.toByteArray run.file.restored.read.bytes = SourceBytes := by
  rw [run.file.restored_read_eq]
  exact run.file.read_bytes_eq_file.trans run.file.bytes_eq_source

theorem restored_session_eq_file_archive (run : FilePayloadCancellationRun) :
    run.file.restored.restored.runner.session =
      run.file.restored.read.validated.validated.final.session :=
  ReadRestoredRunner.session_eq_read run.file.restored

theorem restored_payload_raw_eq_expanded (run : FilePayloadCancellationRun) :
    run.file.restored.restored.payload.events.map EnrichedEvent.raw =
      run.file.restored.read.validated.expandedEvents :=
  ReadRestoredRunner.payload_raw_eq_expanded run.file.restored

theorem restored_payload_length_eq (run : FilePayloadCancellationRun) :
    run.file.restored.restored.payload.events.length =
      run.file.restored.read.validated.expandedEvents.length := by
  have hEvents := congrArg ValidatedPersistedJson.expandedEvents run.file.restored.archive_eq
  have hLength := RestoredRunner.payload_length_eq run.file.restored.restored
  exact hLength.trans (congrArg List.length hEvents)

/-! ## Executable cancellation projections -/

def firstToolCalls
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixtureRetry FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey
      FixtureSource EmptySources emptySources_nodup emptySources_earlier
      runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.round.finished.finished.view.rawToolCalls.length

def cancelledRoundValue
    {finalRunner : ConversationRunner} {finalModel : Nat} :
    RetryCancellableStop FixtureCancellation (retryPolicy := FixtureRetry) FixtureConfig
      FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
      emptySources_nodup emptySources_earlier finalRunner finalModel → Nat
  | .cancelled round .. => round
  | .completed .. | .fuelExhausted => 0

def cancelledReasonText
    {finalRunner : ConversationRunner} {finalModel : Nat} :
    RetryCancellableStop FixtureCancellation (retryPolicy := FixtureRetry) FixtureConfig
      FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
      emptySources_nodup emptySources_earlier finalRunner finalModel → String
  | .cancelled _ reason _ => reasonText reason
  | .completed .. | .fuelExhausted => "not-cancelled"

structure ExecutableSummary where
  sourceBytes : Nat
  readBytes : Nat
  initialNextSeq : Nat
  finalNextSeq : Nat
  payloadLength : Nat
  traceLength : Nat
  firstToolCalls : Nat
  cancelled : Bool
  cancelledRound : Nat
  cancelledReason : String
  finalModel : Nat
deriving BEq, DecidableEq, Repr

def summary (run : FilePayloadCancellationRun) : ExecutableSummary :=
  {
    sourceBytes := SourceBytes.size
    readBytes := run.file.bytes.size
    initialNextSeq := run.file.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    payloadLength := run.file.restored.restored.payload.events.length
    traceLength := StreamRetryTrace.length run.cancellation.trace
    firstToolCalls := firstToolCalls run.cancellation.trace
    cancelled := RetryCancellableStop.isCancelled run.cancellation.stop
    cancelledRound := cancelledRoundValue run.cancellation.stop
    cancelledReason := cancelledReasonText run.cancellation.stop
    finalModel := run.finalModel
  }

def executableInitialNextSeq : Nat := 8
def executableFinalNextSeq : Nat := 11
def executablePayloadLength : Nat := 8
def executableTraceLength : Nat := 1
def executableFirstToolCalls : Nat := 2
def executableCancelled : Bool := true
def executableCancelledRound : Nat := 1
def executableCancelledReason : String := "cancelled:timeout"
def executableFinalModel : Nat := 0

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.sourceBytes = value.readBytes &&
    value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.payloadLength = executablePayloadLength &&
    value.traceLength = executableTraceLength &&
    value.firstToolCalls = executableFirstToolCalls &&
    value.cancelled = executableCancelled &&
    value.cancelledRound = executableCancelledRound &&
    value.cancelledReason = executableCancelledReason &&
    value.finalModel = executableFinalModel

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ←
      Cordis.DeepSeekHarnessPayloadPersistenceFileStreamRetryCancellation.runFixture with
  | .error error => pure (.error error)
  | .ok persisted =>
      pure (.ok
        (Cordis.DeepSeekHarnessPayloadPersistenceFileStreamRetryCancellation.summary persisted))

end Cordis.DeepSeekHarnessPayloadPersistenceFileStreamRetryCancellation
