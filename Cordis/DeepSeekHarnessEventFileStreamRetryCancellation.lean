import Cordis.DeepSeekHarnessEventText
import Cordis.DeepSeekHarnessPersistenceStreamRetry
import Cordis.DeepSeekStreamHarnessRetryCancellation

/-!
# File-backed current-event restore into process-backed cancellation

This is the next composition boundary above the supported current-Harness event
refinement.  The pinned event JSONL fixture is written to a real temporary file,
read back as bytes, checked for byte equality, decoded through
`DeepSeekHarnessEventText.restoreBytesRunner`, and only then used as the initial
runner for the existing process-backed streamed cancellation trace.

The returned dependent value keeps the file-read bytes, their equality to the
source fixture, the restored event archive/session, a streaming request plan
rebuilt from that session, and the exact cancellation prefix together.  The
request plan has exact build/body equations; it is a reconstruction certificate,
not a claim that the process adapter exposes or authenticates the same request
internally.  The temporary file is removed when `withTempFile` returns; this
remains an executable local boundary, not a theorem about fsync, stable media,
crash recovery, blocked-read interruption, process cleanup, provider
authenticity, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventFileStreamRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessEventText
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekHarnessPersistenceStreamRetry
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryCancellation
open Cordis.DeepSeekStreamHarnessRetryConversation

abbrev SourceBytes : ByteArray := DeepSeekHarnessEventText.toolTextSource.toUTF8
abbrev FixtureCancellation := CancellationPolicy.atRound 1 .timeout
abbrev FixtureRetry := RetryPolicy.default
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureProcess := DeepSeekHarnessPersistenceStreamRetry.persistedProcess
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }
abbrev EmptySources : List Nat := []

theorem emptySources_nodup : EmptySources.Nodup := by
  simp [EmptySources]

theorem emptySources_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ EmptySources, source < current.session.nextSeq := by
  simp [EmptySources]

inductive FileReadError where
  | io (message : String)
  | decode (error : TextArchiveError)
  | mismatch (expected actual : Nat)
deriving Repr

/-- A successful temporary-file read retains the exact bytes used for decoding. -/
structure FileRestored where
  bytes : ByteArray
  bytes_eq_source : bytes = SourceBytes
  restored : RestoredBytesRunner bytes

def restoreFile : IO (Except FileReadError FileRestored) :=
  IO.FS.withTempFile fun _ path => do
    try
      IO.FS.writeBinFile path SourceBytes
      let bytes ← IO.FS.readBinFile path
      if same : bytes = SourceBytes then
        match _restored : restoreBytesRunner bytes 1 1 with
        | .error error => pure (.error (.decode error))
        | .ok value => pure (.ok { bytes, bytes_eq_source := same, restored := value })
      else
        pure (.error (.mismatch SourceBytes.size bytes.size))
    catch error =>
      pure (.error (.io error.toString))

inductive EndToEndError where
  | file (error : FileReadError)
  | request (error : RequestError)
  | retry (error : ConversationError FixtureRetry)

structure FileEventCancellationRun where
  file : FileRestored
  request : TypedRequestPlan .streaming
  request_build_eq :
    buildTypedStreamingRequestPlan FixtureBaseUrl FixtureApiKey FixtureSource
      file.restored.restored.restored.runner.session = .ok request
  finalRunner : ConversationRunner
  finalModel : Nat
  cancellation : RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
    FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
    emptySources_nodup emptySources_earlier
    file.restored.restored.restored.runner 0 finalRunner finalModel

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
            file.restored.restored.restored.runner 0 finalRunner finalModel)) :=
  DeepSeekStreamHarnessRetryCancellation.runWithFinish finish
    (policy := FixtureCancellation) (retryPolicy := FixtureRetry) 2 FixtureProcess
    FixtureBaseUrl FixtureApiKey FixtureSource FixtureConfig EmptySources
    emptySources_nodup emptySources_earlier
    0 file.restored.restored.restored.runner

def runRestored
    (file : FileRestored) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
            FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
            emptySources_nodup emptySources_earlier
            file.restored.restored.restored.runner 0 finalRunner finalModel)) :=
  runRestoredWithFinish (finish := finishMulti) file

def runFixtureWithFinish
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body)) :
    IO (Except EndToEndError FileEventCancellationRun) := do
  match ← restoreFile with
  | .error error => pure (.error (.file error))
  | .ok file =>
      match built : buildTypedStreamingRequestPlan FixtureBaseUrl FixtureApiKey FixtureSource
          file.restored.restored.restored.runner.session with
      | .error error => pure (.error (.request error))
      | .ok request =>
          match ← runRestoredWithFinish finish file with
          | .error error => pure (.error (.retry error))
          | .ok ⟨finalRunner, ⟨finalModel, cancellation⟩⟩ =>
              pure (.ok {
                file
                request
                request_build_eq := built
                finalRunner
                finalModel
                cancellation
              })

def runFixture : IO (Except EndToEndError FileEventCancellationRun) :=
  runFixtureWithFinish (finish := finishMulti)

theorem file_bytes_eq_source (run : FileEventCancellationRun) :
    run.file.bytes = SourceBytes :=
  run.file.bytes_eq_source

theorem restored_session_eq_event_archive (run : FileEventCancellationRun) :
    run.file.restored.restored.restored.runner.session =
      run.file.restored.restored.validated.validated.final.session :=
  RestoredTextRunner.session_eq run.file.restored.restored

theorem request_build (run : FileEventCancellationRun) :
    buildTypedStreamingRequestPlan FixtureBaseUrl FixtureApiKey FixtureSource
        run.file.restored.restored.restored.runner.session = .ok run.request :=
  run.request_build_eq

theorem request_body_eq_source (run : FileEventCancellationRun) :
    run.request.request.body = Lean.Json.compress run.request.source.toJson :=
  run.request.body_eq

def firstToolCalls
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixtureRetry FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey
      FixtureSource EmptySources emptySources_nodup emptySources_earlier
      runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.round.finished.finished.view.rawToolCalls.length

def firstRetryFailures
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixtureRetry FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey
      FixtureSource EmptySources emptySources_nodup emptySources_earlier
      runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.retryHistory.failures.length

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
  traceLength : Nat
  firstToolCalls : Nat
  firstRetryFailures : Nat
  cancelled : Bool
  cancelledRound : Nat
  cancelledReason : String
  finalModel : Nat

def summary (run : FileEventCancellationRun) : ExecutableSummary :=
  {
    sourceBytes := SourceBytes.size
    readBytes := run.file.bytes.size
    initialNextSeq := run.file.restored.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    traceLength := StreamRetryTrace.length run.cancellation.trace
    firstToolCalls := firstToolCalls run.cancellation.trace
    firstRetryFailures := firstRetryFailures run.cancellation.trace
    cancelled := RetryCancellableStop.isCancelled run.cancellation.stop
    cancelledRound := cancelledRoundValue run.cancellation.stop
    cancelledReason := cancelledReasonText run.cancellation.stop
    finalModel := run.finalModel
  }

def executableInitialNextSeq : Nat := 8
def executableFinalNextSeq : Nat := 11
def executableTraceLength : Nat := 1
def executableFirstToolCalls : Nat := 2
def executableFirstRetryFailures : Nat := 0
def executableCancelled : Bool := true
def executableCancelledRound : Nat := 1
def executableCancelledReason : String := "cancelled:timeout"
def executableFinalModel : Nat := 0

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.sourceBytes = value.readBytes &&
    value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.traceLength = executableTraceLength &&
    value.firstToolCalls = executableFirstToolCalls &&
    value.firstRetryFailures = executableFirstRetryFailures &&
    value.cancelled = executableCancelled &&
    value.cancelledRound = executableCancelledRound &&
    value.cancelledReason = executableCancelledReason &&
    value.finalModel = executableFinalModel

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok eventRun => pure (.ok (summary eventRun))

end Cordis.DeepSeekHarnessEventFileStreamRetryCancellation
