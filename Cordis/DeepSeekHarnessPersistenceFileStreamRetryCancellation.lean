import Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation

/-!
# File-backed persisted process cancellation

This module is the filesystem sibling of
`DeepSeekHarnessPersistenceStreamRetryCancellation`.  The logical archive is
written to an actual temporary file, read back through the byte/UTF-8/JSONL
certificate, and only then used as the initial index of the process-backed
streaming cancellation trace.  The result keeps the read certificate beside
the dependent runner and cancellation endpoint, so the executable path cannot
silently replace the file read with an injected in-memory session.

`IO.FS.withTempFile` gives this fixture a real filesystem read and flush, but
the temporary file is intentionally deleted when the fixture returns.  This
does not claim fsync, stable media, crash recovery, blocked-read interruption,
process cleanup, provider authenticity, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceFileStreamRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekHarnessPersistenceStreamRetry
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryCancellation
open Cordis.DeepSeekStreamHarnessRetryConversation

/-! ## The same indexed fixture, with a filesystem-origin marker -/

abbrev FixtureCancellation :=
  DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureCancellation
abbrev FixtureRetry := DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureRetry
abbrev FixtureConfig := DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureConfig
abbrev FixtureSource := DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureSource
abbrev FixtureProcess := DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureProcess
abbrev FixtureBaseUrl := DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureBaseUrl
abbrev FixtureApiKey := DeepSeekHarnessPersistenceStreamRetryCancellation.FixtureApiKey
abbrev EmptySources :=
  DeepSeekHarnessPersistenceStreamRetryCancellation.emptySourceEventSeqs

theorem emptySources_nodup : EmptySources.Nodup := by
  exact DeepSeekHarnessPersistenceStreamRetryCancellation.emptySourceEventSeqs_nodup

theorem emptySources_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ EmptySources, source < current.session.nextSeq := by
  exact DeepSeekHarnessPersistenceStreamRetryCancellation.emptySourceEventSeqs_earlier

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | retry (error : ConversationError FixtureRetry)

structure FilePersistedCancellationRun where
  restored : RestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  cancellation : RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
    FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
    emptySources_nodup emptySources_earlier restored.restored.runner 0 finalRunner finalModel

def runRestored
    (restored : RestoredRunner) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
            FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource EmptySources
            emptySources_nodup emptySources_earlier
            restored.restored.runner 0 finalRunner finalModel)) :=
  DeepSeekStreamHarnessRetryCancellation.run
    (policy := FixtureCancellation) (retryPolicy := FixtureRetry) 2 FixtureProcess
    FixtureBaseUrl FixtureApiKey FixtureSource FixtureConfig EmptySources
    emptySources_nodup emptySources_earlier
    0 restored.restored.runner

def runFixture : IO (Except EndToEndError FilePersistedCancellationRun) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureFile with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runRestored restored with
      | .error error => pure (.error (.retry error))
      | .ok ⟨finalRunner, ⟨finalModel, cancellation⟩⟩ =>
          pure (.ok { restored, finalRunner, finalModel, cancellation })

/-! ## The file-backed read remains the exact logical archive endpoint -/

theorem restored_session_eq_file_archive (run : FilePersistedCancellationRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

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
  initialNextSeq : Nat
  finalNextSeq : Nat
  traceLength : Nat
  firstToolCalls : Nat
  firstRetryFailures : Nat
  cancelled : Bool
  cancelledRound : Nat
  cancelledReason : String
  finalModel : Nat
  storage : String

def summary (run : FilePersistedCancellationRun) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    traceLength := StreamRetryTrace.length run.cancellation.trace
    firstToolCalls := firstToolCalls run.cancellation.trace
    firstRetryFailures := firstRetryFailures run.cancellation.trace
    cancelled := RetryCancellableStop.isCancelled run.cancellation.stop
    cancelledRound := cancelledRoundValue run.cancellation.stop
    cancelledReason := cancelledReasonText run.cancellation.stop
    finalModel := run.finalModel
    storage := "temporary-file"
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
def executableStorage : String := "temporary-file"

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.traceLength = executableTraceLength &&
    value.firstToolCalls = executableFirstToolCalls &&
    value.firstRetryFailures = executableFirstRetryFailures &&
    value.cancelled = executableCancelled &&
    value.cancelledRound = executableCancelledRound &&
    value.cancelledReason = executableCancelledReason &&
    value.finalModel = executableFinalModel &&
    value.storage = executableStorage

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok persisted => pure (.ok (summary persisted))

end Cordis.DeepSeekHarnessPersistenceFileStreamRetryCancellation
