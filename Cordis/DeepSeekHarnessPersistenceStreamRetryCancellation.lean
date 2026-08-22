import Cordis.DeepSeekHarnessPersistenceStreamRetry
import Cordis.DeepSeekStreamHarnessRetryCancellation

/-!
# Persisted, process-backed streamed retry cancellation

This module attaches the pre-round cancellation contract to the persisted,
process-backed streamed conversation.  The restored `ConversationRunner` is
the initial index of the retry-aware trace; after one accepted process round,
the cancellation policy stops before the next request and retains the exact
prefix, runner, model, round number, and reason.

The fixture is deliberately a boundary-safe cancellation test.  It proves
that no second request is selected after the decision, but it does not claim
interruption of a blocked process read, HTTP request, stream reader, tool
execution, cleanup of arbitrary processes, durable recovery, provider
authenticity, or deployed Harness cancellation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation

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

/-! ## Fixed fixture indices -/

abbrev FixtureCancellation := CancellationPolicy.atRound 1 .timeout
abbrev FixtureRetry := RetryPolicy.default
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureProcess := DeepSeekHarnessPersistenceStreamRetry.persistedProcess
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def emptySourceEventSeqs : List Nat := []

theorem emptySourceEventSeqs_nodup : emptySourceEventSeqs.Nodup := by
  simp [emptySourceEventSeqs]

theorem emptySourceEventSeqs_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ emptySourceEventSeqs, source < current.session.nextSeq := by
  simp [emptySourceEventSeqs]

/-! ## Errors and dependent result -/

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | retry (error : ConversationError FixtureRetry)

structure PersistedCancellationRun where
  restored : RestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  cancellation : RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
    FixtureConfig
    FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    restored.restored.runner 0 finalRunner finalModel

/-! ## Process-backed continuation with a pre-round cancellation boundary -/

def runRestored
    (restored : RestoredRunner) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry) FixtureConfig
            FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
            emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
            restored.restored.runner 0 finalRunner finalModel)) :=
  DeepSeekStreamHarnessRetryCancellation.run
    (policy := FixtureCancellation) (retryPolicy := FixtureRetry) 2 FixtureProcess
    FixtureBaseUrl FixtureApiKey FixtureSource FixtureConfig emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    0 restored.restored.runner

def runFixture : IO (Except EndToEndError PersistedCancellationRun) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureMemory with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runRestored restored with
      | .error error => pure (.error (.retry error))
      | .ok ⟨finalRunner, ⟨finalModel, cancellation⟩⟩ =>
          pure (.ok {
            restored
            finalRunner
            finalModel
            cancellation
          })

/-! ## Proof projections -/

theorem restored_session_eq_archive (run : PersistedCancellationRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

/-! ## Executable projections -/

def firstToolCalls
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixtureRetry FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey
      FixtureSource emptySourceEventSeqs emptySourceEventSeqs_nodup
      emptySourceEventSeqs_earlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.round.finished.finished.view.rawToolCalls.length

def firstRetryFailures
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixtureRetry FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey
      FixtureSource emptySourceEventSeqs emptySourceEventSeqs_nodup
      emptySourceEventSeqs_earlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.retryHistory.failures.length

def cancelledRoundValue
    {finalRunner : ConversationRunner} {finalModel : Nat} :
    RetryCancellableStop FixtureCancellation (retryPolicy := FixtureRetry) FixtureConfig
      FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
      emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier finalRunner finalModel → Nat
  | .cancelled round .. => round
  | .completed .. | .fuelExhausted => 0

def cancelledReasonText
    {finalRunner : ConversationRunner} {finalModel : Nat} :
    RetryCancellableStop FixtureCancellation (retryPolicy := FixtureRetry) FixtureConfig
      FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
      emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier finalRunner finalModel → String
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

def summary (run : PersistedCancellationRun) : ExecutableSummary :=
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
  | .ok persisted => pure (.ok (summary persisted))

end Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation
