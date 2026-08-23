import Cordis.DeepSeekHarnessCancellation
import Cordis.DeepSeekHarnessPayloadPersistence
import Cordis.DeepSeekHarnessPayloadPersistenceStreamRetry
import Cordis.DeepSeekStreamHarnessRetryCancellation

/-!
# Payload-preserving persisted streamed retry cancellation

This module attaches the pre-round cancellation contract to the payload-preserving persisted
process/retry continuation.  The restored runner and lossless payload ledger remain attached to
the exact accepted prefix; after one process-backed tool round, the cancellation policy stops
before selecting the next request and retains the final runner/model and reason.

This is a boundary-safe cancellation certificate.  It does not claim interruption of a blocked
process read, HTTP request, stream reader, tool execution, arbitrary process cleanup, durable
recovery, external effects, or deployed Harness cancellation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadPersistenceStreamRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessPayloadPersistence
open Cordis.DeepSeekHarnessPayloadPersistenceStreamRetry
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryCancellation
open Cordis.DeepSeekStreamHarnessRetryConversation
open Cordis.HarnessPersistenceRefinement
open Cordis.SessionPayloadArchive

/-! ## Fixed fixture indices -/

abbrev FixtureCancellation := CancellationPolicy.atRound 1 .timeout
abbrev FixtureRetry := RetryPolicy.default
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureProcess := persistedProcess
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def emptySourceEventSeqs : List Nat := []

theorem emptySourceEventSeqs_nodup : emptySourceEventSeqs.Nodup := by
  simp [emptySourceEventSeqs]

theorem emptySourceEventSeqs_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ emptySourceEventSeqs, source < current.session.nextSeq := by
  simp [emptySourceEventSeqs]

/-! ## Errors and dependent cancellation result -/

inductive EndToEndError where
  | store (error : StoreError)
  | retry (error : ConversationError FixtureRetry)

structure PersistedPayloadCancellationRun where
  restored : ReadRestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  cancellation : RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
    FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    restored.restored.runner 0 finalRunner finalModel

/-! ## Process-backed continuation with a pre-round cancellation boundary -/

def runRestoredWithFinish
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
    (restored : ReadRestoredRunner) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
            FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource
            emptySourceEventSeqs emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
            restored.restored.runner 0 finalRunner finalModel)) :=
  runWithFinish finish (policy := FixtureCancellation) (retryPolicy := FixtureRetry) 2
    FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource FixtureConfig emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier 0 restored.restored.runner

def runRestored (restored : ReadRestoredRunner) :
    IO (Except (ConversationError FixtureRetry)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          RetryCancellableRunResult FixtureCancellation (retryPolicy := FixtureRetry)
            FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey FixtureSource
            emptySourceEventSeqs emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
            restored.restored.runner 0 finalRunner finalModel)) :=
  runRestoredWithFinish finishMulti restored

def runFixtureWithFinish
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body)) :
    IO (Except EndToEndError PersistedPayloadCancellationRun) := do
  match ← fixtureMemory with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runRestoredWithFinish finish restored with
      | .error error => pure (.error (.retry error))
      | .ok ⟨finalRunner, ⟨finalModel, cancellation⟩⟩ =>
          pure (.ok {
            restored
            finalRunner
            finalModel
            cancellation
          })

def runFixture : IO (Except EndToEndError PersistedPayloadCancellationRun) :=
  runFixtureWithFinish finishMulti

/-! ## Proof projections -/

theorem restored_session_eq_archive (run : PersistedPayloadCancellationRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  ReadRestoredRunner.session_eq_read run.restored

theorem restored_payload_raw_eq_expanded (run : PersistedPayloadCancellationRun) :
    run.restored.restored.payload.events.map EnrichedEvent.raw =
      run.restored.read.validated.expandedEvents :=
  ReadRestoredRunner.payload_raw_eq_expanded run.restored

theorem restored_payload_length_eq (run : PersistedPayloadCancellationRun) :
    run.restored.restored.payload.events.length =
      run.restored.read.validated.expandedEvents.length := by
  have hEvents := congrArg ValidatedPersistedJson.expandedEvents run.restored.archive_eq
  have hLength := RestoredRunner.payload_length_eq run.restored.restored
  exact hLength.trans (congrArg List.length hEvents)

/-! ## Executable projections -/

def firstToolCalls
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixtureRetry FixtureConfig FixtureProcess FixtureBaseUrl FixtureApiKey
      FixtureSource emptySourceEventSeqs emptySourceEventSeqs_nodup
      emptySourceEventSeqs_earlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.round.finished.finished.view.rawToolCalls.length

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
  payloadLength : Nat
  traceLength : Nat
  firstToolCalls : Nat
  cancelled : Bool
  cancelledRound : Nat
  cancelledReason : String
  finalModel : Nat
deriving BEq, DecidableEq, Repr

def summary (run : PersistedPayloadCancellationRun) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    payloadLength := run.restored.restored.payload.events.length
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
  match ← Cordis.DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.runFixture with
  | .error error => pure (.error error)
  | .ok persisted =>
      pure (.ok
        (Cordis.DeepSeekHarnessPayloadPersistenceStreamRetryCancellation.summary persisted))

end Cordis.DeepSeekHarnessPayloadPersistenceStreamRetryCancellation
