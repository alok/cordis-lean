import Cordis.DeepSeekHarnessPayloadPersistence
import Cordis.DeepSeekStreamHarnessRetryConversation

/-!
# Payload-preserving persisted streamed retry conversation

This module composes the lossless payload-preserving restore boundary with the existing
process-backed, fuel-bounded streamed retry conversation.  The restored runner remains the
initial index of the dependent retry trace, while the payload ledger remains attached to the same
validated archive.  Every successful result therefore carries the restored session/payload
equations beside the two-round tool/text continuation and final runner endpoint.

The fixture is deterministic local process evidence.  It does not prove provider authenticity,
durable filesystem recovery, backoff or idempotency, blocked-read cancellation, external tool
trust, or equivalence to the deployed TypeScript Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadPersistenceStreamRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPayloadPersistence
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryConversation
open Cordis.HarnessPersistenceRefinement
open Cordis.SessionPayloadArchive

/-! ## Fixed fixture indices -/

abbrev FixturePolicy := RetryPolicy.default
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def persistedProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "body=$(cat); case \"$body\" in " ++
      "*'[true,0]'*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; " ++
      "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; esac",
    "cordis-payload-persisted-stream-retry-fixture",
    DeepSeekRichStream.exampleTextStreamBody,
    DeepSeekStreamHarness.counterMultiToolStreamBody
  ]

def emptySourceEventSeqs : List Nat := []

theorem emptySourceEventSeqs_nodup : emptySourceEventSeqs.Nodup := by
  simp [emptySourceEventSeqs]

theorem emptySourceEventSeqs_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ emptySourceEventSeqs, source < current.session.nextSeq := by
  simp [emptySourceEventSeqs]

/-! ## Errors and dependent continuation result -/

inductive EndToEndError where
  | store (error : StoreError)
  | retry (error : ConversationError FixturePolicy)

structure PersistedPayloadStreamRetryRun where
  restored : ReadRestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  conversation : StreamRetryConversationRunResult FixturePolicy FixtureConfig persistedProcess
    FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    restored.restored.runner 0 finalRunner finalModel

/-! ## Process-backed continuation from the payload-preserving endpoint -/

def runRestored
    (restored : ReadRestoredRunner) :
    IO (Except (ConversationError FixturePolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          StreamRetryConversationRunResult FixturePolicy FixtureConfig persistedProcess
            FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
            emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
            restored.restored.runner 0 finalRunner finalModel)) :=
  run (policy := FixturePolicy) 2 persistedProcess FixtureBaseUrl FixtureApiKey FixtureSource
    FixtureConfig emptySourceEventSeqs emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    0 restored.restored.runner

def runFixture : IO (Except EndToEndError PersistedPayloadStreamRetryRun) := do
  match ← fixtureMemory with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runRestored restored with
      | .error error => pure (.error (.retry error))
      | .ok ⟨finalRunner, ⟨finalModel, conversation⟩⟩ =>
          pure (.ok {
            restored
            finalRunner
            finalModel
            conversation
          })

/-! ## Proof projections -/

theorem restored_session_eq_archive (run : PersistedPayloadStreamRetryRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  ReadRestoredRunner.session_eq_read run.restored

theorem restored_payload_raw_eq_expanded (run : PersistedPayloadStreamRetryRun) :
    run.restored.restored.payload.events.map EnrichedEvent.raw =
      run.restored.read.validated.expandedEvents :=
  ReadRestoredRunner.payload_raw_eq_expanded run.restored

theorem restored_payload_length_eq (run : PersistedPayloadStreamRetryRun) :
    run.restored.restored.payload.events.length =
      run.restored.read.validated.expandedEvents.length := by
  have hEvents := congrArg ValidatedPersistedJson.expandedEvents run.restored.archive_eq
  have hLength := RestoredRunner.payload_length_eq run.restored.restored
  exact hLength.trans (congrArg List.length hEvents)

/-! ## Trace and executable projections -/

def firstToolCalls
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixturePolicy FixtureConfig persistedProcess FixtureBaseUrl FixtureApiKey
      FixtureSource emptySourceEventSeqs emptySourceEventSeqs_nodup
      emptySourceEventSeqs_earlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.round.finished.finished.view.rawToolCalls.length

def firstRetryFailures
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixturePolicy FixtureConfig persistedProcess FixtureBaseUrl FixtureApiKey
      FixtureSource emptySourceEventSeqs emptySourceEventSeqs_nodup
      emptySourceEventSeqs_earlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.retryHistory.failures.length

def firstAttemptCount
    {runner finalRunner : ConversationRunner} {before finalModel : Nat} :
    StreamRetryTrace FixturePolicy FixtureConfig persistedProcess FixtureBaseUrl FixtureApiKey
      FixtureSource emptySourceEventSeqs emptySourceEventSeqs_nodup
      emptySourceEventSeqs_earlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.retryHistory.attemptCount

structure ExecutableSummary where
  initialNextSeq : Nat
  finalNextSeq : Nat
  payloadLength : Nat
  traceLength : Nat
  firstToolCalls : Nat
  firstRetryFailures : Nat
  firstAttemptCount : Nat
  finalModel : Nat
  completed : Bool
deriving BEq, DecidableEq, Repr

def summary (run : PersistedPayloadStreamRetryRun) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    payloadLength := run.restored.restored.payload.events.length
    traceLength := StreamRetryTrace.length run.conversation.trace
    firstToolCalls := firstToolCalls run.conversation.trace
    firstRetryFailures := firstRetryFailures run.conversation.trace
    firstAttemptCount := firstAttemptCount run.conversation.trace
    finalModel := run.finalModel
    completed := StreamRetryStop.isCompleted run.conversation.stop
  }

def executableInitialNextSeq : Nat := 8
def executableFinalNextSeq : Nat := 12
def executablePayloadLength : Nat := 8
def executableTraceLength : Nat := 2
def executableFirstToolCalls : Nat := 2
def executableFirstRetryFailures : Nat := 0
def executableFirstAttemptCount : Nat := 1
def executableFinalModel : Nat := 0
def executableCompleted : Bool := true

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.payloadLength = executablePayloadLength &&
    value.traceLength = executableTraceLength &&
    value.firstToolCalls = executableFirstToolCalls &&
    value.firstRetryFailures = executableFirstRetryFailures &&
    value.firstAttemptCount = executableFirstAttemptCount &&
    value.finalModel = executableFinalModel &&
    value.completed = executableCompleted

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessPayloadPersistenceStreamRetry
