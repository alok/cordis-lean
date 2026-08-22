import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekStreamHarnessRetryConversation

/-!
# Persisted, process-backed streamed retry conversation

This module composes the byte-backed JSONL restore boundary with the indexed,
process-backed streamed conversation loop.  The restored `ConversationRunner`
is the initial index of the dependent `StreamRetryConversationRunResult`; every
round head stores its streamed body, retry history, assistant/tool endpoint, and
the next recursive runner.  The terminal `Sigma` therefore cannot detach the
process trace from the validated archive endpoint.

The executable fixture is deliberately deterministic but genuinely process
backed.  Its shell process emits the two-call counter stream until the first
tool result appears in the next request, then emits the terminal text stream.
This proves a two-round continuation from persisted state without claiming
provider authenticity, durable filesystem recovery, backoff, idempotency,
blocked-read cancellation, external-effect correctness, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceStreamRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryConversation

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
    "cordis-persisted-stream-retry-fixture",
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

/-! ## Error and dependent result surfaces -/

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | retry (error : ConversationError FixturePolicy)

structure PersistedStreamRetryRun where
  restored : RestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  conversation : StreamRetryConversationRunResult FixturePolicy FixtureConfig persistedProcess
    FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    restored.restored.runner 0 finalRunner finalModel

/-! ## Process-backed continuation from the restored endpoint -/

def runRestored
    (restored : RestoredRunner) :
    IO (Except (ConversationError FixturePolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          StreamRetryConversationRunResult FixturePolicy FixtureConfig persistedProcess
            FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
            emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
            restored.restored.runner 0 finalRunner finalModel)) :=
  DeepSeekStreamHarnessRetryConversation.run (policy := FixturePolicy) 2 persistedProcess
    FixtureBaseUrl FixtureApiKey FixtureSource FixtureConfig emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    0 restored.restored.runner

def runFixture : IO (Except EndToEndError PersistedStreamRetryRun) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureMemory with
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

theorem restored_session_eq_archive (run : PersistedStreamRetryRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

/-! ## Executable projections -/

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
  traceLength : Nat
  firstToolCalls : Nat
  firstRetryFailures : Nat
  firstAttemptCount : Nat
  finalModel : Nat
  completed : Bool

def summary (run : PersistedStreamRetryRun) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    traceLength := StreamRetryTrace.length run.conversation.trace
    firstToolCalls := firstToolCalls run.conversation.trace
    firstRetryFailures := firstRetryFailures run.conversation.trace
    firstAttemptCount := firstAttemptCount run.conversation.trace
    finalModel := run.finalModel
    completed := StreamRetryStop.isCompleted run.conversation.stop
  }

def executableInitialNextSeq : Nat := 8

def executableFinalNextSeq : Nat := 12

def executableTraceLength : Nat := 2

def executableFirstToolCalls : Nat := 2

def executableFirstRetryFailures : Nat := 0

def executableFirstAttemptCount : Nat := 1

def executableFinalModel : Nat := 0

def executableCompleted : Bool := true

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
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

end Cordis.DeepSeekHarnessPersistenceStreamRetry
