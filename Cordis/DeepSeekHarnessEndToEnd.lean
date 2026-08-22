import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekHarnessTransportRetryConversation

/-!
# Persisted, retry-aware DeepSeek Harness conversation

This module composes two previously separate executable proof boundaries:

* a byte-backed, validated JSONL read restoring a `ConversationRunner`; and
* a retry-aware, fuel-bounded conversation whose result is indexed by its exact
  final runner and model.

The returned `Sigma` keeps the restored runner in the index of the conversation
certificate.  Consequently the trace cannot silently be detached from the
validated archive endpoint.  The fixture uses an in-memory backend and an
injected deterministic transport; it does not claim filesystem durability,
provider reachability, credential validity, backoff, idempotency, concurrency,
external-effect correctness, or deployed TypeScript equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEndToEnd

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessRetry
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekHarnessTransportRetry
open Cordis.DeepSeekHarnessTransportRetryConversation

/-! ## Fixed fixture indices -/

abbrev FixturePolicy := DeepSeekHarnessTransportRetryConversation.Example.retryConversationPolicy
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def emptySourceEventSeqs : List Nat := []

theorem emptySourceEventSeqs_nodup : emptySourceEventSeqs.Nodup := by
  simp [emptySourceEventSeqs]

theorem emptySourceEventSeqs_earlier (runner : ConversationRunner) :
    ∀ source ∈ emptySourceEventSeqs, source < runner.session.nextSeq := by
  simp [emptySourceEventSeqs]

/-! ## Error and indexed result surfaces -/

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | retry (error : RetryRoundError FixturePolicy)

structure PersistedRetryRun where
  restored : RestoredRunner
  finalRunner : ConversationRunner
  finalModel : Nat
  conversation : RetryTransportConversationRunResult FixturePolicy FixtureConfig
    FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
    emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
    restored.restored.runner 0 finalRunner finalModel

/-! ## Composition -/

def runFixture : IO (Except EndToEndError PersistedRetryRun) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureMemory with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      let calls ← IO.mkRef 0
      match ← DeepSeekHarnessTransportRetryConversation.runTransport
          (policy := FixturePolicy) 2
          (DeepSeekHarnessTransportRetryConversation.Example.retryConversationTransport calls)
          FixtureBaseUrl FixtureApiKey FixtureSource emptySourceEventSeqs
          emptySourceEventSeqs_nodup emptySourceEventSeqs_earlier
          0 restored.restored.runner with
      | .error error => pure (.error (.retry error))
      | .ok ⟨finalRunner, ⟨finalModel, conversation⟩⟩ =>
          pure (.ok {
            restored
            finalRunner
            finalModel
            conversation
          })

/-! ## Proof projections for consumers -/

theorem restored_session_eq_archive (run : PersistedRetryRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  DeepSeekHarnessPersistenceIO.RestoredRunner.session_eq_read run.restored

/-! ## Executable fixture projections -/

structure ExecutableSummary where
  initialNextSeq : Nat
  finalNextSeq : Nat
  traceLength : Nat
  retryFailures : Nat
  finalModel : Nat
  completed : Bool

def firstRetryFailures
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model} :
    RetryTransportTrace policy cfg baseUrl apiKey source sourceEventSeqs sourcesNodup
      sourcesEarlier runner before finalRunner finalModel → Nat
  | .nil _ _ => 0
  | .cons head _ => head.round.retryHistory.failures.length

def summary (run : PersistedRetryRun) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.finalRunner.session.nextSeq
    traceLength := RetryTransportTrace.length run.conversation.trace
    retryFailures := firstRetryFailures run.conversation.trace
    finalModel := run.finalModel
    completed := RetryTransportStop.isCompleted run.conversation.stop
  }

def executableInitialNextSeq : Nat := 8

def executableFinalNextSeq : Nat := 11

def executableTraceLength : Nat := 2

def executableRetryFailures : Nat := 1

def executableFinalModel : Nat := 0

def executableCompleted : Bool := true

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.traceLength = executableTraceLength &&
    value.retryFailures = executableRetryFailures &&
    value.finalModel = executableFinalModel &&
    value.completed = executableCompleted

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessEndToEnd
