import Cordis.DeepSeekHarnessPayloadPersistence
import Cordis.DeepSeekHarnessProcessOutcome

/-!
# Payload-preserving persisted process outcome

`DeepSeekHarnessPayloadPersistence` restores a persisted current-Harness event log with both a
typed local runner and a lossless payload ledger.  This module carries that same dependent result
through the repository's deterministic `IO.Process` complete-body outcome path.  The prepared
request, process body, rich/tool outcome, final endpoint, and payload archive all share one source
runner index.

The fixture is local process evidence.  It does not prove provider or credential authenticity,
incremental delivery, blocked-read cancellation, durable persistence, external tool trust, or
equivalence to the deployed TypeScript Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadPersistenceProcessOutcome

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPayloadPersistence
open Cordis.DeepSeekHarnessProcessOutcome
open Cordis.HarnessPersistenceRefinement
open Cordis.SessionPayloadArchive

/-! ## Fixed fixture indices -/

abbrev FixtureSource := DeepSeekHarnessProcessOutcome.Example.toolSource
abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }

def emptySourceEventSeqs : List Nat := []

theorem emptySourceEventSeqs_nodup : emptySourceEventSeqs.Nodup := by
  simp [emptySourceEventSeqs]

theorem emptySourceEventSeqs_earlier (runner : ConversationRunner) :
    ∀ source ∈ emptySourceEventSeqs, source < runner.session.nextSeq := by
  simp [emptySourceEventSeqs]

/-! ## Dependent process result -/

inductive EndToEndError where
  | store (error : DeepSeekHarnessPayloadPersistence.StoreError)
  | process (error : DeepSeekHarnessProcessOutcome.RoundError)
deriving Repr

structure PayloadPersistedProcessRound where
  restored : ReadRestoredRunner
  prepared : PreparedStreamingRequest FixtureBaseUrl FixtureApiKey FixtureSource
    restored.restored.runner
  body : String
  round : ProcessOutcomeRound prepared FixtureConfig 0 emptySourceEventSeqs
    emptySourceEventSeqs_nodup
    (emptySourceEventSeqs_earlier restored.restored.runner) body

/-! ## Process execution attached to the payload-preserving restore -/

def executeRestored
    (restored : ReadRestoredRunner) :
    IO (Except DeepSeekHarnessProcessOutcome.RoundError
      (Sigma fun prepared : PreparedStreamingRequest FixtureBaseUrl FixtureApiKey FixtureSource
          restored.restored.runner =>
        Sigma fun body : String =>
          ProcessOutcomeRound prepared FixtureConfig 0 emptySourceEventSeqs
            emptySourceEventSeqs_nodup
            (emptySourceEventSeqs_earlier restored.restored.runner) body)) :=
  DeepSeekHarnessProcessOutcome.executeSourceOutcome
    DeepSeekHarnessProcessOutcome.Example.toolProcess FixtureBaseUrl FixtureApiKey FixtureSource
    FixtureConfig 0 restored.restored.runner emptySourceEventSeqs
    emptySourceEventSeqs_nodup (emptySourceEventSeqs_earlier restored.restored.runner)

def runFixture : IO (Except EndToEndError PayloadPersistedProcessRound) := do
  match ← DeepSeekHarnessPayloadPersistence.fixtureMemory with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← executeRestored restored with
      | .error error => pure (.error (.process error))
      | .ok ⟨prepared, ⟨body, round⟩⟩ =>
          pure (.ok {
            restored
            prepared
            body
            round
          })

/-! ## Proof projections -/

theorem restored_session_eq_archive (run : PayloadPersistedProcessRound) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  ReadRestoredRunner.session_eq_read run.restored

theorem payload_raw_eq_expanded (run : PayloadPersistedProcessRound) :
    run.restored.restored.payload.events.map EnrichedEvent.raw =
      run.restored.read.validated.expandedEvents :=
  ReadRestoredRunner.payload_raw_eq_expanded run.restored

theorem payload_length_eq (run : PayloadPersistedProcessRound) :
    run.restored.restored.payload.events.length =
      run.restored.read.validated.expandedEvents.length :=
  by
    have hLength := RestoredRunner.payload_length_eq run.restored.restored
    have hEvents := congrArg ValidatedPersistedJson.expandedEvents run.restored.archive_eq
    exact hLength.trans (congrArg List.length hEvents)

theorem request_build_eq_archive (run : PayloadPersistedProcessRound) :
    buildTypedStreamingRequestPlan FixtureBaseUrl FixtureApiKey FixtureSource
        run.restored.read.validated.validated.final.session = .ok run.prepared.plan := by
  rw [← restored_session_eq_archive run]
  exact run.prepared.build_eq

theorem stream_plan_true (run : PayloadPersistedProcessRound) :
    run.prepared.plan.source.stream = true :=
  run.prepared.source_stream

theorem process_endpoint (run : PayloadPersistedProcessRound) :
    run.round.after = executionEndpoint run.round.result :=
  run.round.endpoint_exact

/-! ## Executable projections -/

structure ExecutableSummary where
  initialNextSeq : Nat
  finalNextSeq : Nat
  bodyLength : Nat
  streaming : Bool
  payloadLength : Nat
  typedPayloadCount : Nat
deriving BEq, DecidableEq, Repr

def summary (run : PayloadPersistedProcessRound) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.round.after.session.nextSeq
    bodyLength := run.body.length
    streaming := run.prepared.plan.source.stream
    payloadLength := run.restored.restored.payload.events.length
    typedPayloadCount := run.restored.restored.payload.typedCount
  }

def executableInitialNextSeq : Nat := 8

def executableFinalNextSeq : Nat := 10

def executableBodyLength : Nat := 523

def executableStreaming : Bool := true

def executablePayloadLength : Nat := 8

def executableTypedPayloadCount : Nat := 8

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.bodyLength = executableBodyLength &&
    value.streaming = executableStreaming &&
    value.payloadLength = executablePayloadLength &&
    value.typedPayloadCount = executableTypedPayloadCount

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessPayloadPersistenceProcessOutcome
