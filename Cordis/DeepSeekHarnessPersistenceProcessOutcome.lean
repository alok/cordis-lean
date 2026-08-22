import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekHarnessProcessOutcome

/-!
# Persisted, process-backed DeepSeek Harness outcome

This module composes the byte-backed JSONL restore boundary with the actual
`IO.Process`-based complete-body outcome path.  The restored runner remains a
dependent index of the prepared streaming request, decoded process body,
classified outcome, typed tool execution, and final runner endpoint.

The executable fixture uses the repository's deterministic shell process.  It
does not claim provider authenticity, credential validity, incremental delivery,
blocked-read cancellation, persistence durability, external tool trust, or
deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceProcessOutcome

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekHarnessProcessOutcome

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

/-! ## Errors and dependent result -/

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | process (error : DeepSeekHarnessProcessOutcome.RoundError)

structure PersistedProcessRound where
  restored : RestoredRunner
  prepared : PreparedStreamingRequest FixtureBaseUrl FixtureApiKey FixtureSource
    restored.restored.runner
  body : String
  round : ProcessOutcomeRound prepared FixtureConfig 0 emptySourceEventSeqs
    emptySourceEventSeqs_nodup (emptySourceEventSeqs_earlier restored.restored.runner) body

/-! ## Process execution attached to the restored runner -/

def executeRestored
    (restored : RestoredRunner) :
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

def runFixture : IO (Except EndToEndError PersistedProcessRound) := do
  match ← DeepSeekHarnessPersistenceIO.fixtureMemory with
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

theorem restored_session_eq_archive (run : PersistedProcessRound) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

theorem request_build_eq_archive (run : PersistedProcessRound) :
    buildTypedStreamingRequestPlan FixtureBaseUrl FixtureApiKey FixtureSource
        run.restored.read.validated.validated.final.session = .ok run.prepared.plan := by
  rw [← restored_session_eq_archive run]
  exact run.prepared.build_eq

theorem stream_plan_true (run : PersistedProcessRound) :
    run.prepared.plan.source.stream = true :=
  run.prepared.source_stream

theorem process_endpoint (run : PersistedProcessRound) :
    run.round.after = executionEndpoint run.round.result :=
  run.round.endpoint_exact

/-! ## Executable projections -/

structure ExecutableSummary where
  initialNextSeq : Nat
  finalNextSeq : Nat
  bodyLength : Nat
  streaming : Bool

def summary (run : PersistedProcessRound) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.round.after.session.nextSeq
    bodyLength := run.body.length
    streaming := run.prepared.plan.source.stream
  }

def executableInitialNextSeq : Nat := 8

def executableFinalNextSeq : Nat := 10

def executableBodyLength : Nat := 523

def executableStreaming : Bool := true

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.bodyLength = executableBodyLength &&
    value.streaming = executableStreaming

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessPersistenceProcessOutcome
