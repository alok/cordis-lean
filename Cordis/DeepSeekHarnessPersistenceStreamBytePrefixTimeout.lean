import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekStreamHarnessBytePrefixTimeout

/-!
# Persisted runner into timed byte-prefix streaming

This module composes the byte-backed persistence reader with the timer-backed byte-prefix
streamed Harness continuation.  A successful memory archive read remains attached to the
initial `ConversationRunner`; a real configured process then supplies one tool-producing
streamed round, and the caller-fuel stop retains the exact runner endpoint rather than
fabricating a terminal response.

The fixture is local process evidence.  It does not claim fsync, stable media, crash recovery,
arbitrary descendant cleanup, provider or executable authenticity, backpressure, reconnects,
or deployed asynchronous Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceStreamBytePrefixTimeout

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistenceIO
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessBytePrefixTimeout

abbrev FixtureConfig := Cordis.Harness.counterConfig
abbrev FixtureSource := DeepSeekHarness.counterRequestSource
abbrev FixtureProcess :=
  DeepSeekStreamHarness.streamFlagFixtureProcess DeepSeekStreamHarness.counterToolStreamBody
abbrev FixtureBaseUrl := "https://fixture.invalid"
abbrev FixtureApiKey : ApiKey := { value := "fixture-key" }
abbrev EmptySources : List Nat := []

theorem emptySources_nodup : EmptySources.Nodup := by
  simp [EmptySources]

theorem emptySources_earlier :
    ∀ current : ConversationRunner,
      ∀ source ∈ EmptySources, source < current.session.nextSeq := by
  simp [EmptySources]

inductive EndToEndError where
  | store (error : HarnessPersistenceIO.StoreError)
  | timed (error : TimedBytePrefixConversationError)

structure PersistedTimedRun where
  restored : RestoredRunner
  timed : TimedBytePrefixConversationRunResult FixtureConfig

def runRestored
    (restored : RestoredRunner) :
    IO (Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult FixtureConfig)) :=
  runConversationMultiTimedBytePrefix
    (cfg := FixtureConfig) 1 4096 1 2000 FixtureProcess FixtureBaseUrl FixtureApiKey
    FixtureSource EmptySources emptySources_nodup emptySources_earlier 0
    restored.restored.runner

def runFixture : IO (Except EndToEndError PersistedTimedRun) := do
  match ← fixtureMemory with
  | .error error => pure (.error (.store error))
  | .ok restored =>
      match ← runRestored restored with
      | .error error => pure (.error (.timed error))
      | .ok timed => pure (.ok { restored, timed })

theorem restored_session_eq_archive (run : PersistedTimedRun) :
    run.restored.restored.runner.session =
      run.restored.read.validated.validated.final.session :=
  RestoredRunner.session_eq_read run.restored

def executableInitialNextSeq : Nat := 8
def executableFinalNextSeq : Nat := 10
def executableRoundCount : Nat := 1
def executableFuelExhausted : Bool := true
def executableFinalModel : Nat := 0

def roundCount (run : PersistedTimedRun) : Nat := run.timed.rounds.length

structure ExecutableSummary where
  initialNextSeq : Nat
  finalNextSeq : Nat
  roundCount : Nat
  fuelExhausted : Bool
  finalModel : Nat

def summary (run : PersistedTimedRun) : ExecutableSummary :=
  {
    initialNextSeq := run.restored.restored.runner.session.nextSeq
    finalNextSeq := run.timed.runner.session.nextSeq
    roundCount := roundCount run
    fuelExhausted := run.timed.stop.isCompleted = false
    finalModel := run.timed.finalModel
  }

def summaryMatchesFixture (value : ExecutableSummary) : Bool :=
  value.initialNextSeq = executableInitialNextSeq &&
    value.finalNextSeq = executableFinalNextSeq &&
    value.roundCount = executableRoundCount &&
    value.fuelExhausted = executableFuelExhausted &&
    value.finalModel = executableFinalModel

def runSummary : IO (Except EndToEndError ExecutableSummary) := do
  match ← runFixture with
  | .error error => pure (.error error)
  | .ok run => pure (.ok (summary run))

end Cordis.DeepSeekHarnessPersistenceStreamBytePrefixTimeout
