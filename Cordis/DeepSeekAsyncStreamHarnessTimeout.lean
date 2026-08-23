import Cordis.AsyncHarness
import Cordis.DeepSeekStreamHarnessBytePrefixTimeout
import Cordis.DeepSeekAsyncStreamHarness
import Std.Async.ContextAsync

/-!
# Cooperative races over timed streamed Harness continuations

This module combines the cooperative two-child race with the timer-backed byte-prefix adapter.
Each child keeps its request, process, timeout, dependent runner endpoint, and typed stop.  A
completed child therefore reaches the same proof-carrying streamed conversation as the ordinary
race, while a deadline becomes an explicit cancelled phase carrying the accepted prefix.

The result is local executable evidence: `ContextAsync.race` requests cancellation of the losing
child and the child adapter kills/waits its configured process when its own read deadline wins.
This does not prove arbitrary task cancellation delivery, descendant cleanup, fairness,
backpressure, reconnects, provider authenticity, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekAsyncStreamHarnessTimeout

open Cordis
open Cordis.AsyncHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefixTimeout
open Cordis.DeepSeekHarness
open Cordis.DeepSeekStreamIncremental
open Cordis.DeepSeekStreamHarnessBytePrefixTimeout
open Cordis.DeepSeekAsyncStreamHarness
open Cordis.DeepSeekCurlTransport
open Std.Async

/-! ## A timed streamed process job -/

structure TimedStreamProcessJob
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  id : Nat
  fuel : Nat
  maxReads : Nat
  chunkSize : Nat
  timeoutMs : UInt32
  config : ProcessConfig
  baseUrl : String
  apiKey : ApiKey
  source : RequestSource
  before : Model
  runner : ConversationRunner
  sourceEventSeqs : List Nat
  sourcesNodup : sourceEventSeqs.Nodup
  sourcesEarlier :
    ∀ (current : ConversationRunner),
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq

namespace TimedStreamProcessJob

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (job : TimedStreamProcessJob cfg) :
    ContextAsync
      (Except TimedBytePrefixConversationError
        (TimedBytePrefixConversationRunResult cfg)) := do
  runConversationMultiTimedBytePrefix job.fuel job.maxReads job.chunkSize job.timeoutMs
    job.config job.baseUrl job.apiKey job.source job.sourceEventSeqs job.sourcesNodup
    (by
      intro current source sourceMem
      exact job.sourcesEarlier current source sourceMem)
    job.before job.runner

end TimedStreamProcessJob

/-! ## Race observations and phase projection -/

inductive RaceResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | waiting
  | left (result : Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult cfg))
  | right (result : Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult cfg))

instance
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} : Inhabited (RaceResult cfg) :=
  ⟨.waiting⟩

namespace RaceResult

def winner
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Option Nat
  | .waiting => none
  | .left _ => some 0
  | .right _ => some 1

def result
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Option
      (Except TimedBytePrefixConversationError
        (TimedBytePrefixConversationRunResult cfg))
  | .waiting => none
  | .left result | .right result => some result

def successful
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Bool
  | .waiting => false
  | .left (.ok run) | .right (.ok run) =>
      TimedBytePrefixConversationStop.isCompleted run.stop
  | .left (.error _) | .right (.error _) => false

def phaseOf
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult cfg) → Phase String
  | .error _ => .failed "timed streamed Harness process failed"
  | .ok run =>
      match run.stop with
      | .completed _ _ => .completed "stream completed"
      | .fuelExhausted => .failed "timed streamed Harness fuel exhausted"
      | .prefixStopped response =>
          match response.stop with
          | .completed _ => .completed "stream completed"
          | .timedOut _ timeoutMs => .cancelled ("deadline:" ++ toString timeoutMs)
          | .cancelled _ reason _ => .cancelled reason
          | .fuelExhausted => .failed "timed streamed prefix fuel exhausted"

def phase
    {Model Capability : Type}
  {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Phase String
  | .waiting => .pending
  | .left result | .right result => phaseOf result

theorem winner_mem
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (race : RaceResult cfg) :
    race.winner = none ∨ race.winner = some 0 ∨ race.winner = some 1 := by
  cases race <;> simp [winner]

theorem phase_terminal_of_winner
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {race : RaceResult cfg}
    (h : race.winner ≠ none) :
    race.phase.isTerminal = true := by
  cases race with
  | waiting => exact False.elim (h rfl)
  | left result | right result =>
      cases result with
      | error _ => rfl
      | ok run =>
          rcases run with ⟨rounds, runner, finalModel, stop⟩
          cases stop with
          | completed _ _ | fuelExhausted => rfl
          | prefixStopped response =>
              rcases response with
                ⟨state, rawChunks, pendingRaw, pendingLine, status, statusSeen, stop,
                  stopLine, rawBytes, rawChunksEq, exitCode, stderr⟩
              cases stop with
              | completed _ | fuelExhausted | cancelled _ _ _ | timedOut _ _ => rfl

theorem phase_pending_iff_waiting
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {race : RaceResult cfg} :
    race.phase = .pending ↔ race = .waiting := by
  cases race with
  | waiting => simp [phase]
  | left result | right result =>
      cases result with
      | error _ => simp [phase, phaseOf]
      | ok run =>
          rcases run with ⟨rounds, runner, finalModel, stop⟩
          cases stop with
          | completed _ _ => simp [phase, phaseOf]
          | fuelExhausted => simp [phase, phaseOf]
          | prefixStopped response =>
              rcases response with
                ⟨state, rawChunks, pendingRaw, pendingLine, status, statusSeen, stop,
                  stopLine, rawBytes, rawChunksEq, exitCode, stderr⟩
              cases stop with
              | completed _ => simp [phase, phaseOf]
              | fuelExhausted => simp [phase, phaseOf]
              | cancelled _ _ _ => simp [phase, phaseOf]
              | timedOut _ _ => simp [phase, phaseOf]

end RaceResult

def race
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (left right : TimedStreamProcessJob cfg) : ContextAsync (RaceResult cfg) :=
  ContextAsync.race
    (do
      let result ← left.run
      pure (.left result))
    (do
      let result ← right.run
      pure (.right result))

def executeRace
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (left right : TimedStreamProcessJob cfg) : IO (RaceResult cfg) :=
  Async.block (ContextAsync.run (race left right))

def executeJob
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (job : TimedStreamProcessJob cfg) : IO
      (Except TimedBytePrefixConversationError
        (TimedBytePrefixConversationRunResult cfg)) :=
  Async.block (ContextAsync.run job.run)

/-! ## Executable fast/timeout fixtures -/

namespace Example

def timeoutJob : TimedStreamProcessJob Cordis.Harness.counterConfig where
  id := 1
  fuel := 1
  maxReads := 4096
  chunkSize := 1
  timeoutMs := 100
  config := streamLoopFixtureProcessWithDelay "0.25"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := counterInitialRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def fastJob : TimedStreamProcessJob Cordis.Harness.counterConfig where
  id := 0
  fuel := 2
  maxReads := 4096
  chunkSize := 1
  timeoutMs := 2000
  config := streamLoopFixtureProcessWithDelay "0"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := counterInitialRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def timeoutRun : IO
    (Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult Cordis.Harness.counterConfig)) :=
  executeJob timeoutJob

def fastRun : IO
    (Except TimedBytePrefixConversationError
      (TimedBytePrefixConversationRunResult Cordis.Harness.counterConfig)) :=
  executeJob fastJob

def raceRun : IO (RaceResult Cordis.Harness.counterConfig) :=
  executeRace fastJob timeoutJob

def timeoutSummary : IO Bool := do
  match ← timeoutRun with
  | .error _ => pure false
  | .ok run =>
      match run.stop with
      | .prefixStopped response =>
          pure (match response.stop with
            | .timedOut line timeoutMs => line = 0 && timeoutMs = 100 &&
                response.state.typed.line = 0
            | .completed _ | .fuelExhausted | .cancelled _ _ _ => false)
      | .completed _ _ | .fuelExhausted => pure false

def raceSummary : IO Bool := do
  let race ← raceRun
  pure (race.winner ≠ none && race.phase.isTerminal)

def fastSummary : IO Bool := do
  match ← fastRun with
  | .error _ => pure false
  | .ok run =>
      match run.stop with
      | .completed last _ =>
          pure (last.2.2.round.finalModel = 0)
      | .fuelExhausted | .prefixStopped _ => pure false

theorem timeout_stop_is_cancelled
    {response : TimedBytePrefixResponse (LinePolicy.never)}
    {line : Nat} {timeoutMs : UInt32}
    (stop_eq : response.stop = .timedOut line timeoutMs) :
    RaceResult.phaseOf
      (cfg := Cordis.Harness.counterConfig)
      (.ok {
        rounds := []
        runner := counterInitialRunner
        finalModel := 0
        stop := .prefixStopped response
    }) = .cancelled ("deadline:" ++ toString timeoutMs) := by
  simp [RaceResult.phaseOf, stop_eq]

end Example

end Cordis.DeepSeekAsyncStreamHarnessTimeout
