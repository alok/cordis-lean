import Cordis.DeepSeekAsyncHarness
import Cordis.DeepSeekStreamHarness
import Std.Async.ContextAsync

/-!
# Cooperative races over streamed DeepSeek Harness continuations

This module lifts the existing complete-body streamed Harness round into two cooperative
`ContextAsync` children. A `StreamProcessJob` retains all request/session/configuration evidence
needed by `DeepSeekStreamHarness.runConversationMultiStream`; the race result retains the first
typed continuation result rather than erasing tool executions, runner state, or typed errors.

The executable fixture uses two real `sh` processes. Each process emits a streamed tool-call round
followed by a text terminal under explicit fuel, so the race exercises dependent tool execution and
the append-only conversation runner rather than only wire parsing. `ContextAsync.race` requests
cancellation of the losing child, but the underlying process adapter still performs synchronous
line-oriented reads. Consequently this is an observation-preserving cooperative race boundary,
not a theorem about interruptible blocked reads, wall-clock fairness, arbitrary cleanup, or the
deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekAsyncStreamHarness

open Cordis
open Cordis.AsyncHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekCurlTransport
open Std.Async

/-! ## Generic streamed process jobs -/

structure StreamProcessJob
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  id : Nat
  fuel : Nat
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

namespace StreamProcessJob

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (job : StreamProcessJob cfg) :
    ContextAsync (Except StreamConversationError (StreamConversationRunResult cfg)) := do
  DeepSeekStreamHarness.runConversationMultiStream job.fuel job.config job.baseUrl job.apiKey
    job.source job.sourceEventSeqs job.sourcesNodup
    (by
      intro current source sourceMem
      exact job.sourcesEarlier current source sourceMem)
    job.before job.runner

end StreamProcessJob

inductive RaceResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | waiting
  | left (result : Except StreamConversationError (StreamConversationRunResult cfg))
  | right (result : Except StreamConversationError (StreamConversationRunResult cfg))

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
    RaceResult cfg → Option (Except StreamConversationError (StreamConversationRunResult cfg))
  | .waiting => none
  | .left result | .right result => some result

def successful
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Bool
  | .waiting => false
  | .left (.ok _) | .right (.ok _) => true
  | .left (.error _) | .right (.error _) => false

def phase
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Phase Bool
  | .waiting => .pending
  | .left (.ok _) | .right (.ok _) => .completed true
  | .left (.error _) | .right (.error _) => .failed "deepseek streamed process race failed"

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
  | left result => cases result <;> rfl
  | right result => cases result <;> rfl

theorem phase_pending_iff_waiting
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {race : RaceResult cfg} :
    race.phase = .pending ↔ race = .waiting := by
  cases race with
  | waiting => simp [RaceResult.phase]
  | left result => cases result <;> simp [phase]
  | right result => cases result <;> simp [phase]

end RaceResult

def race
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (left right : StreamProcessJob cfg) : ContextAsync (RaceResult cfg) :=
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
    (left right : StreamProcessJob cfg) : IO (RaceResult cfg) :=
  Async.block (ContextAsync.run (race left right))

/-! ## A real two-process streamed tool/session fixture -/

def streamLoopFixtureProcessWithDelay (delay : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "body=$(cat); sleep \"$1\"; case \"$body\" in " ++
      "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$3\" ;; " ++
      "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; esac",
    "cordis-async-stream-loop-fixture",
    delay,
    counterMultiToolStreamBody,
    DeepSeekRichStream.exampleTextStreamBody
  ]

def counterInitialRunner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 1
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def exampleFastJob : StreamProcessJob Cordis.Harness.counterConfig where
  id := 0
  fuel := 2
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

def exampleSlowJob : StreamProcessJob Cordis.Harness.counterConfig where
  id := 1
  fuel := 2
  config := streamLoopFixtureProcessWithDelay "0.05"
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

def exampleRace : IO (RaceResult Cordis.Harness.counterConfig) :=
  executeRace exampleFastJob exampleSlowJob

theorem phase_of_example_success_is_terminal
    {result : StreamConversationRunResult Cordis.Harness.counterConfig} :
    (RaceResult.phase (.left (.ok result))).isTerminal = true := by
  rfl

theorem phase_of_example_failure_is_terminal
    {error : StreamConversationError} :
    (RaceResult.phase (cfg := Cordis.Harness.counterConfig)
      (.right (.error error))).isTerminal = true := by
  rfl

def exampleRaceSummary {cfg : GenericHarness.Config Nat Cordis.Examples.Counter.Capability}
    (race : RaceResult cfg) : String :=
  match race.winner with
  | none => "waiting"
  | some winner =>
      if race.successful then
        "winner=" ++ toString winner ++ ";success"
      else
        "winner=" ++ toString winner ++ ";error"

end Cordis.DeepSeekAsyncStreamHarness
