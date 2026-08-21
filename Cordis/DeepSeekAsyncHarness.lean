import Cordis.AsyncHarness
import Cordis.DeepSeekCurlPrefixSession
import Std.Async.ContextAsync

/-!
# Process-backed DeepSeek race observations

This module is the first executable bridge from the pure `AsyncHarness` fiber surface to the
DeepSeek process adapters. Two complete-body text-prefix jobs run in separate cooperative
`ContextAsync` children; `ContextAsync.race` returns the first observed result and requests
cancellation of the losing child. The result retains the exact typed prefix/session error or
terminal response from the winning process.

The boundary is intentionally precise. The process adapter is still line-oriented and its
underlying synchronous read is not interruptible by a `ContextAsync` cancellation request. Thus
this module proves an actual asynchronous race observation and a typed bridge to a terminal phase,
not blocked-read cancellation, wall-clock fairness, cleanup of arbitrary external processes, or
equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekAsyncHarness

open Cordis
open Cordis.AsyncHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlPrefixSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekStreamIncremental
open Std.Async

/-! ## A typed process job and race result -/

abbrev PrefixPolicy : LinePolicy := LinePolicy.never

abbrev PrefixResult :=
  Except PrefixSessionError (ProcessedPrefix PrefixPolicy)

structure ProcessJob where
  id : Nat
  maxReads : Nat
  config : ProcessConfig
  request : HttpRequest

namespace ProcessJob

def run (job : ProcessJob) : ContextAsync PrefixResult := do
  executeText PrefixPolicy job.maxReads job.config job.request

end ProcessJob

inductive RaceResult where
  | waiting
  | left (result : PrefixResult)
  | right (result : PrefixResult)

instance : Inhabited RaceResult := ⟨.waiting⟩

namespace RaceResult

def winner : RaceResult → Option Nat
  | .waiting => none
  | .left _ => some 0
  | .right _ => some 1

def result : RaceResult → Option PrefixResult
  | .waiting => none
  | .left result | .right result => some result

def successful : RaceResult → Bool
  | .waiting => false
  | .left (.ok _) | .right (.ok _) => true
  | .left (.error _) | .right (.error _) => false

def phase : RaceResult → Phase Bool
  | .waiting => .pending
  | .left (.ok _) | .right (.ok _) => .completed true
  | .left (.error _) | .right (.error _) => .failed "deepseek process race failed"

theorem winner_mem (race : RaceResult) :
    race.winner = none ∨ race.winner = some 0 ∨ race.winner = some 1 := by
  cases race <;> simp [winner]

theorem phase_terminal_of_winner {race : RaceResult} (h : race.winner ≠ none) :
    race.phase.isTerminal = true := by
  cases race with
  | waiting => exact False.elim (h rfl)
  | left result => cases result <;> rfl
  | right result => cases result <;> rfl

theorem phase_pending_iff_waiting {race : RaceResult} :
    race.phase = .pending ↔ race = .waiting := by
  cases race with
  | waiting => simp [RaceResult.phase]
  | left result => cases result <;> simp [phase]
  | right result => cases result <;> simp [phase]

end RaceResult

def race
    (left right : ProcessJob) : ContextAsync RaceResult :=
  ContextAsync.race
    (do
      let result ← left.run
      pure (.left result))
    (do
      let result ← right.run
      pure (.right result))

def executeRace (left right : ProcessJob) : IO RaceResult :=
  Async.block (ContextAsync.run (race left right))

/-! ## Process fixtures -/

def fixtureProcessWithDelay (delay responseBody : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; sleep \"$1\"; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\"",
    "cordis-async-fixture",
    delay,
    responseBody
  ]

def exampleRequest : HttpRequest := DeepSeekCurlTransport.fixtureRequest.request

def exampleFastJob : ProcessJob where
  id := 0
  maxReads := 64
  config := fixtureProcessWithDelay "0" exampleTextStreamBody
  request := exampleRequest

def exampleSlowJob : ProcessJob where
  id := 1
  maxReads := 64
  config := fixtureProcessWithDelay "0.05" exampleTextStreamBody
  request := exampleRequest

def exampleRace : IO RaceResult := executeRace exampleFastJob exampleSlowJob

/-! ## Pure bridge facts and executable observations -/

theorem phase_of_example_success_is_terminal :
    ∀ response : ProcessedPrefix PrefixPolicy,
      (RaceResult.phase (.left (.ok response))).isTerminal = true := by
  intro response
  rfl

theorem phase_of_example_failure_is_terminal :
    (RaceResult.phase (.right (.error PrefixSessionError.fuelExhausted))).isTerminal = true := by
  rfl

theorem phase_of_waiting_is_pending :
    (RaceResult.phase .waiting : Phase Bool) = .pending := by
  rfl

def exampleRaceSummary (race : RaceResult) : String :=
  match race.winner with
  | none => "waiting"
  | some winner =>
      if race.successful then
        "winner=" ++ toString winner ++ ";success"
      else
        "winner=" ++ toString winner ++ ";error"

end Cordis.DeepSeekAsyncHarness
