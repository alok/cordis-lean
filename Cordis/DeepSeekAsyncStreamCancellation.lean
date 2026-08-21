import Cordis.DeepSeekAsyncStreamHarness
import Cordis.DeepSeekStreamHarnessCancellation
import Std.Async.ContextAsync

/-!
# Cooperative streamed races with typed pre-round cancellation

This module carries the existing boundary-safe streamed cancellation contract through the
process-backed `ContextAsync` race. Each child keeps its cancellation policy and returns the
completed streamed-round witnesses, runner/model endpoint, and typed stop. The race therefore
does not turn a policy decision into an untyped process failure.

The fixture uses two real `sh` processes. One child is configured to cancel before round zero;
the other traverses a streamed tool-call round and a later text terminal. The cancellation check
is still pre-round: synchronous reads, blocked-read interruption, fairness, cleanup, and deployed
async cancellation equivalence remain external.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekAsyncStreamCancellation

open Cordis
open Cordis.AsyncHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessCancellation
open Cordis.DeepSeekAsyncStreamHarness
open Cordis.DeepSeekCurlTransport
open Std.Async

/-! ## A policy-bearing process child -/

structure ProcessJobResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  policy : CancellationPolicy
  result : Except StreamConversationError
    (Cordis.DeepSeekStreamHarnessCancellation.CancellableRunResult policy cfg)

structure ProcessJob
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  id : Nat
  policy : CancellationPolicy
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

namespace ProcessJob

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (job : ProcessJob cfg) : ContextAsync (ProcessJobResult cfg) := do
  let result ← DeepSeekStreamHarnessCancellation.runConversationMultiStreamCancellable
    (cfg := cfg)
    job.policy job.fuel job.config job.baseUrl job.apiKey job.source job.sourceEventSeqs
    job.sourcesNodup (by
      intro current source sourceMem
      exact job.sourcesEarlier current source sourceMem)
    job.before job.runner
  pure { policy := job.policy, result }

end ProcessJob

/-! ## Race result and pure observations -/

inductive RaceResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | waiting
  | left (result : ProcessJobResult cfg)
  | right (result : ProcessJobResult cfg)

instance
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} : Inhabited (RaceResult cfg) :=
  ⟨.waiting⟩

namespace ProcessJobResult

def successful
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (result : ProcessJobResult cfg) : Bool :=
  match result.result with
  | .ok _ => true
  | .error _ => false

def cancelled
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (result : ProcessJobResult cfg) : Bool :=
  match result.result with
  | .error _ => false
  | .ok run => run.stop.isCancelled

def phase
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (result : ProcessJobResult cfg) : Phase Bool :=
  match result.result with
  | .error _ => .failed "deepseek streamed cancellation race failed"
  | .ok run =>
      match run.stop with
      | .completed _ _ | .fuelExhausted => .completed true
      | .cancelled _ _ _ => .cancelled (reasonText result.policy.reason)

theorem phase_terminal_of_result
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (result : ProcessJobResult cfg) :
    (result.phase).isTerminal = true := by
  rcases result with ⟨policy, value⟩
  cases value with
  | error error =>
      simp [phase, Phase.isTerminal]
  | ok run =>
      rcases run with ⟨rounds, runner, finalModel, stop⟩
      cases stop with
      | completed _ _ =>
          simp [phase, Phase.isTerminal]
      | fuelExhausted =>
          simp [phase, Phase.isTerminal]
      | cancelled _ _ _ =>
          simp [phase, Phase.isTerminal]

theorem cancelled_preserves_endpoint
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {rounds : List (StreamConversationWitness cfg)}
    {runner : ConversationRunner}
    {before : Model}
    (policy : CancellationPolicy)
    (round : Nat)
    (reason : CancelReason)
    (decided : policy.decide round runner = true) :
    (Cordis.DeepSeekStreamHarnessCancellation.CancellableRunResult.mk rounds runner before
      (.cancelled round reason decided)).runner = runner := rfl

end ProcessJobResult

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
    RaceResult cfg → Option (ProcessJobResult cfg)
  | .waiting => none
  | .left result | .right result => some result

def successful
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Bool
  | .waiting => false
  | .left result | .right result => result.successful

def cancelled
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Bool
  | .waiting => false
  | .left result | .right result => result.cancelled

def phase
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Phase Bool
  | .waiting => .pending
  | .left result | .right result => result.phase

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
    (winner : race.winner ≠ none) :
    race.phase.isTerminal = true := by
  cases race with
  | waiting => exact False.elim (winner rfl)
  | left result | right result => exact result.phase_terminal_of_result

theorem phase_pending_iff_waiting
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {race : RaceResult cfg} :
    race.phase = .pending ↔ race = .waiting := by
  cases race with
  | waiting => simp [RaceResult.phase]
  | left result | right result =>
      rcases result with ⟨policy, value⟩
      cases value with
      | error error => simp [RaceResult.phase, ProcessJobResult.phase]
      | ok run =>
          rcases run with ⟨rounds, runner, finalModel, stop⟩
          cases stop with
          | completed _ _ => simp [RaceResult.phase, ProcessJobResult.phase]
          | fuelExhausted => simp [RaceResult.phase, ProcessJobResult.phase]
          | cancelled _ _ _ => simp [RaceResult.phase, ProcessJobResult.phase]

end RaceResult

def race
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (left right : ProcessJob cfg) : ContextAsync (RaceResult cfg) :=
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
    (left right : ProcessJob cfg) : IO (RaceResult cfg) :=
  Async.block (ContextAsync.run (race left right))

/-! ## A cancellation-first streamed race fixture -/

def cancelTurn99 : CancellationPolicy where
  reason := .peerFailure
  decide := fun _ runner => runner.turn = 99

theorem cancelTurn99_left_decision :
    cancelTurn99.decide 0 counterInitialRunner = false := by
  rfl

def cancelledRunner : ConversationRunner where
  session := DeepSeekHarness.counterSession
  turn := 99
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

theorem cancelTurn99_right_decision :
    cancelTurn99.decide 0 cancelledRunner = true := by
  rfl

def cancellationFastJob : ProcessJob Cordis.Harness.counterConfig where
  id := 0
  policy := cancelTurn99
  fuel := 2
  config := streamLoopFixtureProcessWithDelay "0.10"
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

def cancellationImmediateJob : ProcessJob Cordis.Harness.counterConfig where
  id := 1
  policy := cancelTurn99
  fuel := 2
  config := streamLoopFixtureProcessWithDelay "0"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := cancelledRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def exampleCancellationRace : IO (RaceResult Cordis.Harness.counterConfig) :=
  executeRace cancellationFastJob cancellationImmediateJob

theorem cancelled_endpoint_model
    {rounds : List (StreamConversationWitness Cordis.Harness.counterConfig)}
    {runner : ConversationRunner}
    (decided : cancelTurn99.decide 0 runner = true) :
    (Cordis.DeepSeekStreamHarnessCancellation.CancellableRunResult.mk rounds runner 0
      (.cancelled 0 .peerFailure decided)).finalModel = 0 := rfl

def exampleCancellationRaceSummary
    {cfg : GenericHarness.Config Nat Cordis.Examples.Counter.Capability}
    (race : RaceResult cfg) : String :=
  match race.winner with
  | none => "waiting"
  | some winner =>
      if race.cancelled then
        "winner=" ++ toString winner ++ ";cancelled"
      else if race.successful then
        "winner=" ++ toString winner ++ ";success"
      else
        "winner=" ++ toString winner ++ ";error"

end Cordis.DeepSeekAsyncStreamCancellation
