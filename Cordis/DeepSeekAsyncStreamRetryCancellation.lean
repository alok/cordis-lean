import Cordis.DeepSeekAsyncStreamCancellation
import Cordis.DeepSeekStreamHarnessRetryCancellation
import Std.Async.ContextAsync

/-!
# Cooperative races over retry-aware cancellable streamed Harness jobs

This module lifts the retry-aware, pre-round-cancellable streamed conversation into two
cooperative `ContextAsync` children.  Each job retains its cancellation and retry policies;
the winning result therefore keeps the exact dependent trace, endpoint, decision certificate,
and per-round retry history instead of collapsing a policy stop into an untyped process error.

The boundary remains cooperative.  `ContextAsync.race` requests cancellation of the losing
child, but the process adapter still performs synchronous reads.  No blocked-read interruption,
wall-clock fairness, arbitrary cleanup, reconnect, or deployed Harness cancellation/retry
equivalence is claimed.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekAsyncStreamRetryCancellation

open Cordis
open Cordis.AsyncHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryCancellation
open Cordis.DeepSeekCurlTransport
open Std.Async

structure RetryProcessJob
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  id : Nat
  cancellationPolicy : CancellationPolicy
  retryPolicy : RetryPolicy
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

/-! The result package retains the job's dependent configuration rather than hiding those
indices in an existential. -/

structure JobResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (job : RetryProcessJob cfg) where
  result : Except (ConversationError job.retryPolicy)
    (Sigma fun finalRunner : ConversationRunner =>
      Sigma fun finalModel : Model =>
        RetryCancellableRunResult job.cancellationPolicy (retryPolicy := job.retryPolicy) cfg
          job.config job.baseUrl job.apiKey job.source job.sourceEventSeqs job.sourcesNodup
          job.sourcesEarlier job.runner job.before finalRunner finalModel)

namespace RetryProcessJob

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (job : RetryProcessJob cfg) : ContextAsync (JobResult cfg job) := do
  let result ← DeepSeekStreamHarnessRetryCancellation.run
    (policy := job.cancellationPolicy) (retryPolicy := job.retryPolicy)
    job.fuel job.config job.baseUrl job.apiKey job.source cfg job.sourceEventSeqs
    job.sourcesNodup (by
      intro current source sourceMem
      exact job.sourcesEarlier current source sourceMem)
    job.before job.runner
  pure { result }

end RetryProcessJob

inductive RaceResult
    {Model Capability : Type}
  (cfg : GenericHarness.Config Model Capability) where
  | waiting
  | left (job : RetryProcessJob cfg) (result : JobResult cfg job)
  | right (job : RetryProcessJob cfg) (result : JobResult cfg job)

instance
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} : Inhabited (RaceResult cfg) :=
  ⟨.waiting⟩

namespace JobResult

def successful
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {job : RetryProcessJob cfg}
    (result : JobResult cfg job) : Bool :=
  match result.result with
  | .ok _ => true
  | .error _ => false

def cancelled
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {job : RetryProcessJob cfg}
    (result : JobResult cfg job) : Bool :=
  match result.result with
  | .error _ => false
  | .ok ⟨_, ⟨_, run⟩⟩ => RetryCancellableStop.isCancelled run.stop

def phase
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {job : RetryProcessJob cfg}
    (result : JobResult cfg job) : Phase Bool :=
  match result.result with
  | .error _ => .failed "deepseek retry stream race failed"
  | .ok ⟨_, ⟨_, run⟩⟩ =>
      match run.stop with
      | .completed _ _ _ _ => .completed true
      | .fuelExhausted => .completed true
      | .cancelled _ reason _ => .cancelled (reasonText reason)

theorem phase_terminal_of_result
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {job : RetryProcessJob cfg}
    (result : JobResult cfg job) :
    result.phase.isTerminal = true := by
  rcases result with ⟨value⟩
  cases value with
  | error error => simp [JobResult.phase, Phase.isTerminal]
  | ok value =>
      rcases value with ⟨_, value⟩
      rcases value with ⟨_, run⟩
      cases stop : run.stop <;> simp [JobResult.phase, Phase.isTerminal, stop]

theorem phase_ne_pending
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {job : RetryProcessJob cfg}
    (result : JobResult cfg job) :
    result.phase ≠ .pending := by
  intro h
  rcases result with ⟨value⟩
  cases value with
  | error error => simp [JobResult.phase] at h
  | ok value =>
      rcases value with ⟨_, value⟩
      rcases value with ⟨_, run⟩
      cases stop : run.stop <;> simp [JobResult.phase, stop] at h

end JobResult

namespace RaceResult

def winner
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    RaceResult cfg → Option Nat
  | .waiting => none
  | .left _ _ => some 0
  | .right _ _ => some 1

def result
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
  RaceResult cfg → Option (Sigma fun job : RetryProcessJob cfg => JobResult cfg job)
  | .waiting => none
  | .left job result => some ⟨job, result⟩
  | .right job result => some ⟨job, result⟩

def successful
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
  RaceResult cfg → Bool
  | .waiting => false
  | .left _ result | .right _ result => result.successful

def cancelled
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
  RaceResult cfg → Bool
  | .waiting => false
  | .left _ result | .right _ result => result.cancelled

def phase
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
  RaceResult cfg → Phase Bool
  | .waiting => .pending
  | .left _ result | .right _ result => result.phase

theorem winner_mem
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (race : RaceResult cfg) :
    race.winner = none ∨ race.winner = some 0 ∨ race.winner = some 1 := by
  cases race <;> simp [RaceResult.winner]

theorem phase_terminal_of_winner
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {race : RaceResult cfg}
    (winner : race.winner ≠ none) :
    race.phase.isTerminal = true := by
  cases race with
  | waiting =>
      simp [RaceResult.winner] at winner
  | left _ result => exact result.phase_terminal_of_result
  | right _ result => exact result.phase_terminal_of_result

theorem phase_pending_iff_waiting
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {race : RaceResult cfg} :
    race.phase = .pending ↔ race = .waiting := by
  cases race with
  | waiting => simp [RaceResult.phase]
  | left _ result =>
      constructor
      · intro h
        exact (JobResult.phase_ne_pending result h).elim
      · intro h
        cases h
  | right _ result =>
      constructor
      · intro h
        exact (JobResult.phase_ne_pending result h).elim
      · intro h
        cases h

end RaceResult

def race
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {left right : RetryProcessJob cfg} :
    ContextAsync (RaceResult cfg) :=
  ContextAsync.race
    (do
      let result ← left.run
      pure (.left left result))
    (do
      let result ← right.run
      pure (.right right result))

def executeRace
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (left right : RetryProcessJob cfg) : IO (RaceResult cfg) :=
  Async.block (ContextAsync.run (race (left := left) (right := right)))

/-! ## Real cancellation-first fixture -/

def cancellationJob : RetryProcessJob Cordis.Harness.counterConfig where
  id := 0
  cancellationPolicy := CancellationPolicy.atRound 0 .peerFailure
  retryPolicy := RetryPolicy.default
  fuel := 2
  config := DeepSeekAsyncStreamHarness.streamLoopFixtureProcessWithDelay "0.10"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := DeepSeekAsyncStreamHarness.counterInitialRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def successJob : RetryProcessJob Cordis.Harness.counterConfig where
  id := 1
  cancellationPolicy := CancellationPolicy.never .user
  retryPolicy := RetryPolicy.default
  fuel := 2
  config := DeepSeekAsyncStreamHarness.streamLoopFixtureProcessWithDelay "0.20"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := DeepSeekAsyncStreamHarness.counterInitialRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def exampleCancellationRace : IO (RaceResult Cordis.Harness.counterConfig) :=
  executeRace cancellationJob successJob

/-! A complementary fixture puts the successful child first and delays its successful sibling.
This exercises the same cooperative boundary from the opposite winner branch without claiming
that the process scheduler is fair or that cancellation interrupts a blocked read. -/

def successFirstJob : RetryProcessJob Cordis.Harness.counterConfig where
  id := 2
  cancellationPolicy := CancellationPolicy.never .user
  retryPolicy := RetryPolicy.default
  fuel := 2
  config := DeepSeekAsyncStreamHarness.streamLoopFixtureProcessWithDelay "0"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := DeepSeekAsyncStreamHarness.counterInitialRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def delayedSuccessJob : RetryProcessJob Cordis.Harness.counterConfig where
  id := 3
  cancellationPolicy := CancellationPolicy.never .user
  retryPolicy := RetryPolicy.default
  fuel := 2
  config := DeepSeekAsyncStreamHarness.streamLoopFixtureProcessWithDelay "0.30"
  baseUrl := "https://fixture.invalid"
  apiKey := { value := "fixture-key" }
  source := DeepSeekHarness.counterRequestSource
  before := 0
  runner := DeepSeekAsyncStreamHarness.counterInitialRunner
  sourceEventSeqs := []
  sourcesNodup := by simp
  sourcesEarlier := by
    intro current source sourceMem
    cases sourceMem

def exampleSuccessRace : IO (RaceResult Cordis.Harness.counterConfig) :=
  executeRace successFirstJob delayedSuccessJob

end Cordis.DeepSeekAsyncStreamRetryCancellation
