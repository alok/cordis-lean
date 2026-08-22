import Cordis.DeepSeekHarnessCancellation
import Cordis.DeepSeekStreamHarnessRetryConversation

/-!
# Boundary-safe cancellation for retry-aware streamed conversations

This module composes the process-backed retry boundary with the existing pre-round
cancellation contract.  A cancellation decision is made before a retry-aware stream
round is started; the result retains the exact accepted round prefix and the exact
runner/model endpoint at that boundary.  Retry histories remain inside each accepted
round, so a transient process or HTTP failure is still typed by `ConversationError`.

This is deliberately not an in-flight IO cancellation theorem.  It does not interrupt
a blocked process read, HTTP request, stream reader, tool execution, or external
process, and it does not claim cleanup, backpressure, reconnect, or deployed Harness
cancellation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekRichStream
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamHarnessRetry
open Cordis.DeepSeekStreamHarnessRetryConversation

/-! ## Typed stops and indexed results -/

inductive RetryCancellableStop
    (policy : CancellationPolicy)
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (finalRunner : ConversationRunner)
    (finalModel : Model) where
  | completed
      {runner : ConversationRunner}
      {before : Model}
      (last : StreamRetryRoundBox retryPolicy cfg config baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (runner_eq : last.round.round.runner = finalRunner)
      (model_eq : last.round.round.finalModel = finalModel)
      (noToolCalls : StreamRetryRoundBox.noToolCalls last)
  | fuelExhausted
  | cancelled
      (round : Nat)
      (reason : CancelReason)
      (decided : policy.decide round finalRunner = true)

namespace RetryCancellableStop

def isCompleted
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableStop policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Bool
  | .completed .. => true
  | .fuelExhausted | .cancelled .. => false

def isFuelExhausted
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableStop policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Bool
  | .completed .. | .cancelled .. => false
  | .fuelExhausted => true

def isCancelled
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableStop policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Bool
  | .completed .. | .fuelExhausted => false
  | .cancelled .. => true

def cancelledRound
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableStop policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Option Nat
  | .completed .. | .fuelExhausted => none
  | .cancelled round .. => some round

def cancelledReason
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {config : ProcessConfig}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableStop policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Option CancelReason
  | .completed .. | .fuelExhausted => none
  | .cancelled _ reason .. => some reason

end RetryCancellableStop

structure RetryCancellableRunResult
    (policy : CancellationPolicy)
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (initialRunner : ConversationRunner)
    (initialModel : Model)
    (finalRunner : ConversationRunner)
    (finalModel : Model) where
  trace : StreamRetryTrace retryPolicy cfg config baseUrl apiKey source sourceEventSeqs
    sourcesNodup sourcesEarlier initialRunner initialModel finalRunner finalModel
  stop : RetryCancellableStop policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey source
    sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel

/-! ## Process-backed retry-aware cancellable loop -/

def runAux
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (round : Nat)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (ConversationError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RetryCancellableRunResult policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey
            source sourceEventSeqs sourcesNodup sourcesEarlier runner before finalRunner
              finalModel)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨runner, ⟨before, {
        trace := .nil runner before
        stop := .fuelExhausted
      }⟩⟩)
  | fuel + 1 =>
      if decided : policy.decide round runner then
        pure (.ok ⟨runner, ⟨before, {
          trace := .nil runner before
          stop := .cancelled round policy.reason decided
        }⟩⟩)
      else
        match ← executeConversationMultiStreamRound retryPolicy config baseUrl apiKey source cfg
            before
            runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
        | .error error => pure (.error error)
        | .ok ⟨body, roundResult⟩ =>
            let head : StreamRetryRoundBox retryPolicy cfg config baseUrl apiKey source
                sourceEventSeqs
                sourcesNodup sourcesEarlier runner before := { body, round := roundResult }
            let callCount := head.round.round.finished.finished.view.rawToolCalls.length
            if noTools : callCount = 0 then
              pure (.ok ⟨roundResult.round.runner, ⟨roundResult.round.finalModel, {
                trace := .cons head (.nil roundResult.round.runner roundResult.round.finalModel)
                stop := .completed head rfl rfl noTools
              }⟩⟩)
            else
              match ← runAux (policy := policy) (retryPolicy := retryPolicy) fuel config baseUrl
                  apiKey
                  source sourceEventSeqs sourcesNodup sourcesEarlier (round + 1)
                  roundResult.round.finalModel roundResult.round.runner with
              | .error error => pure (.error error)
              | .ok ⟨finalRunner, ⟨finalModel, tail⟩⟩ =>
                  pure (.ok ⟨finalRunner, ⟨finalModel, {
                    trace := .cons head tail.trace
                    stop := tail.stop
                  }⟩⟩)
termination_by fuel
decreasing_by omega

def run
    {policy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    (fuel : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (ConversationError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RetryCancellableRunResult policy (retryPolicy := retryPolicy) cfg config baseUrl apiKey
            source sourceEventSeqs sourcesNodup sourcesEarlier runner before finalRunner
              finalModel)) :=
  runAux (policy := policy) (retryPolicy := retryPolicy) fuel config baseUrl apiKey source
    sourceEventSeqs sourcesNodup sourcesEarlier 0 before runner

/-! ## Executable fixture -/

namespace Example

def loop : IO (Except (ConversationError RetryPolicy.default)
    (Sigma fun finalRunner : ConversationRunner =>
      Sigma fun finalModel : Nat =>
        RetryCancellableRunResult (CancellationPolicy.atRound 1 .timeout)
          (retryPolicy := RetryPolicy.default) Cordis.Harness.counterConfig
          DeepSeekStreamHarnessRetryConversation.Example.loopProcess "https://fixture.invalid"
          { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by
            intro current source sourceMem
            cases sourceMem)
          DeepSeekStreamHarnessRetryConversation.Example.counterRunner 0 finalRunner finalModel)) :=
  run (policy := CancellationPolicy.atRound 1 .timeout)
    (retryPolicy := RetryPolicy.default) 2
    DeepSeekStreamHarnessRetryConversation.Example.loopProcess "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig []
    (by simp) (by
      intro current source sourceMem
      cases sourceMem)
    0 DeepSeekStreamHarnessRetryConversation.Example.counterRunner

end Example

end Cordis.DeepSeekStreamHarnessRetryCancellation
