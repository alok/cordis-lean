import Cordis.DeepSeekHarnessTransportRetryConversation
import Cordis.DeepSeekHarnessCancellation

/-!
# Retry-aware cancellation at the injected transport boundary

This module composes the complete-body injected `Transport` retry loop with the existing
pre-round cancellation policy.  A successful result retains the indexed retry trace, including
every retry history and the final runner/model endpoint; a cancellation result retains the exact
completed prefix and proves that no request was issued after the decision.  The two controls are
kept separate: retryable transport/status failures remain in `RetryRoundError`, while cancellation
is a successful typed stop.

The boundary is deliberately immediate and caller-driven.  It does not prove provider backoff,
idempotency, cancellation of an in-flight request, persistence, external effects, fairness, or
deployed Harness retry/cancellation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessTransportRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessRetry
open Cordis.DeepSeekHarnessTransportRetry
open Cordis.DeepSeekHarnessTransportRetryConversation

/-! ## Indexed terminal stop -/

inductive RetryCancellableTransportStop
    (cancellationPolicy : CancellationPolicy)
    (retryPolicy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
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
      (last : RetryTransportRoundBox retryPolicy cfg baseUrl apiKey source sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (runner_eq : last.round.round.finalRunner = finalRunner)
      (model_eq : last.round.round.finalModel = finalModel)
      (noToolCalls : RetryTransportRoundBox.noToolCalls last)
  | fuelExhausted
  | cancelled
      {runner : ConversationRunner}
      {before : Model}
      (round : Nat)
      (reason : CancelReason)
      (decided : cancellationPolicy.decide round runner = true)

namespace RetryCancellableTransportStop

def isCompleted
    {cancellationPolicy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat} {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableTransportStop cancellationPolicy retryPolicy cfg baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Bool
  | .completed .. => true
  | .fuelExhausted | .cancelled .. => false

def isFuelExhausted
    {cancellationPolicy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat} {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableTransportStop cancellationPolicy retryPolicy cfg baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Bool
  | .completed .. | .cancelled .. => false
  | .fuelExhausted => true

def isCancelled
    {cancellationPolicy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat} {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableTransportStop cancellationPolicy retryPolicy cfg baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Bool
  | .completed .. | .fuelExhausted => false
  | .cancelled .. => true

def cancelledRound
    {cancellationPolicy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat} {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableTransportStop cancellationPolicy retryPolicy cfg baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Option Nat
  | .completed .. | .fuelExhausted => none
  | .cancelled round .. => some round

def cancelledReason
    {cancellationPolicy : CancellationPolicy}
    {retryPolicy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {sourceEventSeqs : List Nat} {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {finalRunner : ConversationRunner} {finalModel : Model} :
    RetryCancellableTransportStop cancellationPolicy retryPolicy cfg baseUrl apiKey source
      sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel → Option CancelReason
  | .completed .. | .fuelExhausted => none
  | .cancelled _ reason _ => some reason

end RetryCancellableTransportStop

/-! ## Dependent result and terminal facts -/

structure RetryCancellableTransportRunResult
    (cancellationPolicy : CancellationPolicy)
    (retryPolicy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
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
  trace : RetryTransportTrace retryPolicy cfg baseUrl apiKey source sourceEventSeqs
    sourcesNodup sourcesEarlier initialRunner initialModel finalRunner finalModel
  stop : RetryCancellableTransportStop cancellationPolicy retryPolicy cfg baseUrl apiKey source
    sourceEventSeqs sourcesNodup sourcesEarlier finalRunner finalModel

/-! ## Fuel-bounded execution -/

def runAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (cancellationPolicy : CancellationPolicy)
    (retryPolicy : RetryPolicy)
    (transport : Transport)
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
    IO (Except (RetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RetryCancellableTransportRunResult cancellationPolicy retryPolicy cfg baseUrl apiKey
            source sourceEventSeqs sourcesNodup sourcesEarlier runner before finalRunner
            finalModel)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨runner, ⟨before, {
        trace := .nil runner before
        stop := .fuelExhausted
      }⟩⟩)
  | fuel + 1 =>
      if decided : cancellationPolicy.decide round runner then
        pure (.ok ⟨runner, ⟨before, {
          trace := .nil runner before
          stop := .cancelled (before := before) round cancellationPolicy.reason decided
        }⟩⟩)
      else
        match ← executeSource retryPolicy transport baseUrl apiKey source cfg before runner
            sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
        | .error error => pure (.error error)
        | .ok ⟨plan, ⟨body, roundResult⟩⟩ =>
            let head : RetryTransportRoundBox retryPolicy cfg baseUrl apiKey source
                sourceEventSeqs sourcesNodup sourcesEarlier runner before := {
              plan
              body
              round := roundResult
            }
            let callCount :=
              head.round.round.accepted.validated.response.choices.head.message.toolCalls.length
            if noTools : callCount = 0 then
              pure (.ok ⟨roundResult.round.finalRunner, ⟨roundResult.round.finalModel, {
                trace := .cons head
                  (.nil roundResult.round.finalRunner roundResult.round.finalModel)
                stop := .completed head rfl rfl noTools
              }⟩⟩)
            else
                match ← runAux fuel cancellationPolicy retryPolicy transport baseUrl
                  apiKey source sourceEventSeqs sourcesNodup sourcesEarlier (round + 1)
                  roundResult.round.finalModel roundResult.round.finalRunner with
              | .error error => pure (.error error)
              | .ok ⟨finalRunner, ⟨finalModel, tail⟩⟩ =>
                  pure (.ok ⟨finalRunner, ⟨finalModel, {
                    trace := .cons head tail.trace
                    stop := tail.stop
                  }⟩⟩)

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (cancellationPolicy : CancellationPolicy)
    (retryPolicy : RetryPolicy)
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (RetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          RetryCancellableTransportRunResult cancellationPolicy retryPolicy cfg baseUrl apiKey
            source sourceEventSeqs sourcesNodup sourcesEarlier runner before finalRunner
            finalModel)) :=
  runAux fuel cancellationPolicy retryPolicy transport baseUrl apiKey source sourceEventSeqs
    sourcesNodup sourcesEarlier 0 before runner

/-! ## Executable cancellation and retry fixtures -/

namespace Example

def retryPolicy : RetryPolicy where
  maxRetries := 1
  retryTransport := true
  retryTransientHttp := true

def cancellationPolicy : CancellationPolicy :=
  CancellationPolicy.atRound 0 .peerFailure

def neverCancellation : CancellationPolicy :=
  CancellationPolicy.never .user

def retryTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.set (index + 1)
    pure (.ok {
      status := if index = 0 then 503 else 200
      body := if index = 0 then "busy"
        else if index = 1 then DeepSeekHarness.counterResponseBody
        else DeepSeekHarness.counterFinalResponseBody
    })

def cancellationRun : IO (Except (RetryRoundError retryPolicy)
    (Sigma fun finalRunner : ConversationRunner =>
      Sigma fun finalModel : Nat =>
        RetryCancellableTransportRunResult cancellationPolicy retryPolicy
          Cordis.Harness.counterConfig "https://fixture.invalid" { value := "fixture-key" }
          DeepSeekHarness.counterRequestSource [] (by simp) (by simp)
          (ConversationRunner.empty 1) 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  run cancellationPolicy retryPolicy 2 (retryTransport calls) "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by simp) 0
    (ConversationRunner.empty 1)

def successRun : IO (Except (RetryRoundError retryPolicy)
    (Sigma fun finalRunner : ConversationRunner =>
      Sigma fun finalModel : Nat =>
        RetryCancellableTransportRunResult neverCancellation retryPolicy
          Cordis.Harness.counterConfig "https://fixture.invalid" { value := "fixture-key" }
          DeepSeekHarness.counterRequestSource [] (by simp) (by simp)
          (ConversationRunner.empty 1) 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  run neverCancellation retryPolicy 2 (retryTransport calls) "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by simp) 0
    (ConversationRunner.empty 1)

end Example

end Cordis.DeepSeekHarnessTransportRetryCancellation
