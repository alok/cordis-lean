import Cordis.DeepSeekHarnessCancellation
import Cordis.DeepSeekStreamHarness

/-!
# Boundary-safe cancellation for streamed Harness rounds

This module lifts the existing pre-round cancellation contract over the proof-carrying streamed
conversation loop. A policy is checked before each complete process-backed stream round; a
cancellation result retains the exact streamed-round prefix, runner, and model endpoint. Fuel
exhaustion and a text-only terminal response remain distinct typed stops.

This is deliberately not an in-flight IO cancellation theorem. It does not interrupt a blocked
process read, HTTP request, stream reader, or external tool, and it does not claim cleanup,
backpressure, reconnect, or deployed Harness cancellation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

inductive CancellableStop
    (policy : CancellationPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (runner : ConversationRunner) where
  | completed
      (last : StreamConversationWitness cfg)
      (noToolCalls : StreamConversationWitness.noToolCalls last)
  | fuelExhausted
  | cancelled
      (round : Nat)
      (reason : CancelReason)
      (decided : policy.decide round runner = true)

namespace CancellableStop

def isCancelled
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner → Bool
  | .completed _ _ | .fuelExhausted => false
  | .cancelled _ _ _ => true

def isFuelExhausted
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner → Bool
  | .completed _ _ | .cancelled _ _ _ => false
  | .fuelExhausted => true

def cancelledRound
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner → Option Nat
  | .completed _ _ | .fuelExhausted => none
  | .cancelled round _ _ => some round

def cancelledReason
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner → Option CancelReason
  | .completed _ _ | .fuelExhausted => none
  | .cancelled _ reason _ => some reason

end CancellableStop

structure CancellableRunResult
    (policy : CancellationPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (StreamConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : CancellableStop policy cfg runner

namespace CancellableRunResult

theorem cancelled_runner_is_endpoint
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {rounds : List (StreamConversationWitness cfg)}
    {runner : ConversationRunner}
    {before : Model}
    (round : Nat)
    (reason : CancelReason)
    (decided : policy.decide round runner = true) :
    (CancellableRunResult.mk rounds runner before
      (.cancelled round reason decided)).runner = runner := rfl

theorem cancelled_model_is_endpoint
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {rounds : List (StreamConversationWitness cfg)}
    {runner : ConversationRunner}
    (before : Model)
    (round : Nat)
    (reason : CancelReason)
    (decided : policy.decide round runner = true) :
    (CancellableRunResult.mk rounds runner before
      (.cancelled round reason decided)).finalModel = before := rfl

end CancellableRunResult

def runConversationMultiStreamCancellableAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (policy : CancellationPolicy)
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
    (runner : ConversationRunner)
    (history : List (StreamConversationWitness cfg)) :
    IO (Except StreamConversationError (CancellableRunResult policy cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      if decided : policy.decide round runner then
        pure (.ok {
          rounds := history
          runner
          finalModel := before
          stop := .cancelled round policy.reason decided
        })
      else
        match ← executeConversationStreamRound finishMulti config baseUrl apiKey source cfg before
            runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
        | .error error => pure (.error error)
        | .ok ⟨body, roundResult⟩ =>
            let witness : StreamConversationWitness cfg := ⟨before, ⟨body, roundResult⟩⟩
            let nextHistory := history ++ [witness]
            if noTools : StreamConversationWitness.noToolCalls witness then
              pure (.ok {
                rounds := nextHistory
                runner := roundResult.runner
                finalModel := roundResult.finalModel
                stop := .completed witness noTools
              })
            else
              runConversationMultiStreamCancellableAux policy fuel config baseUrl apiKey source
                sourceEventSeqs sourcesNodup sourcesEarlier (round + 1)
                roundResult.finalModel roundResult.runner nextHistory
termination_by fuel

def runConversationMultiStreamCancellable
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (policy : CancellationPolicy)
    (fuel : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except StreamConversationError (CancellableRunResult policy cfg)) :=
  runConversationMultiStreamCancellableAux policy fuel config baseUrl apiKey source sourceEventSeqs
    sourcesNodup sourcesEarlier 0 before runner []

end Cordis.DeepSeekStreamHarnessCancellation
