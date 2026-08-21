import Cordis.DeepSeekHarness

/-!
# Boundary-safe conversation cancellation

The complete-body conversation runner already has an explicit fuel stop, but the deployed Harness
also needs a caller-controlled cancellation decision. This module adds that decision at a precise
boundary: the policy is checked before each request round, and a cancellation result retains the
unchanged runner, model, and completed-round prefix. No request is issued after the decision.

The boundary is intentionally not an IO cancellation theorem. It does not interrupt an already
running process, HTTP request, stream reader, or external tool; those require an adapter-specific
cancel token and cleanup proof.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness

/-! ## Decision vocabulary -/

inductive CancelReason where
  | user
  | timeout
  | peerFailure
deriving DecidableEq, Repr

def reasonText : CancelReason -> String
  | .user => "cancelled:user"
  | .timeout => "cancelled:timeout"
  | .peerFailure => "cancelled:peer-failure"

structure CancellationPolicy where
  reason : CancelReason
  decide : Nat -> ConversationRunner -> Bool

namespace CancellationPolicy

def never (reason : CancelReason := .user) : CancellationPolicy where
  reason
  decide := fun _ _ => false

def atRound (round : Nat) (reason : CancelReason) : CancellationPolicy where
  reason
  decide := fun current _ => current = round

theorem never_decide
    (reason : CancelReason) (round : Nat) (runner : ConversationRunner) :
    (never reason).decide round runner = false := rfl

theorem atRound_decide
    (round target : Nat) (reason : CancelReason) (runner : ConversationRunner) :
    (atRound target reason).decide round runner = (round == target) := by
  rfl

end CancellationPolicy

/-! ## Indexed stop and result -/

inductive CancellableStop
    (policy : CancellationPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (runner : ConversationRunner) where
  | completed
      (last : ConversationWitness cfg)
      (noToolCalls : ConversationWitness.noToolCalls last)
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
    CancellableStop policy cfg runner -> Bool
  | .completed _ _ | .fuelExhausted => false
  | .cancelled _ _ _ => true

def isFuelExhausted
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner -> Bool
  | .completed _ _ | .cancelled _ _ _ => false
  | .fuelExhausted => true

def cancelledRound
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner -> Option Nat
  | .completed _ _ | .fuelExhausted => none
  | .cancelled round _ _ => some round

def cancelledReason
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {runner : ConversationRunner} :
    CancellableStop policy cfg runner -> Option CancelReason
  | .completed _ _ | .fuelExhausted => none
  | .cancelled _ reason _ => some reason

end CancellableStop

structure CancellableRunResult
    (policy : CancellationPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (ConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : CancellableStop policy cfg runner

namespace CancellableRunResult

theorem cancelled_runner_is_endpoint
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {rounds : List (ConversationWitness cfg)}
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
    {rounds : List (ConversationWitness cfg)}
    {runner : ConversationRunner}
    (before : Model)
    (round : Nat)
    (reason : CancelReason)
    (decided : policy.decide round runner = true) :
    (CancellableRunResult.mk rounds runner before
      (.cancelled round reason decided)).finalModel = before := rfl

end CancellableRunResult

/-! ## Cancellable fuel-bounded runner -/

def runConversationCancellableAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (policy : CancellationPolicy)
    (fuel : Nat)
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
    (runner : ConversationRunner)
    (history : List (ConversationWitness cfg)) :
    IO (Except ConversationError (CancellableRunResult policy cfg)) := do
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
        match ← executeConversationRound transport baseUrl apiKey source cfg before runner
            sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
        | .error error => pure (.error error)
        | .ok ⟨body, roundResult⟩ =>
            let witness : ConversationWitness cfg := ⟨before, ⟨body, roundResult⟩⟩
            let nextHistory := history ++ [witness]
            if noTools : ConversationWitness.noToolCalls witness then
              pure (.ok {
                rounds := nextHistory
                runner := roundResult.runner
                finalModel := roundResult.finalModel
                stop := .completed witness noTools
              })
            else
              runConversationCancellableAux policy fuel transport baseUrl apiKey source
                sourceEventSeqs sourcesNodup sourcesEarlier (round + 1)
                roundResult.finalModel roundResult.runner nextHistory

def runConversationCancellable
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (policy : CancellationPolicy)
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
    IO (Except ConversationError (CancellableRunResult policy cfg)) :=
  runConversationCancellableAux policy fuel transport baseUrl apiKey source sourceEventSeqs
    sourcesNodup sourcesEarlier 0 before runner []

theorem cancelled_round_has_no_new_history
    {policy : CancellationPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {history : List (ConversationWitness cfg)}
    {runner : ConversationRunner}
    {before : Model}
    (round : Nat)
    (reason : CancelReason)
    (decided : policy.decide round runner = true) :
    (CancellableRunResult.mk history runner before
      (.cancelled round reason decided)).rounds = history := rfl

end Cordis.DeepSeekHarnessCancellation
