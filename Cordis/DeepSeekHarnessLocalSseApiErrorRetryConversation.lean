import Cordis.DeepSeekHarnessLocalSseApiErrorRetry

/-!
# Two-round loopback API-error retry conversation

This module lifts the typed 429-then-success loopback retry into a dependent conversation. Each
round starts from the exact `ConversationRunner` produced by the preceding accepted response; a
second request is therefore rebuilt at a genuinely later session index rather than merely replaying
the first request twice. Both first-attempt API-error envelopes, accepted terminal outcomes, append
endpoints, request counts, and clean process exits remain available in the result.

The fixture is a finite local witness. It does not establish provider authenticity, backoff,
idempotency of external effects, cancellation, reconnect semantics, credential/TLS validity,
persistence, or deployed Harness retry/conversation equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessLocalSseApiErrorRetryConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessLocalSseOutcome
open Cordis.DeepSeekHarnessLocalSseApiErrorRetry
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekTerminalOutcome

def dispatchedRunner {body : String} : OutcomeDispatch body → ConversationRunner
  | .providerFailure _ runner => runner
  | .appended _ runner => runner

theorem appended_endpoint_eq
    {source : RequestSource} {runner : ConversationRunner} {body : String}
    (result : OutcomeResult source runner body)
    {finished : FinishedResponse body} {after : ConversationRunner}
    (h : result.dispatch = .appended finished after) :
    after = ConversationRunner.appendFinished runner finished [] (by simp) (by simp) := by
  have hd := result.dispatch_eq
  cases outcome : result.processed.outcome with
  | failure validated =>
      simp [outcome, dispatchOutcome, h] at hd
  | text validated =>
      cases hf : finishResponse (.text validated) with
      | error error => simp [outcome, dispatchOutcome, hf, h] at hd
      | ok finished' =>
          simp [outcome, dispatchOutcome, hf] at hd
          rw [h] at hd
          cases hd
          rfl
  | tool validated =>
      cases hf : finishResponse (.tool validated) with
      | error error => simp [outcome, dispatchOutcome, hf, h] at hd
      | ok finished' =>
          simp [outcome, dispatchOutcome, hf] at hd
          rw [h] at hd
          cases hd
          rfl
  | mixed validated =>
      cases hf : finishResponse (.mixed validated) with
      | error error => simp [outcome, dispatchOutcome, hf, h] at hd
      | ok finished' =>
          simp [outcome, dispatchOutcome, hf] at hd
          rw [h] at hd
          cases hd
          rfl
  | multi validated =>
      cases hf : finishResponse (.multi validated) with
      | error error => simp [outcome, dispatchOutcome, hf, h] at hd
      | ok finished' =>
          simp [outcome, dispatchOutcome, hf] at hd
          rw [h] at hd
          cases hd
          rfl

structure ApiErrorRetryConversationResult
    (source : RequestSource)
    (runner : ConversationRunner) where
  firstErrorBody : String
  firstSuccessBody : String
  first : ApiErrorRetryResult source runner firstErrorBody firstSuccessBody
  firstFinished : FinishedResponse firstSuccessBody
  firstAfter : ConversationRunner
  first_dispatch_eq : first.accepted.dispatch = .appended firstFinished firstAfter
  secondErrorBody : String
  secondSuccessBody : String
  second : ApiErrorRetryResult source firstAfter secondErrorBody secondSuccessBody
  secondFinished : FinishedResponse secondSuccessBody
  secondAfter : ConversationRunner
  second_dispatch_eq : second.accepted.dispatch = .appended secondFinished secondAfter

namespace ApiErrorRetryConversationResult

theorem first_endpoint_eq
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.firstAfter = ConversationRunner.appendFinished runner result.firstFinished []
      (by simp) (by simp) :=
  appended_endpoint_eq result.first.accepted result.first_dispatch_eq

theorem second_endpoint_eq
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.secondAfter =
      ConversationRunner.appendFinished result.firstAfter result.secondFinished []
        (by simp) (by simp) :=
  appended_endpoint_eq result.second.accepted result.second_dispatch_eq

theorem first_session_advance
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.firstAfter.session.nextSeq = runner.session.nextSeq + 1 := by
  rw [result.first_endpoint_eq]
  exact ConversationRunner.appendFinished_nextSeq runner result.firstFinished [] (by simp) (by simp)

theorem second_session_advance
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.secondAfter.session.nextSeq = result.firstAfter.session.nextSeq + 1 := by
  rw [result.second_endpoint_eq]
  exact ConversationRunner.appendFinished_nextSeq result.firstAfter result.secondFinished []
    (by simp) (by simp)

theorem session_advance_twice
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.secondAfter.session.nextSeq = runner.session.nextSeq + 2 := by
  rw [result.second_endpoint_eq, result.first_endpoint_eq]
  rw [ConversationRunner.appendFinished_nextSeq]
  rw [ConversationRunner.appendFinished_nextSeq]

theorem first_attempts_are_two
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.first.attempts = 2 :=
  result.first.attempts_eq

theorem second_attempts_are_two
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.second.attempts = 2 :=
  result.second.attempts_eq

theorem first_requests_are_valid
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.first.accepted.requests = 2 ∧ result.first.accepted.validRequests = 2 :=
  ⟨result.first.requests_eq, result.first.valid_requests_eq⟩

theorem second_requests_are_valid
    {source : RequestSource} {runner : ConversationRunner}
    (result : ApiErrorRetryConversationResult source runner) :
    result.second.accepted.requests = 2 ∧ result.second.accepted.validRequests = 2 :=
  ⟨result.second.requests_eq, result.second.valid_requests_eq⟩

end ApiErrorRetryConversationResult

inductive ApiErrorRetryConversationError where
  | first (error : LocalApiErrorRetryError)
  | firstNotAppended
  | second (error : LocalApiErrorRetryError)
  | secondNotAppended
deriving DecidableEq, Repr

def runTwoRounds
    (source : RequestSource)
    (runner : ConversationRunner)
    (key : ApiKey)
    (errorBody : String)
    (successBody : String)
    (maxReads : Nat := 64) :
    IO (Except ApiErrorRetryConversationError (ApiErrorRetryConversationResult source runner)) := do
  match ← DeepSeekHarnessLocalSseApiErrorRetry.runWithKey source runner key errorBody successBody
      maxReads with
  | .error error => pure (.error (.first error))
  | .ok ⟨firstErrorBody, ⟨firstSuccessBody, first⟩⟩ =>
      match hFirst : first.accepted.dispatch with
      | .providerFailure _ _ => pure (.error .firstNotAppended)
      | .appended firstFinished firstAfter =>
          match ← DeepSeekHarnessLocalSseApiErrorRetry.runWithKey source firstAfter key errorBody
              successBody maxReads with
          | .error error => pure (.error (.second error))
          | .ok ⟨secondErrorBody, ⟨secondSuccessBody, second⟩⟩ =>
              match hSecond : second.accepted.dispatch with
              | .providerFailure _ _ => pure (.error .secondNotAppended)
              | .appended secondFinished secondAfter =>
                  pure (.ok {
                    firstErrorBody
                    firstSuccessBody
                    first
                    firstFinished
                    firstAfter
                    first_dispatch_eq := hFirst
                    secondErrorBody
                    secondSuccessBody
                    second
                    secondFinished
                    secondAfter
                    second_dispatch_eq := hSecond
                  })

namespace Example

abbrev Source : RequestSource := DeepSeekHarness.counterRequestSource

def runner : ConversationRunner := DeepSeekHarnessLocalSseApiErrorRetry.Example.runner

def errorBody : String := DeepSeekHarnessLocalSseApiErrorRetry.Example.errorBody

def successBody : String := DeepSeekHarnessLocalSseApiErrorRetry.Example.successBody

def run : IO (Except ApiErrorRetryConversationError
    (ApiErrorRetryConversationResult Source runner)) :=
  runTwoRounds Source runner { value := "fixture-key" } errorBody successBody 64

end Example

end Cordis.DeepSeekHarnessLocalSseApiErrorRetryConversation
