import Cordis.DeepSeekHarness

/-!
# Explicit complete-request retry

`DeepSeekApi.execute` deliberately exposes one transport attempt. This module adds a separate,
opt-in retry policy around that attempt. Retryable transport and transient HTTP failures are
retained in a proof-carrying history; response decoding failures and API error bodies remain
non-retryable by default. The request plan is reused definitionally for every attempt, so a
caller never silently retries a different body.

This is a complete-body, immediate-retry boundary. It does not claim provider backoff policy,
idempotency of arbitrary tools, cancellation, asynchronous scheduling, persistence, or deployed
DeepSeek-Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner

/-! ## Retry policy and history -/

structure RetryPolicy where
  maxRetries : Nat
  retryTransport : Bool := true
  retryTransientHttp : Bool := true
deriving DecidableEq, Repr

def RetryPolicy.default : RetryPolicy where
  maxRetries := 2
  retryTransport := true
  retryTransientHttp := true

def retryableHttpStatus (status : Nat) : Bool :=
  status = 408 || status = 429 || (500 ≤ status && status < 600)

def RetryPolicy.retryable (policy : RetryPolicy) : ClientError -> Bool
  | .transport _ => policy.retryTransport
  | .httpStatus status _ => policy.retryTransientHttp && retryableHttpStatus status
  | .response _ => false

structure RetryHistory (policy : RetryPolicy) where
  failures : List ClientError
  failures_le : failures.length ≤ policy.maxRetries

namespace RetryHistory

def attemptCount {policy : RetryPolicy} (history : RetryHistory policy) : Nat :=
  history.failures.length + 1

theorem attemptCount_le_maxAttempts
    {policy : RetryPolicy}
    (history : RetryHistory policy) :
    history.attemptCount ≤ policy.maxRetries + 1 := by
  dsimp [attemptCount]
  have failures_le := history.failures_le
  omega

end RetryHistory

inductive RetryResult (policy : RetryPolicy) (plan : RequestPlan) where
  | succeeded
      (history : RetryHistory policy)
      (result : Sigma fun body : String => ValidatedResponse body)
  | failed
      (history : RetryHistory policy)
      (terminal : ClientError)

namespace RetryResult

def history {policy : RetryPolicy} {plan : RequestPlan} :
    RetryResult policy plan -> RetryHistory policy
  | .succeeded history _ | .failed history _ => history

def attemptCount {policy : RetryPolicy} {plan : RequestPlan}
    (result : RetryResult policy plan) : Nat :=
  (result.history).attemptCount

def finalError {policy : RetryPolicy} {plan : RequestPlan}
    (result : RetryResult policy plan) : Option ClientError :=
  match result with
  | .succeeded _ _ => none
  | .failed _ error => some error

theorem attemptCount_le_maxAttempts
    {policy : RetryPolicy} {plan : RequestPlan}
    (result : RetryResult policy plan) :
    result.attemptCount ≤ policy.maxRetries + 1 := by
  exact RetryHistory.attemptCount_le_maxAttempts result.history

theorem succeeded_attemptCount
    {policy : RetryPolicy} {plan : RequestPlan}
    (history : RetryHistory policy)
    (result : Sigma fun body : String => ValidatedResponse body) :
    (RetryResult.succeeded (plan := plan) history result).attemptCount =
      history.failures.length + 1 :=
  rfl

end RetryResult

/-! ## Retrying one fixed request plan -/

def executeWithRetryAux
    (policy : RetryPolicy)
    (transport : Transport)
    (plan : RequestPlan) :
    (remaining : Nat) ->
      (history : RetryHistory policy) ->
      history.failures.length + remaining = policy.maxRetries ->
      IO (RetryResult policy plan)
  | remaining, history, budget => do
      match ← DeepSeekApi.execute transport plan with
      | .ok result => pure (.succeeded history result)
      | .error error =>
          if hRemaining : remaining = 0 then
            pure (.failed history error)
          else if hRetry : policy.retryable error then
            let nextHistory : RetryHistory policy := {
              failures := history.failures ++ [error]
              failures_le := by
                rw [List.length_append]
                simp only [List.length_cons, List.length_nil]
                omega
            }
            executeWithRetryAux policy transport plan (remaining - 1) nextHistory (by
              rw [List.length_append]
              simp only [List.length_cons, List.length_nil]
              omega)
          else
            pure (.failed history error)
termination_by remaining => remaining
decreasing_by omega

def executeWithRetry
    (policy : RetryPolicy)
    (transport : Transport)
    (plan : RequestPlan) :
    IO (RetryResult policy plan) :=
  let history : RetryHistory policy := {
    failures := []
    failures_le := by simp
  }
  executeWithRetryAux policy transport plan policy.maxRetries history (by
    simp [history])

theorem retryPlan_body_eq
    (plan : RequestPlan) :
    plan.request.body = Lean.Json.compress plan.source.toJson :=
  plan.body_eq

theorem retryResult_attemptCount_le
    {policy : RetryPolicy} {plan : RequestPlan}
    (result : RetryResult policy plan) :
    result.attemptCount ≤ policy.maxRetries + 1 :=
  result.attemptCount_le_maxAttempts

/-! ## Conversation continuation with retry evidence -/

inductive RetryConversationError (policy : RetryPolicy) where
  | request (error : RequestError)
  | client (history : RetryHistory policy) (error : ClientError)
  | response (error : ApiSessionError)
  | tool (error : ToolRoundError)

structure RetriedConversationRoundResult
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  accepted : AcceptedApiResponse body
  retryHistory : RetryHistory policy
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  executions : List (ExecutedTool cfg)
  executions_eq :
    executeFunctionCalls cfg before
        accepted.validated.response.choices.head.message.toolCalls =
      .ok (finalModel, executions)
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq

def executeConversationRoundRetry
    (policy : RetryPolicy)
    {Model Capability : Type}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except (RetryConversationError policy)
      (Sigma fun body : String => RetriedConversationRoundResult policy cfg before body)) := do
  match buildTypedCompleteRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeWithRetry policy transport plan.requestPlan with
      | .failed history error => pure (.error (.client history error))
      | .succeeded history ⟨body, _validated⟩ =>
          match acceptResponse body with
          | .error error => pure (.error (.response error))
          | .ok accepted =>
              let assistantSeq := runner.session.nextSeq
              let assistantRunner := ConversationRunner.appendAcceptedApi runner accepted
                sourceEventSeqs sourcesNodup sourcesEarlier
              have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
                rw [ConversationRunner.appendAcceptedApi_nextSeq]
                exact Nat.lt_succ_self _
              match executionEq : executeFunctionCalls cfg before
                  accepted.validated.response.choices.head.message.toolCalls with
              | .error error => pure (.error (.tool error))
              | .ok (finalModel, executions) =>
                  let finalRunner := ConversationRunner.appendToolResults assistantRunner
                    runner.nextCall assistantSeq executions assistantSeqEarlier
                  pure (.ok ⟨body, {
                    accepted
                    retryHistory := history
                    assistantRunner
                    runner := finalRunner
                    finalModel
                    executions
                    executions_eq := executionEq
                    assistantSeq
                    assistantSeq_eq := by
                      change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                      rw [ConversationRunner.appendAcceptedApi_nextSeq]
                  }⟩)

theorem retriedRound_history_bound
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} {body : String}
    (round : RetriedConversationRoundResult policy cfg before body) :
    round.retryHistory.failures.length ≤ policy.maxRetries :=
  round.retryHistory.failures_le

end Cordis.DeepSeekHarnessRetry
