import Cordis.DeepSeekStreamHarness

/-!
# Explicit complete-body retry for streamed Harness rounds

`DeepSeekCurlSession.executeWith` deliberately exposes one process-backed complete-body attempt.
This module adds an opt-in retry policy around the streamed terminal boundary. Process failures
and transient HTTP statuses can be retried; malformed SSE, semantic response failures, and tool
execution failures remain terminal. Every retry retains the exact `SessionClientError` history,
and the same request is supplied to every attempt by construction.

The round result reuses the existing streamed assistant/tool certificates. This is not a claim
about backoff, idempotency of arbitrary tools, cancellation, reconnects, incremental delivery,
persistence, or equivalence to the deployed DeepSeek Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarnessRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness

/-! ## Retry policy and history -/

structure RetryPolicy where
  maxRetries : Nat
  retryProcess : Bool := true
  retryTransientHttp : Bool := true
deriving DecidableEq, Repr

def RetryPolicy.default : RetryPolicy where
  maxRetries := 2
  retryProcess := true
  retryTransientHttp := true

def retryableHttpStatus (status : Nat) : Bool :=
  status = 408 || status = 429 || (500 ≤ status && status < 600)

def RetryPolicy.retryable (policy : RetryPolicy) : SessionClientError → Bool
  | .transport (.process _) => policy.retryProcess
  | .transport (.httpStatus status _) =>
      policy.retryTransientHttp && retryableHttpStatus status
  | .transport (.stream _) => false
  | .response _ => false

structure RetryHistory (policy : RetryPolicy) where
  failures : List SessionClientError
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

abbrev ProcessedStreamResponse :=
  Sigma fun body : String => ProcessedResponse body

inductive RetryResult (policy : RetryPolicy) where
  | succeeded
      (history : RetryHistory policy)
      (result : ProcessedStreamResponse)
  | failed
      (history : RetryHistory policy)
      (terminal : SessionClientError)

namespace RetryResult

def history {policy : RetryPolicy} : RetryResult policy → RetryHistory policy
  | .succeeded history _ | .failed history _ => history

def attemptCount {policy : RetryPolicy} (result : RetryResult policy) : Nat :=
  result.history.attemptCount

def finalError {policy : RetryPolicy} (result : RetryResult policy) :
    Option SessionClientError :=
  match result with
  | .succeeded _ _ => none
  | .failed _ error => some error

theorem attemptCount_le_maxAttempts
    {policy : RetryPolicy}
    (result : RetryResult policy) :
    result.attemptCount ≤ policy.maxRetries + 1 := by
  exact RetryHistory.attemptCount_le_maxAttempts result.history

end RetryResult

/-! ## Retrying the complete streamed response -/

def executeWithRetryAux
    (policy : RetryPolicy)
    (attempt : IO (Except SessionClientError ProcessedStreamResponse)) :
    (remaining : Nat) →
      (history : RetryHistory policy) →
      history.failures.length + remaining = policy.maxRetries →
      IO (RetryResult policy)
  | remaining, history, budget => do
      match ← attempt with
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
            executeWithRetryAux policy attempt (remaining - 1) nextHistory (by
              rw [List.length_append]
              simp only [List.length_cons, List.length_nil]
              omega)
          else
            pure (.failed history error)
termination_by remaining => remaining
decreasing_by omega

def executeWithRetry
    (policy : RetryPolicy)
    (config : ProcessConfig)
    (request : HttpRequest) :
    IO (RetryResult policy) :=
  let history : RetryHistory policy := {
    failures := []
    failures_le := by simp
  }
  executeWithRetryAux policy (DeepSeekCurlSession.executeWith finishMulti config request)
    policy.maxRetries history (by simp [history])

theorem retryRequest_body_eq
    (plan : RequestPlan) :
    plan.request.body = Lean.Json.compress plan.source.toJson :=
  plan.body_eq

/-! ## Streamed conversation round with retry evidence -/

inductive ConversationError (policy : RetryPolicy) where
  | request (error : RequestError)
  | client (history : RetryHistory policy) (error : SessionClientError)
  | tool (error : ToolRoundError)

structure ConversationRoundResult
    (policy : RetryPolicy)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  round : StreamConversationRoundResult cfg before body
  retryHistory : RetryHistory policy

def executeConversationMultiStreamRound
    (policy : RetryPolicy)
    {Model Capability : Type}
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except (ConversationError policy)
      (Sigma fun body : String => ConversationRoundResult policy cfg before body)) := do
  match buildTypedStreamingRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeWithRetry policy config plan.request with
      | .failed history error => pure (.error (.client history error))
      | .succeeded history ⟨body, processed⟩ =>
          let assistantSeq := runner.session.nextSeq
          let assistantRunner := ConversationRunner.appendFinished runner processed.finished
            sourceEventSeqs sourcesNodup sourcesEarlier
          have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
            rw [ConversationRunner.appendFinished_nextSeq]
            exact Nat.lt_succ_self _
          match executionEq : executeFunctionCalls cfg before
              (finishedFunctionCalls processed.finished) with
          | .error error => pure (.error (.tool error))
          | .ok (finalModel, executions) =>
              let finalRunner := ConversationRunner.appendToolResults assistantRunner
                runner.nextCall assistantSeq executions assistantSeqEarlier
              pure (.ok ⟨body, {
                round := {
                  finished := processed.finished
                  assistantRunner
                  runner := finalRunner
                  finalModel
                  executions
                  executions_eq := executionEq
                  assistantSeq
                  assistantSeq_eq := by
                    change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                    rw [ConversationRunner.appendFinished_nextSeq]
                }
                retryHistory := history
              }⟩)

theorem conversationRound_history_bound
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model} {body : String}
    (round : ConversationRoundResult policy cfg before body) :
    round.retryHistory.failures.length ≤ policy.maxRetries :=
  round.retryHistory.failures_le

/-! ## Deterministic process fixtures -/

def fixtureStreamProcess (body : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-stream-retry-fixture",
    body
  ]

def fixtureTransientHttpProcess (body : String) : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf 'temporary\\n__CORDIS_HTTP_STATUS__503\\n'",
    "cordis-stream-retry-transient-fixture",
    body
  ]

end Cordis.DeepSeekStreamHarnessRetry
