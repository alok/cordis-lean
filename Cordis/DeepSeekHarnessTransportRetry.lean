import Cordis.DeepSeekHarnessPersistenceTransportRound
import Cordis.DeepSeekHarnessRetry

/-!
# Single-decoder retry over the typed Harness transport boundary

The existing retry policy is retained here, but the successful attempt is sent through the
single-decoder ValidatedResponse path. A request plan is built once, retryable transport and
transient-HTTP failures are retained in ordered RetryHistory, and a successful body is validated
once before acceptValidated and typed tool execution. The result therefore reconnects retry
evidence to the same assistant/tool endpoint certificate as the non-retrying round.

This is immediate bounded retry over an injected complete-body transport. It does not establish
provider backoff or idempotency, cancellation of an in-flight request, persistence, external
effect correctness, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessTransportRetry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistenceTransportRound
open Cordis.DeepSeekHarnessRetry

private def successfulStatus (status : Nat) : Bool := 200 ≤ status && status < 300

/-! ## Retrying the typed response boundary -/

inductive ValidatedRetryResult
    (policy : RetryPolicy)
    (plan : TypedRequestPlan .complete) where
  | succeeded
      (history : RetryHistory policy)
      (response : HttpResponse)
      (validated : ValidatedResponse response.body)
  | responseFailure
      (history : RetryHistory policy)
      (response : HttpResponse)
      (error : ResponseError)
  | failed
      (history : RetryHistory policy)
      (terminal : ClientError)

def executeValidatedRetryAux
    (policy : RetryPolicy)
    (transport : Transport)
    (plan : TypedRequestPlan .complete) :
    (remaining : Nat) ->
      (history : RetryHistory policy) ->
      history.failures.length + remaining = policy.maxRetries ->
      IO (ValidatedRetryResult policy plan)
  | remaining, history, budget => do
      match ← transport.send plan.request with
      | .error message =>
          let error := ClientError.transport message
          if hRemaining : remaining = 0 then
            pure (.failed history error)
          else if policy.retryable error then
            let nextHistory : RetryHistory policy := {
              failures := history.failures ++ [error]
              failures_le := by
                rw [List.length_append]
                simp only [List.length_cons, List.length_nil]
                omega
            }
            executeValidatedRetryAux policy transport plan (remaining - 1) nextHistory (by
              rw [List.length_append]
              simp only [List.length_cons, List.length_nil]
              omega)
          else
            pure (.failed history error)
      | .ok response =>
          if successfulStatus response.status then
            match validateEq : validateResponse response.body with
            | .error error => pure (.responseFailure history response error)
            | .ok validated => pure (.succeeded history response validated)
          else
            let error := ClientError.httpStatus response.status response.body
            if hRemaining : remaining = 0 then
              pure (.failed history error)
            else if policy.retryable error then
              let nextHistory : RetryHistory policy := {
                failures := history.failures ++ [error]
                failures_le := by
                  rw [List.length_append]
                  simp only [List.length_cons, List.length_nil]
                  omega
              }
              executeValidatedRetryAux policy transport plan (remaining - 1) nextHistory (by
                rw [List.length_append]
                simp only [List.length_cons, List.length_nil]
                omega)
            else
              pure (.failed history error)
termination_by remaining => remaining
decreasing_by
      all_goals
        exact Nat.sub_lt (Nat.pos_of_ne_zero hRemaining) Nat.zero_lt_one

def executeValidatedRetry
    (policy : RetryPolicy)
    (transport : Transport)
    (plan : TypedRequestPlan .complete) :
    IO (ValidatedRetryResult policy plan) :=
  let history : RetryHistory policy := {
    failures := []
    failures_le := by simp
  }
  executeValidatedRetryAux policy transport plan policy.maxRetries history (by
    simp [history])

namespace ValidatedRetryResult

def history
    {policy : RetryPolicy} {plan : TypedRequestPlan .complete} :
    ValidatedRetryResult policy plan → RetryHistory policy
  | .succeeded history _ _ | .responseFailure history _ _ | .failed history _ => history

def attemptCount
    {policy : RetryPolicy} {plan : TypedRequestPlan .complete}
    (result : ValidatedRetryResult policy plan) : Nat :=
  result.history.attemptCount

theorem attemptCount_le_maxAttempts
    {policy : RetryPolicy} {plan : TypedRequestPlan .complete}
    (result : ValidatedRetryResult policy plan) :
    result.attemptCount ≤ policy.maxRetries + 1 :=
  RetryHistory.attemptCount_le_maxAttempts result.history

end ValidatedRetryResult

/-! ## Retried typed round -/

structure RetriedTransportRound
    (policy : RetryPolicy)
    {Model Capability : Type}
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : ConversationRunner)
    (plan : TypedRequestPlan .complete)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs,
      source < runner.session.nextSeq}
    (body : String)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) where
  retryHistory : RetryHistory policy
  round : ConversationTransportToolRound baseUrl apiKey source runner plan
    (sourceEventSeqs := sourceEventSeqs)
    (sourcesNodup := sourcesNodup)
    (sourcesEarlier := sourcesEarlier) body cfg before

namespace RetriedTransportRound

theorem attemptCount_le_maxAttempts
    {policy : RetryPolicy}
    {Model Capability : Type}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner} {plan : TypedRequestPlan .complete}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs,
      source < runner.session.nextSeq}
    {body : String}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : RetriedTransportRound policy baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    round.retryHistory.attemptCount ≤ policy.maxRetries + 1 :=
  RetryHistory.attemptCount_le_maxAttempts round.retryHistory

theorem final_endpoint
    {policy : RetryPolicy}
    {Model Capability : Type}
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner} {plan : TypedRequestPlan .complete}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs,
      source < runner.session.nextSeq}
    {body : String}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : RetriedTransportRound policy baseUrl apiKey source runner plan
      (sourceEventSeqs := sourceEventSeqs) (sourcesNodup := sourcesNodup)
      (sourcesEarlier := sourcesEarlier) body cfg before) :
    round.round.finalRunner =
      ConversationRunner.appendToolResults round.round.assistantRunner runner.nextCall
        round.round.assistantSeq round.round.executions (by
          rw [round.round.assistant_append_eq]
          rw [ConversationRunner.appendAcceptedApi_nextSeq]
          rw [← round.round.assistantSeq_eq]
          exact Nat.lt_succ_self _) :=
  round.round.final_append_eq

end RetriedTransportRound

inductive RetryRoundError (policy : RetryPolicy) where
  | request (error : RequestError)
  | client (history : RetryHistory policy) (error : ClientError)
  | response (history : RetryHistory policy) (error : ResponseError)
  | session (error : ApiSessionError)
  | tool (error : ToolRoundError)

def executeSource
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
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs,
      source < runner.session.nextSeq) :
    IO (Except (RetryRoundError policy)
      (Sigma fun plan : TypedRequestPlan .complete =>
        Sigma fun body : String =>
          RetriedTransportRound policy baseUrl apiKey source runner plan
            (sourceEventSeqs := sourceEventSeqs)
            (sourcesNodup := sourcesNodup)
            (sourcesEarlier := sourcesEarlier) body cfg before)) := do
  match built : buildTypedCompleteRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeValidatedRetry policy transport plan with
      | .failed history error => pure (.error (.client history error))
      | .responseFailure history _response error =>
          pure (.error (.response history error))
      | .succeeded history response validated =>
          match acceptedEq : acceptValidated validated with
          | .error error => pure (.error (.session error))
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
                  pure (.ok ⟨plan, ⟨response.body, {
                    retryHistory := history
                    round := {
                      plan_build_eq := built
                      response
                      body_eq := rfl
                      validated
                      accepted
                      accepted_validated_eq :=
                        DeepSeekHarnessTransportContract.acceptValidated_validated acceptedEq
                      accepted_eq := acceptedEq
                      assistantRunner
                      assistant_append_eq := rfl
                      assistantSeq
                      assistantSeq_eq := rfl
                      executions
                      finalModel
                      executions_eq := executionEq
                      finalRunner
                      final_append_eq := rfl
                    }
                  }⟩⟩)

namespace Example

def retrySequenceTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.set (index + 1)
    pure (.ok {
      status := if index = 0 then 503 else 200
      body := if index = 0 then "busy" else DeepSeekHarness.counterResponseBody
    })

def retryPolicy : RetryPolicy where
  maxRetries := 1
  retryTransport := true
  retryTransientHttp := true

def retryRound :
    IO (Except (RetryRoundError retryPolicy)
      (Sigma fun plan : TypedRequestPlan .complete =>
        Sigma fun body : String =>
          RetriedTransportRound retryPolicy "https://fixture.invalid"
            { value := "fixture-key" } DeepSeekHarness.counterRequestSource
            (ConversationRunner.empty 1) plan (sourceEventSeqs := [])
            (sourcesNodup := by simp) (sourcesEarlier := by simp)
            body Cordis.Harness.counterConfig 0)) := do
  let calls ← IO.mkRef 0
  executeSource retryPolicy (retrySequenceTransport calls) "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig
    0 (ConversationRunner.empty 1) [] (by simp) (by simp)

end Example

end Cordis.DeepSeekHarnessTransportRetry
