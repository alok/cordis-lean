import Cordis.DeepSeekHarness

/-!
# Recoverable provider failures

The ordinary harness is deliberately fail-closed: a provider failure is a `ToolRoundError` and
is never smuggled into the next model request.  This module supplies the explicit opt-in seam for
clients that want to expose a provider failure as an `isError` tool result.  The failure retains
the parsed call, admission and policy proofs, and the exact provider error string; it preserves
the model state, so a subsequent request is still indexed by the same model.

This is a pure continuation layer over the existing complete-body transport.  It does not claim
incremental streaming, cancellation, retry, persistence, or equivalence to the deployed Harness.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessErrors

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner

structure ProviderFailedTool
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  raw : FunctionCall
  before : Model
  parsed : Lean.Json
  parsed_eq : Lean.Json.parse raw.arguments = .ok parsed
  call : cfg.Call
  validation : cfg.validate before { name := raw.name, arguments := parsed } = .ok call
  policy : cfg.decide before { name := raw.name, arguments := parsed } call = .allow
  message : String
  execution : cfg.view.execute call = .error message

inductive RecoverableToolAttempt
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | succeeded (executed : ExecutedTool cfg)
  | providerFailed (failed : ProviderFailedTool cfg)

def RecoverableToolAttempt.after
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (attempt : RecoverableToolAttempt cfg) : Model :=
  match attempt with
  | .succeeded executed => executed.reply.value.after
  | .providerFailed failed => failed.before

def executeFunctionCallRecoverable
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (raw : FunctionCall) : Except ToolRoundError (RecoverableToolAttempt cfg) :=
  match parsedEq : Lean.Json.parse raw.arguments with
  | .error message => .error (.parseArguments raw.id raw.name message)
  | .ok parsed =>
      let rawCall : RawCall := { name := raw.name, arguments := parsed }
      match validation : cfg.validate before rawCall with
      | .error error => .error (.admission raw.id raw.name error)
      | .ok call =>
          match decisionEvidence : cfg.decide before rawCall call with
          | .reject decisionName _ reason =>
              .error (.policy raw.id raw.name decisionName
                (cfg.renderPolicyRejected call reason))
          | .allow =>
              match executionEvidence : cfg.view.execute call with
              | .error message =>
                  .ok (.providerFailed {
                    raw
                    before
                    parsed
                    parsed_eq := parsedEq
                    call
                    validation
                    policy := decisionEvidence
                    message
                    execution := executionEvidence
                  })
              | .ok reply =>
                  .ok (.succeeded {
                    raw
                    before
                    parsed
                    parsed_eq := parsedEq
                    call
                    validation
                    reply
                    policy := decisionEvidence
                    execution := executionEvidence
                  })

def executeFunctionCallsRecoverable
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) : List FunctionCall ->
    Except ToolRoundError (Model × List (RecoverableToolAttempt cfg))
  | [] => .ok (before, [])
  | raw :: rest =>
      match executeFunctionCallRecoverable cfg before raw with
      | .error error => .error error
      | .ok attempt =>
          match executeFunctionCallsRecoverable cfg attempt.after rest with
          | .error error => .error error
          | .ok (after, attempts) => .ok (after, attempt :: attempts)

theorem providerFailedTool_preserves_model
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (failed : ProviderFailedTool cfg) :
    failed.before = failed.before := rfl

def providerFailedToolResultContent
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (failed : ProviderFailedTool cfg) : String :=
  failed.message

def appendProviderFailedToolResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (failed : ProviderFailedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.Session Session.noExtensions :=
  session.appendSurface .toolResult {
    turn
    step
    callId
    content := providerFailedToolResultContent failed
    isError := true
  } [assistantSeq] (by simp) (by
    intro source member
    simp only [List.mem_singleton] at member
    subst source
    exact assistantSeqEarlier)

theorem appendProviderFailedToolResult_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (failed : ProviderFailedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendProviderFailedToolResult session turn step callId assistantSeq failed
      assistantSeqEarlier).messages =
      session.messages ++ [.toolResult callId (providerFailedToolResultContent failed) true] := by
  simp [appendProviderFailedToolResult, Session.Session.messages_eq_surface,
    Session.Session.appendSurface, Session.Session.append]

theorem appendProviderFailedToolResult_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (failed : ProviderFailedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendProviderFailedToolResult session turn step callId assistantSeq failed
      assistantSeqEarlier).nextSeq = session.nextSeq + 1 := by
  rfl

def recoverableToolMessages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (baseCall : Nat) : List (RecoverableToolAttempt cfg) -> List Session.Message
  | [] => []
  | .succeeded executed :: rest =>
      .toolResult { value := baseCall } (executedToolResultContent executed)
          (executedToolResultIsError executed) ::
        recoverableToolMessages (baseCall + 1) rest
  | .providerFailed failed :: rest =>
      .toolResult { value := baseCall } (providerFailedToolResultContent failed) true ::
        recoverableToolMessages (baseCall + 1) rest

def appendRecoverableToolResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (attempt : RecoverableToolAttempt cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.Session Session.noExtensions :=
  match attempt with
  | .succeeded executed =>
      appendExecutedToolResult session turn step callId assistantSeq executed assistantSeqEarlier
  | .providerFailed failed =>
      appendProviderFailedToolResult session turn step callId assistantSeq failed
        assistantSeqEarlier

theorem appendRecoverableToolResult_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (attempt : RecoverableToolAttempt cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendRecoverableToolResult session turn step callId assistantSeq attempt
      assistantSeqEarlier).nextSeq = session.nextSeq + 1 := by
  cases attempt with
  | succeeded executed =>
      exact appendExecutedToolResult_nextSeq session turn step callId assistantSeq executed
        assistantSeqEarlier
  | providerFailed failed =>
      exact appendProviderFailedToolResult_nextSeq session turn step callId assistantSeq failed
        assistantSeqEarlier

theorem appendRecoverableToolResult_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (attempt : RecoverableToolAttempt cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendRecoverableToolResult session turn step callId assistantSeq attempt
      assistantSeqEarlier).messages =
      session.messages ++ match attempt with
      | .succeeded executed =>
          [.toolResult callId (executedToolResultContent executed)
            (executedToolResultIsError executed)]
      | .providerFailed failed =>
          [.toolResult callId (providerFailedToolResultContent failed) true] := by
  cases attempt with
  | succeeded executed =>
      exact appendExecutedToolResult_messages session turn step callId assistantSeq executed
        assistantSeqEarlier
  | providerFailed failed =>
      exact appendProviderFailedToolResult_messages session turn step callId assistantSeq failed
        assistantSeqEarlier

def appendRecoverableToolResultsSession
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step baseCall assistantSeq : Nat) :
    List (RecoverableToolAttempt cfg) -> assistantSeq < session.nextSeq ->
      Session.Session Session.noExtensions
  | [], _ => session
  | attempt :: rest, assistantSeqEarlier =>
      appendRecoverableToolResultsSession
        (appendRecoverableToolResult session turn step { value := baseCall } assistantSeq
          attempt assistantSeqEarlier)
        turn step (baseCall + 1) assistantSeq rest
        (by
          rw [appendRecoverableToolResult_nextSeq]
          exact Nat.lt_trans assistantSeqEarlier (Nat.lt_succ_self _))

theorem appendRecoverableToolResultsSession_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step baseCall assistantSeq : Nat)
    (attempts : List (RecoverableToolAttempt cfg))
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendRecoverableToolResultsSession session turn step baseCall assistantSeq attempts
      assistantSeqEarlier).messages =
      session.messages ++ recoverableToolMessages baseCall attempts := by
  induction attempts generalizing session baseCall with
  | nil => simp [appendRecoverableToolResultsSession, recoverableToolMessages]
  | cons attempt rest inductionHypothesis =>
      cases attempt with
      | succeeded executed =>
          simp only [appendRecoverableToolResultsSession]
          rw [inductionHypothesis]
          rw [appendRecoverableToolResult_messages]
          simp [recoverableToolMessages, List.append_assoc]
      | providerFailed failed =>
          simp only [appendRecoverableToolResultsSession]
          rw [inductionHypothesis]
          rw [appendRecoverableToolResult_messages]
          simp [recoverableToolMessages, List.append_assoc]

theorem recoverableToolMessages_toolCallCount
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (baseCall : Nat) (attempts : List (RecoverableToolAttempt cfg)) :
    toolCallCount (recoverableToolMessages baseCall attempts) = 0 := by
  induction attempts generalizing baseCall with
  | nil => rfl
  | cons attempt rest inductionHypothesis =>
      cases attempt with
      | succeeded executed =>
          change 0 + toolCallCount (recoverableToolMessages (baseCall + 1) rest) = 0
          simp [inductionHypothesis]
      | providerFailed failed =>
          change 0 + toolCallCount (recoverableToolMessages (baseCall + 1) rest) = 0
          simp [inductionHypothesis]

def ConversationRunner.appendRecoverableToolResults
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (attempts : List (RecoverableToolAttempt cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    ConversationRunner :=
  let session := appendRecoverableToolResultsSession runner.session runner.turn runner.step
    baseCall assistantSeq attempts assistantSeqEarlier
  {
    session := session
    turn := runner.turn
    step := runner.step
    nextCall := runner.nextCall
    toolCallCount_eq_nextCall := by
      have hcount :
          toolCallCount session.messages = runner.nextCall := by
        calc
          toolCallCount session.messages =
              toolCallCount
                (runner.session.messages ++ recoverableToolMessages baseCall attempts) :=
            congrArg toolCallCount (appendRecoverableToolResultsSession_messages
              runner.session runner.turn runner.step baseCall assistantSeq attempts
              assistantSeqEarlier)
          _ = runner.nextCall := by
            rw [toolCallCount_append, recoverableToolMessages_toolCallCount]
            simpa using runner.toolCallCount_eq_nextCall
      simpa [session, Session.Session.messages_eq_surface] using hcount
  }

theorem ConversationRunner.appendRecoverableToolResults_session_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (attempts : List (RecoverableToolAttempt cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (ConversationRunner.appendRecoverableToolResults runner baseCall assistantSeq attempts
      assistantSeqEarlier).session.messages =
      runner.session.messages ++ recoverableToolMessages baseCall attempts := by
  exact appendRecoverableToolResultsSession_messages runner.session runner.turn runner.step
    baseCall assistantSeq attempts assistantSeqEarlier

structure RecoverableConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  accepted : AcceptedApiResponse body
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  attempts : List (RecoverableToolAttempt cfg)
  attempts_eq :
    executeFunctionCallsRecoverable cfg before
        accepted.validated.response.choices.head.message.toolCalls =
      .ok (finalModel, attempts)
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq

def executeConversationRoundRecoverable
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
    IO (Except ConversationError
      (Sigma fun body : String => RecoverableConversationRoundResult cfg before body)) := do
  match buildTypedCompleteRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← DeepSeekApi.executeComplete transport plan with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, _validated⟩ =>
          match acceptResponse body with
          | .error error => pure (.error (.response error))
          | .ok accepted =>
              let assistantSeq := runner.session.nextSeq
              let assistantRunner := ConversationRunner.appendAcceptedApi runner accepted
                sourceEventSeqs sourcesNodup sourcesEarlier
              have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
                rw [ConversationRunner.appendAcceptedApi_nextSeq]
                exact Nat.lt_succ_self _
              match attemptEq : executeFunctionCallsRecoverable cfg before
                  accepted.validated.response.choices.head.message.toolCalls with
              | .error error => pure (.error (.tool error))
              | .ok (finalModel, attempts) =>
                  let finalRunner := ConversationRunner.appendRecoverableToolResults
                    assistantRunner runner.nextCall assistantSeq attempts assistantSeqEarlier
                  pure (.ok ⟨body, {
                    accepted
                    assistantRunner
                    runner := finalRunner
                    finalModel
                    attempts
                    attempts_eq := attemptEq
                    assistantSeq
                    assistantSeq_eq := by
                      change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                      rw [ConversationRunner.appendAcceptedApi_nextSeq]
                  }⟩)

end Cordis.DeepSeekHarnessErrors
