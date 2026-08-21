import Cordis.DeepSeekApi
import Cordis.DeepSeekApiSession
import Cordis.DeepSeekCurlTransport
import Cordis.GenericHarness
import Cordis.Harness

/-!
# Typed DeepSeek harness round

This module connects four already-certified boundaries in one small, executable round:

* the canonical session surface is converted to an OpenAI-compatible `ChatRequest`;
* `DeepSeekApi.execute` performs process/HTTP transport and dependent response validation;
* `DeepSeekApiSession.acceptResponse` admits only a singleton, supported assistant response;
* every returned function call is parsed, admitted, policy-checked, and executed through a
  `GenericHarness.Config`.

The result retains the source response, the proof-carrying assistant append, and every dependent
tool reply. Provider IDs are wire data and local numeric `CallId`s are allocated by the existing
session bridge. `appendRoundToolResults` encodes each certified result and appends it with exact
source-sequence, message-order, and protocol-projection certificates. Persistence, remote
credentials, asynchronous scheduling, and deployed-Harness equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarness

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekSessionRunner

/-! ## Session surface to request -/

inductive RequestError where
  | emptyMessages
  | errorToolResult (id : CallId)
deriving DecidableEq, Repr

def callIdText (id : CallId) : String := toString id.value

def sessionToolCallToFunctionCall (call : Session.ToolCall) : FunctionCall where
  id := callIdText call.id
  name := call.name
  arguments := call.arguments

def sessionMessageToChatMessage : Session.Message -> Except RequestError ChatMessage
  | .user content => .ok (.user content)
  | .assistant content calls =>
      .ok (.assistant (some content) none (calls.map sessionToolCallToFunctionCall))
  | .toolResult id content isError =>
      if isError then
        .error (.errorToolResult id)
      else
        .ok (.tool (callIdText id) content)

def sessionMessagesToChatMessages : List Session.Message -> Except RequestError (List ChatMessage)
  | [] => .ok []
  | message :: rest => do
      let converted ← sessionMessageToChatMessage message
      let convertedRest ← sessionMessagesToChatMessages rest
      .ok (converted :: convertedRest)

def nonemptyMessages : List ChatMessage -> Except RequestError (MessageList ChatMessage)
  | [] => .error .emptyMessages
  | head :: tail => .ok { head, tail }

structure RequestSource where
  model : String
  system : Option String := none
  thinking : Option ThinkingMode := none
  reasoningEffort : Option ReasoningEffort := none
  maxTokens : Option Nat := none
  responseFormat : Option ResponseFormat := none
  tools : List ToolDefinition := []
  toolChoice : Option ToolChoice := none

def requestSourceMessages
    (_source : RequestSource)
    (session : Session.Session Session.noExtensions) : List Session.Message :=
  session.messages

def buildChatRequest
    (source : RequestSource)
    (session : Session.Session Session.noExtensions) :
    Except RequestError ChatRequest := do
  let converted ← sessionMessagesToChatMessages (requestSourceMessages source session)
  let messages ←
    match source.system with
    | none => nonemptyMessages converted
    | some system =>
        .ok { head := .system system, tail := converted }
  .ok {
    model := source.model
    messages
    thinking := source.thinking
    reasoningEffort := source.reasoningEffort
    maxTokens := source.maxTokens
    responseFormat := source.responseFormat
    tools := source.tools
    toolChoice := source.toolChoice
  }

def buildRequestPlan
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session Session.noExtensions) :
    Except RequestError RequestPlan := do
  let request ← buildChatRequest source session
  .ok (buildRequest baseUrl apiKey request)

theorem sessionMessageToChatMessage_error_toolResult
    (id : CallId) (content : String) :
    sessionMessageToChatMessage (.toolResult id content true) =
      .error (.errorToolResult id) := by
  simp [sessionMessageToChatMessage]

/-! ## Dependent tool admission and execution -/

inductive ToolRoundError where
  | parseArguments (id name message : String)
  | admission (id name : String) (error : AdmissionError)
  | policy (id name : String) (decision : Decision) (reason : String)
  | provider (id name message : String)
deriving DecidableEq, Repr

structure ExecutedTool
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  raw : FunctionCall
  before : Model
  parsed : Lean.Json
  parsed_eq : Lean.Json.parse raw.arguments = .ok parsed
  call : cfg.Call
  validation : cfg.validate before { name := raw.name, arguments := parsed } = .ok call
  reply : Reply call
  policy : cfg.decide before { name := raw.name, arguments := parsed } call = .allow
  execution : cfg.view.execute call = .ok reply

def executeFunctionCall
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (raw : FunctionCall) : Except ToolRoundError (ExecutedTool cfg) :=
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
              | .error message => .error (.provider raw.id raw.name message)
              | .ok reply =>
                  .ok {
                    raw
                    before
                    parsed
                    parsed_eq := parsedEq
                    call
                    validation
                    reply
                    policy := decisionEvidence
                    execution := executionEvidence
                  }

def executeFunctionCalls
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) : List FunctionCall ->
    Except ToolRoundError (Model × List (ExecutedTool cfg))
  | [] => .ok (before, [])
  | raw :: rest =>
      match executeFunctionCall cfg before raw with
      | .error error => .error error
      | .ok executed =>
          match executeFunctionCalls cfg executed.reply.value.after rest with
          | .error error => .error error
          | .ok (after, executions) => .ok (after, executed :: executions)

theorem executedTool_policy_is_allow
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (executed : ExecutedTool cfg) :
    cfg.decide executed.before { name := executed.raw.name, arguments := executed.parsed }
        executed.call = GenericHarness.PolicyDecision.allow :=
  executed.policy

theorem executedTool_provider_reply
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (executed : ExecutedTool cfg) :
    cfg.view.execute executed.call = .ok executed.reply :=
  executed.execution

/-! ## Typed tool-result surface append -/

def executedToolResultJson
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (executed : ExecutedTool cfg) : Lean.Json :=
  cfg.wire.encodeCertifiedResult executed.call.op executed.call.request executed.reply.value

def executedToolResultContent
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (executed : ExecutedTool cfg) : String :=
  (executedToolResultJson executed).compress

theorem executedToolResultJson_decodes
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (executed : ExecutedTool cfg) :
    (cfg.wire.resultCodec executed.call.op executed.call.request.input).decode
        (executedToolResultJson executed) = .ok executed.reply.value.result :=
  cfg.wire.decode_encoded_certified_result executed.call.op executed.call.request
    executed.reply.value

def executedToolResultIsError
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (executed : ExecutedTool cfg) : Bool :=
  match executed.reply.value.result with
  | .error _ => true
  | .ok _ => false

def appendExecutedToolResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : ExecutedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.Session Session.noExtensions :=
  session.appendSurface .toolResult {
    turn
    step
    callId
    content := executedToolResultContent executed
    isError := executedToolResultIsError executed
  } [assistantSeq] (by simp) (by
    intro source member
    simp only [List.mem_singleton] at member
    subst source
    exact assistantSeqEarlier)

theorem appendExecutedToolResult_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : ExecutedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendExecutedToolResult session turn step callId assistantSeq executed
      assistantSeqEarlier).messages =
      session.messages ++ [.toolResult callId (executedToolResultContent executed)
        (executedToolResultIsError executed)] := by
  simp [appendExecutedToolResult, Session.Session.messages_eq_surface,
    Session.Session.appendSurface, Session.Session.append]

theorem appendExecutedToolResult_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : ExecutedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendExecutedToolResult session turn step callId assistantSeq executed
      assistantSeqEarlier).nextSeq = session.nextSeq + 1 := by
  rfl

theorem appendExecutedToolResult_protocolProjection
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step : Nat)
    (callId : CallId)
    (assistantSeq : Nat)
    (executed : ExecutedTool cfg)
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.protocolProjection
        (appendExecutedToolResult session turn step callId assistantSeq executed
          assistantSeqEarlier).events =
      Session.protocolProjection session.events ++ [.toolResult turn step callId] := by
  simp [appendExecutedToolResult, Session.Session.appendSurface,
    Session.Session.append, Session.protocolProjection,
    Session.LoggedEvent.protocolEvent?]

def executedToolMessages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (baseCall : Nat) : List (ExecutedTool cfg) -> List Session.Message
  | [] => []
  | executed :: rest =>
      .toolResult { value := baseCall } (executedToolResultContent executed)
          (executedToolResultIsError executed) ::
        executedToolMessages (baseCall + 1) rest

def appendExecutedToolResults
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step baseCall assistantSeq : Nat) :
    List (ExecutedTool cfg) -> assistantSeq < session.nextSeq ->
      Session.Session Session.noExtensions
  | [], _ => session
  | executed :: rest, assistantSeqEarlier =>
      appendExecutedToolResults
        (appendExecutedToolResult session turn step { value := baseCall } assistantSeq
          executed assistantSeqEarlier)
        turn step (baseCall + 1) assistantSeq rest
        (Nat.lt_trans assistantSeqEarlier (Nat.lt_succ_self session.nextSeq))

theorem appendExecutedToolResults_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendExecutedToolResults session turn step baseCall assistantSeq executions
      assistantSeqEarlier).messages =
      session.messages ++ executedToolMessages baseCall executions := by
  induction executions generalizing session baseCall with
  | nil => simp [appendExecutedToolResults, executedToolMessages]
  | cons executed rest inductionHypothesis =>
      simp only [appendExecutedToolResults]
      rw [inductionHypothesis]
      rw [appendExecutedToolResult_messages]
      simp [executedToolMessages, List.append_assoc]

def executedToolRuntimeEvents
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (turn step baseCall : Nat) : List (ExecutedTool cfg) -> List RuntimeEvent
  | [] => []
  | _ :: rest =>
      .toolResult turn step { value := baseCall } ::
        executedToolRuntimeEvents turn step (baseCall + 1) rest

theorem appendExecutedToolResults_protocolProjection
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    Session.protocolProjection
        (appendExecutedToolResults session turn step baseCall assistantSeq executions
          assistantSeqEarlier).events =
      Session.protocolProjection session.events ++
        executedToolRuntimeEvents turn step baseCall executions := by
  induction executions generalizing session baseCall with
  | nil => simp [appendExecutedToolResults, executedToolRuntimeEvents]
  | cons executed rest inductionHypothesis =>
      simp only [appendExecutedToolResults]
      rw [inductionHypothesis]
      rw [appendExecutedToolResult_protocolProjection]
      simp [executedToolRuntimeEvents, List.append_assoc]

theorem appendExecutedToolResults_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (session : Session.Session Session.noExtensions)
    (turn step baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < session.nextSeq) :
    (appendExecutedToolResults session turn step baseCall assistantSeq executions
      assistantSeqEarlier).nextSeq = session.nextSeq + executions.length := by
  induction executions generalizing session baseCall with
  | nil => simp [appendExecutedToolResults]
  | cons executed rest inductionHypothesis =>
      simp only [appendExecutedToolResults]
      rw [inductionHypothesis]
      rw [appendExecutedToolResult_nextSeq]
      simp [List.length, Nat.add_assoc, Nat.add_comm]

/-! ## One transport-backed round -/

inductive RoundError where
  | client (error : ClientError)
  | response (error : ApiSessionError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

structure RoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  accepted : AcceptedApiResponse body
  runner : Runner
  finalModel : Model
  executions : List (ExecutedTool cfg)
  executions_eq :
    executeFunctionCalls cfg before
        accepted.validated.response.choices.head.message.toolCalls =
      .ok (finalModel, executions)
  assistantTurn : Nat
  assistantStep : Nat
  callBase : Nat
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = runner.session.nextSeq

def executeRound
    {Model Capability : Type}
    (transport : Transport)
    (plan : RequestPlan)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : Runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun body : String => RoundResult cfg before body)) := do
  match ← DeepSeekApi.execute transport plan with
  | .error error => pure (.error (.client error))
  | .ok ⟨body, _validated⟩ =>
      match acceptResponse body with
      | .error error => pure (.error (.response error))
      | .ok accepted =>
          let assistantSeq := runner.session.nextSeq
          let nextRunner :=
            Runner.appendApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier
          match executionEq : executeFunctionCalls cfg before
              accepted.validated.response.choices.head.message.toolCalls with
          | .error error => pure (.error (.tool error))
          | .ok (finalModel, executions) =>
              pure (.ok ⟨body, {
                accepted
                runner := nextRunner
                finalModel
                executions
                executions_eq := executionEq
                assistantTurn := runner.turn
                assistantStep := runner.step
                callBase := runner.nextCall
                assistantSeq
                assistantSeq_eq := by
                  change runner.session.nextSeq + 1 = runner.session.nextSeq + 1
                  rfl
              }⟩)

def appendRoundToolResults
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : RoundResult cfg before body) : Session.Session Session.noExtensions :=
  appendExecutedToolResults round.runner.session round.assistantTurn round.assistantStep
    round.callBase round.assistantSeq round.executions (by
      rw [← round.assistantSeq_eq]
      exact Nat.lt_succ_self _)

theorem appendRoundToolResults_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : RoundResult cfg before body) :
    (appendRoundToolResults round).messages =
      round.runner.session.messages ++ executedToolMessages round.callBase round.executions := by
  exact appendExecutedToolResults_messages round.runner.session round.assistantTurn
    round.assistantStep round.callBase round.assistantSeq round.executions (by
      rw [← round.assistantSeq_eq]
      exact Nat.lt_succ_self _)

theorem appendRoundToolResults_protocolProjection
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : RoundResult cfg before body) :
    Session.protocolProjection (appendRoundToolResults round).events =
      Session.protocolProjection round.runner.session.events ++
        executedToolRuntimeEvents round.assistantTurn round.assistantStep round.callBase
          round.executions := by
  exact appendExecutedToolResults_protocolProjection round.runner.session round.assistantTurn
    round.assistantStep round.callBase round.assistantSeq round.executions (by
      rw [← round.assistantSeq_eq]
      exact Nat.lt_succ_self _)

/-! ## Tool-aware continuation runner -/

theorem executedToolMessages_toolCallCount
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (baseCall : Nat)
    (executions : List (ExecutedTool cfg)) :
    toolCallCount (executedToolMessages baseCall executions) = 0 := by
  induction executions generalizing baseCall with
  | nil => rfl
  | cons executed rest inductionHypothesis =>
      change 0 + toolCallCount (executedToolMessages (baseCall + 1) rest) = 0
      simp [inductionHypothesis]

structure ConversationRunner where
  session : Session.Session Session.noExtensions
  turn : Nat
  step : Nat
  nextCall : Nat
  toolCallCount_eq_nextCall : toolCallCount session.messages = nextCall

namespace ConversationRunner

def empty (turn : Nat := 1) : ConversationRunner where
  session := Session.Session.empty Session.noExtensions
  turn
  step := 0
  nextCall := 0
  toolCallCount_eq_nextCall := by rfl

def appendAcceptedApi
    (runner : ConversationRunner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    ConversationRunner :=
  let assistantView := view accepted
  let assignment := sequentialAssignment runner.nextCall assistantView
  let session := StreamSession.appendAssistant runner.session runner.turn runner.step
    assistantView assignment sourceEventSeqs sourcesNodup sourcesEarlier
  {
    session
    turn := runner.turn
    step := runner.step + 1
    nextCall := runner.nextCall + assistantView.rawToolCalls.length
    toolCallCount_eq_nextCall := by
      have messages_eq :
          session.messages = runner.session.messages ++ [.assistant assistantView.content
            (StreamSession.toSessionToolCalls assistantView assignment)] := by
        simp [session, StreamSession.appendAssistant, Session.Session.appendSurface,
          Session.Session.append, Session.Session.messages_eq_surface,
          StreamSession.toAssistantPayload]
      simp only [messages_eq]
      rw [toolCallCount_append]
      rw [runner.toolCallCount_eq_nextCall]
      simp [toolCallCount, messageToolCallCount,
        StreamSession.toSessionToolCalls_length]
  }

theorem appendAcceptedApi_session_messages
    (runner : ConversationRunner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendAcceptedApi runner accepted sourceEventSeqs sourcesNodup
      sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant (view accepted).content
        (StreamSession.toSessionToolCalls (view accepted)
          (sequentialAssignment runner.nextCall (view accepted)))] := by
  change (StreamSession.appendAssistant runner.session runner.turn runner.step
      (view accepted) (sequentialAssignment runner.nextCall (view accepted))
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  simp [StreamSession.appendAssistant, Session.Session.appendSurface,
    Session.Session.append, Session.Session.messages_eq_surface,
    StreamSession.toAssistantPayload]

theorem appendAcceptedApi_nextCall
    (runner : ConversationRunner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendAcceptedApi runner accepted sourceEventSeqs sourcesNodup sourcesEarlier).nextCall =
      runner.nextCall +
        accepted.validated.response.choices.head.message.toolCalls.length := by
  change runner.nextCall + (view accepted).rawToolCalls.length = _
  rw [view_rawToolCalls_length]

theorem appendAcceptedApi_nextSeq
    (runner : ConversationRunner)
    {body : String}
    (accepted : AcceptedApiResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (appendAcceptedApi runner accepted sourceEventSeqs sourcesNodup
      sourcesEarlier).session.nextSeq =
      runner.session.nextSeq + 1 := by
  rfl

def afterRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : RoundResult cfg before body) :
    ConversationRunner :=
  let session := appendRoundToolResults round
  {
    session := session
    turn := round.runner.turn
    step := round.runner.step
    nextCall := round.runner.nextCall
    toolCallCount_eq_nextCall := by
      have hcount :
          toolCallCount (appendRoundToolResults round).messages = round.runner.nextCall := by
        calc
          toolCallCount (appendRoundToolResults round).messages =
              toolCallCount
                (round.runner.session.messages ++
                  executedToolMessages round.callBase round.executions) :=
            congrArg toolCallCount (appendRoundToolResults_messages round)
          _ = round.runner.nextCall := by
            rw [toolCallCount_append]
            rw [executedToolMessages_toolCallCount]
            change toolCallCount round.runner.session.messages = round.runner.nextCall
            exact round.runner.toolCallCount_eq_nextCall
      simpa [session, Session.Session.messages_eq_surface] using hcount
  }

theorem afterRound_session_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (round : RoundResult cfg before body) :
    (afterRound round).session.messages =
      round.runner.session.messages ++ executedToolMessages round.callBase round.executions := by
  exact appendRoundToolResults_messages round

def appendToolResults
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    ConversationRunner :=
  let session := appendExecutedToolResults runner.session runner.turn runner.step
    baseCall assistantSeq executions assistantSeqEarlier
  {
    session := session
    turn := runner.turn
    step := runner.step
    nextCall := runner.nextCall
    toolCallCount_eq_nextCall := by
      have hcount :
          toolCallCount
              (appendExecutedToolResults runner.session runner.turn runner.step baseCall
                assistantSeq executions assistantSeqEarlier).messages = runner.nextCall := by
        calc
          toolCallCount
              (appendExecutedToolResults runner.session runner.turn runner.step baseCall
                assistantSeq executions assistantSeqEarlier).messages =
              toolCallCount (runner.session.messages ++ executedToolMessages baseCall executions) :=
            congrArg toolCallCount (appendExecutedToolResults_messages runner.session runner.turn
              runner.step baseCall assistantSeq executions assistantSeqEarlier)
          _ = runner.nextCall := by
            rw [toolCallCount_append]
            rw [executedToolMessages_toolCallCount]
            change toolCallCount runner.session.messages = runner.nextCall
            exact runner.toolCallCount_eq_nextCall
      simpa [session, Session.Session.messages_eq_surface] using hcount
  }

theorem appendToolResults_session_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendToolResults runner baseCall assistantSeq executions
      assistantSeqEarlier).session.messages =
      runner.session.messages ++ executedToolMessages baseCall executions := by
  exact appendExecutedToolResults_messages runner.session runner.turn runner.step baseCall
    assistantSeq executions assistantSeqEarlier

end ConversationRunner

/-! ## Transport-backed conversation continuation -/

inductive ConversationError where
  | request (error : RequestError)
  | client (error : ClientError)
  | response (error : ApiSessionError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

structure ConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  accepted : AcceptedApiResponse body
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

def executeConversationRound
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
      (Sigma fun body : String => ConversationRoundResult cfg before body)) := do
  match buildRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← DeepSeekApi.execute transport plan with
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
              match executionEq : executeFunctionCalls cfg before
                  accepted.validated.response.choices.head.message.toolCalls with
              | .error error => pure (.error (.tool error))
              | .ok (finalModel, executions) =>
                  let finalRunner := ConversationRunner.appendToolResults assistantRunner
                    runner.nextCall assistantSeq executions assistantSeqEarlier
                  pure (.ok ⟨body, {
                    accepted
                    assistantRunner
                    runner := finalRunner
                    finalModel
                    executions
                    executions_eq := executionEq
                    assistantSeq := assistantSeq
                    assistantSeq_eq := by
                      change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                      rw [ConversationRunner.appendAcceptedApi_nextSeq]
                  }⟩)

/-! ## Fuel-bounded conversation execution -/

abbrev ConversationWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model => Sigma fun body : String => ConversationRoundResult cfg before body

namespace ConversationWitness

abbrev noToolCalls
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
  ConversationWitness cfg -> Prop
  | ⟨_, ⟨_, round⟩⟩ =>
      round.accepted.validated.response.choices.head.message.toolCalls.length = 0

end ConversationWitness

inductive ConversationStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : ConversationWitness cfg)
      (noToolCalls : ConversationWitness.noToolCalls last)
  | fuelExhausted

namespace ConversationStop

def isCompleted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    ConversationStop cfg -> Bool
  | .completed _ _ => true
  | .fuelExhausted => false

end ConversationStop

structure ConversationRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (ConversationWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : ConversationStop cfg

def runConversationAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
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
    (runner : ConversationRunner)
    (history : List (ConversationWitness cfg)) :
    IO (Except ConversationError (ConversationRunResult cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeConversationRound transport baseUrl apiKey source cfg before runner
          sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let witness : ConversationWitness cfg := ⟨before, ⟨body, round⟩⟩
          let nextHistory := history ++ [witness]
          if noTools : ConversationWitness.noToolCalls witness then
            pure (.ok {
              rounds := nextHistory
              runner := round.runner
              finalModel := round.finalModel
              stop := .completed witness noTools
            })
          else
            runConversationAux fuel transport baseUrl apiKey source sourceEventSeqs sourcesNodup
              sourcesEarlier round.finalModel round.runner nextHistory

def runConversation
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
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
    IO (Except ConversationError (ConversationRunResult cfg)) :=
  runConversationAux fuel transport baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier before runner []

/-! ## Deterministic executable fixture -/

def counterReadTool : ToolDefinition where
  function := {
    name := "counter_read"
    description := some "Read the deterministic counter."
    parameters := .mkObj [("type", .str "null")]
    strict := some true
  }

def counterResponseJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-read"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("finish_reason", .str "tool_calls"),
    ("message", .mkObj [
      ("role", .str "assistant"),
      ("content", .str "I will read the counter."),
      ("tool_calls", .arr #[.mkObj [
        ("id", .str "counter-call-0"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "counter_read"),
          ("arguments", .str "null")
        ])
      ]])
    ])
  ]])
]

def counterResponseBody : String := Lean.Json.compress counterResponseJson

def counterFinalResponseJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-final"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("finish_reason", .str "stop"),
    ("message", .mkObj [
      ("role", .str "assistant"),
      ("content", .str "The counter is 0."),
      ("tool_calls", .arr #[])
    ])
  ]])
]

def counterFinalResponseBody : String := Lean.Json.compress counterFinalResponseJson

def counterSession : Session.Session Session.noExtensions :=
  (Session.Session.empty Session.noExtensions).appendSurface .userMessage
    { content := "Read the counter." } [] (by simp) (by simp)

def counterRequestSource : RequestSource where
  model := "deterministic-counter"
  system := some "Use the supplied proof-carrying counter tool."
  tools := [counterReadTool]
  toolChoice := some .auto

def counterPlan : Except RequestError RequestPlan :=
  buildRequestPlan "https://fixture.invalid" { value := "fixture-key" }
    counterRequestSource counterSession

def counterFixture : IO (Except RoundError
    (Sigma fun body : String => RoundResult Cordis.Harness.counterConfig 0 body)) := do
  match counterPlan with
  | .error error => pure (.error (.tool (.parseArguments "" "request" (reprStr error))))
  | .ok plan =>
      executeRound (fixtureTransport counterResponseBody) plan
        Cordis.Harness.counterConfig 0 (Runner.empty 1) [] (by simp) (by simp)

end Cordis.DeepSeekHarness
