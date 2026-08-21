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
session bridge. Persistence, remote credentials, asynchronous scheduling, and tool-result
surface appends remain explicit follow-up boundaries.
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
                assistantSeq
                assistantSeq_eq := by
                  change runner.session.nextSeq + 1 = runner.session.nextSeq + 1
                  rfl
              }⟩)

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
