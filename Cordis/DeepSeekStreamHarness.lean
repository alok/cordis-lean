import Cordis.DeepSeekCurlSession
import Cordis.DeepSeekHarness

/-!
# Complete-body DeepSeek stream to generic harness continuation

This module composes the existing process-backed SSE/session boundary with the generic
proof-carrying `ConversationRunner`. A terminal rich-stream response is assigned local numeric
call IDs, each streamed function call is routed through the same dependent admission, policy, and
provider execution path as a non-streaming response, and certified tool results are appended to
the resulting session. The returned runner can therefore be passed to the existing subsequent
request or fuel-bounded conversation APIs.

The adapter intentionally consumes a complete response body through `ProcessConfig`; it does not
claim incremental delivery, cancellation, backpressure, reconnects, provider-complete assembly,
or equivalence to the deployed DeepSeek Harness. The executable fixtures cover both a single
streamed call and two calls in one terminal response; each call still passes through the same
dependent admission, policy, and provider path.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamHarness

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.RichStream
open Cordis.StreamSession

def projectedToolCallToFunctionCall (call : ProjectedToolCall) : FunctionCall where
  id := call.providerId
  name := call.name
  arguments := call.rawArguments

def finishedFunctionCalls {body : String}
    (finished : FinishedResponse body) : List FunctionCall :=
  finished.finished.view.rawToolCalls.map projectedToolCallToFunctionCall

def counterToolStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-stream"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "counter-stream-call-0"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "counter_read"),
          ("arguments", .str "null")
        ])
      ]])
    ]),
    ("finish_reason", .null)
  ]])
]

def counterToolFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-stream"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "counter-stream-call-0"),
        ("function", .mkObj [("arguments", .str "")])
      ]])
    ]),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 4)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 3)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 7))
  ])
]

def counterToolStreamBody : String :=
  "data: " ++ Lean.Json.compress counterToolStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress counterToolFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def counterMultiToolStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-stream-multi"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 0)),
          ("id", .str "counter-stream-call-0"),
          ("type", .str "function"),
          ("function", .mkObj [
            ("name", .str "counter_read"),
            ("arguments", .str "null")
          ])
        ],
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 1)),
          ("id", .str "counter-stream-call-1"),
          ("type", .str "function"),
          ("function", .mkObj [
            ("name", .str "counter_read"),
            ("arguments", .str "null")
          ])
        ]
      ])
    ]),
    ("finish_reason", .null)
  ]])
]

def counterMultiToolFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter-stream-multi"),
  ("model", .str "deterministic-counter"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 0)),
          ("function", .mkObj [("arguments", .str "")])
        ],
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 1)),
          ("function", .mkObj [("arguments", .str "")])
        ]
      ])
    ]),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 4)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 5)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 9))
  ])
]

def counterMultiToolStreamBody : String :=
  "data: " ++ Lean.Json.compress counterMultiToolStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress counterMultiToolFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def ConversationRunner.appendFinished
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    ConversationRunner :=
  let assistantView := finished.finished.view
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

theorem ConversationRunner.appendFinished_session_messages
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (ConversationRunner.appendFinished runner finished sourceEventSeqs sourcesNodup
      sourcesEarlier).session.messages =
      runner.session.messages ++ [.assistant finished.finished.view.content
        (StreamSession.toSessionToolCalls finished.finished.view
          (sequentialAssignment runner.nextCall finished.finished.view))] := by
  change (StreamSession.appendAssistant runner.session runner.turn runner.step
      finished.finished.view (sequentialAssignment runner.nextCall finished.finished.view)
      sourceEventSeqs sourcesNodup sourcesEarlier).messages = _
  simp [StreamSession.appendAssistant, Session.Session.appendSurface,
    Session.Session.append, Session.Session.messages_eq_surface,
    StreamSession.toAssistantPayload]

theorem ConversationRunner.appendFinished_nextSeq
    (runner : ConversationRunner)
    {body : String}
    (finished : FinishedResponse body)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    (ConversationRunner.appendFinished runner finished sourceEventSeqs sourcesNodup
      sourcesEarlier).session.nextSeq = runner.session.nextSeq + 1 := by
  rfl

inductive StreamConversationError where
  | request (error : RequestError)
  | client (error : SessionClientError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

structure StreamConversationRoundResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  finished : FinishedResponse body
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  executions : List (ExecutedTool cfg)
  executions_eq :
    executeFunctionCalls cfg before (finishedFunctionCalls finished) =
      .ok (finalModel, executions)
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq

def executeConversationStreamRound
    {Model Capability : Type}
    (finish : (body : String) →
      Except DeepSeekSessionRunner.ResponseError (FinishedResponse body))
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
    IO (Except StreamConversationError
      (Sigma fun body : String => StreamConversationRoundResult cfg before body)) := do
  match buildRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← DeepSeekCurlSession.executeWith finish config plan.request with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, processed⟩ =>
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
              }⟩)

def executeConversationMultiStreamRound
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
    IO (Except StreamConversationError
      (Sigma fun body : String => StreamConversationRoundResult cfg before body)) :=
  executeConversationStreamRound finishMulti config baseUrl apiKey source cfg before runner
    sourceEventSeqs sourcesNodup sourcesEarlier

end Cordis.DeepSeekStreamHarness
