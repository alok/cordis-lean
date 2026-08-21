import Cordis.Codec
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
# Proof-carrying OpenAI-compatible DeepSeek chat boundary

This module is the next executable boundary after `TextRefinement`. It describes a small,
non-streaming subset of DeepSeek's OpenAI-compatible `/chat/completions` API as typed Lean data,
constructs the exact HTTP request plan, and decodes successful and error JSON responses into
proof-carrying values.

The supported request vocabulary intentionally retains the fields needed by a tool-using harness:
system/user/assistant/tool messages, assistant reasoning and tool calls, function tools with raw
JSON-schema parameters, thinking mode, reasoning effort, a token limit, JSON-output response format,
tool choice, and the explicit non-streaming flag. The response decoder requires a nonempty choice
list, an assistant message, an exact finish-reason vocabulary, optional reasoning/tool calls, and
optional token usage. Unknown optional provider fields are not interpreted as local semantics.

`Transport` is an explicit effect boundary. `execute` can be tested with a deterministic fake
transport, but this module does not claim that an HTTP request was sent, that a credential was
valid, that a remote model answered, or that provider tool arguments satisfy a local `ToolSpec`.
Those claims require an adapter and credential policy outside the pure kernel.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekApi

open Cordis

universe u

/-! ## Typed request vocabulary -/

structure MessageList (alpha : Type u) where
  head : alpha
  tail : List alpha

namespace MessageList

def toList {alpha : Type u} (messages : MessageList alpha) : List alpha :=
  messages.head :: messages.tail

end MessageList

structure FunctionCall where
  id : String
  name : String
  arguments : String
  deriving DecidableEq, Repr

inductive ChatMessage where
  | system (content : String)
  | user (content : String)
  | assistant
      (content : Option String)
      (reasoningContent : Option String)
      (toolCalls : List FunctionCall)
  | tool (toolCallId : String) (content : String)
deriving DecidableEq, Repr

inductive ThinkingMode where
  | enabled
  | disabled
deriving DecidableEq, Repr

namespace ThinkingMode

def toJson : ThinkingMode -> Lean.Json
  | .enabled => Lean.Json.mkObj [("type", .str "enabled")]
  | .disabled => Lean.Json.mkObj [("type", .str "disabled")]

end ThinkingMode

inductive ReasoningEffort where
  | high
  | max
deriving DecidableEq, Repr

namespace ReasoningEffort

def toJson : ReasoningEffort -> Lean.Json
  | .high => .str "high"
  | .max => .str "max"

end ReasoningEffort

structure FunctionTool where
  name : String
  description : Option String
  parameters : Lean.Json
  strict : Option Bool

structure ToolDefinition where
  function : FunctionTool

inductive ToolChoice where
  | none
  | auto
  | required
  | function (name : String)
deriving DecidableEq, Repr

namespace ToolChoice

def toJson : ToolChoice -> Lean.Json
  | .none => .str "none"
  | .auto => .str "auto"
  | .required => .str "required"
  | .function name =>
      .mkObj [("type", .str "function"),
        ("function", .mkObj [("name", .str name)])]

end ToolChoice

inductive ResponseFormat where
  | text
  | jsonObject
deriving DecidableEq, Repr

namespace ResponseFormat

def toJson : ResponseFormat -> Lean.Json
  | .text => .mkObj [("type", .str "text")]
  | .jsonObject => .mkObj [("type", .str "json_object")]

end ResponseFormat

structure ChatRequest where
  model : String
  messages : MessageList ChatMessage
  thinking : Option ThinkingMode := none
  reasoningEffort : Option ReasoningEffort := none
  maxTokens : Option Nat := none
  responseFormat : Option ResponseFormat := none
  tools : List ToolDefinition := []
  toolChoice : Option ToolChoice := none

namespace ChatRequest

private def optionalField (name : String) : Option Lean.Json -> List (String × Lean.Json)
  | none => []
  | some value => [(name, value)]

private def functionCallJson (call : FunctionCall) : Lean.Json :=
  .mkObj [
    ("id", .str call.id),
    ("type", .str "function"),
    ("function", .mkObj [
      ("name", .str call.name),
      ("arguments", .str call.arguments)
    ])
  ]

private def messageJson : ChatMessage -> Lean.Json
  | .system content => .mkObj [("role", .str "system"), ("content", .str content)]
  | .user content => .mkObj [("role", .str "user"), ("content", .str content)]
  | .assistant content reasoningContent toolCalls =>
      .mkObj (
        [("role", .str "assistant"),
          ("content", content.map Lean.Json.str |>.getD .null),
          ("tool_calls", .arr (toolCalls.map functionCallJson).toArray)]
        ++ optionalField "reasoning_content" (reasoningContent.map Lean.Json.str))
  | .tool toolCallId content =>
      .mkObj [
        ("role", .str "tool"),
        ("tool_call_id", .str toolCallId),
        ("content", .str content)
      ]

private def functionToolJson (tool : FunctionTool) : Lean.Json :=
  .mkObj (
    [("name", .str tool.name), ("parameters", tool.parameters)]
      ++ optionalField "description" (tool.description.map Lean.Json.str)
      ++ optionalField "strict" (tool.strict.map Lean.Json.bool))

private def toolJson (tool : ToolDefinition) : Lean.Json :=
  .mkObj [("type", .str "function"), ("function", functionToolJson tool.function)]

def toJson (request : ChatRequest) : Lean.Json :=
  .mkObj (
    [("model", .str request.model),
      ("messages", .arr (request.messages.toList.map messageJson).toArray),
      ("stream", .bool false)]
      ++ optionalField "thinking" (request.thinking.map ThinkingMode.toJson)
      ++ optionalField "reasoning_effort" (request.reasoningEffort.map ReasoningEffort.toJson)
      ++ optionalField "max_tokens"
        (request.maxTokens.map (fun value => .num (Lean.JsonNumber.fromNat value)))
      ++ optionalField "response_format" (request.responseFormat.map ResponseFormat.toJson)
      ++ (if request.tools.isEmpty then [] else
        [("tools", .arr (request.tools.map toolJson).toArray)])
      ++ optionalField "tool_choice" (request.toolChoice.map ToolChoice.toJson))

end ChatRequest

/-! ## HTTP request plan -/

inductive HttpMethod where
  | post
deriving DecidableEq, Repr

structure Header where
  name : String
  value : String
  deriving DecidableEq, Repr

structure HttpRequest where
  method : HttpMethod
  url : String
  headers : List Header
  body : String
  deriving DecidableEq, Repr

structure ApiKey where
  value : String

structure RequestPlan where
  request : HttpRequest
  source : ChatRequest
  body_eq : request.body = Lean.Json.compress (source.toJson)

def buildRequest (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) : RequestPlan :=
  let body := Lean.Json.compress source.toJson
  {
    request := {
      method := .post
      url := baseUrl ++ "/chat/completions"
      headers := [
        { name := "Content-Type", value := "application/json" },
        { name := "Authorization", value := "Bearer " ++ apiKey.value }
      ]
      body := body
    }
    source := source
    body_eq := rfl
  }

theorem buildRequest_body_eq
    (baseUrl : String) (apiKey : ApiKey) (source : ChatRequest) :
    (buildRequest baseUrl apiKey source).request.body = Lean.Json.compress source.toJson :=
  (buildRequest baseUrl apiKey source).body_eq

/-! ## Response vocabulary -/

inductive FinishReason where
  | stop
  | length
  | contentFilter
  | toolCalls
  | insufficientSystemResource
deriving DecidableEq, Repr

structure Usage where
  promptTokens : Nat
  completionTokens : Nat
  totalTokens : Nat
  deriving DecidableEq, Repr

structure AssistantResponse where
  content : Option String
  reasoningContent : Option String
  toolCalls : List FunctionCall
  deriving DecidableEq, Repr

structure Choice where
  index : Nat
  message : AssistantResponse
  finishReason : Option FinishReason
  deriving DecidableEq, Repr

structure NonemptyChoices where
  head : Choice
  tail : List Choice
  deriving DecidableEq, Repr

namespace NonemptyChoices

def toList (choices : NonemptyChoices) : List Choice := choices.head :: choices.tail

end NonemptyChoices

structure ChatResponse where
  id : String
  model : String
  choices : NonemptyChoices
  usage : Option Usage
  deriving DecidableEq, Repr

structure ApiErrorBody where
  message : String
  type : Option String
  param : Option String
  code : Option String
  deriving DecidableEq, Repr

inductive ApiDecodeError where
  | typeMismatch
      (path : List PathSegment)
      (expected : String)
      (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | invalidLength (path : List PathSegment) (expected actual : Nat)
  | unsupportedTag (path : List PathSegment) (tag : String)
deriving DecidableEq, Repr

inductive ResponseError where
  | invalidJson (message : String)
  | decode (error : ApiDecodeError)
  | api (error : ApiErrorBody)
deriving DecidableEq, Repr

structure HttpResponse where
  status : Nat
  body : String
  deriving DecidableEq, Repr

inductive ClientError where
  | transport (message : String)
  | httpStatus (status : Nat) (body : String)
  | response (error : ResponseError)
deriving DecidableEq, Repr

structure Transport where
  send : HttpRequest -> IO (Except String HttpResponse)

/-! ## Response decoding -/

private def jsonKind : Lean.Json -> JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def field? : Lean.Json -> String -> Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def indexPath (path : List PathSegment) (index : Nat) : List PathSegment :=
  path ++ [.index index]

private def requireField (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def decodeString (path : List PathSegment) : Lean.Json -> Except ApiDecodeError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeBool (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Bool
  | .bool value => .ok value
  | json => .error (.typeMismatch path "boolean" (jsonKind json))

private def decodeNat (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Nat
  | .num ⟨Int.ofNat value, 0⟩ => .ok value
  | json => .error (.typeMismatch path "nonnegative integer" (jsonKind json))

private def decodeRequiredString (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError String :=
  do decodeString (fieldPath path name) (← requireField json path name)

private def decodeRequiredNat (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError Nat :=
  do decodeNat (fieldPath path name) (← requireField json path name)

private def decodeOptionalString (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError (Option String) :=
  match field? json name with
  | none | some .null => .ok none
  | some value => .some <$> decodeString (fieldPath path name) value

private def decodeOptionalBool (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError (Option Bool) :=
  match field? json name with
  | none | some .null => .ok none
  | some value => .some <$> decodeBool (fieldPath path name) value

private def decodeNullableString (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError (Option String) :=
  decodeOptionalString json path name

private def decodeFunctionCall (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError FunctionCall
  | json@(.obj _) => do
      let id ← decodeRequiredString json path "id"
      let kind ← decodeRequiredString json path "type"
      if kind != "function" then
        .error (.unsupportedTag (fieldPath path "type") kind)
      else
        let functionJson ← requireField json path "function"
        let name ← decodeRequiredString functionJson (fieldPath path "function") "name"
        let arguments ← decodeRequiredString functionJson (fieldPath path "function") "arguments"
        .ok { id, name, arguments }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeFunctionCalls (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError (List FunctionCall)
  | .arr values =>
      let rec loop : Nat -> List Lean.Json -> Except ApiDecodeError (List FunctionCall)
        | _, [] => .ok []
        | index, value :: rest => do
            let call ← decodeFunctionCall (indexPath path index) value
            let calls ← loop (index + 1) rest
            .ok (call :: calls)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeAssistantResponse (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError AssistantResponse
  | json@(.obj _) => do
      let role ← decodeRequiredString json path "role"
      if role != "assistant" then
        .error (.unsupportedTag (fieldPath path "role") role)
      else
        let content ← decodeNullableString json path "content"
        let reasoningContent ← decodeOptionalString json path "reasoning_content"
        let toolCalls ← match field? json "tool_calls" with
          | none | some .null => .ok []
          | some value => decodeFunctionCalls (fieldPath path "tool_calls") value
        .ok { content, reasoningContent, toolCalls }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeFinishReason (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError (Option FinishReason)
  | .null => .ok none
  | .str "stop" => .ok (some .stop)
  | .str "length" => .ok (some .length)
  | .str "content_filter" => .ok (some .contentFilter)
  | .str "tool_calls" => .ok (some .toolCalls)
  | .str "insufficient_system_resource" => .ok (some .insufficientSystemResource)
  | .str tag => .error (.unsupportedTag path tag)
  | json => .error (.typeMismatch path "nullable finish reason" (jsonKind json))

private def decodeChoice (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Choice
  | json@(.obj _) => do
      let index ← decodeRequiredNat json path "index"
      let message ← decodeAssistantResponse (fieldPath path "message")
        (← requireField json path "message")
      let finishReason ← decodeFinishReason (fieldPath path "finish_reason")
        (← requireField json path "finish_reason")
      .ok { index, message, finishReason }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeChoices (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError NonemptyChoices
  | .arr values =>
      match values.toList with
      | [] => .error (.invalidLength path 1 0)
      | head :: tail => do
          let first ← decodeChoice (indexPath path 0) head
          let rec loop : Nat -> List Lean.Json -> Except ApiDecodeError (List Choice)
            | _, [] => .ok []
            | index, value :: rest => do
                let choice ← decodeChoice (indexPath path index) value
                let choices ← loop (index + 1) rest
                .ok (choice :: choices)
          .ok { head := first, tail := ← loop 1 tail }
  | json => .error (.typeMismatch path "nonempty array" (jsonKind json))

private def decodeUsage (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Usage
  | json@(.obj _) => do
      let promptTokens ← decodeRequiredNat json path "prompt_tokens"
      let completionTokens ← decodeRequiredNat json path "completion_tokens"
      let totalTokens ← decodeRequiredNat json path "total_tokens"
      .ok { promptTokens, completionTokens, totalTokens }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeApiError (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError ApiErrorBody
  | json@(.obj _) => do
      let message ← decodeRequiredString json path "message"
      let type ← decodeOptionalString json path "type"
      let param ← decodeOptionalString json path "param"
      let code ← decodeOptionalString json path "code"
      .ok { message, type, param, code }
  | json => .error (.typeMismatch path "object" (jsonKind json))

def decodeResponseJson (json : Lean.Json) : Except ResponseError ChatResponse :=
  match json with
  | .obj _ =>
      match field? json "error" with
      | some errorJson =>
          match decodeApiError [.field "error"] errorJson with
          | .ok error => .error (.api error)
          | .error error => .error (.decode error)
      | none =>
          match _hId : requireField json [] "id" with
          | .error error => .error (.decode error)
          | .ok idJson =>
              match _hModel : requireField json [] "model" with
              | .error error => .error (.decode error)
              | .ok modelJson =>
                  match _hChoices : requireField json [] "choices" with
                  | .error error => .error (.decode error)
                  | .ok choicesJson =>
                      match decodeString [.field "id"] idJson,
                        decodeString [.field "model"] modelJson,
                        decodeChoices [.field "choices"] choicesJson with
                      | .ok id, .ok model, .ok choices =>
                          let usage : Except ApiDecodeError (Option Usage) :=
                            match field? json "usage" with
                            | none | some .null => .ok none
                            | some usageJson => do
                                let value ← decodeUsage [.field "usage"] usageJson
                                .ok (some value)
                          match usage with
                          | .ok usage => .ok { id, model, choices, usage }
                          | .error error => .error (.decode error)
                      | .error error, _, _ | _, .error error, _ | _, _, .error error =>
                          .error (.decode error)
  | value => .error (.decode (.typeMismatch [] "object" (jsonKind value)))

structure ValidatedResponse (body : String) where
  json : Lean.Json
  response : ChatResponse
  parsed : Lean.Json.parse body = .ok json
  decoded : decodeResponseJson json = .ok response

def validateResponse (body : String) : Except ResponseError (ValidatedResponse body) :=
  match parsed : Lean.Json.parse body with
  | .error message => .error (.invalidJson message)
  | .ok json =>
      match decoded : decodeResponseJson json with
      | .error error => .error error
      | .ok response => .ok { json, response, parsed, decoded }

/-! ## Explicit transport composition -/

private def successfulStatus (status : Nat) : Bool := 200 ≤ status && status < 300

def execute
    (transport : Transport)
    (plan : RequestPlan) :
    IO (Except ClientError (Σ body : String, ValidatedResponse body)) := do
  match ← transport.send plan.request with
  | .error message => pure (.error (.transport message))
  | .ok response =>
      if successfulStatus response.status then
        match validateResponse response.body with
        | .error error => pure (.error (.response error))
        | .ok validated => pure (.ok ⟨response.body, validated⟩)
      else
        pure (.error (.httpStatus response.status response.body))

/-! ## Kernel-checked fixtures -/

def exampleTool : ToolDefinition where
  function := {
    name := "get_weather"
    description := some "Read the weather for a city."
    parameters := .mkObj [
      ("type", .str "object"),
      ("properties", .mkObj [("city", .mkObj [("type", .str "string")])]),
      ("required", .arr #[.str "city"]),
      ("additionalProperties", .bool false)
    ]
    strict := some true
  }

def exampleRequest : ChatRequest where
  model := "deepseek-reasoner"
  messages := {
    head := .system "You are a helpful assistant."
    tail := [.user "What is the weather in San Francisco?"]
  }
  thinking := some .enabled
  reasoningEffort := some .high
  maxTokens := some 256
  responseFormat := none
  tools := [exampleTool]
  toolChoice := some .auto

def exampleResponseJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("finish_reason", .str "tool_calls"),
    ("message", .mkObj [
      ("role", .str "assistant"),
      ("content", .str "I will check that."),
      ("reasoning_content", .str "The user asked for weather."),
      ("tool_calls", .arr #[.mkObj [
        ("id", .str "call-weather-0"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "get_weather"),
          ("arguments", .str "{\"city\":\"San Francisco\"}")
        ])
      ]])
    ])
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 20)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 14)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 34))
  ])
]

def exampleResponse : ChatResponse where
  id := "chatcmpl-example"
  model := "deepseek-v4-pro"
  choices := {
    head := {
      index := 0
      message := {
        content := some "I will check that."
        reasoningContent := some "The user asked for weather."
        toolCalls := [{
          id := "call-weather-0"
          name := "get_weather"
          arguments := "{\"city\":\"San Francisco\"}"
        }]
      }
      finishReason := some .toolCalls
    }
    tail := []
  }
  usage := some { promptTokens := 20, completionTokens := 14, totalTokens := 34 }

def exampleResponseBody : String := Lean.Json.compress exampleResponseJson

def exampleTransport : Transport where
  send _request := pure <| .ok {
    status := 200
    body := exampleResponseBody
  }

end Cordis.DeepSeekApi
