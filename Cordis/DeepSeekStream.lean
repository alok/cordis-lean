import Cordis.DeepSeekApi
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
# Proof-carrying DeepSeek SSE boundary

This module adds the wire layer immediately after `DeepSeekApi`: it parses the strict
`data: <JSON>` / `data: [DONE]` framing used by a non-error streaming chat response and
decodes a small OpenAI-compatible delta vocabulary. Every accepted data frame retains its
raw JSON payload together with parser and decoder equalities. The result is deliberately
not a `RichStream.Trace`: block assembly, provider chunk ordering, cancellation, backpressure,
and a live HTTP reader remain separate semantic obligations.

The parser rejects malformed lines, malformed JSON, unsupported finish/tool tags, data after
`[DONE]`, and bodies that omit the terminal marker. Blank SSE separator lines are accepted;
other SSE fields such as `event:`, `id:`, and comments are outside this strict subset.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStream

open Cordis
open Cordis.DeepSeekApi

/-! ## Typed streaming delta vocabulary -/

structure ToolCallDelta where
  index : Nat
  id : Option String
  name : Option String
  arguments : Option String
  deriving DecidableEq, Repr

structure Delta where
  role : Option String
  content : Option String
  reasoningContent : Option String
  toolCalls : List ToolCallDelta
  deriving DecidableEq, Repr

structure Choice where
  index : Nat
  delta : Delta
  finishReason : Option FinishReason
  deriving DecidableEq, Repr

structure StreamChunk where
  id : String
  model : String
  choices : List Choice
  usage : Option Usage
  deriving DecidableEq, Repr

/-! ## Errors and proof-carrying frames -/

inductive StreamError where
  | invalidUtf8
  | unexpectedLine (line : Nat) (text : String)
  | invalidJson (line : Nat) (message : String)
  | decode (line : Nat) (error : ApiDecodeError)
  | missingDone
  | dataAfterDone (line : Nat)
deriving DecidableEq, Repr

/-! ## JSON helpers -/

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

private def decodeOptionalNat (json : Lean.Json) (path : List PathSegment) (name : String) :
    Except ApiDecodeError (Option Nat) :=
  match field? json name with
  | none | some .null => .ok none
  | some value => .some <$> decodeNat (fieldPath path name) value

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

private def decodeToolCallDelta (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError ToolCallDelta
  | json@(.obj _) => do
      let index ← decodeRequiredNat json path "index"
      let id ← decodeOptionalString json path "id"
      let kind ← decodeOptionalString json path "type"
      match kind with
      | some value =>
          if value = "function" then
            pure ()
          else
            .error (.unsupportedTag (fieldPath path "type") value)
      | none => pure ()
      let functionFields : Option Lean.Json := match field? json "function" with
        | none | some .null => none
        | some value => some value
      let name ← match functionFields with
        | none => .ok none
        | some functionJson => decodeOptionalString functionJson (fieldPath path "function") "name"
      let arguments ← match functionFields with
        | none => .ok none
        | some functionJson =>
            decodeOptionalString functionJson (fieldPath path "function") "arguments"
      .ok { index, id, name, arguments }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeToolCallDeltas (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError (List ToolCallDelta)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except ApiDecodeError (List ToolCallDelta)
        | _, [] => .ok []
        | index, value :: rest => do
            let call ← decodeToolCallDelta (indexPath path index) value
            let calls ← loop (index + 1) rest
            .ok (call :: calls)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeDelta (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Delta
  | json@(.obj _) => do
      let role ← decodeOptionalString json path "role"
      let content ← decodeOptionalString json path "content"
      let reasoningContent ← decodeOptionalString json path "reasoning_content"
      let toolCalls ← match field? json "tool_calls" with
        | none | some .null => .ok []
        | some value => decodeToolCallDeltas (fieldPath path "tool_calls") value
      .ok { role, content, reasoningContent, toolCalls }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeChoice (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Choice
  | json@(.obj _) => do
      let index ← decodeRequiredNat json path "index"
      let delta ← decodeDelta (fieldPath path "delta")
        (← requireField json path "delta")
      let finishReason ← decodeFinishReason (fieldPath path "finish_reason")
        (← requireField json path "finish_reason")
      .ok { index, delta, finishReason }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeChoices (path : List PathSegment) :
    Lean.Json -> Except ApiDecodeError (List Choice)
  | .arr values =>
      let rec loop : Nat → List Lean.Json → Except ApiDecodeError (List Choice)
        | _, [] => .ok []
        | index, value :: rest => do
            let choice ← decodeChoice (indexPath path index) value
            let choices ← loop (index + 1) rest
            .ok (choice :: choices)
      loop 0 values.toList
  | json => .error (.typeMismatch path "array" (jsonKind json))

private def decodeUsage (path : List PathSegment) : Lean.Json -> Except ApiDecodeError Usage
  | json@(.obj _) => do
      let promptTokens ← decodeRequiredNat json path "prompt_tokens"
      let completionTokens ← decodeRequiredNat json path "completion_tokens"
      let totalTokens ← decodeRequiredNat json path "total_tokens"
      .ok { promptTokens, completionTokens, totalTokens }
  | json => .error (.typeMismatch path "object" (jsonKind json))

def decodeStreamChunkJson (json : Lean.Json) : Except ApiDecodeError StreamChunk :=
  match json with
  | .obj _ => do
      let id ← decodeRequiredString json [] "id"
      let model ← decodeRequiredString json [] "model"
      let choices ← decodeChoices [.field "choices"] (← requireField json [] "choices")
      let usage ← match field? json "usage" with
        | none | some .null => .ok none
        | some usageJson => some <$> decodeUsage [.field "usage"] usageJson
      .ok { id, model, choices, usage }
  | value => .error (.typeMismatch [] "object" (jsonKind value))

structure DataFrame where
  raw : String
  json : Lean.Json
  chunk : StreamChunk
  parsed : Lean.Json.parse raw = .ok json
  decoded : decodeStreamChunkJson json = .ok chunk

inductive Frame where
  | data (frame : DataFrame)
  | done

/-! ## Strict SSE framing -/

private def normalizeLine (line : String) : String :=
  if line.endsWith "\r" then (line.dropEnd 1).toString else line

private def dataPayload (line : String) : Option String :=
  if line.startsWith "data:" then
    let payload := (line.drop 5).toString
    if payload.startsWith " " then some (payload.drop 1).toString else some payload
  else
    none

private def parseSseLines (requireDone : Bool) (line : Nat) (done : Bool) :
    List String → Except StreamError (List Frame)
  | [] =>
      if done || !requireDone then .ok [] else .error .missingDone
  | rawLine :: rest =>
      let current := normalizeLine rawLine
      if current.isEmpty then
        parseSseLines requireDone (line + 1) done rest
      else if done then
        .error (.dataAfterDone line)
      else
        match dataPayload current with
        | none => .error (.unexpectedLine line current)
        | some "[DONE]" =>
            match parseSseLines requireDone (line + 1) true rest with
            | .ok frames => .ok (.done :: frames)
            | .error error => .error error
        | some payload =>
            match parsed : Lean.Json.parse payload with
            | .error message => .error (.invalidJson line message)
            | .ok json =>
                match decoded : decodeStreamChunkJson json with
                | .error error => .error (.decode line error)
                | .ok chunk =>
                    let frame : DataFrame := { raw := payload, json, chunk, parsed, decoded }
                    match parseSseLines requireDone (line + 1) false rest with
                    | .ok frames => .ok (.data frame :: frames)
                    | .error error => .error error

def parseSse (body : String) : Except StreamError (List Frame) :=
  parseSseLines true 0 false (body.splitOn "\n")

def parseSsePrefix (body : String) : Except StreamError (List Frame) :=
  if body.isEmpty then
    .ok []
  else
    parseSseLines false 0 false (body.splitOn "\n")

theorem parseSsePrefix_empty : parseSsePrefix "" = .ok [] := by
  rfl

structure ValidatedSseStream (body : String) where
  frames : List Frame
  parsed : parseSse body = .ok frames

def validateSse (body : String) : Except StreamError (ValidatedSseStream body) :=
  match parsed : parseSse body with
  | .error error => .error error
  | .ok frames => .ok { frames, parsed }

def validateSseBytes (body : ByteArray) :
    Except StreamError (Sigma fun source : String => ValidatedSseStream source) :=
  match String.fromUTF8? body with
  | none => .error .invalidUtf8
  | some source =>
      match validateSse source with
      | .error error => .error error
      | .ok validated => .ok ⟨source, validated⟩

/-! ## Executable fixture -/

def exampleChunkJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-stream-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("role", .str "assistant"),
      ("content", .str "Hello")
    ]),
    ("finish_reason", .null)
  ]])
]

def exampleStreamBody : String :=
  "data: " ++ Lean.Json.compress exampleChunkJson ++ "\n\n" ++
  "data: [DONE]\n\n"

end Cordis.DeepSeekStream
