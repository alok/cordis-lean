import Cordis.DeepSeekStream
import Cordis.RichStream

/-!
# Source-honest DeepSeek SSE to rich tool-call projection

This module is the tool-call companion to `DeepSeekRichStream`. It composes the
validated DeepSeek wire frames with the existing `RichStream` validator for one
deliberately small language: one choice at index zero, at most one provider tool
call at provider index zero, optional assistant text, no reasoning, and a
terminal `tool_calls` finish when a tool call is present. Provider tool-call IDs
are required on every accepted delta so the local raw language can retain its
stable identifier without inventing state.

The projection tracks first-seen text/tool order, concatenates raw argument
fragments without parsing them, closes the exact local blocks, and retains wire,
projection, and intrinsic rich-trace certificates. Multiple tool calls,
reasoning, mixed text/tool deltas, missing IDs/names, and richer provider
assembler behavior fail closed rather than being silently normalized.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekRichToolStream

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekStream
open Cordis.RichStream

inductive ProjectionError where
  | noChoices
  | multipleChoices (count : Nat)
  | nonzeroChoiceIndex (index : Nat)
  | unsupportedRole (role : String)
  | reasoningUnsupported
  | multipleToolCalls (count : Nat)
  | nonzeroToolIndex (index : Nat)
  | mixedTextAndTool
  | missingToolId
  | toolIdMismatch (expected actual : String)
  | toolNameMismatch (expected actual : String)
  | missingToolName
  | usageBeforeFinish
  | missingUsage
  | missingContentAndTool
  | unsupportedFinish (reason : DeepSeekApi.FinishReason)
  | finishMismatch (reason : DeepSeekApi.FinishReason)
  | dataAfterFinish
  | missingFinish
  | extraAfterDone
  | richValidation (error : RichStream.ValidationError)
deriving DecidableEq, Repr

inductive ToolStreamError where
  | wire (error : DeepSeekStream.StreamError)
  | projection (error : ProjectionError)
deriving DecidableEq, Repr

structure ToolState where
  textStarted : Bool
  text : String
  toolStarted : Bool
  toolId : Option String
  toolName : Option String
  toolArguments : String
  finished : Bool
deriving DecidableEq, Repr

namespace ToolState

def initial : ToolState := {
  textStarted := false
  text := ""
  toolStarted := false
  toolId := none
  toolName := none
  toolArguments := ""
  finished := false
}

def textIndex (state : ToolState) : Nat := if state.toolStarted then 1 else 0

def toolIndex (state : ToolState) : Nat := if state.textStarted then 1 else 0

end ToolState

def toUsage (usage : Usage) : RichStream.TokenUsage := {
  inputTokens := usage.promptTokens
  outputTokens := usage.completionTokens
}

def toFinishReason : DeepSeekApi.FinishReason → Option RichStream.FinishReason
  | .stop => some .stop
  | .toolCalls => some .toolCalls
  | .length => some .maxTokens
  | .contentFilter => none
  | .insufficientSystemResource => none

private def onlyChoice : List DeepSeekStream.Choice → Except ProjectionError DeepSeekStream.Choice
  | [] => .error .noChoices
  | [choice] => .ok choice
  | choices => .error (.multipleChoices choices.length)

private def checkRole (delta : DeepSeekStream.Delta) : Except ProjectionError Unit := do
  match delta.role with
  | none => pure ()
  | some "assistant" => pure ()
  | some role => .error (.unsupportedRole role)
  match delta.reasoningContent with
  | none => pure ()
  | some _ => .error .reasoningUnsupported

private def onlyToolCall : List DeepSeekStream.ToolCallDelta →
    Except ProjectionError (Option DeepSeekStream.ToolCallDelta)
  | [] => .ok none
  | [call] =>
      if call.index = 0 then .ok (some call) else .error (.nonzeroToolIndex call.index)
  | calls => .error (.multipleToolCalls calls.length)

private def mergeId (current : Option String) (incoming : String) : Except ProjectionError String :=
  match current with
  | none => .ok incoming
  | some expected =>
      if expected = incoming then .ok expected
      else .error (.toolIdMismatch expected incoming)

private def mergeName (current : Option String) (incoming : Option String) :
    Except ProjectionError (Option String) :=
  match current, incoming with
  | none, none => .ok none
  | none, some name => .ok (some name)
  | some expected, none => .ok (some expected)
  | some expected, some actual =>
      if expected = actual then .ok (some expected)
      else .error (.toolNameMismatch expected actual)

private def appendText (state : ToolState) (content : Option String) :
    ToolState × List RichStream.RawChunk :=
  match content with
  | none => (state, [])
  | some fragment =>
      let index := state.textIndex
      if state.textStarted then
        ({ state with text := state.text ++ fragment }, [.textDelta index fragment])
      else
        ({ state with textStarted := true, text := fragment },
          [.blockStart index .text, .textDelta index fragment])

private def appendTool (state : ToolState) (call : DeepSeekStream.ToolCallDelta) :
    Except ProjectionError (ToolState × List RichStream.RawChunk) := do
  let id ← match call.id with
    | none => .error .missingToolId
    | some value => .ok value
  let mergedId ← mergeId state.toolId id
  let mergedName ← mergeName state.toolName call.name
  let arguments := match call.arguments with
    | none => ""
    | some value => value
  let index := state.toolIndex
  let next := {
    state with
    toolStarted := true
    toolId := some mergedId
    toolName := mergedName
    toolArguments := state.toolArguments ++ arguments
  }
  let delta : RichStream.ToolDelta := {
    id := id
    name := call.name
    argumentsDelta := arguments
  }
  if state.toolStarted then
    .ok (next, [.toolCallDelta index delta])
  else
    .ok (next, [.blockStart index .toolCall, .toolCallDelta index delta])

private def applyDelta (state : ToolState) (delta : DeepSeekStream.Delta) :
    Except ProjectionError (ToolState × List RichStream.RawChunk) := do
  let call ← onlyToolCall delta.toolCalls
  match delta.content, call with
  | some _, some _ => .error .mixedTextAndTool
  | some content, none => .ok (appendText state (some content))
  | none, some tool => appendTool state tool
  | none, none => .ok (appendText state none)

private def closeBlocks (state : ToolState) :
    Except ProjectionError (List RichStream.RawChunk) := do
  let textEnd := if state.textStarted then
      [.blockEnd state.textIndex (.text state.text)]
    else []
  let toolEnd ← if state.toolStarted then
      let id ← match state.toolId with
        | none => .error .missingToolId
        | some value => .ok value
      let name ← match state.toolName with
        | none => .error .missingToolName
        | some value => .ok value
      .ok [.blockEnd state.toolIndex (.toolCall id name state.toolArguments)]
    else
      .ok []
  .ok (textEnd ++ toolEnd)

private def finishReason (state : ToolState) (reason : DeepSeekApi.FinishReason) :
    Except ProjectionError RichStream.FinishReason :=
  if state.toolStarted then
    if reason = .toolCalls then
      .ok .toolCalls
    else
      .error (.finishMismatch reason)
  else if reason = .toolCalls then
    .error (.finishMismatch reason)
  else
    match toFinishReason reason with
    | none => .error (.unsupportedFinish reason)
    | some value => .ok value

private def applyData (state : ToolState) (chunk : DeepSeekStream.StreamChunk) :
    Except ProjectionError (ToolState × List RichStream.RawChunk) := do
  if state.finished then
    .error .dataAfterFinish
  let choice ← onlyChoice chunk.choices
  if choice.index = 0 then
    pure ()
  else
    .error (.nonzeroChoiceIndex choice.index)
  checkRole choice.delta
  let (next, emitted) ← applyDelta state choice.delta
  match choice.finishReason with
  | none =>
      match chunk.usage with
      | none => pure ()
      | some _ => .error .usageBeforeFinish
      .ok (next, emitted)
  | some reason =>
      if !next.textStarted && !next.toolStarted then
        .error .missingContentAndTool
      let usage ← match chunk.usage with
        | none => .error .missingUsage
        | some value => .ok value
      let richReason ← finishReason next reason
      let endings ← closeBlocks next
      .ok ({ next with finished := true }, emitted ++ endings ++ [
        .usage (toUsage usage),
        .finish richReason none
      ])

def projectFrames : ToolState → List DeepSeekStream.Frame →
    Except ProjectionError (List RichStream.RawChunk)
  | state, [] =>
      if state.finished then .ok [] else .error .missingFinish
  | state, .done :: rest =>
      if rest.isEmpty then
        if state.finished then .ok [] else .error .missingFinish
      else
        .error .extraAfterDone
  | state, .data frame :: rest => do
      let (next, emitted) ← applyData state frame.chunk
      let suffix ← projectFrames next rest
      .ok (emitted ++ suffix)

structure ValidatedToolStream (body : String) where
  wire : DeepSeekStream.ValidatedSseStream body
  raw : List RichStream.RawChunk
  projection : projectFrames ToolState.initial wire.frames = .ok raw
  rich : RichStream.ValidatedTrace RichStream.State.initial raw

def validateToolStream (body : String) :
    Except ToolStreamError (ValidatedToolStream body) :=
  match DeepSeekStream.validateSse body with
  | .error error => .error (.wire error)
  | .ok validated =>
      match projected : projectFrames ToolState.initial validated.frames with
      | .error error => .error (.projection error)
      | .ok raw =>
          match RichStream.validateTrace RichStream.State.initial raw with
          | .error error => .error (.projection (.richValidation error))
          | .ok witness => .ok {
              wire := validated
              raw
              projection := projected
              rich := witness
            }

/-! ## Executable single-tool fixture -/

def exampleToolStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-tool-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "call-a"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "lookup"),
          ("arguments", .str "{\\\"q\\\":")
        ])
      ]])
    ]),
    ("finish_reason", .null)
  ]])
]

def exampleToolFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-tool-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "call-a"),
        ("function", .mkObj [("arguments", .str "lean\\\"}")])
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

def exampleToolStreamBody : String :=
  "data: " ++ Lean.Json.compress exampleToolStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress exampleToolFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

end Cordis.DeepSeekRichToolStream
