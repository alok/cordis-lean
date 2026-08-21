import Cordis.DeepSeekStream
import Cordis.RichStream

/-!
# Source-honest multi-call DeepSeek SSE to rich-stream projection

This module extends the mixed provider boundary to the next useful assembler case: one
assistant choice can interleave text, reasoning, and any finite number of function calls across
data frames. Provider tool indices are retained in a small state machine and are mapped to
contiguous local rich-stream block indices in first-seen order. Each call keeps its own stable
identifier/name and raw argument accumulator, so calls may be resumed in an arbitrary frame
order without losing which arguments belong to which provider index.

The accepted language is intentionally still narrow: one choice at index zero, function tool
calls only, no same-frame mixture of content/reasoning/tool fields, and successful stop,
max-token, or tool-call finishes with terminal usage. Multiple choices, provider failure or
content-filter finishes, replay metadata, live transport, and deployed assembler equivalence
remain outside this source-grounded slice.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekRichMultiStream

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekStream
open Cordis.RichStream

inductive ProjectionError where
  | noChoices
  | multipleChoices (count : Nat)
  | nonzeroChoiceIndex (index : Nat)
  | unsupportedRole (role : String)
  | mixedKinds
  | missingToolId (providerIndex : Nat)
  | toolIdMismatch (providerIndex : Nat) (expected actual : String)
  | toolNameMismatch (providerIndex : Nat) (expected actual : String)
  | missingToolName (providerIndex : Nat)
  | usageBeforeFinish
  | missingUsage
  | missingBlock
  | unsupportedFinish (reason : DeepSeekApi.FinishReason)
  | finishMismatch (reason : DeepSeekApi.FinishReason)
  | dataAfterFinish
  | extraAfterDone
  | richValidation (error : RichStream.ValidationError)
deriving DecidableEq, Repr

inductive MultiStreamError where
  | wire (error : DeepSeekStream.StreamError)
  | projection (error : ProjectionError)
deriving DecidableEq, Repr

structure ToolState where
  providerIndex : Nat
  localIndex : Nat
  id : Option String := none
  name : Option String := none
  arguments : String := ""
deriving DecidableEq, Repr

structure MultiState where
  nextIndex : Nat := 0
  textIndex : Option Nat := none
  text : String := ""
  reasoningIndex : Option Nat := none
  reasoning : String := ""
  tools : List ToolState := []
  finished : Bool := false
deriving DecidableEq, Repr

namespace MultiState

def initial : MultiState := {}

def hasBlock (state : MultiState) : Bool :=
  state.textIndex.isSome || state.reasoningIndex.isSome || !state.tools.isEmpty

end MultiState

def toUsage (usage : Usage) : RichStream.TokenUsage := {
  inputTokens := usage.promptTokens
  outputTokens := usage.completionTokens
}

def toFinishReason : DeepSeekApi.FinishReason → Option RichStream.FinishReason
  | .stop => some .stop
  | .length => some .maxTokens
  | .toolCalls => some .toolCalls
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

private def mergeId (providerIndex : Nat) (current : Option String)
    (incoming : Option String) : Except ProjectionError String :=
  match current, incoming with
  | none, none => .error (.missingToolId providerIndex)
  | none, some value => .ok value
  | some expected, none => .ok expected
  | some expected, some actual =>
      if expected = actual then .ok expected
      else .error (.toolIdMismatch providerIndex expected actual)

private def mergeName (providerIndex : Nat) (current : Option String)
    (incoming : Option String) : Except ProjectionError (Option String) :=
  match current, incoming with
  | none, none => .ok none
  | none, some value => .ok (some value)
  | some expected, none => .ok (some expected)
  | some expected, some actual =>
      if expected = actual then .ok (some expected)
      else .error (.toolNameMismatch providerIndex expected actual)

private def findTool (providerIndex : Nat) : List ToolState → Option ToolState
  | [] => none
  | tool :: rest =>
      if tool.providerIndex = providerIndex then some tool else findTool providerIndex rest

private def replaceTool (replacement : ToolState) : List ToolState → List ToolState
  | [] => []
  | tool :: rest =>
      if tool.providerIndex = replacement.providerIndex then replacement :: rest
      else tool :: replaceTool replacement rest

private def appendText (state : MultiState) (content : Option String) :
    MultiState × List RichStream.RawChunk :=
  match content with
  | none => (state, [])
  | some fragment =>
      match state.textIndex with
      | some index =>
          ({ state with text := state.text ++ fragment }, [.textDelta index fragment])
      | none =>
          let index := state.nextIndex
          ({ state with
              nextIndex := index + 1
              textIndex := some index
              text := fragment },
            [.blockStart index .text, .textDelta index fragment])

private def appendReasoning (state : MultiState) (content : Option String) :
    MultiState × List RichStream.RawChunk :=
  match content with
  | none => (state, [])
  | some fragment =>
      match state.reasoningIndex with
      | some index =>
          ({ state with reasoning := state.reasoning ++ fragment },
            [.reasoningDelta index fragment])
      | none =>
          let index := state.nextIndex
          ({ state with
              nextIndex := index + 1
              reasoningIndex := some index
              reasoning := fragment },
            [.blockStart index .reasoning, .reasoningDelta index fragment])

private def appendToolCall (state : MultiState) (call : DeepSeekStream.ToolCallDelta) :
    Except ProjectionError (MultiState × List RichStream.RawChunk) := do
  match findTool call.index state.tools with
  | none =>
      let id ← mergeId call.index none call.id
      let name ← mergeName call.index none call.name
      let localIndex := state.nextIndex
      let tool : ToolState := {
        providerIndex := call.index
        localIndex
        id := some id
        name
        arguments := call.arguments.getD ""
      }
      let delta : RichStream.ToolDelta := {
        id
        name := call.name
        argumentsDelta := call.arguments.getD ""
      }
      .ok ({ state with nextIndex := localIndex + 1, tools := state.tools ++ [tool] },
        [.blockStart localIndex .toolCall, .toolCallDelta localIndex delta])
  | some current =>
      let id ← mergeId call.index current.id call.id
      let name ← mergeName call.index current.name call.name
      let delta : RichStream.ToolDelta := {
        id
        name := call.name
        argumentsDelta := call.arguments.getD ""
      }
      let updated : ToolState := {
        current with id := some id, name, arguments := current.arguments ++ delta.argumentsDelta
      }
      .ok ({ state with tools := replaceTool updated state.tools },
        [.toolCallDelta current.localIndex delta])

private def appendToolCalls (state : MultiState) :
    List DeepSeekStream.ToolCallDelta → Except ProjectionError
      (MultiState × List RichStream.RawChunk)
  | [] => .ok (state, [])
  | call :: rest => do
      let (next, emitted) ← appendToolCall state call
      let (final, suffix) ← appendToolCalls next rest
      .ok (final, emitted ++ suffix)

private def applyDelta (state : MultiState) (delta : DeepSeekStream.Delta) :
    Except ProjectionError (MultiState × List RichStream.RawChunk) := do
  checkRole delta
  let hasContent := delta.content.isSome
  let hasReasoning := delta.reasoningContent.isSome
  let hasTools := !delta.toolCalls.isEmpty
  if (hasContent && hasReasoning) || (hasContent && hasTools) || (hasReasoning && hasTools) then
    .error .mixedKinds
  else if hasContent then
    .ok (appendText state delta.content)
  else if hasReasoning then
    .ok (appendReasoning state delta.reasoningContent)
  else
    appendToolCalls state delta.toolCalls

private def closeToolBlocks : List ToolState → Except ProjectionError (List RichStream.RawChunk)
  | [] => .ok []
  | tool :: rest => do
      let id ← match tool.id with
        | none => .error (.missingToolId tool.providerIndex)
        | some value => .ok value
      let name ← match tool.name with
        | none => .error (.missingToolName tool.providerIndex)
        | some value => .ok value
      let suffix ← closeToolBlocks rest
      .ok (.blockEnd tool.localIndex (.toolCall id name tool.arguments) :: suffix)

private def closeBlocks (state : MultiState) :
    Except ProjectionError (List RichStream.RawChunk) := do
  let textEnd := match state.textIndex with
    | none => []
    | some index => [.blockEnd index (.text state.text)]
  let reasoningEnd := match state.reasoningIndex with
    | none => []
    | some index => [.blockEnd index (.reasoning state.reasoning)]
  let tools ← closeToolBlocks state.tools
  .ok (textEnd ++ reasoningEnd ++ tools)

private def finishReason (state : MultiState) (reason : DeepSeekApi.FinishReason) :
    Except ProjectionError RichStream.FinishReason :=
  if !state.tools.isEmpty then
    if reason = .toolCalls then .ok .toolCalls else .error (.finishMismatch reason)
  else if reason = .toolCalls then
    .error (.finishMismatch reason)
  else
    match toFinishReason reason with
    | none => .error (.unsupportedFinish reason)
    | some value => .ok value

private def applyData (state : MultiState) (chunk : DeepSeekStream.StreamChunk) :
    Except ProjectionError (MultiState × List RichStream.RawChunk) := do
  if state.finished then .error .dataAfterFinish
  let choice ← onlyChoice chunk.choices
  if choice.index = 0 then pure () else .error (.nonzeroChoiceIndex choice.index)
  let (next, emitted) ← applyDelta state choice.delta
  match choice.finishReason with
  | none =>
      match chunk.usage with
      | none => .ok (next, emitted)
      | some _ => .error .usageBeforeFinish
  | some reason =>
      if !next.hasBlock then .error .missingBlock
      let usage ← match chunk.usage with
        | none => .error .missingUsage
        | some value => .ok value
      let richReason ← finishReason next reason
      let endings ← closeBlocks next
      .ok ({ next with finished := true }, emitted ++ endings ++
        [.usage (toUsage usage), .finish richReason none])

def projectFrames : MultiState → List DeepSeekStream.Frame →
    Except ProjectionError (List RichStream.RawChunk)
  | state, [] => if state.finished then .ok [] else .error .missingBlock
  | state, .done :: rest =>
      if rest.isEmpty then
        if state.finished then .ok [] else .error .missingBlock
      else .error .extraAfterDone
  | state, .data frame :: rest => do
      let (next, emitted) ← applyData state frame.chunk
      let suffix ← projectFrames next rest
      .ok (emitted ++ suffix)

def projectChunks : MultiState → List DeepSeekStream.StreamChunk →
    Except ProjectionError (List RichStream.RawChunk)
  | state, [] => if state.finished then .ok [] else .error .missingBlock
  | state, chunk :: rest => do
      let (next, emitted) ← applyData state chunk
      let suffix ← projectChunks next rest
      .ok (emitted ++ suffix)

structure ValidatedMultiStream (body : String) where
  wire : DeepSeekStream.ValidatedSseStream body
  raw : List RichStream.RawChunk
  projection : projectFrames MultiState.initial wire.frames = .ok raw
  rich : RichStream.ValidatedTrace RichStream.State.initial raw

def validateMultiStream (body : String) :
    Except MultiStreamError (ValidatedMultiStream body) :=
  match DeepSeekStream.validateSse body with
  | .error error => .error (.wire error)
  | .ok validated =>
      match projected : projectFrames MultiState.initial validated.frames with
      | .error error => .error (.projection error)
      | .ok raw =>
          match RichStream.validateTrace RichStream.State.initial raw with
          | .error error => .error (.projection (.richValidation error))
          | .ok witness => .ok { wire := validated, raw, projection := projected, rich := witness }

/-! ## Kernel and runtime fixtures with two provider calls -/

def textChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := some "answer ", reasoningContent := none, toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def callAStart : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 4, id := some "call-a", name := some "lookup", arguments := some "{\"q\":"
    }] }
    finishReason := none
  }]
  usage := none
}

def callBStart : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 9, id := some "call-b", name := some "sum", arguments := some "{\"xs\":["
    }] }
    finishReason := none
  }]
  usage := none
}

def reasoningChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := some "check", toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def callBContinuation : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 9, id := none, name := none, arguments := some "1,2]}"
    }] }
    finishReason := none
  }]
  usage := none
}

def callAContinuation : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 4, id := none, name := none, arguments := some "\"lean\"}"
    }] }
    finishReason := none
  }]
  usage := none
}

def textContinuation : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := some "done", reasoningContent := none, toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def finishChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [] }
    finishReason := some .toolCalls
  }]
  usage := some { promptTokens := 5, completionTokens := 9, totalTokens := 14 }
}

def multiChunks : List DeepSeekStream.StreamChunk :=
  [textChunk, callAStart, callBStart, reasoningChunk, callBContinuation,
    callAContinuation, textContinuation, finishChunk]

def multiRaw : List RichStream.RawChunk := [
  .blockStart 0 .text,
  .textDelta 0 "answer ",
  .blockStart 1 .toolCall,
  .toolCallDelta 1 { id := "call-a", name := some "lookup", argumentsDelta := "{\"q\":" },
  .blockStart 2 .toolCall,
  .toolCallDelta 2 { id := "call-b", name := some "sum", argumentsDelta := "{\"xs\":[" },
  .blockStart 3 .reasoning,
  .reasoningDelta 3 "check",
  .toolCallDelta 2 { id := "call-b", name := none, argumentsDelta := "1,2]}" },
  .toolCallDelta 1 { id := "call-a", name := none, argumentsDelta := "\"lean\"}" },
  .textDelta 0 "done",
  .blockEnd 0 (.text "answer done"),
  .blockEnd 3 (.reasoning "check"),
  .blockEnd 1 (.toolCall "call-a" "lookup" "{\"q\":\"lean\"}"),
  .blockEnd 2 (.toolCall "call-b" "sum" "{\"xs\":[1,2]}"),
  .usage { inputTokens := 5, outputTokens := 9 },
  .finish .toolCalls none
]

def chunkRawSummary (chunks : List DeepSeekStream.StreamChunk) :
    Option (List RichStream.RawChunk) :=
  match projectChunks MultiState.initial chunks with
  | .ok raw => some raw
  | .error _ => none

theorem project_multi_chunks_exact :
    chunkRawSummary multiChunks = some multiRaw := by
  rfl

theorem multi_call_indices_are_local_contiguous :
    (multiRaw.filterMap (fun chunk => match chunk with
      | .blockStart index .toolCall => some index
      | _ => none)) = [1, 2] := by
  rfl

def mismatchedCallChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-error"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 9, id := some "other", name := none, arguments := some "x"
    }] }
    finishReason := none
  }]
  usage := none
}

theorem reject_mismatched_call_id :
    projectChunks
      { MultiState.initial with tools := [{
        providerIndex := 9, localIndex := 0, id := some "call-b", name := some "sum"
      }] }
      [mismatchedCallChunk] =
      .error (.toolIdMismatch 9 "call-b" "other") := by
  rfl

def multiChoiceChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-multi-error"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := some "a", reasoningContent := none, toolCalls := [] }
    finishReason := none
  }, {
    index := 1
    delta := { role := none, content := some "b", reasoningContent := none, toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

theorem reject_multiple_choices :
    projectChunks MultiState.initial [multiChoiceChunk] =
      .error (.multipleChoices 2) := by
  rfl

def multiJsonBody : String :=
  "data: " ++ Lean.Json.compress (.mkObj [
    ("id", .str "chatcmpl-multi-example"), ("model", .str "deepseek-reasoner"),
    ("choices", .arr #[.mkObj [
      ("index", .num (Lean.JsonNumber.fromNat 0)),
      ("delta", .mkObj [("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 4)), ("id", .str "call-a"),
        ("type", .str "function"), ("function", .mkObj [
          ("name", .str "lookup"), ("arguments", .str "{\"q\":\"")
        ])
      ]])]), ("finish_reason", .null)
    ]]), ("usage", .null)
  ]) ++ "\n\n" ++ "data: [DONE]\n\n"

def multiStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-multi-json"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("tool_calls", .arr #[
      .mkObj [("index", .num (Lean.JsonNumber.fromNat 4)), ("id", .str "call-a"),
        ("type", .str "function"), ("function", .mkObj [
          ("name", .str "lookup"), ("arguments", .str "{\"q\":\"")
        ])],
      .mkObj [("index", .num (Lean.JsonNumber.fromNat 9)), ("id", .str "call-b"),
        ("type", .str "function"), ("function", .mkObj [
          ("name", .str "sum"), ("arguments", .str "{\"xs\":[")
        ])]
    ])]),
    ("finish_reason", .null)
  ]])
]

def multiContinueJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-multi-json"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("tool_calls", .arr #[
      .mkObj [("index", .num (Lean.JsonNumber.fromNat 4)),
        ("function", .mkObj [("arguments", .str "lean\"}")])],
      .mkObj [("index", .num (Lean.JsonNumber.fromNat 9)),
        ("function", .mkObj [("arguments", .str "1,2]}")])]
    ])]),
    ("finish_reason", .null)
  ]])
]

def multiFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-multi-json"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj []),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 5)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 9)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 14))
  ])
]

def multiBody : String :=
  "data: " ++ Lean.Json.compress multiStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress multiContinueJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress multiFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def jsonSummary (body : String) : Option Nat :=
  match validateMultiStream body with
  | .ok validated => some validated.wire.frames.length
  | .error _ => none

end Cordis.DeepSeekRichMultiStream
