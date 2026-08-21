import Cordis.DeepSeekStream
import Cordis.RichStream

/-!
# Source-honest mixed DeepSeek SSE to rich-stream projection

`DeepSeekRichStream` and `DeepSeekRichToolStream` are deliberately narrow projections. This
module takes the next useful step without pretending that a provider chunk carries an ordering
between simultaneously present fields: it accepts one choice at index zero, interleaves text,
reasoning, and at most one function call across data frames, and rejects a frame that presents
more than one block kind at once. The first-seen order is reified as contiguous rich-stream
indices. Tool ids may be introduced once and omitted on later deltas; the stateful projection
repeats the already certified id in the local raw delta.

The resulting `ValidatedMixedStream` retains the strict wire certificate, the exact projection,
and the intrinsic `RichStream.ValidatedTrace`. It still excludes multiple choices/calls,
content-filter and provider-failure finishes, replay metadata, live transport, and deployed
assembler behavior.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekRichMixedStream

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
  | multipleToolCalls (count : Nat)
  | nonzeroToolIndex (index : Nat)
  | missingToolId
  | toolIdMismatch (expected actual : String)
  | toolNameMismatch (expected actual : String)
  | missingToolName
  | usageBeforeFinish
  | missingUsage
  | missingBlock
  | unsupportedFinish (reason : DeepSeekApi.FinishReason)
  | finishMismatch (reason : DeepSeekApi.FinishReason)
  | dataAfterFinish
  | missingFinish
  | extraAfterDone
  | richValidation (error : RichStream.ValidationError)
deriving DecidableEq, Repr

inductive MixedStreamError where
  | wire (error : DeepSeekStream.StreamError)
  | projection (error : ProjectionError)
deriving DecidableEq, Repr

structure MixedState where
  nextIndex : Nat := 0
  textIndex : Option Nat := none
  text : String := ""
  reasoningIndex : Option Nat := none
  reasoning : String := ""
  toolIndex : Option Nat := none
  toolId : Option String := none
  toolName : Option String := none
  toolArguments : String := ""
  finished : Bool := false
deriving DecidableEq, Repr

namespace MixedState

def initial : MixedState := {}

def hasBlock (state : MixedState) : Bool :=
  state.textIndex.isSome || state.reasoningIndex.isSome || state.toolIndex.isSome

end MixedState

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

private def mergeId (current : Option String) (incoming : Option String) :
    Except ProjectionError String :=
  match current, incoming with
  | none, none => .error .missingToolId
  | none, some value => .ok value
  | some expected, none => .ok expected
  | some expected, some actual =>
      if expected = actual then .ok expected else .error (.toolIdMismatch expected actual)

private def mergeName (current : Option String) (incoming : Option String) :
    Except ProjectionError (Option String) :=
  match current, incoming with
  | none, none => .ok none
  | none, some value => .ok (some value)
  | some expected, none => .ok (some expected)
  | some expected, some actual =>
      if expected = actual then .ok (some expected)
      else .error (.toolNameMismatch expected actual)

private def appendText (state : MixedState) (content : Option String) :
    MixedState × List RichStream.RawChunk :=
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

private def appendReasoning (state : MixedState) (content : Option String) :
    MixedState × List RichStream.RawChunk :=
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

private def onlyToolCall : List DeepSeekStream.ToolCallDelta →
    Except ProjectionError (Option DeepSeekStream.ToolCallDelta)
  | [] => .ok none
  | [call] =>
      if call.index = 0 then .ok (some call) else .error (.nonzeroToolIndex call.index)
  | calls => .error (.multipleToolCalls calls.length)

private def appendTool (state : MixedState) (call : DeepSeekStream.ToolCallDelta) :
    Except ProjectionError (MixedState × List RichStream.RawChunk) := do
  let id ← mergeId state.toolId call.id
  let name ← mergeName state.toolName call.name
  let arguments := call.arguments.getD ""
  let delta : RichStream.ToolDelta := {
    id
    name := call.name
    argumentsDelta := arguments
  }
  match state.toolIndex with
  | some index =>
      .ok ({ state with
          toolId := some id
          toolName := name
          toolArguments := state.toolArguments ++ arguments },
        [.toolCallDelta index delta])
  | none =>
      let index := state.nextIndex
      .ok ({ state with
          nextIndex := index + 1
          toolIndex := some index
          toolId := some id
          toolName := name
          toolArguments := arguments },
        [.blockStart index .toolCall, .toolCallDelta index delta])

private def applyDelta (state : MixedState) (delta : DeepSeekStream.Delta) :
    Except ProjectionError (MixedState × List RichStream.RawChunk) := do
  checkRole delta
  let call ← onlyToolCall delta.toolCalls
  match delta.content, delta.reasoningContent, call with
  | some content, none, none => .ok (appendText state (some content))
  | none, some reasoning, none => .ok (appendReasoning state (some reasoning))
  | none, none, none => .ok (appendText state none)
  | none, none, some tool => appendTool state tool
  | _, _, _ => .error .mixedKinds

private def closeBlocks (state : MixedState) :
    Except ProjectionError (List RichStream.RawChunk) := do
  let textEnd := match state.textIndex with
    | none => []
    | some index => [.blockEnd index (.text state.text)]
  let reasoningEnd := match state.reasoningIndex with
    | none => []
    | some index => [.blockEnd index (.reasoning state.reasoning)]
  let toolEnd ← match state.toolIndex with
    | none => .ok []
    | some index =>
        let id ← match state.toolId with
          | none => .error .missingToolId
          | some value => .ok value
        let name ← match state.toolName with
          | none => .error .missingToolName
          | some value => .ok value
        .ok [.blockEnd index (.toolCall id name state.toolArguments)]
  .ok (textEnd ++ reasoningEnd ++ toolEnd)

private def finishReason (state : MixedState) (reason : DeepSeekApi.FinishReason) :
    Except ProjectionError RichStream.FinishReason :=
  if state.toolIndex.isSome then
    if reason = .toolCalls then .ok .toolCalls else .error (.finishMismatch reason)
  else if reason = .toolCalls then
    .error (.finishMismatch reason)
  else
    match toFinishReason reason with
    | none => .error (.unsupportedFinish reason)
    | some value => .ok value

private def applyData (state : MixedState) (chunk : DeepSeekStream.StreamChunk) :
    Except ProjectionError (MixedState × List RichStream.RawChunk) := do
  if state.finished then
    .error .dataAfterFinish
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
      .ok ({ next with finished := true }, emitted ++ endings ++ [
        .usage (toUsage usage),
        .finish richReason none
      ])

def projectFrames : MixedState → List DeepSeekStream.Frame →
    Except ProjectionError (List RichStream.RawChunk)
  | state, [] => if state.finished then .ok [] else .error .missingFinish
  | state, .done :: rest =>
      if rest.isEmpty then
        if state.finished then .ok [] else .error .missingFinish
      else
        .error .extraAfterDone
  | state, .data frame :: rest => do
      let (next, emitted) ← applyData state frame.chunk
      let suffix ← projectFrames next rest
      .ok (emitted ++ suffix)

/-! The same state machine can be exercised on already-decoded chunks. This small
    executable surface is what the kernel examples below use; the JSON/SSE wrapper
    remains separately testable without making the JSON parser part of a theorem's
    reduction footprint. -/

def projectChunks : MixedState → List DeepSeekStream.StreamChunk →
    Except ProjectionError (List RichStream.RawChunk)
  | state, [] => if state.finished then .ok [] else .error .missingFinish
  | state, chunk :: rest => do
      let (next, emitted) ← applyData state chunk
      let suffix ← projectChunks next rest
      .ok (emitted ++ suffix)

structure ValidatedMixedStream (body : String) where
  wire : DeepSeekStream.ValidatedSseStream body
  raw : List RichStream.RawChunk
  projection : projectFrames MixedState.initial wire.frames = .ok raw
  rich : RichStream.ValidatedTrace RichStream.State.initial raw

def validateMixedStream (body : String) :
    Except MixedStreamError (ValidatedMixedStream body) :=
  match DeepSeekStream.validateSse body with
  | .error error => .error (.wire error)
  | .ok validated =>
      match projected : projectFrames MixedState.initial validated.frames with
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

/-! ## Executable mixed reasoning/text/tool fixture -/

def mixedStartTextJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("content", .str "Hello ")]),
    ("finish_reason", .null)
  ]])
]

def mixedReasoningJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("reasoning_content", .str "plan")]),
    ("finish_reason", .null)
  ]])
]

def mixedToolStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("tool_calls", .arr #[.mkObj [
      ("index", .num (Lean.JsonNumber.fromNat 0)),
      ("id", .str "call-a"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "lookup"),
          ("arguments", .str "{\"q\":\"")
        ])
      ]])]),
    ("finish_reason", .null)
  ]])
]

def mixedTextContinuationJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("content", .str "world")]),
    ("finish_reason", .null)
  ]])
]

def mixedReasoningContinuationJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("reasoning_content", .str " check")]),
    ("finish_reason", .null)
  ]])
]

def mixedFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj []),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 4)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 8)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 12))
  ])
]

def mixedContinuationJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("tool_calls", .arr #[.mkObj [
      ("index", .num (Lean.JsonNumber.fromNat 0)),
      ("function", .mkObj [("arguments", .str "lean\"}")])
    ]])]),
    ("finish_reason", .null)
  ]])
]

def mixedStreamBody : String :=
  "data: " ++ Lean.Json.compress mixedStartTextJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress mixedReasoningJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress mixedToolStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress mixedContinuationJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress mixedTextContinuationJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress mixedReasoningContinuationJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress mixedFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def mixedBlocks : List RichStream.ContentBlock := [
  .text "Hello world",
  .reasoning "plan check",
  .toolCall "call-a" "lookup" "{\"q\":\"lean\"}"
]

def mixedUsage : RichStream.TokenUsage := {
  inputTokens := 4
  outputTokens := 8
}

def mixedRaw : List RichStream.RawChunk := [
  .blockStart 0 .text,
  .textDelta 0 "Hello ",
  .blockStart 1 .reasoning,
  .reasoningDelta 1 "plan",
  .blockStart 2 .toolCall,
  .toolCallDelta 2 { id := "call-a", name := some "lookup", argumentsDelta := "{\"q\":\"" },
  .toolCallDelta 2 { id := "call-a", name := none, argumentsDelta := "lean\"}" },
  .textDelta 0 "world",
  .reasoningDelta 1 " check",
  .blockEnd 0 (.text "Hello world"),
  .blockEnd 1 (.reasoning "plan check"),
  .blockEnd 2 (.toolCall "call-a" "lookup" "{\"q\":\"lean\"}"),
  .usage mixedUsage,
  .finish .toolCalls none
]

def rawSummary (body : String) : Option (List RichStream.RawChunk) :=
  match validateMixedStream body with
  | .ok validated => some validated.raw
  | .error _ => none

def mixedTextChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := some "Hello ", reasoningContent := none, toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def mixedReasoningChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := some "plan", toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def mixedToolStartChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 0
      id := some "call-a"
      name := some "lookup"
      arguments := some "{\"q\":\""
    }] }
    finishReason := none
  }]
  usage := none
}

def mixedToolContinuationChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [{
      index := 0
      id := none
      name := none
      arguments := some "lean\"}"
    }] }
    finishReason := none
  }]
  usage := none
}

def mixedTextContinuationChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := some "world", reasoningContent := none, toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def mixedReasoningContinuationChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := some " check", toolCalls := [] }
    finishReason := none
  }]
  usage := none
}

def mixedFinishChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-example"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := { role := none, content := none, reasoningContent := none, toolCalls := [] }
    finishReason := some .toolCalls
  }]
  usage := some { promptTokens := 4, completionTokens := 8, totalTokens := 12 }
}

def mixedChunks : List DeepSeekStream.StreamChunk := [
  mixedTextChunk,
  mixedReasoningChunk,
  mixedToolStartChunk,
  mixedToolContinuationChunk,
  mixedTextContinuationChunk,
  mixedReasoningContinuationChunk,
  mixedFinishChunk
]

def chunkRawSummary (chunks : List DeepSeekStream.StreamChunk) :
    Option (List RichStream.RawChunk) :=
  match projectChunks MixedState.initial chunks with
  | .ok raw => some raw
  | .error _ => none

theorem project_mixed_chunks_exact :
    chunkRawSummary mixedChunks = some mixedRaw := by
  rfl

theorem mixed_blocks_exact : mixedBlocks = [
  .text "Hello world",
  .reasoning "plan check",
  .toolCall "call-a" "lookup" "{\"q\":\"lean\"}"
] := by
  rfl

def mixedKindsJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-mixed-error"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("content", .str "text"),
      ("reasoning_content", .str "private")
    ]),
    ("finish_reason", .null)
  ]])
]

def mixedKindsBody : String :=
  "data: " ++ Lean.Json.compress mixedKindsJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def projectionErrorSummary (body : String) : Option ProjectionError :=
  match validateMixedStream body with
  | .error (.projection error) => some error
  | _ => none

def mixedKindsChunk : DeepSeekStream.StreamChunk := {
  id := "chatcmpl-mixed-error"
  model := "deepseek-reasoner"
  choices := [{
    index := 0
    delta := {
      role := none
      content := some "text"
      reasoningContent := some "private"
      toolCalls := []
    }
    finishReason := none
  }]
  usage := none
}

def chunkProjectionErrorSummary (chunks : List DeepSeekStream.StreamChunk) :
    Option ProjectionError :=
  match projectChunks MixedState.initial chunks with
  | .error error => some error
  | .ok _ => none

theorem reject_sameFrame_mixedKinds :
    chunkProjectionErrorSummary [mixedKindsChunk] = some .mixedKinds := by
  rfl

end Cordis.DeepSeekRichMixedStream
