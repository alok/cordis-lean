import Cordis.DeepSeekStream
import Cordis.RichStream

/-!
# Source-honest DeepSeek SSE to rich-stream projection

`DeepSeekStream` retains provider JSON frames but intentionally does not infer the
block-indexed semantics used by `RichStream`. This module supplies one explicit,
strict projection for a useful subset: a single assistant text choice at index
zero, with no reasoning or tool-call deltas, one terminal stop/max-token reason,
and usage supplied on that terminal data frame. The projection inserts the local
text block start/end events and proves the resulting raw list with the existing
`RichStream.validateTrace` validator.

The source boundary is intentionally visible. Provider streaming can contain
multiple choices, reasoning, tool-call fragments, missing usage, and richer
finish/error behavior; those cases are rejected here instead of being silently
treated as the local rich-stream language.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekRichStream

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
  | toolCallsUnsupported
  | usageBeforeFinish
  | missingUsage
  | missingText
  | unsupportedFinish (reason : DeepSeekApi.FinishReason)
  | dataAfterFinish
  | missingFinish
  | extraAfterDone
  | richValidation (error : RichStream.ValidationError)
deriving DecidableEq, Repr

inductive TextStreamError where
  | wire (error : DeepSeekStream.StreamError)
  | projection (error : ProjectionError)
deriving DecidableEq, Repr

structure TextState where
  started : Bool
  content : String
  finished : Bool
deriving DecidableEq, Repr

namespace TextState

def initial : TextState := { started := false, content := "", finished := false }

end TextState

def toUsage (usage : Usage) : RichStream.TokenUsage := {
  inputTokens := usage.promptTokens
  outputTokens := usage.completionTokens
}

def toFinishReason : DeepSeekApi.FinishReason → Option RichStream.FinishReason
  | .stop => some .stop
  | .length => some .maxTokens
  | .toolCalls => none
  | .contentFilter => none
  | .insufficientSystemResource => none

private def onlyChoice : List DeepSeekStream.Choice → Except ProjectionError DeepSeekStream.Choice
  | [] => .error .noChoices
  | [choice] => .ok choice
  | choices => .error (.multipleChoices choices.length)

private def checkDelta (delta : DeepSeekStream.Delta) : Except ProjectionError Unit := do
  match delta.role with
  | none => pure ()
  | some "assistant" => pure ()
  | some role => .error (.unsupportedRole role)
  match delta.reasoningContent with
  | none => pure ()
  | some _ => .error .reasoningUnsupported
  if delta.toolCalls.isEmpty then
    pure ()
  else
    .error .toolCallsUnsupported

private def appendContent (state : TextState) (content : Option String) :
    TextState × List RichStream.RawChunk :=
  match content with
  | none => (state, [])
  | some fragment =>
      if state.started then
        ({ state with content := state.content ++ fragment },
          [.textDelta 0 fragment])
      else
        ({ state with started := true, content := fragment },
          [.blockStart 0 .text, .textDelta 0 fragment])

private def applyData (state : TextState) (chunk : DeepSeekStream.StreamChunk) :
    Except ProjectionError (TextState × List RichStream.RawChunk) := do
  if state.finished then
    .error .dataAfterFinish
  let choice ← onlyChoice chunk.choices
  if choice.index = 0 then
    pure ()
  else
    .error (.nonzeroChoiceIndex choice.index)
  checkDelta choice.delta
  match choice.finishReason with
  | none =>
      match chunk.usage with
      | none => pure ()
      | some _ => .error .usageBeforeFinish
      pure (appendContent state choice.delta.content)
  | some reason =>
      let (next, emitted) := appendContent state choice.delta.content
      if next.started then
        pure ()
      else
        .error .missingText
      let usage ← match chunk.usage with
        | none => .error .missingUsage
        | some value => .ok value
      let richReason ← match toFinishReason reason with
        | none => .error (.unsupportedFinish reason)
        | some value => .ok value
      let finalChunks := emitted ++ [
        .blockEnd 0 (.text next.content),
        .usage (toUsage usage),
        .finish richReason none
      ]
      .ok ({ next with finished := true }, finalChunks)

def projectFrames : TextState → List DeepSeekStream.Frame →
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

structure ValidatedTextStream (body : String) where
  wire : DeepSeekStream.ValidatedSseStream body
  raw : List RichStream.RawChunk
  projection : projectFrames TextState.initial wire.frames = .ok raw
  rich : RichStream.ValidatedTrace RichStream.State.initial raw

def validateTextStream (body : String) :
    Except TextStreamError (ValidatedTextStream body) :=
  match DeepSeekStream.validateSse body with
  | .error error => .error (.wire error)
  | .ok validated =>
      match projected : projectFrames TextState.initial validated.frames with
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

/-! ## Executable text-only fixture -/

def exampleFinishChunkJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-stream-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [("content", .str " world")]),
    ("finish_reason", .str "stop")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 3)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 2)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 5))
  ])
]

def exampleTextStreamBody : String :=
  "data: " ++ Lean.Json.compress DeepSeekStream.exampleChunkJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress exampleFinishChunkJson ++ "\n\n" ++
  "data: [DONE]\n\n"

end Cordis.DeepSeekRichStream
