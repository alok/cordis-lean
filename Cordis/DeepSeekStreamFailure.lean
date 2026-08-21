import Cordis.DeepSeekStream

/-!
# Proof-carrying DeepSeek terminal failures

`DeepSeekStream` already decodes the provider's `content_filter` and
`insufficient_system_resource` finish tags, while the rich-stream projectors
intentionally reject them because they are not ordinary completed text/tool
traces. This module preserves that boundary instead of erasing the failure:
it validates a complete strict SSE body whose final data frame is one of those
two provider failures, retaining the raw prefix, terminal frame, choice, and
optional usage certificate.

The result is deliberately not a `RichStream.Trace` or a session message. It
does not claim provider-complete block assembly, retry/cancellation behavior,
or support for wire-level `error`/`aborted` envelopes that are outside the
current `DeepSeekStream` vocabulary.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekStreamFailure

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekStream

inductive FailureReason where
  | contentFilter
  | insufficientSystemResource
deriving DecidableEq, Repr

namespace FailureReason

def wire : FailureReason → FinishReason
  | .contentFilter => .contentFilter
  | .insufficientSystemResource => .insufficientSystemResource

def ofWire : FinishReason → Option FailureReason
  | .contentFilter => some .contentFilter
  | .insufficientSystemResource => some .insufficientSystemResource
  | .stop | .length | .toolCalls => none

theorem ofWire_wire (reason : FailureReason) : ofWire reason.wire = some reason := by
  cases reason <;> rfl

end FailureReason

inductive FailureProjectionError where
  | noChoices
  | multipleChoices (count : Nat)
  | nonzeroChoiceIndex (index : Nat)
  | usageBeforeFailure
  | unsupportedFinish (reason : FinishReason)
  | missingFailure
  | missingDone
  | dataAfterFailure
  | extraAfterDone
deriving DecidableEq, Repr

structure TerminalInfo (chunk : StreamChunk) where
  reason : FailureReason
  choice : DeepSeekStream.Choice
  choices_eq : chunk.choices = [choice]
  finish_eq : choice.finishReason = some reason.wire

inductive ChunkStatus (chunk : StreamChunk) where
  | open
  | terminal (info : TerminalInfo chunk)

private structure ChoiceWitness (choices : List DeepSeekStream.Choice) where
  choice : DeepSeekStream.Choice
  choices_eq : choices = [choice]

private def onlyChoice (choices : List DeepSeekStream.Choice) :
    Except FailureProjectionError (ChoiceWitness choices) :=
  match choices with
  | [] => .error .noChoices
  | [choice] => .ok { choice, choices_eq := rfl }
  | choices => .error (.multipleChoices choices.length)

private def classifyChunk (chunk : StreamChunk) :
    Except FailureProjectionError (ChunkStatus chunk) := do
  let witness ← onlyChoice chunk.choices
  let choice := witness.choice
  if choice.index ≠ 0 then
    .error (.nonzeroChoiceIndex choice.index)
  else
    match h : choice.finishReason with
    | none => .ok .open
    | some .contentFilter =>
        .ok (.terminal {
          reason := .contentFilter
          choice
          choices_eq := witness.choices_eq
          finish_eq := by simpa [FailureReason.wire] using h
        })
    | some .insufficientSystemResource =>
        .ok (.terminal {
          reason := .insufficientSystemResource
          choice
          choices_eq := witness.choices_eq
          finish_eq := by simpa [FailureReason.wire] using h
        })
    | some reason => .error (.unsupportedFinish reason)

structure FailureView where
  leading : List DataFrame
  terminal : DataFrame
  info : TerminalInfo terminal.chunk
  terminalIndex : Nat

namespace FailureView

def reason (view : FailureView) : FailureReason := view.info.reason

def usage (view : FailureView) : Option Usage := view.terminal.chunk.usage

def frames (view : FailureView) : List Frame :=
  view.leading.map Frame.data ++ [.data view.terminal, .done]

def chunks (view : FailureView) : List StreamChunk :=
  view.leading.map (fun frame => frame.chunk) ++ [view.terminal.chunk]

theorem terminal_reason (view : FailureView) :
    view.info.choice.finishReason = some view.info.reason.wire :=
  view.info.finish_eq

theorem terminal_choice (view : FailureView) :
    view.terminal.chunk.choices = [view.info.choice] :=
  view.info.choices_eq

end FailureView

def projectFrames : Nat → List Frame →
    Except FailureProjectionError FailureView
  | _, [] => .error .missingFailure
  | _, .done :: rest =>
      if rest.isEmpty then .error .missingFailure else .error .extraAfterDone
  | index, .data frame :: rest =>
      match classifyChunk frame.chunk with
      | .error error => .error error
      | .ok .open =>
          if frame.chunk.usage.isSome then
            .error .usageBeforeFailure
          else
            match projectFrames (index + 1) rest with
            | .error error => .error error
            | .ok view => .ok { view with leading := frame :: view.leading }
      | .ok (.terminal info) =>
          match rest with
          | [.done] => .ok {
              leading := []
              terminal := frame
              info
              terminalIndex := index
            }
          | [] => .error .missingDone
          | _ => .error .dataAfterFailure

structure ValidatedFailureStream (body : String) where
  wire : ValidatedSseStream body
  view : FailureView
  projection : projectFrames 0 wire.frames = .ok view

def validateFailureStream (body : String) :
    Except (Sum StreamError FailureProjectionError) (ValidatedFailureStream body) :=
  match validateSse body with
  | .error error => .error (.inl error)
  | .ok validated =>
      match projected : projectFrames 0 validated.frames with
      | .error error => .error (.inr error)
      | .ok view => .ok { wire := validated, view, projection := projected }

theorem validateFailureStream_reason
    {body : String} (validated : ValidatedFailureStream body) :
    validated.view.info.choice.finishReason = some validated.view.info.reason.wire :=
  validated.view.terminal_reason

theorem validateFailureStream_terminal_choice
    {body : String} (validated : ValidatedFailureStream body) :
    validated.view.terminal.chunk.choices = [validated.view.info.choice] :=
  validated.view.terminal_choice

/-! ## Executable provider-failure fixtures -/

def exampleFailureChunkJson (reason : String) : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-failure-example"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("content", .str "partial")
    ]),
    ("finish_reason", .str reason)
  ]])
]

def exampleFailureBody (reason : String) : String :=
  "data: " ++ Lean.Json.compress DeepSeekStream.exampleChunkJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress (exampleFailureChunkJson reason) ++ "\n\n" ++
  "data: [DONE]\n\n"

def exampleContentFilterBody : String := exampleFailureBody "content_filter"

def exampleInsufficientResourceBody : String :=
  exampleFailureBody "insufficient_system_resource"

def exampleContentFilter :
    Except (Sum StreamError FailureProjectionError)
      (ValidatedFailureStream exampleContentFilterBody) :=
  validateFailureStream exampleContentFilterBody

def exampleInsufficientResource :
    Except (Sum StreamError FailureProjectionError)
      (ValidatedFailureStream exampleInsufficientResourceBody) :=
  validateFailureStream exampleInsufficientResourceBody

end Cordis.DeepSeekStreamFailure
