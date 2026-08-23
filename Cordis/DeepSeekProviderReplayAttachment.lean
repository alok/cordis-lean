import Cordis.DeepSeekProviderStreamAssembly

/-!
# Opaque replay attachment beside provider assembly

`DeepSeekProviderAssembler` follows the source-shaped post-decoder vocabulary and stores
`replayState` as an opaque `String`.  The strict wire projector intentionally does not invent a
serialization for that field, while `RichStream` already carries a proof-aligned
`RawReplayEnvelope`.  This module is the narrow bridge between those choices: it assembles the
canonical provider blocks and carries the rich replay envelope as a separate typed attachment.

The attachment is therefore lossless at this boundary, but it is not a provider replay encoder.
The provider assembler result keeps `replayState = none`; the exact envelope is available in the
dependent `replay` field.  Wire-backed bodies from the current accepted stream subset continue to
carry no replay attachment because that subset emits none.  JSON replay schemas, provider replay
semantics, transport, and deployed TypeScript equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProviderReplayAttachment

open Cordis
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.RichStream

/-! ## Rich chunks into canonical provider chunks -/

/-- Map a validated rich raw chunk while deliberately retaining replay separately. -/
def mapRichRawChunk : RawChunk → Chunk
  | .blockStart index kind => .blockStart index (blockTypeOf kind)
  | .textDelta index fragment => .textDelta index fragment
  | .reasoningDelta index fragment => .reasoningDelta index fragment
  | .toolCallDelta index fragment =>
      .toolCallDelta index fragment.id fragment.name fragment.argumentsDelta
  | .blockEnd index block => .blockEnd index (blockOf block)
  | .usage usage => .usage (usageOf usage)
  | .finish reason _ => .finish (finishOf reason) none

def mapRichRawChunks : List RawChunk → List Chunk := List.map mapRichRawChunk

/-- The replay envelope carried by an indexed rich terminal state, with its alignment proof
erased. -/
def stateReplay : RichStream.State → Option RawReplayEnvelope
  | .active _ _ => none
  | .terminal _ _ _ replay => replay.map ReplayEnvelope.erase

theorem finish_replay_is_attached_not_serialized
    (reason : FinishReason) (replay : Option RawReplayEnvelope) :
    mapRichRawChunk (.finish reason replay) =
      .finish (finishOf reason) none :=
  rfl

/-! ## Proof-carrying assembly -/

inductive ReplayAttachmentError where
  | rich (error : ValidationError)
  | assembly (error : AssemblyError)
deriving DecidableEq, Repr

structure ValidatedReplayAssembly (raw : List RawChunk) where
  source : ValidatedTrace RichStream.State.initial raw
  source_eq : validateTrace RichStream.State.initial raw = .ok source
  assembly : Certificate (mapRichRawChunks raw)
  replay : Option RawReplayEnvelope
  replay_eq : stateReplay source.finish = replay

/-- Validate the rich trace and assemble its canonical provider chunks in one certificate. -/
def validateRaw (raw : List RawChunk) :
    Except ReplayAttachmentError (ValidatedReplayAssembly raw) :=
  match sourceEq : validateTrace RichStream.State.initial raw with
  | .error error => .error (.rich error)
  | .ok source =>
      match _assemblyEq : DeepSeekProviderAssembler.validate (mapRichRawChunks raw) with
      | .error error => .error (.assembly error)
      | .ok assembly =>
          .ok {
            source
            source_eq := sourceEq
            assembly
            replay := stateReplay source.finish
            replay_eq := rfl
          }

theorem ValidatedReplayAssembly.source_exact
    {raw : List RawChunk} (value : ValidatedReplayAssembly raw) :
    validateTrace RichStream.State.initial raw = .ok value.source :=
  value.source_eq

theorem ValidatedReplayAssembly.assembly_exact
    {raw : List RawChunk} (value : ValidatedReplayAssembly raw) :
    assemble value.assembly.state = .ok value.assembly.result :=
  value.assembly.result_eq

theorem ValidatedReplayAssembly.replay_exact
    {raw : List RawChunk} (value : ValidatedReplayAssembly raw) :
    stateReplay value.source.finish = value.replay :=
  value.replay_eq

/-! ## Wire-backed companion and explicit absence witness -/

structure ValidatedProviderAssembly (body : String) where
  source : DeepSeekRichMultiStream.ValidatedMultiStream body
  source_eq : DeepSeekRichMultiStream.validateMultiStream body = .ok source
  assembly : ValidatedReplayAssembly source.raw

inductive ProviderAssemblyError where
  | projection (error : DeepSeekRichMultiStream.MultiStreamError)
  | attachment (error : ReplayAttachmentError)
deriving DecidableEq, Repr

def validateBody (body : String) :
    Except ProviderAssemblyError (ValidatedProviderAssembly body) :=
  match sourceEq : DeepSeekRichMultiStream.validateMultiStream body with
  | .error error => .error (.projection error)
  | .ok source =>
      match _attached : validateRaw source.raw with
      | .error error => .error (.attachment error)
      | .ok assembly => .ok { source, source_eq := sourceEq, assembly }

theorem ValidatedProviderAssembly.source_exact
    {body : String} (value : ValidatedProviderAssembly body) :
    DeepSeekRichMultiStream.validateMultiStream body = .ok value.source :=
  value.source_eq

theorem ValidatedProviderAssembly.replay_exact
    {body : String} (value : ValidatedProviderAssembly body) :
    stateReplay (ValidatedReplayAssembly.source value.assembly).finish =
      ValidatedReplayAssembly.replay value.assembly :=
  ValidatedReplayAssembly.replay_eq value.assembly

/-! ## Executable witnesses -/

def interleavedResult :
    Option (ValidatedReplayAssembly RichStream.interleavedRaw) :=
  match validateRaw RichStream.interleavedRaw with
  | .error _ => none
  | .ok value => some value

def interleavedExpectedBlocks : List Block := [
  .text "Hello world",
  .reasoning "plan: check",
  .toolCall "call-a" "lookup" "{\"q\":\"lean\"}",
  .toolCall "call-b" "sum" "{\"xs\":[1,2]}"
]

def interleavedExpectedAssembly : Assembled := {
  role := "assistant"
  blocks := interleavedExpectedBlocks
  usage := some (usageOf RichStream.interleavedUsage)
  finish := .stop
  replayState := none
}

def interleavedSummary : Bool :=
  match interleavedResult with
  | none => false
  | some value =>
      value.replay = some RichStream.interleavedReplay.erase &&
      value.assembly.result.blocks = interleavedExpectedBlocks &&
      value.assembly.result.finish = .stop &&
      value.assembly.result.replayState = none

theorem interleaved_result_exact :
    interleavedResult.isSome = true := by
  rfl

private theorem interleaved_replay_of_value
    (value : ValidatedReplayAssembly RichStream.interleavedRaw) :
    value.replay = some RichStream.interleavedReplay.erase := by
  have source_eq : value.source = RichStream.validatedInterleavedTrace := by
    apply Except.ok.inj
    exact value.source_eq.symm.trans RichStream.validate_interleaved_exact
  have finish_eq : value.source.finish = RichStream.validatedInterleavedTrace.finish :=
    congrArg (fun source => source.finish) source_eq
  calc
    value.replay = stateReplay value.source.finish := value.replay_eq.symm
    _ = stateReplay RichStream.validatedInterleavedTrace.finish := congrArg stateReplay finish_eq
    _ = some RichStream.interleavedReplay.erase := by
      rfl

private theorem interleaved_assembly_result_of_value
    (value : ValidatedReplayAssembly RichStream.interleavedRaw) :
    value.assembly.result = interleavedExpectedAssembly := by
  have assembled_eq :
      DeepSeekProviderAssembler.assemble
          (DeepSeekProviderAssembler.pushMany (mapRichRawChunks RichStream.interleavedRaw)) =
        .ok value.assembly.result := by
    calc
      DeepSeekProviderAssembler.assemble
          (DeepSeekProviderAssembler.pushMany (mapRichRawChunks RichStream.interleavedRaw)) =
          DeepSeekProviderAssembler.assemble value.assembly.state :=
        congrArg DeepSeekProviderAssembler.assemble value.assembly.state_eq
      _ = .ok value.assembly.result := value.assembly.result_eq
  apply Except.ok.inj
  exact assembled_eq.symm.trans (by rfl)

theorem interleaved_replay_attachment_exact :
    match interleavedResult with
    | none => False
    | some value => value.replay = some RichStream.interleavedReplay.erase := by
  cases h : interleavedResult with
  | none =>
      have hSome := interleaved_result_exact
      rw [h] at hSome
      simp at hSome
  | some value => simpa [h] using interleaved_replay_of_value value

theorem interleaved_provider_assembly_keeps_attachment_out_of_wire_slot :
    match interleavedResult with
    | none => False
    | some value =>
        value.assembly.result.replayState = none ∧
          value.replay = some RichStream.interleavedReplay.erase := by
  cases h : interleavedResult with
  | none =>
      have hSome := interleaved_result_exact
      rw [h] at hSome
      simp at hSome
  | some value =>
      have hAssembly := interleaved_assembly_result_of_value value
      have hReplay := interleaved_replay_of_value value
      simp [hAssembly, hReplay, interleavedExpectedAssembly]

theorem executable_summaries :
    interleavedSummary = true ∧
      interleavedResult.isSome = true := by
  cases h : interleavedResult with
  | none =>
      have hSome := interleaved_result_exact
      rw [h] at hSome
      simp at hSome
  | some value =>
      have hReplay := interleaved_replay_of_value value
      have hAssembly := interleaved_assembly_result_of_value value
      simp [interleavedSummary, h, hReplay, hAssembly, interleavedExpectedAssembly]

end Cordis.DeepSeekProviderReplayAttachment
