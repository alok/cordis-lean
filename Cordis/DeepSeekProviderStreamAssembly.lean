import Cordis.DeepSeekProviderAssembler
import Cordis.DeepSeekRichMultiStream

/-!
# Strict DeepSeek stream to provider assembly

This module composes the strict one-choice/multi-call SSE projection with the
source-shaped post-decoder `BlockAssembler` model.  `DeepSeekRichMultiStream` first
certifies wire frames and their kind-indexed rich trace; this module then erases only
that rich-trace proof layer into the provider assembler's canonical chunk vocabulary
and retains a second exact fold/assembly certificate.

The bridge intentionally rejects aligned replay metadata rather than guessing a
provider serialization.  It also normalizes rich structured failure/abort causes to
the smaller provider `Failure` vocabulary.  Wire decoding, transport, external tool
effects, call-ID authenticity, and deployed TypeScript equivalence remain outside.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProviderStreamAssembly

open Cordis
open Cordis.DeepSeekProviderAssembler
open Cordis.DeepSeekRichMultiStream
open Cordis.RichStream

inductive ProviderStreamError where
  | projection (error : MultiStreamError)
  | replayMetadata
  | assembly (error : AssemblyError)
deriving DecidableEq, Repr

def blockTypeOf : BlockKind → BlockType
  | .text => .text
  | .reasoning => .reasoning
  | .toolCall => .toolCall

def blockOf : ContentBlock → Block
  | .text content => .text content
  | .reasoning content => .reasoning content
  | .toolCall id name arguments => .toolCall id name arguments

def usageOf (usage : TokenUsage) : Usage := {
  inputTokens := usage.inputTokens
  outputTokens := usage.outputTokens
  cacheReadTokens := some usage.cacheReadTokens
  cacheWriteTokens := some usage.cacheWriteTokens
  reasoningTokens := some usage.reasoningTokens
}

def failureOf (failure : StructuredFailure) : Failure := {
  code := failure.code
  message := failure.message
}

def abortOf (cause : AbortCause) : Failure := {
  code := "aborted"
  message := cause.detail
}

def finishOf : FinishReason → Finish
  | .stop => .stop
  | .toolCalls => .toolCalls
  | .maxTokens => .maxTokens
  | .error failure => .error (failureOf failure)
  | .aborted cause => .aborted (abortOf cause)

def mapRawChunk : RawChunk → Except ProviderStreamError Chunk
  | .blockStart index kind => .ok (.blockStart index (blockTypeOf kind))
  | .textDelta index fragment => .ok (.textDelta index fragment)
  | .reasoningDelta index fragment => .ok (.reasoningDelta index fragment)
  | .toolCallDelta index fragment =>
      .ok (.toolCallDelta index fragment.id fragment.name fragment.argumentsDelta)
  | .blockEnd index block => .ok (.blockEnd index (blockOf block))
  | .usage usage => .ok (.usage (usageOf usage))
  | .finish reason replay =>
      match replay with
      | none => .ok (.finish (finishOf reason) none)
      | some _ => .error .replayMetadata

def mapRawChunks : List RawChunk → Except ProviderStreamError (List Chunk)
  | [] => .ok []
  | chunk :: rest => do
      let mapped ← mapRawChunk chunk
      let suffix ← mapRawChunks rest
      .ok (mapped :: suffix)

structure ValidatedProviderAssembly (body : String) where
  source : ValidatedMultiStream body
  source_eq : validateMultiStream body = .ok source
  chunks : List Chunk
  chunks_eq : mapRawChunks source.raw = .ok chunks
  assembly : Certificate chunks

def validateBody (body : String) :
    Except ProviderStreamError (ValidatedProviderAssembly body) :=
  match sourceEq : validateMultiStream body with
  | .error error => .error (.projection error)
  | .ok source =>
      match chunksEq : mapRawChunks source.raw with
      | .error error => .error error
      | .ok chunks =>
          match _assemblyEq : DeepSeekProviderAssembler.validate chunks with
          | .error error => .error (.assembly error)
          | .ok assembly => .ok {
              source
              source_eq := sourceEq
              chunks
              chunks_eq := chunksEq
              assembly
            }

theorem ValidatedProviderAssembly.source_exact
    {body : String} (validated : ValidatedProviderAssembly body) :
    validateMultiStream body = .ok validated.source :=
  validated.source_eq

theorem ValidatedProviderAssembly.chunks_exact
    {body : String} (validated : ValidatedProviderAssembly body) :
    mapRawChunks validated.source.raw = .ok validated.chunks :=
  validated.chunks_eq

theorem ValidatedProviderAssembly.assembly_exact
    {body : String} (validated : ValidatedProviderAssembly body) :
    assemble validated.assembly.state = .ok validated.assembly.result :=
  validated.assembly.result_eq

/-! ## Executable wire-backed counter fixture -/

def counterStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("id", .str "counter-call-0"),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "counter_increment"),
          ("arguments", .str "[3,")
        ])
      ]])
    ]),
    ("finish_reason", .null)
  ]])
]

def counterContinueJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("function", .mkObj [("arguments", .str "10]")])
      ]])
    ]),
    ("finish_reason", .null)
  ]])
]

def counterFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-counter"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj []),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 2)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 3)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 5))
  ])
]

def counterBody : String :=
  "data: " ++ Lean.Json.compress counterStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress counterContinueJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress counterFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def counterAssemblySummary : Bool :=
  match validateBody counterBody with
  | .error _ => false
  | .ok validated =>
      validated.assembly.result.blocks == [
        .toolCall "counter-call-0" "counter_increment" "[3,10]"
      ] && validated.assembly.result.finish == .toolCalls

end Cordis.DeepSeekProviderStreamAssembly
