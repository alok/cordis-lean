import Cordis.RichStream
import Lean.Data.Json.Basic

/-!
# Current DeepSeek stream JSON refinement

This module closes one executable boundary between DeepSeek Harness commit `99f6f02` and the
proof-carrying stream core. It decodes the JSON-AST shape of the current TypeScript `StreamChunk`
subset, preserves optional fields in a wire type, then refines decoded chunks through
`RichStream.validateTrace` to an intrinsic trace witness.

The supported source facts are the current fields in `packages/llm/llm/src/types.ts`: block-start,
text/reasoning/tool-call deltas, block-end, usage, and the successful stop/tool-calls/max-tokens
finish tags. Tool ids and arguments remain strings exactly as supplied.

Three gaps are rejected rather than guessed. Image and tool-result blocks are not represented by
`RichStream.ContentBlock`. Upstream error and aborted finishes both carry `LlmFailure`, while the
local terminal types have different fields. Upstream replay state is opaque lossless JSON, while
the local replay envelope has structured metadata. A present `replayState` therefore fails closed.

TypeScript optional usage counts remain optional in `WireUsage`. Refinement maps absence to local
zero; `WireUsage.toLocal` is the named, reviewable local normalization. JSON numbers are accepted
only as canonical nonnegative JavaScript-safe integers. Byte parsing, UTF-8, JSON text rendering,
transport, TypeScript object identity, and behavioral equivalence with `BlockAssembler` remain
outside this module.

The semantic validator deliberately follows the stronger local contract: contiguous block starts,
explicit starts and exact ends, one usage chunk, and usage before finish. The current TypeScript
`BlockAssembler` is more tolerant of malformed or delta-only streams. Acceptance here therefore
proves the local fail-closed refinement; it does not claim completeness for every input that the
TypeScript assembler happens to tolerate.
-/

set_option autoImplicit false

namespace Cordis.RuntimeRefinement

open Cordis

/-- Largest integer represented exactly by every JavaScript `number`. -/
def maxSafeInteger : Nat := 9007199254740991

/-- A canonical nonnegative JSON integer inside JavaScript's exact range. -/
structure SafeNat where
  value : Nat
  safe : value ≤ maxSafeInteger
  deriving DecidableEq, Repr

/-- JSON constructor observed at a failing decoder path. -/
inductive JsonKind where
  | null
  | boolean
  | number
  | string
  | array
  | object
  deriving BEq, DecidableEq, Repr

/-- One root-to-leaf segment in a wire decoding error. -/
inductive PathSegment where
  | field (name : String)
  | index (index : Nat)
  deriving BEq, DecidableEq, Repr

/-- Precise failures at the current TypeScript-to-Lean JSON-AST boundary. -/
inductive DecodeError where
  | typeMismatch (path : List PathSegment) (expected : String) (actual : JsonKind)
  | missingField (path : List PathSegment) (name : String)
  | unsupportedTag (path : List PathSegment) (tag : String)
  | unsupportedField (path : List PathSegment) (name : String)
  | unsafeInteger (path : List PathSegment) (value : Nat)
  deriving BEq, DecidableEq, Repr

/-- Exact optional token fields from the current TypeScript `TokenUsage` interface. -/
structure WireUsage where
  inputTokens : SafeNat
  outputTokens : SafeNat
  cacheReadTokens : Option SafeNat := none
  cacheWriteTokens : Option SafeNat := none
  reasoningTokens : Option SafeNat := none
  deriving DecidableEq, Repr

namespace WireUsage

/--
Named local normalization: an absent upstream optional count becomes zero in `RichStream`.
-/
def toLocal (usage : WireUsage) : RichStream.TokenUsage where
  inputTokens := usage.inputTokens.value
  outputTokens := usage.outputTokens.value
  cacheReadTokens := (usage.cacheReadTokens.map SafeNat.value).getD 0
  cacheWriteTokens := (usage.cacheWriteTokens.map SafeNat.value).getD 0
  reasoningTokens := (usage.reasoningTokens.map SafeNat.value).getD 0

end WireUsage

/-- Successful finish tags whose upstream and local meanings coincide. -/
inductive SuccessfulFinish where
  | stop
  | toolCalls
  | maxTokens
  deriving BEq, DecidableEq, Repr

namespace SuccessfulFinish

/-- Refine a supported upstream finish tag to the local terminal reason. -/
def toLocal : SuccessfulFinish → RichStream.FinishReason
  | .stop => .stop
  | .toolCalls => .toolCalls
  | .maxTokens => .maxTokens

end SuccessfulFinish

/-- Exact supported subset of the current TypeScript `StreamChunk` union. -/
inductive SupportedChunk where
  | blockStart (index : SafeNat) (kind : RichStream.BlockKind)
  | textDelta (index : SafeNat) (text : String)
  | reasoningDelta (index : SafeNat) (text : String)
  | toolCallDelta (index : SafeNat) (id : String) (name : Option String)
      (argumentsDelta : String)
  | blockEnd (index : SafeNat) (block : RichStream.ContentBlock)
  | tokenUsage (usage : WireUsage)
  | finish (reason : SuccessfulFinish)
  deriving DecidableEq, Repr

namespace SupportedChunk

/-- Forget wire-only optionality and safe-integer proofs into the rich-stream runtime chunk. -/
def toRaw : SupportedChunk → RichStream.RawChunk
  | SupportedChunk.blockStart index kind => .blockStart index.value kind
  | SupportedChunk.textDelta index text => .textDelta index.value text
  | SupportedChunk.reasoningDelta index text => .reasoningDelta index.value text
  | SupportedChunk.toolCallDelta index id name argumentsDelta =>
      .toolCallDelta index.value { id, name, argumentsDelta }
  | SupportedChunk.blockEnd index block => .blockEnd index.value block
  | SupportedChunk.tokenUsage usage => RichStream.RawChunk.usage usage.toLocal
  | SupportedChunk.finish reason => .finish reason.toLocal none

end SupportedChunk

private def jsonKind : Lean.Json → JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def field? : Lean.Json → String → Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def requireField (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError Lean.Json :=
  match field? json name with
  | some value => .ok value
  | none => .error (.missingField path name)

private def decodeString (path : List PathSegment) : Lean.Json → Except DecodeError String
  | .str value => .ok value
  | json => .error (.typeMismatch path "string" (jsonKind json))

private def decodeSafeNat (path : List PathSegment) : Lean.Json → Except DecodeError SafeNat
  | .num ⟨Int.ofNat value, 0⟩ =>
      if safe : value ≤ maxSafeInteger then
        .ok { value, safe }
      else
        .error (.unsafeInteger path value)
  | json => .error (.typeMismatch path "nonnegative safe integer" (jsonKind json))

private def decodeRequiredString (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError String := do
  decodeString (fieldPath path name) (← requireField json path name)

private def decodeRequiredNat (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError SafeNat := do
  decodeSafeNat (fieldPath path name) (← requireField json path name)

private def decodeOptionalString (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError (Option String) :=
  match field? json name with
  | none => .ok none
  | some value => return some (← decodeString (fieldPath path name) value)

private def decodeOptionalNat (json : Lean.Json) (path : List PathSegment)
    (name : String) : Except DecodeError (Option SafeNat) :=
  match field? json name with
  | none => .ok none
  | some value => return some (← decodeSafeNat (fieldPath path name) value)

private def decodeBlockKind (path : List PathSegment) (tag : String) :
    Except DecodeError RichStream.BlockKind :=
  match tag with
  | "text" => .ok .text
  | "reasoning" => .ok .reasoning
  | "tool-call" => .ok .toolCall
  | tag => .error (.unsupportedTag path tag)

private def decodeContentBlock (path : List PathSegment) : Lean.Json →
    Except DecodeError RichStream.ContentBlock
  | json@(.obj _) => do
      let tag ← decodeRequiredString json path "type"
      match tag with
      | "text" => return .text (← decodeRequiredString json path "text")
      | "reasoning" => return .reasoning (← decodeRequiredString json path "text")
      | "tool-call" =>
          return .toolCall
            (← decodeRequiredString json path "id")
            (← decodeRequiredString json path "name")
            (← decodeRequiredString json path "arguments")
      | tag => .error (.unsupportedTag (fieldPath path "type") tag)
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeWireUsage (path : List PathSegment) : Lean.Json →
    Except DecodeError WireUsage
  | json@(.obj _) => do
      .ok {
        inputTokens := ← decodeRequiredNat json path "inputTokens"
        outputTokens := ← decodeRequiredNat json path "outputTokens"
        cacheReadTokens := ← decodeOptionalNat json path "cacheReadTokens"
        cacheWriteTokens := ← decodeOptionalNat json path "cacheWriteTokens"
        reasoningTokens := ← decodeOptionalNat json path "reasoningTokens"
      }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeSuccessfulFinish (path : List PathSegment) : Lean.Json →
    Except DecodeError SuccessfulFinish
  | json@(.obj _) => do
      let tag ← decodeRequiredString json path "kind"
      match tag with
      | "stop" => .ok .stop
      | "tool-calls" => .ok .toolCalls
      | "max-tokens" => .ok .maxTokens
      | tag => .error (.unsupportedTag (fieldPath path "kind") tag)
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeChunkAt (path : List PathSegment) : Lean.Json →
    Except DecodeError SupportedChunk
  | json@(.obj _) => do
      let tag ← decodeRequiredString json path "type"
      match tag with
      | "block-start" =>
          let index ← decodeRequiredNat json path "index"
          let blockType ← decodeRequiredString json path "blockType"
          return .blockStart index
            (← decodeBlockKind (fieldPath path "blockType") blockType)
      | "text-delta" =>
          return .textDelta
            (← decodeRequiredNat json path "index")
            (← decodeRequiredString json path "text")
      | "reasoning-delta" =>
          return .reasoningDelta
            (← decodeRequiredNat json path "index")
            (← decodeRequiredString json path "text")
      | "tool-call-delta" =>
          return .toolCallDelta
            (← decodeRequiredNat json path "index")
            (← decodeRequiredString json path "id")
            (← decodeOptionalString json path "name")
            (← decodeRequiredString json path "argumentsDelta")
      | "block-end" =>
          return .blockEnd
            (← decodeRequiredNat json path "index")
            (← decodeContentBlock (fieldPath path "block")
              (← requireField json path "block"))
      | "usage" =>
          return .tokenUsage
            (← decodeWireUsage (fieldPath path "usage")
              (← requireField json path "usage"))
      | "finish" =>
          if (field? json "replayState").isSome then
            .error (.unsupportedField path "replayState")
          else
            return .finish
              (← decodeSuccessfulFinish (fieldPath path "reason")
                (← requireField json path "reason"))
      | tag => .error (.unsupportedTag (fieldPath path "type") tag)
  | json => .error (.typeMismatch path "object" (jsonKind json))

/-- Decode one current upstream JSON-AST chunk in the supported refinement subset. -/
def decodeChunk (json : Lean.Json) : Except DecodeError SupportedChunk :=
  decodeChunkAt [] json

private def decodeChunksAt : Nat → List Lean.Json →
    Except DecodeError (List SupportedChunk)
  | _, [] => .ok []
  | index, json :: rest => do
      let chunk ← decodeChunkAt [.index index] json
      let chunks ← decodeChunksAt (index + 1) rest
      .ok (chunk :: chunks)

/-- Decode a JSON-AST chunk list while retaining the failing element in every path. -/
def decodeChunks (json : List Lean.Json) : Except DecodeError (List SupportedChunk) :=
  decodeChunksAt 0 json

/-- Boundary failures distinguish JSON shape rejection from semantic stream rejection. -/
inductive ValidationError where
  | decode (error : DecodeError)
  | stream (error : RichStream.ValidationError)
  deriving BEq, DecidableEq, Repr

/-- JSON input, exact decoded chunks, and the intrinsic rich-stream witness they produce. -/
structure ValidatedJsonTrace (input : List Lean.Json) where
  chunks : List SupportedChunk
  decode_eq : decodeChunks input = .ok chunks
  validated : RichStream.ValidatedTrace RichStream.State.initial
    (chunks.map SupportedChunk.toRaw)

/-- Decode and semantically validate a finite upstream JSON-AST stream. -/
def validateJsonTrace (input : List Lean.Json) :
    Except ValidationError (ValidatedJsonTrace input) :=
  match decoded : decodeChunks input with
  | .error error => .error (.decode error)
  | .ok chunks =>
      match RichStream.validateTrace RichStream.State.initial
          (chunks.map SupportedChunk.toRaw) with
      | .error error => .error (.stream error)
      | .ok validated => .ok { chunks, decode_eq := decoded, validated }

namespace ValidatedJsonTrace

/-- Successful JSON refinement replays to the exact endpoint carried by its intrinsic witness. -/
theorem replay_eq {input : List Lean.Json} (trace : ValidatedJsonTrace input) :
    RichStream.replayRaw (RichStream.eraseState RichStream.State.initial)
        (trace.chunks.map SupportedChunk.toRaw) =
      .ok (RichStream.eraseState trace.validated.finish) :=
  trace.validated.replayRaw_eq

end ValidatedJsonTrace

/-! ## Executable refinement and fail-closed examples -/

def zero : SafeNat := { value := 0, safe := by decide }

def exampleUsage : WireUsage := {
  inputTokens := { value := 5, safe := by decide }
  outputTokens := { value := 2, safe := by decide }
}

def exampleChunks : List SupportedChunk := [
  .blockStart zero .text,
  .textDelta zero "hello",
  .blockEnd zero (.text "hello"),
  .tokenUsage exampleUsage,
  .finish .stop
]

/-- JSON-AST values with the exact current upstream field names and discriminant tags. -/
def exampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "block-start"),
    ("index", .num 0),
    ("blockType", .str "text")
  ],
  Lean.Json.mkObj [
    ("type", .str "text-delta"),
    ("index", .num 0),
    ("text", .str "hello")
  ],
  Lean.Json.mkObj [
    ("type", .str "block-end"),
    ("index", .num 0),
    ("block", Lean.Json.mkObj [("type", .str "text"), ("text", .str "hello")])
  ],
  Lean.Json.mkObj [
    ("type", .str "usage"),
    ("usage", Lean.Json.mkObj [("inputTokens", .num 5), ("outputTokens", .num 2)])
  ],
  Lean.Json.mkObj [
    ("type", .str "finish"),
    ("reason", Lean.Json.mkObj [("kind", .str "stop")])
  ]
]

/-- The current wire-shaped JSON example decodes to the exact supported chunk sequence. -/
theorem decode_example_exact : decodeChunks exampleJson = .ok exampleChunks := by
  rfl

def exampleRaw : List RichStream.RawChunk := exampleChunks.map SupportedChunk.toRaw

def exampleTrace :
    RichStream.Trace RichStream.State.initial
      (.terminal [.text "hello"] exampleUsage.toLocal .stop none) :=
  .cons (.blockStart .text) <|
  .cons (.delta 0 (.text "hello") rfl) <|
  .cons (.blockEnd 0 (.text "hello") rfl) <|
  .cons (.usage exampleUsage.toLocal) <|
  .cons (.finish .stop none rfl) .nil

def exampleValidated :
    RichStream.ValidatedTrace RichStream.State.initial exampleRaw := {
  finish := .terminal [.text "hello"] exampleUsage.toLocal .stop none
  trace := exampleTrace
  erase_eq := rfl
}

def exampleJsonValidated : ValidatedJsonTrace exampleJson := {
  chunks := exampleChunks
  decode_eq := decode_example_exact
  validated := exampleValidated
}

/-- The composed decoder and semantic validator return the exact dependent example witness. -/
theorem validate_example_exact :
    validateJsonTrace exampleJson = .ok exampleJsonValidated := by
  rfl

/-- Optional usage fields are absent upstream and become zero only at the named local boundary. -/
theorem example_optionalUsage_normalization :
    exampleUsage.toLocal = {
      inputTokens := 5
      outputTokens := 2
      cacheReadTokens := 0
      cacheWriteTokens := 0
      reasoningTokens := 0
    } :=
  rfl

/-- A present opaque replay envelope is rejected rather than silently discarded. -/
theorem reject_opaqueReplayState :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "finish"),
      ("reason", Lean.Json.mkObj [("kind", .str "stop")]),
      ("replayState", Lean.Json.mkObj [("response", .null)])
    ]) = .error (.unsupportedField [] "replayState") :=
  rfl

/-- Current upstream error payloads are rejected because their local shape is not equivalent. -/
theorem reject_unmodeledErrorFinish :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "finish"),
      ("reason", Lean.Json.mkObj [
        ("kind", .str "error"),
        ("failure", Lean.Json.mkObj [
          ("message", .str "failed"),
          ("code", .str "PROVIDER_ERROR")
        ])
      ])
    ]) = .error (.unsupportedTag [.field "reason", .field "kind"] "error") :=
  rfl

/-- Upstream aborted finishes carry the same unmodeled `LlmFailure` shape and also fail closed. -/
theorem reject_unmodeledAbortedFinish :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "finish"),
      ("reason", Lean.Json.mkObj [
        ("kind", .str "aborted"),
        ("failure", Lean.Json.mkObj [
          ("message", .str "cancelled"),
          ("code", .str "ABORTED")
        ])
      ])
    ]) = .error (.unsupportedTag [.field "reason", .field "kind"] "aborted") :=
  rfl

/-- JSON shape success cannot bypass the rich stream's contiguous-index invariant. -/
theorem reject_semantic_noncontiguousStart :
    validateJsonTrace [Lean.Json.mkObj [
      ("type", .str "block-start"),
      ("index", .num 1),
      ("blockType", .str "text")
    ]] =
      .error (.stream (.wrongStartIndex 0 1)) := by
  rfl

/-- Image output is a current upstream block tag but remains outside the local rich-stream slice. -/
theorem reject_unmodeledImageBlock :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "block-end"),
      ("index", .num 0),
      ("block", Lean.Json.mkObj [
        ("type", .str "image"),
        ("attachment", Lean.Json.mkObj [])
      ])
    ]) = .error (.unsupportedTag [.field "block", .field "type"] "image") :=
  rfl

/-- Tool-result output is also current upstream data but has no local content-block constructor. -/
theorem reject_unmodeledToolResultBlock :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "block-end"),
      ("index", .num 0),
      ("block", Lean.Json.mkObj [
        ("type", .str "tool-result"),
        ("toolCallId", .str "call-7"),
        ("content", .arr #[])
      ])
    ]) = .error (.unsupportedTag [.field "block", .field "type"] "tool-result") :=
  rfl

/-- Tool-call IDs and raw JSON argument fragments survive the JSON boundary byte-for-byte. -/
theorem decode_toolCallDelta_exact :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "tool-call-delta"),
      ("index", .num 0),
      ("id", .str "call-7"),
      ("name", .str "lookup"),
      ("argumentsDelta", .str "{\"q\":")
    ]) = .ok (.toolCallDelta zero "call-7" (some "lookup") "{\"q\":") :=
  rfl

/-- The decoder reports both the chunk index and nested field for a malformed list element. -/
theorem reject_nestedFieldType :
    decodeChunks [
      Lean.Json.mkObj [
        ("type", .str "block-start"),
        ("index", .num 0),
        ("blockType", .str "text")
      ],
      Lean.Json.mkObj [
        ("type", .str "text-delta"),
        ("index", .str "zero"),
        ("text", .str "bad")
      ]
    ] = .error (.typeMismatch [.index 1, .field "index"]
      "nonnegative safe integer" .string) :=
  rfl

/-- Integers outside JavaScript's exact range are rejected before semantic validation. -/
theorem reject_unsafeInteger :
    decodeChunk (Lean.Json.mkObj [
      ("type", .str "block-start"),
      ("index", .num 9007199254740992),
      ("blockType", .str "text")
    ]) = .error (.unsafeInteger [.field "index"] 9007199254740992) :=
  rfl

end Cordis.RuntimeRefinement
