import Cordis.RuntimeRefinement
import Lean.Data.Json.Basic

/-!
# In-band Harness failure-finish refinement

The current Harness `StreamChunk` vocabulary has two in-band terminal branches that are
deliberately different from a successful rich-stream finish:

* `{ kind: "error", failure: LlmFailure }`;
* `{ kind: "aborted", failure: LlmFailure }`.

`RuntimeRefinement` accepts the successful `stop`, `tool-calls`, and `max-tokens` branches and
then proves the stronger local block/usage/finish invariant.  The upstream assembler may instead
terminate an error or abort while a block is still open.  This module therefore does not pretend
that such an input is a `RichStream.ValidatedTrace`.  It supplies a separate, exact certificate:
the ordinary prefix is decoded with the existing supported-chunk decoder, the final chunk is a
typed `LlmFailure`, and any chunk after the failure is rejected.

The certificate preserves every current `LlmFailure` field (`message`, `code`, optional status,
provider retry delay, and optional request id).  It is a JSON-AST refinement only: it makes no
claim about provider authenticity, retry safety, cancellation policy, open-block reconstruction,
transport bytes, or behavioral equivalence with the TypeScript assembler.
-/

set_option autoImplicit false

namespace Cordis.RuntimeFailureRefinement

open Cordis
open Cordis.RuntimeRefinement

abbrev SafeNat := RuntimeRefinement.SafeNat
abbrev JsonKind := RuntimeRefinement.JsonKind
abbrev PathSegment := RuntimeRefinement.PathSegment
abbrev DecodeError := RuntimeRefinement.DecodeError
abbrev SupportedChunk := RuntimeRefinement.SupportedChunk
abbrev SuccessfulFinish := RuntimeRefinement.SuccessfulFinish

/-- The two normalized in-band failure finish discriminants. -/
inductive FailureKind where
  | error
  | aborted
  deriving BEq, DecidableEq, Repr

/-- Exact current-Harness provider failure data carried by an in-band finish. -/
structure LlmFailure where
  message : String
  code : String
  status : Option SafeNat
  providerRetryAfterMs : Option SafeNat
  requestId : Option String
  deriving BEq, DecidableEq, Repr

/-- A typed failure finish, before any local policy chooses what it means. -/
structure FailureTerminal where
  kind : FailureKind
  failure : LlmFailure
  deriving BEq, DecidableEq, Repr

/-- Decoder failures specific to the terminal-failure trace shape. -/
inductive FailureDecodeError where
  | ordinary (index : Nat) (error : DecodeError)
  | terminal (index : Nat) (error : DecodeError)
  | missingFinish
  | failureBeforeEnd (index : Nat)
  | successfulFinish (index : Nat) (reason : SuccessfulFinish)
  deriving BEq, DecidableEq, Repr

namespace FailureKind

/-- Stable source spelling used by the normalized JSON `reason.kind` field. -/
def toWire : FailureKind → String
  | .error => "error"
  | .aborted => "aborted"

end FailureKind

private def fieldPath (path : List PathSegment) (name : String) : List PathSegment :=
  path ++ [.field name]

private def jsonKind : Lean.Json → JsonKind
  | .null => .null
  | .bool _ => .boolean
  | .num _ => .number
  | .str _ => .string
  | .arr _ => .array
  | .obj _ => .object

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

private def decodeLlmFailure (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError LlmFailure :=
  match json with
  | .obj _ => do
      .ok {
        message := ← decodeRequiredString json path "message"
        code := ← decodeRequiredString json path "code"
        status := ← decodeOptionalNat json path "status"
        providerRetryAfterMs := ← decodeOptionalNat json path "providerRetryAfterMs"
        requestId := ← decodeOptionalString json path "requestId"
      }
  | json => .error (.typeMismatch path "object" (jsonKind json))

private def decodeFailureTerminal (path : List PathSegment) (json : Lean.Json) :
    Except DecodeError FailureTerminal :=
  match json with
  | .obj _ => do
      let kind ← decodeRequiredString json path "kind"
      let failureJson ← requireField json path "failure"
      let failure ← decodeLlmFailure (fieldPath path "failure") failureJson
      match kind with
      | "error" => .ok { kind := .error, failure }
      | "aborted" => .ok { kind := .aborted, failure }
      | tag => .error (.unsupportedTag (fieldPath path "kind") tag)
  | json => .error (.typeMismatch path "object" (jsonKind json))

private inductive DecodedFailureChunk where
  | ordinary (chunk : SupportedChunk)
  | terminal (failure : FailureTerminal)

private def decodeFailureChunkAt (index : Nat) (json : Lean.Json) :
    Except FailureDecodeError DecodedFailureChunk :=
  match json with
  | .obj _ =>
      match field? json "type" with
      | some typeJson =>
          match decodeString [.index index, .field "type"] typeJson with
          | .error error => .error (.ordinary index error)
          | .ok "finish" =>
              if (field? json "replayState").isSome then
                .error (.terminal index (.unsupportedField [.index index] "replayState"))
              else
                match field? json "reason" with
                | none => .error (.terminal index (.missingField [.index index] "reason"))
                | some reasonJson =>
                    match reasonJson with
                    | .obj _ =>
                        match field? reasonJson "kind" with
                        | some kindJson =>
                            match decodeString
                                [.index index, .field "reason", .field "kind"] kindJson with
                            | .error error => .error (.terminal index error)
                            | .ok "error" | .ok "aborted" =>
                                match decodeFailureTerminal
                                    [.index index, .field "reason"] reasonJson with
                                | .error error => .error (.terminal index error)
                                | .ok failure => .ok (.terminal failure)
                            | .ok _ =>
                                match RuntimeRefinement.decodeChunk json with
                                | .error error => .error (.ordinary index error)
                                | .ok chunk => .ok (.ordinary chunk)
                        | none => .error (.terminal index
                            (.missingField [.index index, .field "reason"] "kind"))
                    | _ => .error (.terminal index (.typeMismatch
                        [.index index, .field "reason"] "object" (jsonKind reasonJson)))
          | .ok _ =>
              match RuntimeRefinement.decodeChunk json with
              | .error error => .error (.ordinary index error)
              | .ok chunk => .ok (.ordinary chunk)
      | none =>
          match RuntimeRefinement.decodeChunk json with
          | .error error => .error (.ordinary index error)
          | .ok chunk => .ok (.ordinary chunk)
  | _ =>
      match RuntimeRefinement.decodeChunk json with
      | .error error => .error (.ordinary index error)
      | .ok chunk => .ok (.ordinary chunk)

private def decodeFailureTraceAt : Nat → List Lean.Json →
    Except FailureDecodeError (List SupportedChunk × FailureTerminal)
  | _, [] => .error .missingFinish
  | index, json :: rest =>
      match decodeFailureChunkAt index json with
      | .error error => .error error
      | .ok (.terminal failure) =>
          match rest with
          | [] => .ok ([], failure)
          | _ => .error (.failureBeforeEnd index)
      | .ok (.ordinary (.finish reason)) =>
          .error (.successfulFinish index reason)
      | .ok (.ordinary chunk) =>
          match decodeFailureTraceAt (index + 1) rest with
          | .error error => .error error
          | .ok (chunks, failure) => .ok (chunk :: chunks, failure)

private def decodeFailureTraceResult (input : List Lean.Json) :
    Except FailureDecodeError (List SupportedChunk × FailureTerminal) :=
  decodeFailureTraceAt 0 input

/-- Decode a finite list whose final chunk is exactly one in-band failure finish. -/
def decodeFailureTrace (input : List Lean.Json) :
    Except FailureDecodeError (List SupportedChunk × FailureTerminal) :=
  decodeFailureTraceResult input

/-- A source-shaped failure trace with its complete decoded prefix and terminal payload. -/
structure ValidatedFailureTrace (input : List Lean.Json) where
  chunks : List SupportedChunk
  terminal : FailureTerminal
  decoded : decodeFailureTrace input = .ok (chunks, terminal)

/-- Decode and retain the exact normalized failure terminal without claiming rich-trace success. -/
def validateFailureTrace (input : List Lean.Json) :
    Except FailureDecodeError (ValidatedFailureTrace input) :=
  match decoded : decodeFailureTrace input with
  | .error error => .error error
  | .ok (chunks, terminal) => .ok { chunks, terminal, decoded }

namespace ValidatedFailureTrace

theorem decoded_exact {input : List Lean.Json} (trace : ValidatedFailureTrace input) :
    decodeFailureTrace input = .ok (trace.chunks, trace.terminal) :=
  trace.decoded

end ValidatedFailureTrace

/-! ## Exact examples and negative boundaries -/

def zero : SafeNat := { value := 0, safe := by decide }

def exampleChunks : List SupportedChunk := [
  .blockStart zero .text,
  .textDelta zero "partial"
]

def exampleFailure : LlmFailure := {
  message := "rate limited"
  code := "RATE_LIMIT"
  status := some { value := 429, safe := by decide }
  providerRetryAfterMs := some { value := 250, safe := by decide }
  requestId := some "req-42"
}

def exampleTerminal : FailureTerminal := {
  kind := .error
  failure := exampleFailure
}

def exampleJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "block-start"),
    ("index", .num 0),
    ("blockType", .str "text")
  ],
  Lean.Json.mkObj [
    ("type", .str "text-delta"),
    ("index", .num 0),
    ("text", .str "partial")
  ],
  Lean.Json.mkObj [
    ("type", .str "finish"),
    ("reason", Lean.Json.mkObj [
      ("kind", .str "error"),
      ("failure", Lean.Json.mkObj [
        ("message", .str "rate limited"),
        ("code", .str "RATE_LIMIT"),
        ("status", .num 429),
        ("providerRetryAfterMs", .num 250),
        ("requestId", .str "req-42")
      ])
    ])
  ]
]

theorem decode_example_exact :
    decodeFailureTrace exampleJson = .ok (exampleChunks, exampleTerminal) := by
  rfl

def exampleValidated : ValidatedFailureTrace exampleJson := {
  chunks := exampleChunks
  terminal := exampleTerminal
  decoded := decode_example_exact
}

theorem validate_example_exact :
    validateFailureTrace exampleJson = .ok exampleValidated := by
  rfl

def abortedFailure : LlmFailure := {
  message := "caller cancelled"
  code := "ABORTED"
  status := none
  providerRetryAfterMs := none
  requestId := some "req-abort"
}

def abortedJson : List Lean.Json := [
  Lean.Json.mkObj [
    ("type", .str "finish"),
    ("reason", Lean.Json.mkObj [
      ("kind", .str "aborted"),
      ("failure", Lean.Json.mkObj [
        ("message", .str "caller cancelled"),
        ("code", .str "ABORTED"),
        ("requestId", .str "req-abort")
      ])
    ])
  ]
]

theorem decode_aborted_exact :
    decodeFailureTrace abortedJson = .ok ([], {
      kind := .aborted
      failure := abortedFailure
    }) := by
  rfl

theorem reject_successfulFinish :
    decodeFailureTrace [Lean.Json.mkObj [
      ("type", .str "finish"),
      ("reason", Lean.Json.mkObj [("kind", .str "stop")])
    ]] = .error (.successfulFinish 0 .stop) := by
  rfl

theorem reject_failureBeforeEnd :
    decodeFailureTrace [
      Lean.Json.mkObj [
        ("type", .str "finish"),
        ("reason", Lean.Json.mkObj [
          ("kind", .str "error"),
          ("failure", Lean.Json.mkObj [
            ("message", .str "bad"),
            ("code", .str "E")
          ])
        ])
      ],
      Lean.Json.mkObj [
        ("type", .str "block-start"),
        ("index", .num 0),
        ("blockType", .str "text")
      ]
    ] = .error (.failureBeforeEnd 0) := by
  rfl

theorem reject_malformedFailure :
    decodeFailureTrace [Lean.Json.mkObj [
      ("type", .str "finish"),
      ("reason", Lean.Json.mkObj [
        ("kind", .str "error"),
        ("failure", Lean.Json.mkObj [
          ("message", .str "bad"),
          ("code", .str "E"),
          ("status", .str "not-a-number")
        ])
      ])
    ]] = .error (.terminal 0 (.typeMismatch
      [.index 0, .field "reason", .field "failure", .field "status"]
      "nonnegative safe integer" .string)) := by
  rfl

theorem reject_opaqueReplayState :
    decodeFailureTrace [Lean.Json.mkObj [
      ("type", .str "finish"),
      ("replayState", Lean.Json.mkObj [("response", .null)]),
      ("reason", Lean.Json.mkObj [
        ("kind", .str "aborted"),
        ("failure", Lean.Json.mkObj [
          ("message", .str "cancelled"),
          ("code", .str "ABORTED")
        ])
      ])
    ]] = .error (.terminal 0 (.unsupportedField [.index 0] "replayState")) := by
  rfl

end Cordis.RuntimeFailureRefinement
