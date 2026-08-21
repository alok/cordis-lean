import Cordis.RuntimeRefinement
import Cordis.RuntimeFailureRefinement
import Cordis.RuntimeOutcomeRefinement
import Cordis.SessionRefinement
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
# Text and UTF-8 refinement boundary

The current stream, normalized-failure, outcome, and session refinements deliberately start at
`Lean.Json`. This module adds the next executable boundary used by an append-only Harness log:
newline-delimited UTF-8 text is parsed into exact JSON AST lines, and only then is the existing
proof-producing refinement run.

The parser is the Lean library's JSON parser. Its behavior is therefore an explicit host/library
boundary, not a new theorem that every external producer is valid JSON or follows DeepSeek's
schema. Successful validation still carries the exact parsed lines and the existing intrinsic
stream/session/outcome certificates. Blank interior lines, invalid JSON, invalid UTF-8, and
semantic stream/session/outcome failures remain separated and fail closed.

Rendering uses Lean's canonical compact JSON printer and is a convenience for deterministic test
fixtures. No theorem here claims byte-for-byte compatibility with a deployed Harness logger,
newline policy, transport framing, or crash persistence.
-/

set_option autoImplicit false

namespace Cordis.TextRefinement

open Cordis

/-- Failures before a JSON AST exists. Line numbers are zero-based. -/
inductive TextError where
  | emptyInput
  | blankLine (line : Nat)
  | invalidUtf8
  | invalidJson (line : Nat) (message : String)
deriving BEq, DecidableEq, Repr

private def parseLinesFrom : Nat → List String → Except TextError (List Lean.Json)
  | _, [] => .ok []
  | line, text :: rest =>
      if text.trimAscii.isEmpty then
        match rest with
        | [] => .ok []
        | _ => .error (.blankLine line)
      else
        match Lean.Json.parse text.trimAscii.toString with
        | .error message => .error (.invalidJson line message)
        | .ok value => do
            let tail ← parseLinesFrom (line + 1) rest
            .ok (value :: tail)

/-- Parse a nonempty newline-delimited JSON text source into its exact AST lines. -/
def parseJsonLines (source : String) : Except TextError (List Lean.Json) :=
  if source.trimAscii.isEmpty then
    .error .emptyInput
  else
    parseLinesFrom 0 (source.splitOn "\n")

/-- Parse UTF-8 bytes, preserving invalid encoding as a distinct boundary error. -/
def parseJsonLinesBytes (source : ByteArray) : Except TextError (List Lean.Json) :=
  match String.fromUTF8? source with
  | none => .error .invalidUtf8
  | some text => parseJsonLines text

/-- Lean's canonical compact JSONL rendering for deterministic fixtures and local adapters. -/
def renderJsonLines (values : List Lean.Json) : String :=
  String.join (List.intersperse "\n" (values.map Lean.Json.compress))

/-- The corresponding UTF-8 byte representation of the canonical fixture renderer. -/
def renderJsonLinesBytes (values : List Lean.Json) : ByteArray :=
  (renderJsonLines values).toUTF8

/-- Parsed text plus a proof that the stored AST lines came from the supplied source. -/
structure ParsedText (source : String) where
  lines : List Lean.Json
  parsed : parseJsonLines source = .ok lines

/-- Stream validation after parsing text, retaining both text parsing and intrinsic validation. -/
structure ValidatedStreamText (source : String) where
  parsed : ParsedText source
  validated : RuntimeRefinement.ValidatedJsonTrace parsed.lines

/-- In-band failure validation after parsing text, retaining the typed terminal certificate. -/
structure ValidatedFailureText (source : String) where
  parsed : ParsedText source
  validated : RuntimeFailureRefinement.ValidatedFailureTrace parsed.lines

/-- Unified successful/failure validation after parsing text. -/
structure ValidatedOutcomeText (source : String) where
  parsed : ParsedText source
  validated : RuntimeOutcomeRefinement.ValidatedOutcome parsed.lines

/-- Session validation after parsing text, retaining both text parsing and intrinsic validation. -/
structure ValidatedSessionText (source : String) where
  parsed : ParsedText source
  validated : SessionRefinement.ValidatedJsonLog parsed.lines

/-- Parse and validate a supported current-Harness stream JSONL text source. -/
def validateStreamText (source : String) :
    Except (TextError ⊕ RuntimeRefinement.ValidationError) (ValidatedStreamText source) :=
  match parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok lines =>
      match _validated : RuntimeRefinement.validateJsonTrace lines with
      | .error error => .error (.inr error)
      | .ok result => .ok {
          parsed := { lines, parsed }
          validated := result
        }

/-- Parse and validate a normalized current-Harness error/abort JSONL source. -/
def validateFailureText (source : String) :
    Except (TextError ⊕ RuntimeFailureRefinement.FailureDecodeError)
      (ValidatedFailureText source) :=
  match parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok lines =>
      match _validated : RuntimeFailureRefinement.validateFailureTrace lines with
      | .error error => .error (.inr error)
      | .ok result => .ok {
          parsed := { lines, parsed }
          validated := result
        }

/-- Parse and validate either a successful or normalized failure JSONL stream. -/
def validateOutcomeText (source : String) :
    Except (TextError ⊕ RuntimeOutcomeRefinement.ValidationError)
      (ValidatedOutcomeText source) :=
  match parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok lines =>
      match _validated : RuntimeOutcomeRefinement.validateOutcome lines with
      | .error error => .error (.inr error)
      | .ok result => .ok {
          parsed := { lines, parsed }
          validated := result
        }

/-- Parse and validate a supported current-Harness session JSONL text source. -/
def validateSessionText (source : String) :
    Except
      (TextError ⊕ (SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError))
      (ValidatedSessionText source) :=
  match parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok lines =>
      match _validated : SessionRefinement.validateJsonLog lines with
      | .error error => .error (.inr error)
      | .ok result => .ok {
          parsed := { lines, parsed }
          validated := result
        }

/-- UTF-8 stream validation returns the decoded source together with its dependent certificate. -/
def validateStreamBytes (source : ByteArray) :
    Except (TextError ⊕ RuntimeRefinement.ValidationError)
      (Σ text : String, ValidatedStreamText text) :=
  match _decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match _validated : validateStreamText text with
      | .error error => .error error
      | .ok result => .ok ⟨text, result⟩

/-- UTF-8 failure validation returns the decoded source and its terminal certificate. -/
def validateFailureBytes (source : ByteArray) :
    Except (TextError ⊕ RuntimeFailureRefinement.FailureDecodeError)
      (Σ text : String, ValidatedFailureText text) :=
  match _decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match _validated : validateFailureText text with
      | .error error => .error error
      | .ok result => .ok ⟨text, result⟩

/-- UTF-8 outcome validation returns the decoded source and either branch certificate. -/
def validateOutcomeBytes (source : ByteArray) :
    Except (TextError ⊕ RuntimeOutcomeRefinement.ValidationError)
      (Σ text : String, ValidatedOutcomeText text) :=
  match _decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match _validated : validateOutcomeText text with
      | .error error => .error error
      | .ok result => .ok ⟨text, result⟩

/-- UTF-8 session validation returns the decoded source together with its dependent certificate. -/
def validateSessionBytes (source : ByteArray) :
    Except
      (TextError ⊕ (SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError))
      (Σ text : String, ValidatedSessionText text) :=
  match _decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match _validated : validateSessionText text with
      | .error error => .error error
      | .ok result => .ok ⟨text, result⟩

namespace ValidatedStreamText

/-- The parsed text certificate exposes the exact AST-to-rich-stream replay theorem. -/
theorem replay_eq {source : String} (validated : ValidatedStreamText source) :
    RichStream.replayRaw (RichStream.eraseState RichStream.State.initial)
        (validated.validated.chunks.map RuntimeRefinement.SupportedChunk.toRaw) =
      .ok (RichStream.eraseState validated.validated.validated.finish) :=
  validated.validated.replay_eq

end ValidatedStreamText

namespace ValidatedFailureText

/-- The parsed text certificate exposes the exact text-to-failure decoding theorem. -/
theorem decoded_exact {source : String} (validated : ValidatedFailureText source) :
    RuntimeFailureRefinement.decodeFailureTrace validated.parsed.lines =
      .ok (validated.validated.chunks, validated.validated.terminal) :=
  validated.validated.decoded_exact

end ValidatedFailureText

namespace ValidatedSessionText

/-- The parsed text certificate exposes the exact session-to-protocol projection theorem. -/
theorem projection_exact {source : String} (validated : ValidatedSessionText source) :
    Session.protocolProjection validated.validated.final.session.events =
      validated.validated.sequence.protocolTrace.erase :=
  validated.validated.projection_exact

end ValidatedSessionText

/-! ## Kernel-checked boundary examples -/

theorem invalid_utf8_rejected :
    parseJsonLinesBytes (ByteArray.mk #[255]) = .error .invalidUtf8 := by
  rfl

def streamTextExample : String := renderJsonLines RuntimeRefinement.exampleJson

def failureTextExample : String :=
  renderJsonLines RuntimeFailureRefinement.exampleJson

def outcomeTextExample : String :=
  renderJsonLines RuntimeRefinement.exampleJson

def sessionTextExample : String := renderJsonLines SessionRefinement.exampleJson

end Cordis.TextRefinement
