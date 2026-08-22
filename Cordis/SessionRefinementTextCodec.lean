import Cordis.SessionRefinementCodec
import Cordis.TextRefinement

/-!
# Text boundary for the canonical current-Harness event codec

`SessionRefinement.Codec` is deliberately an AST codec.  This module composes it with the
repository's newline-delimited JSON parser without pretending that the parser is a theorem about
arbitrary external text.  Encoding emits one compact canonical JSON line; decoding accepts exactly
one parsed line and then runs the proof-producing semantic decoder.

The parser and semantic failures remain separate constructors.  The main theorem is consequently
certificate-shaped: if a text line is proved to parse to the AST emitted by the canonical encoder,
then decoding the line returns the exact dependent `WireEvent`.  A small executable fixture also
checks the complete parser/codec path, while UTF-8 framing, process I/O, and deployed logger
compatibility remain owned by the existing text and process modules.
-/

set_option autoImplicit false

namespace Cordis.SessionRefinement.Codec

open Cordis
open Cordis.SessionRefinement

inductive TextDecodeError where
  | text (error : TextRefinement.TextError)
  | empty
  | multiple (count : Nat)
  | semantic (error : DecodeError)
  deriving BEq, DecidableEq, Repr

private def decodeSemantic (json : Lean.Json) : Except TextDecodeError WireEvent :=
  (decodeEvent json).mapError TextDecodeError.semantic

/-- The canonical compact JSON text emitted for one supported event. -/
def encodeWireEventLine (event : WireEvent) : Except EncodeError String :=
  (encodeWireEvent event).map Lean.Json.compress

/-- Decode one and only one JSONL line through the existing parser and semantic decoder. -/
def decodeWireEventLine (text : String) : Except TextDecodeError WireEvent :=
  match _parsed : TextRefinement.parseJsonLines text with
  | .error error => .error (.text error)
  | .ok [] => .error .empty
  | .ok [json] => decodeSemantic json
  | .ok (_first :: _second :: rest) => .error (.multiple (rest.length + 2))

theorem encodeWireEventLine_eq_compress
    {event : WireEvent} {json : Lean.Json}
    (encoded : encodeWireEvent event = .ok json) :
    encodeWireEventLine event = .ok (Lean.Json.compress json) := by
  change (encodeWireEvent event).map Lean.Json.compress = .ok (Lean.Json.compress json)
  rw [encoded]
  rfl

theorem decodeWireEventLine_of_encoded
    {event : WireEvent} {json : Lean.Json} {text : String}
    (encoded : encodeWireEvent event = .ok json)
    (parsed : TextRefinement.parseJsonLines text = .ok [json]) :
    decodeWireEventLine text = .ok event := by
  unfold decodeWireEventLine
  generalize h : TextRefinement.parseJsonLines text = result
  cases result with
  | error error => simp_all
  | ok lines =>
      cases lines with
      | nil => simp_all
      | cons first rest =>
          cases rest with
          | nil =>
              have lines_eq :
                  (Except.ok [first] : Except TextRefinement.TextError (List Lean.Json)) =
                    .ok [json] := h.symm.trans parsed
              cases lines_eq
              simp [decodeSemantic, decode_encode encoded, Except.mapError]
          | cons second rest => simp_all

/-! ## Executable parser/codec witness -/

def executableEvent : WireEvent := {
  seq := { value := 1, safe := by decide }
  time := { value := 100, safe := by decide }
  payload := .turnStart { value := 1, safe := by decide }
}

def executableLine : String :=
  match encodeWireEventLine executableEvent with
  | .ok line => line
  | .error _ => ""

def executableLineDecodes : Bool :=
  match decodeWireEventLine executableLine with
  | .ok _ => true
  | .error _ => false

end Cordis.SessionRefinement.Codec
