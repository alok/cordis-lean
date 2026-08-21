import Cordis.HarnessPersistenceRefinement

/-!
# Byte-level Harness persistence refinement

`HarnessPersistenceRefinement` validates the logical JSONL AST used by the current Harness
storage writer. This module closes the preceding byte boundary without pretending to implement
the filesystem backend: UTF-8 decoding, JSONL parsing, packed-row expansion, and the existing
stateful session/protocol projection are composed into one proof-carrying result.

The result retains the original byte array and proves exactly which text and JSON rows were
decoded from it. Invalid UTF-8, empty input, malformed JSON, malformed packed rows, and semantic
session failures remain distinct errors. No theorem here claims compression compatibility,
newline-policy compatibility, crash-tail repair, path safety, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.HarnessPersistenceBytes

open Cordis
open Cordis.HarnessPersistenceRefinement

abbrev TextError := Cordis.TextRefinement.TextError

@[simp] theorem fromUTF8_toUTF8 (text : String) :
    String.fromUTF8? text.toUTF8 = some text := by
  cases text with
  | ofByteArray bytes valid =>
      simp [String.fromUTF8?, String.fromUTF8, valid]

theorem fromUTF8_empty (valid : ByteArray.empty.IsValidUTF8) :
    String.fromUTF8 ByteArray.empty valid = "" := by
  rfl

/-! ## The dependent byte certificate -/

/-- A successful byte decode with every intermediate representation retained. -/
structure ValidatedPersistedBytes (source : ByteArray) where
  text : String
  input : List Lean.Json
  decoded : String.fromUTF8? source = some text
  parsed : TextRefinement.parseJsonLines text = .ok input
  persisted : ValidatedPersistedJson input

/-- Decode UTF-8, parse JSONL, and validate the logical persisted session. -/
def validatePersistedBytes (source : ByteArray) :
    Except (TextError ⊕ PersistenceError) (ValidatedPersistedBytes source) :=
  match decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match parsed : TextRefinement.parseJsonLines text with
      | .error error => .error (.inl error)
      | .ok input =>
          match _persisted : validatePersistedJson input with
          | .error error => .error (.inr error)
          | .ok result => .ok {
              text, input, decoded, parsed, persisted := result
            }

namespace ValidatedPersistedBytes

theorem decoded_exact {source : ByteArray} (validated : ValidatedPersistedBytes source) :
    String.fromUTF8? source = some validated.text :=
  validated.decoded

theorem parsed_exact {source : ByteArray} (validated : ValidatedPersistedBytes source) :
    TextRefinement.parseJsonLines validated.text = .ok validated.input :=
  validated.parsed

theorem persisted_split_exact {source : ByteArray}
    (validated : ValidatedPersistedBytes source) :
    validated.input = validated.persisted.headerJson :: validated.persisted.storageRows :=
  validated.persisted.split_eq

theorem projection_exact {source : ByteArray} (validated : ValidatedPersistedBytes source) :
    Session.protocolProjection validated.persisted.validated.final.session.events =
      validated.persisted.validated.sequence.protocolTrace.erase :=
  validated.persisted.projection_exact

end ValidatedPersistedBytes

/-! ## Executable byte fixtures -/

def packedPersistenceBytesExample : ByteArray :=
  (TextRefinement.renderJsonLines packedPersistenceExample).toUTF8

def packedReasoningPersistenceBytesExample : ByteArray :=
  (TextRefinement.renderJsonLines packedReasoningPersistenceExample).toUTF8

def malformedPackedRowBytes : ByteArray :=
  (TextRefinement.renderJsonLines [headerExample, malformedPackedRow]).toUTF8

def persistedBytesSummary (source : ByteArray) :
    Option (Nat × Nat × Nat) :=
  match String.fromUTF8? source with
  | none => none
  | some text =>
      match TextRefinement.parseJsonLines text with
      | .error _ => none
      | .ok input =>
          match validatePersistedJson input with
          | .error _ => none
          | .ok validated => some (
              validated.header.version,
              validated.expandedEvents.length,
              validated.validated.final.session.nextSeq)

def packedPersistenceBytesRuntime : IO Bool :=
  pure (persistedBytesSummary packedPersistenceBytesExample == some (0, 3, 3))

def packedReasoningPersistenceBytesRuntime : IO Bool :=
  pure (persistedBytesSummary packedReasoningPersistenceBytesExample == some (0, 2, 2))

def malformedPackedRowBytesRuntime : IO Bool :=
  pure (persistedBytesSummary malformedPackedRowBytes == none)

theorem invalidUtf8Bytes_rejected :
    validatePersistedBytes (ByteArray.mk #[255]) =
      .error (.inl .invalidUtf8) := by
  rfl

def emptyBytesRuntime : IO Bool :=
  pure (persistedBytesSummary (ByteArray.mk #[]) == none)

end Cordis.HarnessPersistenceBytes
