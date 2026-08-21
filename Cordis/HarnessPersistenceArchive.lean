import Cordis.HarnessPersistenceRefinement
import Cordis.SessionArchive
import Cordis.TextRefinement

/-!
# Lossless archive boundary for Harness JSONL persistence

`HarnessPersistenceRefinement` validates a deliberately small semantic JSONL language: the
session header, three packed chunk-row forms, and the supported `SessionEvent` subset. This
module keeps the same logical header validation but separates storage-shape preservation from
semantic expansion. Packed rows are retained with their exact raw JSON and a typed row tag;
ordinary event envelopes delegate to `SessionArchive`, which preserves supported certificates and
required/ignorable opaque records.

The result is useful for migration, inspection, and quarantine: no row is silently discarded, and
malformed ordinary envelopes report their storage index. It does not expand packed rows into
events, assign payload semantics to opaque records, repair torn tails, or claim filesystem,
compression, crash-recovery, or whole-session equivalence.
-/

set_option autoImplicit false

namespace Cordis.HarnessPersistenceArchive

open Cordis
open Cordis.HarnessPersistenceRefinement
open Cordis.SessionArchive
open Cordis.TextRefinement

/-- The three packed row tags defined by the pinned logical persistence format. -/
inductive PackedTag where
  | textChunks
  | reasoningChunks
  | toolCallChunks
  deriving BEq, DecidableEq, Repr

namespace PackedTag

def wire : PackedTag → String
  | .textChunks => "text-chunks"
  | .reasoningChunks => "reasoning-chunks"
  | .toolCallChunks => "tool-call-chunks"

end PackedTag

/-- A storage row retained without pretending that packed data has been semantically expanded. -/
inductive ArchivedStorageRow where
  | packed (tag : PackedTag) (raw : Lean.Json)
  | envelope (event : SessionArchive.ArchivedEvent)

namespace ArchivedStorageRow

def raw : ArchivedStorageRow → Lean.Json
  | .packed _ raw => raw
  | .envelope event => event.raw

def tag : ArchivedStorageRow → String
  | .packed packedTag _ => "packed:" ++ packedTag.wire
  | .envelope (.supported _) => "supported"
  | .envelope (.opaqueRequired _) => "opaque-required"
  | .envelope (.opaqueIgnorable _) => "opaque-ignorable"

def isPacked : ArchivedStorageRow → Bool
  | .packed _ _ => true
  | .envelope _ => false

end ArchivedStorageRow

/-- Failures at the persisted-document boundary remain distinct from envelope failures. -/
inductive ArchiveError where
  | missingHeader
  | header (error : HeaderError)
  | row (index : Nat) (error : SessionArchive.ArchiveError)
  deriving BEq, DecidableEq, Repr

private def field? : Lean.Json → String → Option Lean.Json
  | .obj fields, name => fields.get? name
  | _, _ => none

private def rowTag : Lean.Json → Option String
  | json =>
      match field? json "type" with
      | some (.str tag) => some tag
      | _ => none

private def classifyPacked : String → Option PackedTag
  | "text-chunks" => some .textChunks
  | "reasoning-chunks" => some .reasoningChunks
  | "tool-call-chunks" => some .toolCallChunks
  | _ => none

private def archiveRowAt (index : Nat) (raw : Lean.Json) :
    Except ArchiveError { row : ArchivedStorageRow // row.raw = raw } :=
  match rowTag raw >>= classifyPacked with
  | some tag => .ok ⟨.packed tag raw, rfl⟩
  | none =>
      match decoded : SessionArchive.decodeEnvelopeAtPath [.index index] raw with
      | .error error => .error (.row index error)
      | .ok envelope =>
          let event := SessionArchive.classify envelope
          .ok ⟨.envelope event, by
            dsimp [event]
            exact (SessionArchive.classify_raw envelope).trans
              (SessionArchive.decodeEnvelopeAtPath_raw [.index index] raw envelope decoded)⟩

private structure ArchivedRows (input : List Lean.Json) where
  rows : List ArchivedStorageRow
  length_eq : rows.length = input.length
  raw_eq : rows.map ArchivedStorageRow.raw = input

private def archiveRowsAt : (index : Nat) → (input : List Lean.Json) →
    Except ArchiveError (ArchivedRows input)
  | _, [] => .ok { rows := [], length_eq := rfl, raw_eq := rfl }
  | index, raw :: rest =>
      match headResult : archiveRowAt index raw with
      | .error error => .error error
      | .ok head =>
          match tailResult : archiveRowsAt (index + 1) rest with
          | .error error => .error error
          | .ok tail =>
              .ok {
                rows := head.1 :: tail.rows
                length_eq := by simp [tail.length_eq]
                raw_eq := by simp [head.2, tail.raw_eq]
              }

/-- A persisted JSONL document with its typed header and every storage row retained. -/
structure ArchivedPersistedJson (input : List Lean.Json) where
  headerJson : Lean.Json
  header : SessionHeader
  storageRows : List Lean.Json
  rows : List ArchivedStorageRow
  split_eq : input = headerJson :: storageRows
  length_eq : rows.length = storageRows.length
  raw_eq : rows.map ArchivedStorageRow.raw = storageRows

/-- Decode the header and archive every storage row without semantic expansion or loss. -/
def archivePersistedJson (input : List Lean.Json) :
    Except ArchiveError (ArchivedPersistedJson input) :=
  match input with
  | [] => .error .missingHeader
  | headerJson :: storageRows =>
      match _headerResult : decodeSessionHeader headerJson with
      | .error error => .error (.header error)
      | .ok header =>
          match _rowsResult : archiveRowsAt 1 storageRows with
          | .error error => .error error
          | .ok rows =>
              .ok {
                headerJson, header, storageRows, rows := rows.rows
                split_eq := rfl
                length_eq := rows.length_eq
                raw_eq := rows.raw_eq
              }

namespace ArchivedPersistedJson

theorem split_exact {input : List Lean.Json} (archived : ArchivedPersistedJson input) :
    input = archived.headerJson :: archived.storageRows :=
  archived.split_eq

theorem rows_length_exact {input : List Lean.Json} (archived : ArchivedPersistedJson input) :
    archived.rows.length = archived.storageRows.length :=
  archived.length_eq

theorem rows_raw_exact {input : List Lean.Json} (archived : ArchivedPersistedJson input) :
    archived.rows.map ArchivedStorageRow.raw = archived.storageRows :=
  archived.raw_eq

def rowTags {input : List Lean.Json} (archived : ArchivedPersistedJson input) : List String :=
  archived.rows.map ArchivedStorageRow.tag

end ArchivedPersistedJson

/-- Parse JSONL text, then retain its typed header and every storage row. -/
def archivePersistedText (source : String) :
    Except (TextError ⊕ ArchiveError)
      (Σ input : List Lean.Json, ArchivedPersistedJson input) :=
  match _parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok input =>
      match _archived : archivePersistedJson input with
      | .error error => .error (.inr error)
      | .ok result => .ok ⟨input, result⟩

/-- Parse UTF-8 bytes and retain the decoded text, JSON lines, and archive certificate. -/
def archivePersistedBytes (source : ByteArray) :
    Except (TextError ⊕ ArchiveError)
      (String × Σ input : List Lean.Json, ArchivedPersistedJson input) :=
  match _decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match _archived : archivePersistedText text with
      | .error error => .error error
      | .ok ⟨input, result⟩ => .ok ⟨text, input, result⟩

/-! ## Executable fixtures and exact raw-retention witnesses -/

def archivePersistenceExample : List Lean.Json :=
  [HarnessPersistenceRefinement.headerExample,
    HarnessPersistenceRefinement.packedTextExample,
    SessionArchive.requiredExtensionJson,
    SessionArchive.ignorableExtensionJson]

def archivePersistenceTextExample : String :=
  TextRefinement.renderJsonLines archivePersistenceExample

theorem archive_persistence_example_tags :
    (match archivePersistedJson archivePersistenceExample with
    | .error _ => []
    | .ok archived => archived.rows.map ArchivedStorageRow.tag) =
      ["packed:text-chunks", "opaque-required", "opaque-ignorable"] := by
  rfl

theorem archive_persistence_example_rows_preserved :
    (match archivePersistedJson archivePersistenceExample with
    | .error _ => []
    | .ok archived => archived.rows.map ArchivedStorageRow.raw) =
      [HarnessPersistenceRefinement.packedTextExample,
        SessionArchive.requiredExtensionJson, SessionArchive.ignorableExtensionJson] := by
  rfl

theorem archive_persistence_example_header :
    (match archivePersistedJson archivePersistenceExample with
    | .error _ => none
    | .ok archived => some (archived.header.version, archived.header.id)) =
      some (0, "session-example") := by
  rfl

def malformedPersistedEnvelope : Lean.Json := Lean.Json.mkObj [
  ("type", .str "vendor/malformed"), ("seq", .num 5),
  ("data", Lean.Json.mkObj [])]

def archiveErrorSummary {α : Type} : Except ArchiveError α → Option (Nat × String)
  | .error (.row index (.missingField _ name)) => some (index, name)
  | .error _ => none
  | .ok _ => none

theorem malformed_persisted_envelope_indexed :
    archiveErrorSummary
        (archivePersistedJson
          [HarnessPersistenceRefinement.headerExample,
            HarnessPersistenceRefinement.packedTextExample,
            malformedPersistedEnvelope]) =
      some (2, "time") := by
  decide

end Cordis.HarnessPersistenceArchive
