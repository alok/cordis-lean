import Cordis.HarnessPersistenceRefinement
import Cordis.DurableIO

/-!
# Stateful Harness JSONL persistence adapter

`HarnessPersistenceRefinement` validates the pinned logical JSONL format at a JSON-AST boundary.
This module moves that certificate across the next executable boundary: UTF-8 bytes supplied by a
`DurableIO.Backend`. Reads retain the exact bytes, decoded text, parsed rows, header/packed-row
certificate, and session projection. Replacing a document and appending one canonical row are
separate operations, and `appendValidatedRow` refuses to append unless the existing document is
already a valid persisted session.

The backend acknowledgement remains distinct from the semantic certificate. The filesystem and
memory adapters do not prove fsync, stable media, crash atomicity, locking, torn-tail repair,
compression, authentication, or external-effect exactly-once behavior. A malformed or truncated
document is returned as a structured validation failure rather than silently repaired.
-/

set_option autoImplicit false

namespace Cordis.HarnessPersistenceIO

open Cordis.DurableIO
open Cordis.HarnessPersistenceRefinement
open Cordis.TextRefinement

abbrev Bytes := DurableIO.Bytes

inductive StoreError where
  | io (operation : String) (message : String)
  | text (error : TextError)
  | persistence (error : PersistenceError)
deriving Repr

/-- A successful byte read retains every representation used to validate it. -/
structure ReadCertificate where
  bytes : Bytes
  text : String
  input : List Lean.Json
  validated : ValidatedPersistedJson input
  decoded : String.fromUTF8? (DurableIO.toByteArray bytes) = some text
  parsed : parseJsonLines text = .ok input

namespace ReadCertificate

/-- The exact semantic protocol projection of a successfully read persisted session. -/
theorem projection_exact (certificate : ReadCertificate) :
    Session.protocolProjection certificate.validated.validated.final.session.events =
      certificate.validated.validated.sequence.protocolTrace.erase :=
  certificate.validated.projection_exact

/-- The source rows are exactly the retained header followed by storage rows. -/
theorem split_exact (certificate : ReadCertificate) :
    certificate.input = certificate.validated.headerJson :: certificate.validated.storageRows :=
  certificate.validated.split_exact

end ReadCertificate

private def validateBytes (bytes : Bytes) : Except StoreError ReadCertificate :=
  match decoded : String.fromUTF8? (DurableIO.toByteArray bytes) with
  | none => .error (.text .invalidUtf8)
  | some text =>
      match parsed : parseJsonLines text with
      | .error error => .error (.text error)
      | .ok input =>
          match _validated : validatePersistedJson input with
          | .error error => .error (.persistence error)
          | .ok result => .ok {
              bytes, text, input, validated := result, decoded, parsed
            }

/-- Read bytes and validate the complete logical Harness JSONL document. -/
def readValidated (backend : Backend) : IO (Except StoreError ReadCertificate) := do
  try
    let bytes ← backend.read
    pure (validateBytes bytes)
  catch error =>
    pure (.error (.io "read" error.toString))

/-- Render a list of JSON rows in the canonical compact UTF-8 representation. -/
def encodeRows (rows : List Lean.Json) : Bytes :=
  (renderJsonLines rows).toUTF8.toList

private def encodeRow (row : Lean.Json) : Bytes :=
  row.compress.toUTF8.toList

/-- Replace the backend contents with a canonical JSONL document. -/
def replaceRows (backend : Backend) (rows : List Lean.Json) : IO (Except StoreError Unit) := do
  try
    backend.replaceFlush (encodeRows rows)
    pure (.ok ())
  catch error =>
    pure (.error (.io "replace" error.toString))

private def hasTrailingNewline : Bytes → Bool
  | [] => false
  | bytes => bytes.getLast? == some 10

private def separatorFor (bytes : Bytes) : Bytes :=
  if bytes.isEmpty || hasTrailingNewline bytes then [] else [10]

/-- Append one compact JSON row, inserting a separator only when one is needed. -/
def appendRow (backend : Backend) (row : Lean.Json) : IO (Except StoreError Unit) := do
  try
    let current ← backend.read
    backend.appendFlush (separatorFor current ++ encodeRow row)
    pure (.ok ())
  catch error =>
    pure (.error (.io "append" error.toString))

/-- Append only after validating the existing document, then return the new certificate. -/
def appendValidatedRow (backend : Backend) (row : Lean.Json) :
    IO (Except StoreError ReadCertificate) := do
  match ← readValidated backend with
  | .error error => pure (.error error)
  | .ok _ =>
      match ← appendRow backend row with
      | .error error => pure (.error error)
      | .ok _ => readValidated backend

/-- Replace a document and immediately re-enter the proof-producing read boundary. -/
def replaceAndRead (backend : Backend) (rows : List Lean.Json) :
    IO (Except StoreError ReadCertificate) := do
  match ← replaceRows backend rows with
  | .error error => pure (.error error)
  | .ok _ => readValidated backend

/-- A deterministic memory-backed valid packed-session read. -/
def fixtureMemory : IO (Except StoreError ReadCertificate) := do
  let store ← MemoryStore.new
  replaceAndRead store.backend packedPersistenceExample

/-- A deterministic memory-backed append that grows a header into a valid packed session. -/
def fixtureAppend : IO (Except StoreError ReadCertificate) := do
  let store ← MemoryStore.new
  match ← replaceRows store.backend [headerExample] with
  | .error error => pure (.error error)
  | .ok _ => appendValidatedRow store.backend packedTextExample

/-- A filesystem-backed fixture using the same typed read certificate as the memory adapter. -/
def fixtureFile : IO (Except StoreError ReadCertificate) :=
  IO.FS.withTempFile fun _ path =>
    replaceAndRead (FileBackend.mk path).backend packedPersistenceExample

/-- Invalid UTF-8 remains a text-boundary error rather than a persistence error. -/
def fixtureInvalidUtf8 : IO (Except StoreError ReadCertificate) := do
  let store ← MemoryStore.new
  store.backend.replaceFlush [255]
  readValidated store.backend

end Cordis.HarnessPersistenceIO
