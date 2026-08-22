import Cordis.DeepSeekHarnessExtensionRequest
import Cordis.HarnessPersistenceRefinement
import Cordis.TextRefinement
import Cordis.DurableIO

/-!
# Proof-carrying persistence for schema-indexed extension sessions

`HarnessPersistenceRefinement` validates the deployed current-Harness header and packed rows,
while `SessionExtensionArchive` validates a caller-owned dependent extension list.  This module
composes the two at the JSONL boundary: one session header is followed by required extension rows,
and a successful certificate retains the exact header, raw rows, lossless archive, and indexed
session endpoint.

The format is deliberately extension-only after the header.  Known current-Harness event tags,
ignorable rows, packed rows, mixed core/extension replay, provider compatibility, crash repair,
and deployed persistence equivalence remain explicit nonclaims.  Text, UTF-8 bytes, and the
`DurableIO.Backend` read/replace/append seams preserve the same dependent certificate rather than
silently erasing the schema or treating a backend acknowledgement as a semantic proof.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessExtensionPersistence

open Cordis
open Cordis.DurableIO
open Cordis.HarnessPersistenceRefinement
open Cordis.DeepSeekHarnessExtensionArchive
open Cordis.SessionExtensionArchive
open Cordis.SessionExtensionRefinement
open Cordis.TextRefinement

abbrev Bytes := DurableIO.Bytes

/-! ## JSON-AST persistence certificate -/

inductive PersistenceError where
  | emptyDocument
  | header (error : HeaderError)
  | extension (error : ArchiveExtensionError)
  deriving BEq, DecidableEq, Repr

/-- A header plus an exact extension-only storage suffix. -/
structure ValidatedJson
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (input : List Lean.Json) where
  headerJson : Lean.Json
  header : SessionHeader
  storageRows : List Lean.Json
  extension : ValidatedExtensionArchive codec initial storageRows
  split_eq : input = headerJson :: storageRows

namespace ValidatedJson

theorem split_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (validated : ValidatedJson codec initial input) :
    input = validated.headerJson :: validated.storageRows :=
  validated.split_eq

theorem raw_rows_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (validated : ValidatedJson codec initial input) :
    validated.extension.archive.events.map SessionEventArchive.ArchivedEvent.raw =
      validated.storageRows :=
  validated.extension.raw_exact

theorem final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (validated : ValidatedJson codec initial input) :
    validated.extension.validated.final.nextSeq =
      initial.nextSeq + validated.storageRows.length :=
  validated.extension.final_nextSeq

theorem row_count
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (validated : ValidatedJson codec initial input) :
    validated.storageRows.length + 1 = input.length := by
  have length_eq := congrArg List.length validated.split_eq
  simp at length_eq
  omega

end ValidatedJson

/-- Validate one header followed by a required, dependent extension suffix. -/
def validate
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (input : List Lean.Json) :
    Except PersistenceError (ValidatedJson codec initial input) :=
  match input with
  | [] => .error .emptyDocument
  | headerJson :: storageRows =>
      match _headerResult : decodeSessionHeader headerJson with
      | .error error => .error (.header error)
      | .ok header =>
          match _extensionResult : SessionExtensionArchive.validate codec initial storageRows with
          | .error error => .error (.extension error)
          | .ok extension =>
              .ok {
                headerJson,
                header,
                storageRows,
                extension,
                split_eq := rfl
              }

/-! ## Text and byte boundaries -/

structure ValidatedText
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (source : String) where
  parsed : ParsedText source
  persisted : ValidatedJson codec initial parsed.lines

def validateText
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (source : String) :
    Except (TextError ⊕ PersistenceError) (ValidatedText codec initial source) :=
  match parsed : parseJsonLines source with
  | .error error => .error (.inl error)
  | .ok input =>
      match _persistedResult : validate codec initial input with
      | .error error => .error (.inr error)
      | .ok persisted =>
          .ok { parsed := { lines := input, parsed }, persisted := persisted }

namespace ValidatedText

theorem parsed_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {source : String}
    (validated : ValidatedText codec initial source) :
    parseJsonLines source = .ok validated.parsed.lines :=
  validated.parsed.parsed

theorem persisted_split_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {source : String}
    (validated : ValidatedText codec initial source) :
    validated.parsed.lines = validated.persisted.headerJson ::
      validated.persisted.storageRows :=
  validated.persisted.split_exact

end ValidatedText

structure ValidatedBytes
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (source : ByteArray) where
  text : String
  input : List Lean.Json
  decoded : String.fromUTF8? source = some text
  parsed : parseJsonLines text = .ok input
  persisted : ValidatedJson codec initial input

def validateBytes
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (source : ByteArray) :
    Except (TextError ⊕ PersistenceError) (ValidatedBytes codec initial source) :=
  match decoded : String.fromUTF8? source with
  | none => .error (.inl .invalidUtf8)
  | some text =>
      match parsed : parseJsonLines text with
      | .error error => .error (.inl error)
      | .ok input =>
          match _persistedResult : validate codec initial input with
          | .error error => .error (.inr error)
          | .ok persisted =>
              .ok { text, input, decoded, parsed, persisted }

namespace ValidatedBytes

theorem decoded_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {source : ByteArray}
    (validated : ValidatedBytes codec initial source) :
    String.fromUTF8? source = some validated.text :=
  validated.decoded

theorem parsed_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {source : ByteArray}
    (validated : ValidatedBytes codec initial source) :
    parseJsonLines validated.text = .ok validated.input :=
  validated.parsed

theorem persisted_split_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {source : ByteArray}
    (validated : ValidatedBytes codec initial source) :
    validated.input = validated.persisted.headerJson :: validated.persisted.storageRows :=
  validated.persisted.split_exact

end ValidatedBytes

/-! ## DurableIO read/replace/append -/

inductive StoreError where
  | io (operation : String) (message : String)
  | text (error : TextError)
  | persistence (error : PersistenceError)
  deriving Repr

structure ReadCertificate
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema) where
  bytes : Bytes
  text : String
  input : List Lean.Json
  validated : ValidatedJson codec initial input
  decoded : String.fromUTF8? (DurableIO.toByteArray bytes) = some text
  parsed : parseJsonLines text = .ok input

namespace ReadCertificate

theorem split_exact
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    (certificate : ReadCertificate codec initial) :
    certificate.input = certificate.validated.headerJson ::
      certificate.validated.storageRows :=
  certificate.validated.split_exact

theorem final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    (certificate : ReadCertificate codec initial) :
    certificate.validated.extension.validated.final.nextSeq =
      initial.nextSeq + certificate.validated.storageRows.length :=
  certificate.validated.final_nextSeq

end ReadCertificate

/-! ## Runner attachment -/

structure RestoredRunner
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    {input : List Lean.Json} where
  persisted : ValidatedJson codec initial input
  restored : DeepSeekHarnessExtensionArchive.RestoredRunner
    (codec := codec) (initial := initial) (input := persisted.storageRows)
  archive_eq : restored.archive = persisted.extension

def restoreRunner
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    {input : List Lean.Json}
    (persisted : ValidatedJson codec initial input)
    (turn : Nat) :
    RestoredRunner codec initial (input := input) :=
  {
    persisted,
    restored := DeepSeekHarnessExtensionArchive.restoreRunner persisted.extension turn,
    archive_eq := rfl
  }

theorem RestoredRunner.session_eq_persisted
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner codec initial (input := input)) :
    restored.restored.runner.session = restored.persisted.extension.validated.final := by
  calc
    restored.restored.runner.session = restored.restored.archive.validated.final :=
      restored.restored.session_eq
    _ = restored.persisted.extension.validated.final := by rw [restored.archive_eq]

def buildRequestCertificate
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner codec initial (input := input))
    (source : DeepSeekHarness.RequestSource) :
    Except (DeepSeekToolSchema.ToolSchemaError ⊕ DeepSeekHarness.RequestError)
      (DeepSeekHarnessExtensionRequest.CertifiedRequest restored.restored source) :=
  DeepSeekHarnessExtensionRequest.buildCertifiedRequest restored.restored source

private def validateReadBytes
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (bytes : Bytes) :
    Except StoreError (ReadCertificate codec initial) :=
  match decoded : String.fromUTF8? (DurableIO.toByteArray bytes) with
  | none => .error (.text .invalidUtf8)
  | some text =>
      match parsed : parseJsonLines text with
      | .error error => .error (.text error)
      | .ok input =>
          match _persistedResult : validate codec initial input with
          | .error error => .error (.persistence error)
          | .ok validated => .ok { bytes, text, input, validated, decoded, parsed }

def readValidated
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (backend : Backend) :
    IO (Except StoreError (ReadCertificate codec initial)) := do
  try
    let bytes ← backend.read
    pure (validateReadBytes codec initial bytes)
  catch error =>
    pure (.error (.io "read" error.toString))

def encodeRows (rows : List Lean.Json) : Bytes :=
  (renderJsonLines rows).toUTF8.toList

def replaceRows (backend : Backend) (rows : List Lean.Json) : IO (Except StoreError Unit) := do
  try
    backend.replaceFlush (encodeRows rows)
    pure (.ok ())
  catch error =>
    pure (.error (.io "replace" error.toString))

private def encodeRow (row : Lean.Json) : Bytes := row.compress.toUTF8.toList

private def hasTrailingNewline : Bytes → Bool
  | [] => false
  | bytes => bytes.getLast? == some 10

private def separatorFor : Bytes → Bytes
  | bytes => if bytes.isEmpty || hasTrailingNewline bytes then [] else [10]

def appendRow (backend : Backend) (row : Lean.Json) : IO (Except StoreError Unit) := do
  try
    let current ← backend.read
    backend.appendFlush (separatorFor current ++ encodeRow row)
    pure (.ok ())
  catch error =>
    pure (.error (.io "append" error.toString))

def appendValidatedRow
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (backend : Backend)
    (row : Lean.Json) :
    IO (Except StoreError (ReadCertificate codec initial)) := do
  match ← readValidated codec initial backend with
  | .error error => pure (.error error)
  | .ok _ =>
      match ← appendRow backend row with
      | .error error => pure (.error error)
      | .ok _ => readValidated codec initial backend

def replaceAndRead
    {schema : Session.ExtensionSchema}
    (codec : ExtensionCodec schema)
    (initial : Session.Session schema)
    (backend : Backend)
    (rows : List Lean.Json) :
    IO (Except StoreError (ReadCertificate codec initial)) := do
  match ← replaceRows backend rows with
  | .error error => pure (.error error)
  | .ok _ => readValidated codec initial backend

/-! ## Executable fixtures -/

namespace Example

open SessionExtensionArchive.Example
open SessionExtensionRefinement.Example
open DeepSeekHarnessExtensions

def persistenceInput : List Lean.Json :=
  HarnessPersistenceRefinement.headerExample :: exampleInput

def validatedExample :
    Except PersistenceError
      (ValidatedJson exampleCodec (Session.Session.empty exampleSchema) persistenceInput) :=
  validate exampleCodec (Session.Session.empty exampleSchema) persistenceInput

theorem validated_example_summary :
    (match validatedExample with
    | .error _ => none
    | .ok validated =>
        some (validated.header.version, validated.storageRows.length,
          validated.extension.validated.final.nextSeq,
          validated.extension.validated.final.messages)) =
      some (0, 2, 2, [Session.Message.user "extension:ready"]) := by
  rfl

theorem validated_example_rows_exact :
    (match validatedExample with
    | .error _ => []
    | .ok validated => validated.extension.archive.events.map
        SessionEventArchive.ArchivedEvent.raw) = exampleInput := by
  rfl

def textExample : String := renderJsonLines persistenceInput

def textExampleSummary : Option (Nat × Nat) :=
  match validateText exampleCodec (Session.Session.empty exampleSchema) textExample with
  | .error _ => none
  | .ok validated =>
      some (validated.persisted.header.version,
        validated.persisted.extension.validated.final.nextSeq)

def bytesExample : ByteArray := textExample.toUTF8

def bytesExampleSummary : Option Nat :=
  match validateBytes exampleCodec (Session.Session.empty exampleSchema) bytesExample with
  | .error _ => none
  | .ok validated => some validated.persisted.extension.validated.final.nextSeq

theorem reject_empty :
    validate exampleCodec (Session.Session.empty exampleSchema) [] =
      .error .emptyDocument := by
  rfl

theorem reject_known_core :
    validate exampleCodec (Session.Session.empty exampleSchema)
      [HarnessPersistenceRefinement.headerExample,
        knownCoreJson] =
      .error (.extension (.notExtension 0 (some .turnStart))) := by
  rfl

theorem reject_ignorable :
    validate exampleCodec (Session.Session.empty exampleSchema)
      [HarnessPersistenceRefinement.headerExample,
        ignorableExtensionJson] =
      .error (.extension (.ignorable 0)) := by
  rfl

theorem reject_bad_header :
    (match validate exampleCodec (Session.Session.empty exampleSchema)
      [HarnessPersistenceRefinement.foreignVersionHeader] with
    | .error (.header (.foreignVersion 1)) => true
    | .error _ | .ok _ => false) = true := by
  decide

def fixtureMemory : IO
    (Except StoreError
      (ReadCertificate exampleCodec (Session.Session.empty exampleSchema))) := do
  let store ← MemoryStore.new
  replaceAndRead exampleCodec (Session.Session.empty exampleSchema) store.backend
    persistenceInput

def fixtureAppend : IO
    (Except StoreError
      (ReadCertificate exampleCodec (Session.Session.empty exampleSchema))) := do
  let store ← MemoryStore.new
  let backend := MemoryStore.backend store
  let replaced ← replaceRows backend [HarnessPersistenceRefinement.headerExample]
  match replaced with
  | .error error =>
      pure (Except.error error : Except StoreError
        (ReadCertificate exampleCodec (Session.Session.empty exampleSchema)))
  | .ok _ =>
      appendValidatedRow exampleCodec (Session.Session.empty exampleSchema)
        backend heartbeatJson

def fixtureFile : IO
    (Except StoreError
      (ReadCertificate exampleCodec (Session.Session.empty exampleSchema))) :=
  IO.FS.withTempFile fun _ path =>
    replaceAndRead exampleCodec (Session.Session.empty exampleSchema)
      (FileBackend.mk path).backend persistenceInput

def fixtureInvalidUtf8 : IO
    (Except StoreError
      (ReadCertificate exampleCodec (Session.Session.empty exampleSchema))) := do
  let store ← MemoryStore.new
  let backend := MemoryStore.backend store
  backend.replaceFlush [255]
  readValidated exampleCodec (Session.Session.empty exampleSchema) backend

end Example

end Cordis.DeepSeekHarnessExtensionPersistence
