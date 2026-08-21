import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.HarnessPersistenceBytes
import Cordis.SessionPayloadArchive

/-!
# Payload-preserving persisted DeepSeek Harness runner

`DeepSeekHarnessPersistenceIO` restores a `ConversationRunner` from a validated UTF-8/JSONL
archive, while `SessionPayloadArchive` retains the raw payload objects behind the current Harness
event union. This module composes the two certificates at the *expanded-event* index. A successful
result therefore carries the header/storage proof, the semantic session endpoint, and a lossless
payload ledger whose raw event list is definitionally the same list consumed by
`SessionRefinement`.

The byte and backend adapters are deliberately thin: they reuse the existing UTF-8 parser,
logical persistence validator, and `DurableIO.Backend` certificates. Payload-shape errors remain
distinct from storage and text errors. This does not claim provider-schema semantics, opaque-event
replay, fsync, crash atomicity, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPayloadPersistence

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.HarnessPersistenceBytes
open Cordis.HarnessPersistenceIO
open Cordis.HarnessPersistenceRefinement
open Cordis.SessionEventArchive
open Cordis.SessionPayloadArchive

/-! ## Logical persisted attachment -/

/-- A persisted archive with one semantic runner and one lossless payload ledger. -/
structure RestoredRunner (input : List Lean.Json) where
  archive : ValidatedPersistedJson input
  runner : ConversationRunner
  payload : PayloadLog archive.expandedEvents
  session_eq : runner.session = archive.validated.final.session

namespace RestoredRunner

theorem session_eq_archive {input : List Lean.Json} (restored : RestoredRunner input) :
    restored.runner.session = restored.archive.validated.final.session :=
  restored.session_eq

theorem payload_raw_eq_expanded {input : List Lean.Json} (restored : RestoredRunner input) :
    restored.payload.events.map EnrichedEvent.raw = restored.archive.expandedEvents :=
  restored.payload.raw_exact

theorem payload_length_eq {input : List Lean.Json} (restored : RestoredRunner input) :
    restored.payload.events.length = restored.archive.expandedEvents.length := by
  rw [restored.payload.length_exact]

theorem projection_exact {input : List Lean.Json} (restored : RestoredRunner input) :
    Session.protocolProjection restored.runner.session.events =
      restored.archive.validated.sequence.protocolTrace.erase := by
  rw [restored.session_eq]
  exact restored.archive.projection_exact

end RestoredRunner

inductive PayloadError where
  | archive (error : SessionEventArchive.ArchiveError)
deriving BEq, DecidableEq, Repr

/-- Restore a logical archive and enrich exactly the expanded event list it validated. -/
def restoreRunner
    {input : List Lean.Json}
    (archive : ValidatedPersistedJson input)
    (turn step nextCall : Nat)
    (toolCallCount_eq : toolCallCount archive.validated.final.session.messages = nextCall) :
    Except PayloadError (RestoredRunner input) :=
  match archivePayload archive.expandedEvents with
  | .error error => .error (.archive error)
  | .ok payload =>
      .ok {
        archive
        runner := {
          session := archive.validated.final.session
          turn
          step
          nextCall
          toolCallCount_eq_nextCall := toolCallCount_eq
        }
        payload
        session_eq := rfl
      }

/-! ## Request construction after payload-preserving restoration -/

structure RequestCertificate
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource) where
  request : ChatRequest
  build_eq : buildChatRequest source restored.runner.session = .ok request

def buildRequestCertificate
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource) :
    Except RequestError (RequestCertificate restored source) :=
  match built : buildChatRequest source restored.runner.session with
  | .error error => .error error
  | .ok request => .ok { request, build_eq := built }

theorem buildRequest_session_eq_archive
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource)
    {request : ChatRequest}
    (request_eq : buildChatRequest source restored.runner.session = .ok request) :
    buildChatRequest source restored.archive.validated.final.session = .ok request := by
  rw [← restored.session_eq]
  exact request_eq

/-! ## Pure byte attachment -/

structure RestoredBytesRunner (source : ByteArray) where
  validated : ValidatedPersistedBytes source
  restored : RestoredRunner validated.input
  archive_eq : restored.archive = validated.persisted

inductive BytesError where
  | text (error : TextRefinement.TextError)
  | persistence (error : PersistenceError)
  | payload (error : PayloadError)
deriving BEq, DecidableEq, Repr

def restoreBytesRunner
    (source : ByteArray)
    (turn step : Nat) :
    Except BytesError (RestoredBytesRunner source) :=
  match validatePersistedBytes source with
  | .error (.inl error) => .error (.text error)
  | .error (.inr error) => .error (.persistence error)
  | .ok validated =>
      match archivePayload validated.persisted.expandedEvents with
      | .error error => .error (.payload (.archive error))
      | .ok payload => .ok {
          validated
          restored := {
            archive := validated.persisted
            runner := {
              session := validated.persisted.validated.final.session
              turn
              step
              nextCall := toolCallCount validated.persisted.validated.final.session.messages
              toolCallCount_eq_nextCall := rfl
            }
            payload
            session_eq := rfl
          }
          archive_eq := rfl
        }

namespace RestoredBytesRunner

theorem decoded_eq {source : ByteArray} (restored : RestoredBytesRunner source) :
    String.fromUTF8? source = some restored.validated.text :=
  restored.validated.decoded_exact

theorem payload_raw_eq_expanded {source : ByteArray} (restored : RestoredBytesRunner source) :
    restored.restored.payload.events.map EnrichedEvent.raw =
      restored.validated.persisted.expandedEvents := by
  have hEvents := congrArg ValidatedPersistedJson.expandedEvents restored.archive_eq
  exact hEvents ▸ restored.restored.payload_raw_eq_expanded

end RestoredBytesRunner

/-! ## Backend attachment -/

structure ReadRestoredRunner where
  read : ReadCertificate
  restored : RestoredRunner read.input
  archive_eq : restored.archive = read.validated

inductive StoreError where
  | store (error : HarnessPersistenceIO.StoreError)
  | payload (error : PayloadError)
deriving Repr

def restoreRead
    (read : ReadCertificate)
    (turn step : Nat) :
    Except PayloadError (ReadRestoredRunner) :=
  match archivePayload read.validated.expandedEvents with
  | .error error => .error (.archive error)
  | .ok payload => .ok {
      read
      restored := {
        archive := read.validated
        runner := {
          session := read.validated.validated.final.session
          turn
          step
          nextCall := toolCallCount read.validated.validated.final.session.messages
          toolCallCount_eq_nextCall := rfl
        }
        payload
        session_eq := rfl
      }
      archive_eq := rfl
    }

namespace ReadRestoredRunner

theorem session_eq_read (restored : ReadRestoredRunner) :
    restored.restored.runner.session = restored.read.validated.validated.final.session := by
  rw [← restored.archive_eq]
  exact restored.restored.session_eq_archive

theorem payload_raw_eq_expanded (restored : ReadRestoredRunner) :
    restored.restored.payload.events.map EnrichedEvent.raw =
      restored.read.validated.expandedEvents := by
  have hEvents := congrArg ValidatedPersistedJson.expandedEvents restored.archive_eq
  exact hEvents ▸ restored.restored.payload_raw_eq_expanded

end ReadRestoredRunner

def readRunner (backend : DurableIO.Backend) (turn step : Nat) :
    IO (Except StoreError ReadRestoredRunner) := do
  match ← HarnessPersistenceIO.readValidated backend with
  | .error error => pure (.error (.store error))
  | .ok read =>
      match restoreRead read turn step with
      | .error error => pure (.error (.payload error))
      | .ok restored => pure (.ok restored)

def replaceAndRestore
    (backend : DurableIO.Backend)
    (rows : List Lean.Json)
    (turn step : Nat) :
    IO (Except StoreError ReadRestoredRunner) := do
  match ← HarnessPersistenceIO.replaceRows backend rows with
  | .error error => pure (.error (.store error))
  | .ok _ => readRunner backend turn step

def appendAndRestore
    (backend : DurableIO.Backend)
    (row : Lean.Json)
    (turn step : Nat) :
    IO (Except StoreError ReadRestoredRunner) := do
  match ← HarnessPersistenceIO.appendValidatedRow backend row with
  | .error error => pure (.error (.store error))
  | .ok read =>
      match restoreRead read turn step with
      | .error error => pure (.error (.payload error))
      | .ok restored => pure (.ok restored)

def fixtureMemory : IO (Except StoreError ReadRestoredRunner) := do
  let store ← DurableIO.MemoryStore.new
  replaceAndRestore store.backend DeepSeekHarnessPersistence.persistedToolInput 1 1

def fixtureAppend : IO (Except StoreError ReadRestoredRunner) := do
  let store ← DurableIO.MemoryStore.new
  match ← HarnessPersistenceIO.replaceRows store.backend
      [HarnessPersistenceRefinement.headerExample] with
  | .error error => pure (.error (.store error))
  | .ok _ => appendAndRestore store.backend HarnessPersistenceRefinement.packedTextExample 1 1

def fixtureFile : IO (Except StoreError ReadRestoredRunner) :=
  IO.FS.withTempFile fun _ path => do
    let backend := DurableIO.FileBackend.mk path
    replaceAndRestore backend.backend DeepSeekHarnessPersistence.persistedToolInput 1 1

def fixtureInvalidUtf8 : IO (Except StoreError ReadRestoredRunner) := do
  let store ← DurableIO.MemoryStore.new
  store.backend.replaceFlush [255]
  readRunner store.backend 1 1

/-! ## Concrete payload-preserving persistence witnesses -/

def persistedToolPayloadRestored :
    Except (PersistenceError ⊕ PayloadError)
      (RestoredRunner DeepSeekHarnessPersistence.persistedToolInput) :=
  match DeepSeekHarnessPersistence.persistedToolArchive with
  | .error error => .error (.inl error)
  | .ok archive =>
      match restoreRunner archive 1 1
          (toolCallCount archive.validated.final.session.messages) rfl with
      | .error error => .error (.inr error)
      | .ok restored => .ok restored

def persistedToolBytes : ByteArray :=
  (TextRefinement.renderJsonLines DeepSeekHarnessPersistence.persistedToolInput).toUTF8

def persistedToolBytesRestored :
    Except BytesError (RestoredBytesRunner persistedToolBytes) :=
  restoreBytesRunner persistedToolBytes 1 1

end Cordis.DeepSeekHarnessPayloadPersistence
