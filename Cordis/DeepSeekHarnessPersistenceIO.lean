import Cordis.DeepSeekHarnessPersistence
import Cordis.HarnessPersistenceIO

/-!
# Byte-backed persistence attachment for the DeepSeek harness

`HarnessPersistenceIO` reads UTF-8 JSONL through a `DurableIO.Backend` and returns a
proof-carrying `ReadCertificate`.  `DeepSeekHarnessPersistence` already attaches the
logical JSON-AST certificate to a `ConversationRunner`; this module composes the two
boundaries.  A successful read therefore restores a runner whose session is exactly the
validated archive endpoint, and request construction can be checked against that same
byte-backed certificate.

The adapter deliberately stops at the read certificate.  Backend acknowledgement is not
fsync, and no filesystem, compression, torn-tail, locking, authenticity, or deployed
crash-recovery theorem is claimed here.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistenceIO

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessPersistence
open Cordis.DeepSeekSessionRunner
open Cordis.HarnessPersistenceIO

/-! ## Read-backed restored runner -/

structure RestoredRunner where
  read : ReadCertificate
  restored : DeepSeekHarnessPersistence.RestoredRunner read.input
  archive_eq : restored.archive = read.validated

def restoreRead (read : ReadCertificate) (turn step : Nat) : RestoredRunner :=
  {
    read
    restored := DeepSeekHarnessPersistence.restoreRunner read.validated turn step
      (toolCallCount read.validated.validated.final.session.messages) rfl
    archive_eq := rfl
  }

theorem RestoredRunner.session_eq_read (restored : RestoredRunner) :
    restored.restored.runner.session = restored.read.validated.validated.final.session :=
  by rw [← restored.archive_eq]; exact restored.restored.session_eq

theorem RestoredRunner.raw_rows_eq_input (restored : RestoredRunner) :
    restored.read.input = restored.read.validated.headerJson ::
      restored.read.validated.storageRows :=
  restored.read.split_exact

/-! ## Request certificate after a byte-backed read -/

structure RequestCertificate
    (restored : RestoredRunner)
    (source : RequestSource) where
  request : ChatRequest
  build_eq : buildChatRequest source restored.restored.runner.session = .ok request

def buildRequestCertificate
    (restored : RestoredRunner)
    (source : RequestSource) :
    Except RequestError (RequestCertificate restored source) :=
  match built : buildChatRequest source restored.restored.runner.session with
  | .error error => .error error
  | .ok request => .ok { request, build_eq := built }

theorem buildRequest_session_eq_read
    (restored : RestoredRunner)
    (source : RequestSource)
    {request : ChatRequest}
    (request_eq : buildChatRequest source restored.restored.runner.session = .ok request) :
    buildChatRequest source restored.read.validated.validated.final.session = .ok request := by
  rw [← restored.archive_eq]
  exact DeepSeekHarnessPersistence.buildRequest_session_eq_archive
    restored.restored source request_eq

/-! ## IO boundary -/

def readRunner (backend : DurableIO.Backend) (turn step : Nat) :
    IO (Except StoreError RestoredRunner) := do
  match ← HarnessPersistenceIO.readValidated backend with
  | .error error => pure (.error error)
  | .ok read => pure (.ok (restoreRead read turn step))

def replaceAndRestore
    (backend : DurableIO.Backend)
    (rows : List Lean.Json)
    (turn step : Nat) :
    IO (Except StoreError RestoredRunner) := do
  match ← HarnessPersistenceIO.replaceRows backend rows with
  | .error error => pure (.error error)
  | .ok _ => readRunner backend turn step

def appendAndRestore
    (backend : DurableIO.Backend)
    (row : Lean.Json)
    (turn step : Nat) :
    IO (Except StoreError RestoredRunner) := do
  match ← HarnessPersistenceIO.appendValidatedRow backend row with
  | .error error => pure (.error error)
  | .ok read => pure (.ok (restoreRead read turn step))

def fixtureMemory : IO (Except StoreError RestoredRunner) := do
  let store ← DurableIO.MemoryStore.new
  replaceAndRestore store.backend persistedToolInput 1 1

def fixtureAppend : IO (Except StoreError RestoredRunner) := do
  let store ← DurableIO.MemoryStore.new
  replaceAndRestore store.backend [HarnessPersistenceRefinement.headerExample] 1 1
    >>= fun result =>
      match result with
      | .error error => pure (.error error)
      | .ok _ => appendAndRestore store.backend HarnessPersistenceRefinement.packedTextExample 1 1

def fixtureFile : IO (Except StoreError RestoredRunner) :=
  IO.FS.withTempFile fun _ path => do
    let backend := DurableIO.FileBackend.mk path
    replaceAndRestore backend.backend persistedToolInput 1 1

def fixtureInvalidUtf8 : IO (Except StoreError RestoredRunner) := do
  let store ← DurableIO.MemoryStore.new
  store.backend.replaceFlush [255]
  readRunner store.backend 1 1

/-! ## Executable request fixture -/

def fixtureRequest : IO (Except StoreError (Except RequestError ChatRequest)) := do
  match ← fixtureMemory with
  | .error error => pure (.error error)
  | .ok restored =>
      match buildRequestCertificate restored persistedToolSource with
      | .error error => pure (.ok (.error error))
      | .ok certificate => pure (.ok (.ok certificate.request))

end Cordis.DeepSeekHarnessPersistenceIO
