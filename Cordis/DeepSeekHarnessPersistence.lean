import Cordis.DeepSeekHarness
import Cordis.HarnessPersistenceRefinement

/-!
# Logical persistence attachment for the DeepSeek harness

`HarnessPersistenceRefinement` validates the pinned JSONL archive format, while
`DeepSeekHarness.ConversationRunner` carries the typed continuation state used by
the request/response loop.  This module is the missing attachment between those
two certificates: a restored runner is indexed by a successful persisted archive
and stores an exact equality between its session and the archive's final session.

The boundary is intentionally logical.  It proves exact state attachment and
request preservation after validation; it does not claim to read a filesystem,
decompress zstd, repair torn tails, coordinate concurrent writers, or authenticate
an archive supplied by an external process.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessPersistence

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.HarnessPersistenceRefinement

/-! ## Restored continuation state -/

structure RestoredRunner (input : List Lean.Json) where
  archive : ValidatedPersistedJson input
  runner : ConversationRunner
  session_eq : runner.session = archive.validated.final.session

def restoreRunner
    {input : List Lean.Json}
    (archive : ValidatedPersistedJson input)
    (turn step nextCall : Nat)
    (toolCallCount_eq : toolCallCount archive.validated.final.session.messages = nextCall) :
    RestoredRunner input :=
  {
    archive
    runner := {
      session := archive.validated.final.session
      turn
      step
      nextCall
      toolCallCount_eq_nextCall := toolCallCount_eq
    }
    session_eq := rfl
  }

theorem RestoredRunner.session_messages_eq
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.runner.session.messages = restored.archive.validated.final.session.messages := by
  rw [restored.session_eq]

theorem RestoredRunner.nextSeq_eq
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.runner.session.nextSeq = restored.archive.validated.final.session.nextSeq := by
  rw [restored.session_eq]

/-! ## Request certificate after restoration -/

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

/-! ## Concrete archive/restore/request witness -/

def persistedToolInput : List Lean.Json :=
  HarnessPersistenceRefinement.headerExample :: SessionRefinement.toolMessageExampleJson

def persistedToolArchive :
    Except PersistenceError (ValidatedPersistedJson persistedToolInput) :=
  validatePersistedJson persistedToolInput

theorem persistedToolArchive_valid :
    persistenceSummary persistedToolArchive = some (0, 8, 8) := by
  rfl

def persistedToolSource : RequestSource where
  model := "deepseek-reasoner"
  errorToolResults := .reject

def persistedToolRestored :
    Except PersistenceError (RestoredRunner persistedToolInput) :=
  match persistedToolArchive with
  | .error error => .error error
  | .ok archive =>
      .ok (restoreRunner archive 1 1
        (toolCallCount archive.validated.final.session.messages) rfl)

theorem persistedToolRequest_messages :
    match persistedToolRestored with
    | .error _ => false
    | .ok restored =>
        match buildChatRequest persistedToolSource restored.runner.session with
        | .error _ => false
        | .ok request => request.messages.toList = [
            .user "look up lean",
            .assistant (some "I will look it up.") none [{
              id := "0"
              name := "lookup"
              arguments := "{\"q\":\"lean\"}"
            }],
            .tool "0" "result"
          ] := by
  rfl

end Cordis.DeepSeekHarnessPersistence
