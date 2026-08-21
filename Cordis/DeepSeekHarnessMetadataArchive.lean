import Cordis.DeepSeekHarnessOpaqueMetadata
import Cordis.SessionEventArchive

/-!
# Current-event archive plus opaque metadata attachment

`SessionEventArchive` retains every current-Harness envelope, including a known opaque
`tool/result` payload.  `SessionOpaqueMetadata` separately sanitizes only the provider/tool-owned
`error` and `meta` fields before validating the local session.  This module composes those two
certificates: the restored runner uses the sanitized endpoint, while the full raw event archive
and exact metadata ledger remain available beside it.

The composition is deliberately limited to this quarantine.  It does not assign provider/tool
metadata semantics, replay opaque events, or claim complete deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessMetadataArchive

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.SessionEventArchive
open Cordis.SessionOpaqueMetadata
open Cordis.SessionRefinement

abbrev MetadataError := SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError

structure AttachedLog (input : List Lean.Json) where
  archive : SessionEventArchive.ArchivedLog input
  retained : RetainedLog input

def validate (input : List Lean.Json) :
    Except (SessionEventArchive.ArchiveError ⊕ MetadataError) (AttachedLog input) :=
  match _archived : SessionEventArchive.archive input with
  | .error error => .error (.inl error)
  | .ok archive =>
      match _retained : validateLogRetainingMetadata input with
      | .error error => .error (.inr error)
      | .ok log => .ok { archive, retained := log }

theorem AttachedLog.raw_exact
    {input : List Lean.Json}
    (log : AttachedLog input) :
    log.archive.events.map SessionEventArchive.ArchivedEvent.raw = input :=
  log.archive.raw_exact

theorem AttachedLog.metadata_eq_source
    {input : List Lean.Json}
    (log : AttachedLog input) :
    log.retained.metadata = metadataEvents input :=
  log.retained.metadata_eq

theorem AttachedLog.sanitized_eq_source
    {input : List Lean.Json}
    (log : AttachedLog input) :
    log.retained.sanitized = sanitizeEvents input :=
  log.retained.sanitized_eq

structure RestoredRunner (input : List Lean.Json) where
  log : AttachedLog input
  runner : ConversationRunner
  session_eq : runner.session = log.retained.validation.final.session

def restoreRunner
    {input : List Lean.Json}
    (log : AttachedLog input)
    (turn step nextCall : Nat)
    (toolCallCount_eq : toolCallCount log.retained.validation.final.session.messages = nextCall) :
    RestoredRunner input :=
  {
    log
    runner := {
      session := log.retained.validation.final.session
      turn
      step
      nextCall
      toolCallCount_eq_nextCall := toolCallCount_eq
    }
    session_eq := rfl
  }

theorem RestoredRunner.session_eq_log
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.runner.session = restored.log.retained.validation.final.session :=
  restored.session_eq

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

theorem buildRequest_session_eq_log
    {input : List Lean.Json}
    (restored : RestoredRunner input)
    (source : RequestSource)
    {request : ChatRequest}
    (request_eq : buildChatRequest source restored.runner.session = .ok request) :
    buildChatRequest source restored.log.retained.validation.final.session = .ok request := by
  rw [← restored.session_eq]
  exact request_eq

/-! ## Executable current-event metadata fixture -/

def metadataAttached :
    Except (SessionEventArchive.ArchiveError ⊕ MetadataError)
      (AttachedLog SessionOpaqueMetadata.metadataExampleJson) :=
  validate SessionOpaqueMetadata.metadataExampleJson

def metadataRestored :
    Except (SessionEventArchive.ArchiveError ⊕ MetadataError)
      (RestoredRunner SessionOpaqueMetadata.metadataExampleJson) :=
  match metadataAttached with
  | .error error => .error error
  | .ok log =>
      .ok (restoreRunner log 1 1
        (toolCallCount log.retained.validation.final.session.messages) rfl)

theorem metadataAttached_valid :
    match metadataAttached with
    | .ok _ => true
    | .error _ => false := by
  rfl

theorem metadataAttached_has_one_opaque_event :
    match metadataAttached with
    | .error _ => false
    | .ok log => log.archive.events.countP SessionEventArchive.ArchivedEvent.isOpaque = 1 := by
  rfl

theorem metadataRestored_metadata_exact :
    match metadataRestored with
    | .error _ => false
    | .ok restored =>
        (restored.log.retained.metadata.filterMap (fun metadata =>
          metadata.map (fun value => (value.error, value.metaValue)))) =
          [(some (Lean.Json.mkObj [
              ("name", .str "ToolError"), ("code", .str "E_FIXTURE")]),
            some (Lean.Json.mkObj [("opaque", .str "tool-owned")]))] := by
  rfl

def metadataToolSource : RequestSource where
  model := "deepseek-reasoner"
  errorToolResults := .reject

theorem metadataRestored_request_messages :
    match metadataRestored with
    | .error _ => false
    | .ok restored =>
        match buildChatRequest metadataToolSource restored.runner.session with
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

end Cordis.DeepSeekHarnessMetadataArchive
