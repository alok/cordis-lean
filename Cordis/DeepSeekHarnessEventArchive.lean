import Cordis.DeepSeekHarness
import Cordis.SessionEventArchive

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventArchive

open Cordis
open Cordis.DeepSeekHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekSessionRunner
open Cordis.SessionEventArchive
open Cordis.SessionRefinement

/--
An event archive can be attached to a typed runner only after every retained event has
both the lossless archive certificate and the semantic current-Harness certificate.
Opaque known events and extension events therefore cannot be silently discarded while
restoring a runner.
-/
structure SupportedEventLog (input : List Lean.Json) where
  archive : ArchivedLog input
  validated : ValidatedJsonLog input
  supported : ∀ event ∈ archive.events, event.isOpaque = false

/-- A runner whose session is definitionally the session certified by the event log. -/
structure RestoredRunner (input : List Lean.Json) where
  log : SupportedEventLog input
  runner : ConversationRunner
  session_eq : runner.session = log.validated.final.session

def restoreRunner
    {input : List Lean.Json}
    (log : SupportedEventLog input)
    (turn step nextCall : Nat)
    (toolCallCount_eq : toolCallCount log.validated.final.session.messages = nextCall) :
    RestoredRunner input :=
  {
    log
    runner := {
      session := log.validated.final.session
      turn
      step
      nextCall
      toolCallCount_eq_nextCall := toolCallCount_eq
    }
    session_eq := rfl
  }

theorem RestoredRunner.session_eq_archive
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.runner.session = restored.log.validated.final.session :=
  restored.session_eq

theorem RestoredRunner.archive_raw_eq_input
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.log.archive.events.map ArchivedEvent.raw = input :=
  restored.log.archive.raw_eq

theorem RestoredRunner.all_events_supported
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    ∀ event ∈ restored.log.archive.events, event.isOpaque = false :=
  restored.log.supported

/-- A request retains the exact request-builder certificate from the restored session. -/
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
    buildChatRequest source restored.log.validated.final.session = .ok request := by
  rw [← restored.session_eq]
  exact request_eq

/-- The current supported tool-message fixture at the archive boundary. -/
def toolEventLog :
    Except SessionEventArchive.ArchiveError
      (ArchivedLog SessionRefinement.toolMessageExampleJson) :=
  SessionEventArchive.archive SessionRefinement.toolMessageExampleJson

def toolEventLogValidated :
    Except (SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
      (ValidatedJsonLog SessionRefinement.toolMessageExampleJson) :=
  SessionRefinement.validateJsonLog SessionRefinement.toolMessageExampleJson

def toolSupportedLog :
    Except String (SupportedEventLog SessionRefinement.toolMessageExampleJson) :=
  match _archiveResult : toolEventLog with
  | .error _ => .error "archive failed"
  | .ok archive =>
      match _validatedResult : toolEventLogValidated with
      | .error _ => .error "semantic validation failed"
      | .ok validated =>
          if supported : ∀ event ∈ archive.events, event.isOpaque = false then
            .ok { archive, validated, supported }
          else
            .error "opaque event present"

/-- Executable fixture showing the supported archive can be attached to a runner. -/
def toolRestored :
    Except String (RestoredRunner SessionRefinement.toolMessageExampleJson) :=
  match toolSupportedLog with
  | .error error => .error error
  | .ok log =>
      .ok (restoreRunner log 1 1
        (toolCallCount log.validated.final.session.messages) rfl)

end Cordis.DeepSeekHarnessEventArchive
