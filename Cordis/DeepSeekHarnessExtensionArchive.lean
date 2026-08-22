import Cordis.SessionExtensionArchive
import Cordis.DeepSeekHarnessExtensions

/-!
# Schema-indexed Harness runner attachment for typed extension archives

`SessionExtensionArchive` certifies a lossless raw extension archive and its dependent replay.
This module carries that final indexed session into the schema-polymorphic `ExtensionRunner` and
rebuilds a request from the restored session.  The runner/session equality is stored in the result
type, so request reconstruction cannot accidentally use a different erased session.

The attachment remains pure and certificate-gated: the codec, request source, tool-count witness,
and all provider/transport/persistence semantics are explicit caller boundaries.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessExtensionArchive

open Cordis
open Cordis.DeepSeekHarness
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarnessExtensions
open Cordis.DeepSeekSessionRunner
open Cordis.SessionExtensionArchive
open Cordis.SessionExtensionRefinement

/-- A schema-indexed runner whose session is exactly an extension archive endpoint. -/
structure RestoredRunner
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json} where
  archive : ValidatedExtensionArchive codec initial input
  runner : ExtensionRunner schema
  session_eq : runner.session = archive.validated.final

def restoreRunner
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (archive : ValidatedExtensionArchive codec initial input)
    (turn : Nat) :
    RestoredRunner (codec := codec) (initial := initial) (input := input) :=
  {
    archive,
    runner := {
      session := archive.validated.final
      turn
      step := archive.validated.final.nextSeq
      nextCall := toolCallCount archive.validated.final.messages
      nextSeq_eq_step := rfl
      toolCallCount_eq_nextCall := rfl
    }
    session_eq := rfl
  }

theorem RestoredRunner.session_eq_archive
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input)) :
    restored.runner.session = restored.archive.validated.final :=
  restored.session_eq

theorem RestoredRunner.archive_raw_eq_input
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input)) :
    restored.archive.archive.events.map SessionEventArchive.ArchivedEvent.raw = input :=
  restored.archive.raw_exact

theorem RestoredRunner.archive_final_nextSeq
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input)) :
    restored.runner.session.nextSeq = initial.nextSeq + input.length := by
  rw [restored.session_eq]
  exact restored.archive.final_nextSeq

/-- A request retained together with the exact builder equation from the restored session. -/
structure RequestCertificate
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input))
    (source : RequestSource) where
  request : DeepSeekApi.ChatRequest
  build_eq : buildChatRequestFor source restored.runner.session = .ok request

def buildRequestCertificate
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input))
    (source : RequestSource) :
    Except RequestError (RequestCertificate restored source) :=
  match built : buildChatRequestFor source restored.runner.session with
  | .error error => .error error
  | .ok request => .ok { request, build_eq := built }

theorem buildRequest_session_eq_archive
    {schema : Session.ExtensionSchema}
    {codec : ExtensionCodec schema}
    {initial : Session.Session schema}
    {input : List Lean.Json}
    (restored : RestoredRunner (codec := codec) (initial := initial) (input := input))
    (source : RequestSource)
    {request : DeepSeekApi.ChatRequest}
    (request_eq : buildChatRequestFor source restored.runner.session = .ok request) :
    buildChatRequestFor source restored.archive.validated.final = .ok request := by
  rw [← restored.session_eq]
  exact request_eq

namespace Example

open SessionExtensionRefinement.Example
open SessionExtensionArchive.Example

def restoredExample :
    Except String
      (RestoredRunner (codec := exampleCodec)
        (initial := Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
        (input := exampleInput)) :=
  match archivedExample with
  | .error _ => .error "extension archive failed"
  | .ok archive =>
      .ok (restoreRunner archive 1)

def exampleSource : RequestSource where
  model := "deepseek-chat"

def exampleRequest :
    Except RequestError DeepSeekApi.ChatRequest :=
  match restoredExample with
  | .error _ => .error .emptyMessages
  | .ok restored =>
      (buildRequestCertificate restored exampleSource).map RequestCertificate.request

theorem restored_example_summary :
    (match restoredExample with
    | .error _ => none
    | .ok restored =>
        some (restored.runner.session.nextSeq, restored.runner.step,
          restored.runner.nextCall)) =
      some (2, 2, 0) := by
  rfl

theorem restored_example_request :
    (match exampleRequest with
    | .error _ => none
    | .ok request => some (request.model, some request.messages.head)) =
      some ("deepseek-chat", some (DeepSeekApi.ChatMessage.user "extension:ready")) := by
  rfl

end Example

end Cordis.DeepSeekHarnessExtensionArchive
