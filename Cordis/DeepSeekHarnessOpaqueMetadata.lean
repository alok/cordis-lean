import Cordis.DeepSeekHarness
import Cordis.SessionOpaqueMetadata

/-!
# Opaque tool metadata attachment for the DeepSeek harness

`SessionOpaqueMetadata` validates a sanitized session while retaining the exact
`tool/result.data.error` and `tool/result.data.meta` values in source order.  This module attaches
that certificate to a `ConversationRunner`: the runner sees only the validated local session,
while the restored value keeps the opaque metadata ledger beside it.

The metadata remains intentionally uninterpreted.  This is a lossless quarantine and runner
continuation seam, not provider/tool schema validation, replay semantics, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessOpaqueMetadata

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.SessionOpaqueMetadata
open Cordis.SessionRefinement

/-! ## Metadata-bearing restored runner -/

structure RestoredRunner (input : List Lean.Json) where
  log : RetainedLog input
  runner : ConversationRunner
  session_eq : runner.session = log.validation.final.session

def restoreRunner
    {input : List Lean.Json}
    (log : RetainedLog input)
    (turn step nextCall : Nat)
    (toolCallCount_eq : toolCallCount log.validation.final.session.messages = nextCall) :
    RestoredRunner input :=
  {
    log
    runner := {
      session := log.validation.final.session
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
    restored.runner.session = restored.log.validation.final.session :=
  restored.session_eq

theorem RestoredRunner.metadata_eq_source
    {input : List Lean.Json}
    (restored : RestoredRunner input) :
    restored.log.metadata = metadataEvents input :=
  restored.log.metadata_eq

/-! ## Request certificate after metadata restoration -/

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
    buildChatRequest source restored.log.validation.final.session = .ok request := by
  rw [← restored.session_eq]
  exact request_eq

/-! ## Executable metadata fixture -/

def metadataToolArchive :
    Except (SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
      (RetainedLog SessionOpaqueMetadata.metadataExampleJson) :=
  validateLogRetainingMetadata SessionOpaqueMetadata.metadataExampleJson

def metadataRestored :
    Except (SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
      (RestoredRunner SessionOpaqueMetadata.metadataExampleJson) :=
  match metadataToolArchive with
  | .error error => .error error
  | .ok log =>
      .ok (restoreRunner log 1 1
        (toolCallCount log.validation.final.session.messages) rfl)

theorem metadataRestored_valid :
    match metadataRestored with
    | .ok _ => true
    | .error _ => false := by
  rfl

theorem metadataRestored_metadata_exact :
    match metadataRestored with
    | .error _ => false
    | .ok restored =>
        (restored.log.metadata.filterMap (fun metadata =>
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

end Cordis.DeepSeekHarnessOpaqueMetadata
