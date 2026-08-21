import Cordis.SessionRefinement

/-!
# Lossless tool-result metadata over the semantic session refinement

`SessionRefinement` deliberately rejects provider/tool-owned `error` and `meta` fields inside a
`tool/result`: the local `Session.ToolResultPayload` has no semantics for those payloads. This
module adds the missing source-honest middle boundary. It removes only those two fields before
calling the existing dependent decoder, retains their exact original `Lean.Json` values in a
typed certificate, and validates the resulting sanitized list with the existing session/protocol
refinement.

The result is not a claim that the local session understands provider error metadata. It proves
that metadata can be quarantined without loss while the supported event/session projection stays
exact. Unknown tags, malformed events, unsupported surface shapes, and all external logger or
provider semantics remain governed by the existing refinement boundary.
-/

set_option autoImplicit false

namespace Cordis.SessionOpaqueMetadata

open Cordis
open Cordis.SessionRefinement

/-! ## Exact opaque values and the sanitizing map -/

/-- The two source fields retained without assigning them local semantics. -/
structure ToolResultMetadata where
  error : Option Lean.Json
  metaValue : Option Lean.Json

private def eraseToolResultFields : Lean.Json → Lean.Json
  | .obj fields => .obj ((fields.erase "error").erase "meta")
  | json => json

/-- Remove only `tool/result.data.error` and `tool/result.data.meta`. -/
def sanitizeEvent : Lean.Json → Lean.Json
  | .obj fields =>
      match fields.get? "type", fields.get? "data" with
      | some (.str "tool/result"), some data =>
          .obj ((fields.erase "data").insert "data" (eraseToolResultFields data))
      | _, _ => .obj fields
  | json => json

/-- Retain the exact metadata values found in one source event, if it is a tool result. -/
def metadataOf : Lean.Json → Option ToolResultMetadata
  | .obj fields =>
      match fields.get? "type", fields.get? "data" with
      | some (.str "tool/result"), some (.obj data) =>
          some { error := data.get? "error", metaValue := data.get? "meta" }
      | _, _ => none
  | _ => none

/-! ## Event and list certificates -/

/-- One source event, its sanitized form, opaque metadata, and semantic decode certificate. -/
structure RetainedEvent (input : Lean.Json) where
  sanitized : Lean.Json
  metadata : Option ToolResultMetadata
  wire : WireEvent
  sanitized_eq : sanitized = sanitizeEvent input
  metadata_eq : metadata = metadataOf input
  decode_eq : decodeEvent sanitized = .ok wire

/-- Decode after sanitizing only opaque tool-result metadata, retaining the source values. -/
def decodeEventRetainingMetadata (input : Lean.Json) :
    Except DecodeError (RetainedEvent input) :=
  let sanitized := sanitizeEvent input
  match decoded : decodeEvent sanitized with
  | .error error => .error error
  | .ok wire => .ok {
      sanitized
      metadata := metadataOf input
      wire
      sanitized_eq := rfl
      metadata_eq := rfl
      decode_eq := decoded
    }

def sanitizeEvents : List Lean.Json → List Lean.Json
  | [] => []
  | input :: rest => sanitizeEvent input :: sanitizeEvents rest

def metadataEvents : List Lean.Json → List (Option ToolResultMetadata)
  | [] => []
  | input :: rest => metadataOf input :: metadataEvents rest

/-- A full validated session over a sanitized list, with source metadata retained in order. -/
structure RetainedLog (input : List Lean.Json) where
  sanitized : List Lean.Json
  metadata : List (Option ToolResultMetadata)
  validation : ValidatedJsonLog sanitized
  sanitized_eq : sanitized = sanitizeEvents input
  metadata_eq : metadata = metadataEvents input

/-- Validate a metadata-bearing source list without losing its opaque fields. -/
def validateLogRetainingMetadata (input : List Lean.Json) :
    Except (DecodeError ⊕ RefinementError) (RetainedLog input) :=
  let sanitized := sanitizeEvents input
  match _validated : validateJsonLog sanitized with
  | .error error => .error error
  | .ok validation => .ok {
      sanitized
      metadata := metadataEvents input
      validation
      sanitized_eq := rfl
      metadata_eq := rfl
    }

/-! ## Executable positive witness -/

def addMetadata : Lean.Json → Lean.Json
  | .obj fields =>
      match fields.get? "type", fields.get? "data" with
      | some (.str "tool/result"), some (.obj data) =>
          let data := data.insert "error"
            (Lean.Json.mkObj [("name", .str "ToolError"), ("code", .str "E_FIXTURE")])
          let data := data.insert "meta"
            (Lean.Json.mkObj [("opaque", .str "tool-owned")])
          .obj ((fields.erase "data").insert "data" (.obj data))
      | _, _ => .obj fields
  | json => json

/-- The existing complete tool-call session with opaque error/meta fields added to its result. -/
def metadataExampleJson : List Lean.Json :=
  SessionRefinement.toolMessageExampleJson.map addMetadata

theorem metadata_example_valid :
    match validateLogRetainingMetadata metadataExampleJson with
    | .ok _ => true
    | .error _ => false := by
  rfl

theorem metadata_example_retained :
    (metadataEvents metadataExampleJson).filterMap (fun metadata =>
      metadata.map (fun value => (value.error.isSome, value.metaValue.isSome))) =
      [(true, true)] := by
  rfl

theorem metadata_example_exact :
    (metadataEvents metadataExampleJson).filterMap (fun metadata =>
      metadata.map (fun value => (value.error, value.metaValue))) =
      [(some (Lean.Json.mkObj [
          ("name", .str "ToolError"), ("code", .str "E_FIXTURE")]),
        some (Lean.Json.mkObj [("opaque", .str "tool-owned")]))] := by
  rfl

/-- The exact existing protocol projection theorem applies to the sanitized certificate. -/
theorem metadata_example_projection :
    match validateLogRetainingMetadata metadataExampleJson with
    | .ok retained =>
        Session.protocolProjection retained.validation.final.session.events =
          retained.validation.sequence.protocolTrace.erase
    | .error _ => false := by
  rfl

end Cordis.SessionOpaqueMetadata
