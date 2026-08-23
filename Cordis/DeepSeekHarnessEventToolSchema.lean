import Cordis.DeepSeekToolSchema
import Cordis.SessionRefinement

/-!
# Source-preserving tool schemas at the current Harness request boundary

`SessionRefinement.WireRequestToolSchema` deliberately stores the compressed JSON text that the
small local `Session` header can represent.  That projection is useful for replay, but it is not
enough to run the bounded JSON-schema validator in `DeepSeekToolSchema`: compression is a
presentation step, not a parsed JSON value.  This module therefore adds a parallel, source-shaped
certificate for the request-header tool object.

The certificate retains the exact parameter AST, its compressed local projection, and a
`ValidatedToolDefinition` for the shallow primitive object-schema vocabulary.  The decoder is
still only a supported subset: it does not claim complete JSON Schema, provider validation,
model obedience, or equivalence to the deployed TypeScript Harness.  In particular, the existing
local header projection remains available even when a caller chooses not to request this stronger
schema certificate.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventToolSchema

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekToolSchema
open Cordis.SessionRefinement

abbrev SessionPathSegment := SessionRefinement.PathSegment
abbrev SessionDecodeError := SessionRefinement.DecodeError

def sourceToolDefinition (source : WireRequestToolSchemaSource) : ToolDefinition := {
  function := {
    name := source.name
    description := some source.description
    parameters := source.parameters
    strict := none
  }
}

structure ValidatedSourceToolSchema (source : WireRequestToolSchemaSource) where
  certificate : ValidatedToolDefinition (sourceToolDefinition source)

inductive ToolSchemaDecodeError where
  | decode (error : SessionDecodeError)
  | schema (error : ToolSchemaError)
deriving DecidableEq, Repr

def decodeValidatedSourceToolSchema (path : List SessionPathSegment) (json : Lean.Json) :
    Except ToolSchemaDecodeError
      (Σ source : WireRequestToolSchemaSource, ValidatedSourceToolSchema source) :=
  match _source_eq : decodeWireRequestToolSchemaSource path json with
  | .error error => .error (.decode error)
  | .ok source =>
      match _schema_eq : validateToolDefinition (sourceToolDefinition source) with
      | .error error => .error (.schema error)
      | .ok certificate =>
          .ok ⟨source, { certificate }⟩

theorem decodeValidatedSourceToolSchema_source
    {path : List SessionPathSegment} {json : Lean.Json}
    {source : WireRequestToolSchemaSource}
    {certificate : ValidatedSourceToolSchema source}
    (h : decodeValidatedSourceToolSchema path json = .ok ⟨source, certificate⟩) :
    decodeWireRequestToolSchemaSource path json = .ok source := by
  unfold decodeValidatedSourceToolSchema at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · cases h
      assumption

theorem decodeValidatedSourceToolSchema_wire_projection
    {path : List SessionPathSegment} {json : Lean.Json}
    {source : WireRequestToolSchemaSource}
    {certificate : ValidatedSourceToolSchema source}
    (h : decodeValidatedSourceToolSchema path json = .ok ⟨source, certificate⟩) :
    decodeWireRequestToolSchema path json = .ok source.toWire := by
  apply decodeWireRequestToolSchema_source_projection
  exact decodeValidatedSourceToolSchema_source h

/-! ## A current-shaped positive and negative schema boundary -/

def headerToolJson : Lean.Json := Lean.Json.mkObj [
  ("name", .str "lookup"),
  ("description", .str "Look up a key"),
  ("parameters", SessionRefinement.headerChunkParametersJson)
]

def headerToolSource : WireRequestToolSchemaSource := {
  name := "lookup"
  description := "Look up a key"
  parameters := SessionRefinement.headerChunkParametersJson
}

def headerToolCertificate :
    Except ToolSchemaDecodeError
      (Σ source : WireRequestToolSchemaSource, ValidatedSourceToolSchema source) :=
  decodeValidatedSourceToolSchema [.field "tools", .index 0] headerToolJson

theorem headerToolCertificate_is_ok : headerToolCertificate.isOk := by
  rfl

theorem headerToolCertificate_source :
    match headerToolCertificate with
    | .error _ => False
    | .ok result => result.1 = headerToolSource := by
  rfl

def malformedHeaderToolJson : Lean.Json := Lean.Json.mkObj [
  ("name", .str "lookup"),
  ("description", .str "Look up a key"),
  ("parameters", Lean.Json.mkObj [
    ("type", .str "object"),
    ("properties", Lean.Json.mkObj [
      ("query", Lean.Json.mkObj [("type", .str "date")])
    ])
  ])
]

def malformedHeaderToolRejected : Bool :=
  match decodeValidatedSourceToolSchema [.field "tools", .index 0] malformedHeaderToolJson with
  | .error _ => true
  | .ok _ => false

theorem malformedHeaderToolRejected_true : malformedHeaderToolRejected = true := by
  rfl

end Cordis.DeepSeekHarnessEventToolSchema
