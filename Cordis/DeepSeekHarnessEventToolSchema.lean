import Cordis.DeepSeekToolSchema
import Cordis.DeepSeekHarnessEventRequest
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
open Cordis.DeepSeekHarnessEventRequest
open Cordis.DeepSeekSessionRequest
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

def sourceToLocalTool (source : WireRequestToolSchemaSource) : Session.ToolSchema := {
  name := source.name
  description := source.description
  inputSchema := Lean.Json.compress source.parameters
}

structure ValidatedSourceToolSchema (source : WireRequestToolSchemaSource) where
  certificate : ValidatedToolDefinition (sourceToolDefinition source)

inductive ValidatedSourceToolList : List WireRequestToolSchemaSource → Type where
  | nil : ValidatedSourceToolList []
  | cons {source : WireRequestToolSchemaSource}
      {tail : List WireRequestToolSchemaSource}
      (head : ValidatedSourceToolSchema source)
      (tailProof : ValidatedSourceToolList tail) : ValidatedSourceToolList (source :: tail)

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

def decodeValidatedSourceToolSchemas (path : List SessionPathSegment) (json : Lean.Json) :
    Except ToolSchemaDecodeError
      (Σ sources : List WireRequestToolSchemaSource, ValidatedSourceToolList sources) :=
  match json with
  | .arr values =>
      let rec loop : Nat → List Lean.Json →
          Except ToolSchemaDecodeError
            (Σ sources : List WireRequestToolSchemaSource,
              ValidatedSourceToolList sources)
        | _, [] => .ok ⟨[], .nil⟩
        | index, value :: rest => do
            let head ← decodeValidatedSourceToolSchema (path ++ [.index index]) value
            let tail ← loop (index + 1) rest
            .ok ⟨head.1 :: tail.1, .cons head.2 tail.2⟩
      loop 0 values.toList
  | _ => .error (.decode (.typeMismatch path "array" .array))

def requestHeaderToolsJson : Lean.Json → Option Lean.Json
  | json =>
      match objectField? json "type" with
      | some (.str "request/header") =>
          match objectField? json "data" with
          | some data =>
              match objectField? data "header" with
              | some header =>
                  match objectField? header "tools" with
                  | some tools => some tools
                  | none => some (.arr #[])
              | _ => none
          | _ => none
      | _ => none

def latestRequestHeaderToolsJson : List Lean.Json → Option Lean.Json
  | [] => none
  | head :: tail =>
      match latestRequestHeaderToolsJson tail with
      | some tools => some tools
      | none => requestHeaderToolsJson head

structure PreparedSchemaLogRequest
    (input : List Lean.Json)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions)
    (sources : List WireRequestToolSchemaSource) where
  base : PreparedLogRequest input encoder options
  sourceCertificates : ValidatedSourceToolList sources
  sourceJson : Lean.Json
  source_decode :
    decodeValidatedSourceToolSchemas [.field "tools"] sourceJson =
      .ok ⟨sources, sourceCertificates⟩
  raw_header_tools_eq : latestRequestHeaderToolsJson input = some sourceJson
  header_tools_eq :
    sources.map sourceToLocalTool = base.request.header.toolSchemas

namespace PreparedSchemaLogRequest

theorem request_header_eq
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    certificate.base.request.header.toolSchemas = sources.map sourceToLocalTool :=
  certificate.header_tools_eq.symm

theorem source_names_eq_request_names
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
  {sources : List WireRequestToolSchemaSource}
    (certificate : PreparedSchemaLogRequest input encoder options sources) :
    sources.map WireRequestToolSchemaSource.name =
      certificate.base.request.header.toolSchemas.map Session.ToolSchema.name := by
  rw [← certificate.header_tools_eq]
  simp [sourceToLocalTool]

end PreparedSchemaLogRequest

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

def headerToolSourcesJson : Lean.Json := .arr #[headerToolJson]

def headerToolSourcesDecoded :=
  decodeValidatedSourceToolSchemas [.field "tools"] headerToolSourcesJson

theorem headerToolSourcesDecoded_is_ok : headerToolSourcesDecoded.isOk := by
  rfl

theorem headerToolSourcesDecoded_source :
    match headerToolSourcesDecoded with
    | .error _ => False
    | .ok result => result.1 = [headerToolSource] := by
  rfl

/-! ## Prepared-request attachment -/

def headerPreparedCertificate :
    PreparedLogRequest SessionRefinement.headerChunkExampleJson
      structuralToolSchemaEncoder headerOptions := by
  match h : headerPrepared with
  | .ok certificate => exact certificate
  | .error error =>
      have impossible : False := by
        have status := DeepSeekHarnessEventRequest.headerPrepared_is_ok
        rw [h] at status
        change (false : Bool) = true at status
        exact Bool.noConfusion status
      exact impossible.elim

theorem headerPreparedCertificate_header :
    headerPreparedCertificate.request.header = SessionRefinement.headerChunkExpectedHeader := by
  unfold headerPreparedCertificate
  split
  · rename_i certificate h
    have header_eq := DeepSeekHarnessEventRequest.headerPrepared_request_header
    rw [h] at header_eq
    exact header_eq
  · rename_i error h
    have status := DeepSeekHarnessEventRequest.headerPrepared_is_ok
    rw [h] at status
    change (false : Bool) = true at status
    exact Bool.noConfusion status

def headerSourceCertificate : ValidatedSourceToolList [headerToolSource] := by
  match h : headerToolCertificate with
  | .error error =>
      have status := headerToolCertificate_is_ok
      rw [h] at status
      change (false : Bool) = true at status
      exact Bool.noConfusion status
  | .ok result =>
      have source_eq : result.1 = headerToolSource := by
        have source_theorem := headerToolCertificate_source
        rw [h] at source_theorem
        exact source_theorem
      exact .cons (source_eq ▸ result.2) .nil

def headerSchemaAttachment :
    Σ sources : List WireRequestToolSchemaSource,
      PreparedSchemaLogRequest SessionRefinement.headerChunkExampleJson
        structuralToolSchemaEncoder headerOptions sources :=
  ⟨[headerToolSource], {
    base := headerPreparedCertificate
    sourceCertificates := headerSourceCertificate
    sourceJson := headerToolSourcesJson
    source_decode := by rfl
    raw_header_tools_eq := by rfl
    header_tools_eq := by
      rw [headerPreparedCertificate_header]
      rfl
  }⟩

theorem headerSchemaAttachment_source : headerSchemaAttachment.1 = [headerToolSource] := by
  rfl

theorem headerSchemaAttachment_request_tools :
    headerSchemaAttachment.2.base.request.header.toolSchemas =
      [sourceToLocalTool headerToolSource] := by
  change headerPreparedCertificate.request.header.toolSchemas =
    [sourceToLocalTool headerToolSource]
  rw [headerPreparedCertificate_header]
  rfl

end Cordis.DeepSeekHarnessEventToolSchema
