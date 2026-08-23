import Cordis.DeepSeekHarnessEventArchive
import Cordis.DeepSeekSessionRequest

/-!
# Validated Harness event logs to certified DeepSeek requests

`DeepSeekHarnessEventSimulation` proves a source-shaped JSON prefix by replaying each retained
event into an indexed local session.  `DeepSeekSessionRequest` proves a request only when a
`Session.ModelRequest` agrees with an explicit DeepSeek source/header and a tool-schema encoder.
This module is the small composition boundary between those certificates: a validated event log
must first expose a request header, then its exact endpoint is used to build the request.

The source/header agreement is intentionally explicit.  The structural fixture encoder below
preserves names and descriptions but does not claim that an upstream JSON schema is equivalent to
the empty parameter object it emits.  Transport, credentials, provider behavior, and equivalence
to the complete deployed TypeScript Harness remain outside this slice.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessEventRequest

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessEventArchive
open Cordis.DeepSeekSessionRequest
open Cordis.SessionRefinement

inductive PreparationError where
  | validation (error : SessionRefinement.DecodeError ⊕ SessionRefinement.RefinementError)
  | noRequestHeader
  | request (error : RequestError)
deriving DecidableEq, Repr

/-- A request certificate whose session index is the endpoint of a validated event log. -/
structure PreparedLogRequest
    (input : List Lean.Json)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) where
  log : ValidatedJsonLog input
  request : Session.ModelRequest log.final.session
  prepared : PreparedRequest request (sourceFor request encoder options) encoder
  request_eq : Session.mkRequest log.final.session = some request

namespace PreparedLogRequest

theorem messages_eq_session
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    certificate.request.messages = certificate.log.final.session.messages :=
  certificate.prepared.messages_eq_session

theorem log_length_eq_next_seq
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    certificate.request.logLength = certificate.log.final.session.nextSeq :=
  certificate.request.nextSeq_eq

theorem latest_header_eq_request
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    Session.latestRequestHeader certificate.log.final.session.events =
      some certificate.request.header :=
  certificate.request.latestHeader_eq

theorem protocol_projection_eq_replay
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    Session.protocolProjection certificate.log.final.session.events =
      certificate.log.sequence.protocolTrace.erase :=
  certificate.log.projection_exact

theorem source_model_eq_header
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    (sourceFor certificate.request encoder options).model = certificate.request.header.model :=
  certificate.prepared.agreement.model_eq

theorem source_system_eq_header
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    (sourceFor certificate.request encoder options).system = certificate.request.header.system :=
  certificate.prepared.agreement.system_eq

theorem source_tools_eq_header
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    (sourceFor certificate.request encoder options).tools =
      certificate.request.header.toolSchemas.map encoder.encode :=
  certificate.prepared.agreement.tools_eq

theorem chat_model_eq_header
    {input : List Lean.Json}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (certificate : PreparedLogRequest input encoder options) :
    certificate.prepared.chat.model = certificate.request.header.model :=
  certificate.prepared.chat_model_eq_header

end PreparedLogRequest

/-- Prepare an already validated endpoint.  The `noRequestHeader` branch is explicit rather than
silently inventing a model request from a log that contains only turn/message events. -/
def prepareValidated
    {input : List Lean.Json}
    (log : ValidatedJsonLog input)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) :
    Except PreparationError (PreparedLogRequest input encoder options) :=
  match request_eq : Session.mkRequest log.final.session with
  | none => .error .noRequestHeader
  | some request =>
      match _prepared_eq : prepareFromHeader request encoder options with
      | .error error => .error (.request error)
      | .ok prepared =>
          .ok { log, request, prepared, request_eq }

/-- Decode, replay, and prepare a request in one dependent result. -/
def prepareJsonLog
    (input : List Lean.Json)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) :
    Except PreparationError (PreparedLogRequest input encoder options) :=
  match _validated : SessionRefinement.validateJsonLog input with
  | .error error => .error (.validation error)
  | .ok log => prepareValidated log encoder options

/-! ## A current-shaped fixture with an actual request header -/

def headerOptions : RequestOptions := {
  errorToolResults := .reject
}

def headerPrepared :
    Except PreparationError
      (PreparedLogRequest SessionRefinement.headerChunkExampleJson
        structuralToolSchemaEncoder headerOptions) :=
  prepareJsonLog SessionRefinement.headerChunkExampleJson
    structuralToolSchemaEncoder headerOptions

theorem headerPrepared_is_ok : headerPrepared.isOk := by
  rfl

theorem headerPrepared_request_header :
    match headerPrepared with
    | .error _ => False
    | .ok certificate => certificate.request.header =
        SessionRefinement.headerChunkExpectedHeader := by
  rfl

theorem headerPrepared_protocol_projection :
    match headerPrepared with
    | .error _ => False
    | .ok certificate =>
        Session.protocolProjection certificate.log.final.session.events =
          certificate.log.sequence.protocolTrace.erase := by
  rfl

/-! ## Explicit negative boundary -/

def headerlessPrepared :
    Except PreparationError
      (PreparedLogRequest SessionRefinement.messageExampleJson
        structuralToolSchemaEncoder headerOptions) :=
  prepareJsonLog SessionRefinement.messageExampleJson
    structuralToolSchemaEncoder headerOptions

theorem headerless_is_rejected : headerlessPrepared = .error .noRequestHeader := by
  rfl

end Cordis.DeepSeekHarnessEventRequest
