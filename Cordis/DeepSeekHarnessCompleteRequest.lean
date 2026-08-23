import Cordis.DeepSeekHarnessCompleteSimulation
import Cordis.DeepSeekHarnessEventRequest

/-!
# Complete supported-subset event simulation to a prepared request

This module closes a useful end-to-end composition boundary for the current-Harness subset:
lossless archive, explicit ignorable-row projection, contiguous local normalization, dependent
semantic replay, and a header-indexed DeepSeek request certificate.  The request is indexed by
the exact `NormalizedLog.validated` endpoint, so it cannot be built from a stale or independently
reparsed session.

The source replay is retained in the same result, but this module deliberately does not assert
that its existential endpoint is definitionally equal to the validator's endpoint.  Establishing
that equality would require a separate replay/validator determinism theorem; the two certificates
are therefore exposed without silently strengthening the claim.  Opaque payload semantics,
provider behavior, transport, persistence, cancellation delivery, and equivalence to the complete
deployed TypeScript Harness remain outside this finite source-honest slice.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessCompleteRequest

open Cordis
open Cordis.DeepSeekHarnessCompleteSimulation
open Cordis.DeepSeekHarnessEventIgnorableNormalization
open Cordis.DeepSeekHarnessEventIgnorableProjection
open Cordis.DeepSeekHarnessEventRequest
open Cordis.DeepSeekSessionRequest
open Cordis.SessionRefinement

inductive PreparationError where
  | simulation (error : SimulationError)
  | request (error : Cordis.DeepSeekHarnessEventRequest.PreparationError)
deriving DecidableEq, Repr

/-- A request certificate built from one particular complete simulation result. -/
structure PreparedSimulation
    {input : List Lean.Json}
    (simulation : CompleteSimulation input)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) where
  request : PreparedLogRequest simulation.normalized.normalizedInput encoder options
  request_log_eq : request.log = simulation.normalized.validated

def prepareSimulation
    {input : List Lean.Json}
    (simulation : CompleteSimulation input)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) :
    Except Cordis.DeepSeekHarnessEventRequest.PreparationError
      (PreparedSimulation simulation encoder options) :=
  match h : prepareValidated simulation.normalized.validated encoder options with
  | .error error => .error error
  | .ok request => .ok {
      request
      request_log_eq := by
        unfold prepareValidated at h
        split at h
        · contradiction
        · rename_i request' request_eq
          split at h
          · contradiction
          · rename_i prepared prepared_eq
            cases h
            rfl
    }

/-- Run archive, normalization, replay, and request preparation as one dependent computation. -/
def prepare
    (input : List Lean.Json)
    (encoder : ToolSchemaEncoder)
    (options : RequestOptions) :
    Except PreparationError
      (Sigma fun simulation : CompleteSimulation input =>
        PreparedSimulation simulation encoder options) :=
  match _h : simulate input with
  | .error error => .error (.simulation error)
  | .ok simulation =>
      match _hRequest : prepareSimulation simulation encoder options with
      | .error error => .error (.request error)
      | .ok prepared => .ok ⟨simulation, prepared⟩

namespace PreparedSimulation

theorem request_log_eq_validated
    {input : List Lean.Json}
    {simulation : CompleteSimulation input}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (prepared : PreparedSimulation simulation encoder options) :
    prepared.request.log = simulation.normalized.validated :=
  prepared.request_log_eq

theorem request_messages_eq_final
    {input : List Lean.Json}
    {simulation : CompleteSimulation input}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (prepared : PreparedSimulation simulation encoder options) :
    prepared.request.request.messages = simulation.normalized.validated.final.session.messages := by
  simpa [prepared.request_log_eq] using prepared.request.messages_eq_session

theorem request_protocol_projection_eq_replay
    {input : List Lean.Json}
    {simulation : CompleteSimulation input}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (prepared : PreparedSimulation simulation encoder options) :
    Session.protocolProjection simulation.normalized.validated.final.session.events =
      prepared.request.log.sequence.protocolTrace.erase := by
  rw [← prepared.request_log_eq]
  exact prepared.request.protocol_projection_eq_replay

theorem request_source_model_eq_header
    {input : List Lean.Json}
    {simulation : CompleteSimulation input}
    {encoder : ToolSchemaEncoder}
    {options : RequestOptions}
    (prepared : PreparedSimulation simulation encoder options) :
    (sourceFor prepared.request.request encoder options).model =
      prepared.request.request.header.model :=
  prepared.request.source_model_eq_header

end PreparedSimulation

/-! ## Executable positive and negative boundaries -/

def ignorableHeaderPrepared :
    Except PreparationError
      (Sigma fun simulation : CompleteSimulation ignorableMiddleFixtureJson =>
        PreparedSimulation simulation structuralToolSchemaEncoder headerOptions) :=
  prepare ignorableMiddleFixtureJson structuralToolSchemaEncoder headerOptions

theorem ignorableHeaderPrepared_is_ok : ignorableHeaderPrepared.isOk := by
  rfl

theorem ignorableHeaderPrepared_request_header :
    match ignorableHeaderPrepared with
    | .error _ => False
    | .ok ⟨_, prepared⟩ =>
        prepared.request.request.header = headerChunkExpectedHeader := by
  rfl

theorem ignorableHeaderPrepared_archive_length :
    match ignorableHeaderPrepared with
    | .error _ => False
    | .ok ⟨simulation, _⟩ => simulation.archive.events.length = 7 := by
  rfl

theorem ignorableHeaderPrepared_dropped_positions :
    match ignorableHeaderPrepared with
    | .error _ => False
    | .ok ⟨simulation, _⟩ =>
        simulation.certificate.ledger.decisions.droppedPositions = [1] := by
  rfl

def requiredOpaqueRejected : Bool :=
  match prepare requiredFixtureJson structuralToolSchemaEncoder headerOptions with
  | .error _ => true
  | .ok _ => false

theorem requiredOpaqueRejected_eq_true : requiredOpaqueRejected = true := by
  decide

end Cordis.DeepSeekHarnessCompleteRequest
