import Cordis.DeepSeekCurlStream
import Cordis.DeepSeekScopedStreamToolRound

/-!
# Process-backed scoped streamed tool round

This module carries the scoped/approval-routed stream round through the existing complete-body
process/SSE adapter.  The process witness, strict wire witness, scoped execution trace, and
session append remain separate indexed fields, so a process or dispatch failure cannot be
mistaken for a successful session endpoint.

The fixture is deterministic and local.  It does not claim network reachability, credential or
provider authenticity, incremental delivery, backpressure, cancellation, persistence, external
tool effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProcessScopedStreamToolRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekScopedStreamToolRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.GenericHarness

inductive ProcessScopedRoundError where
  | transport (error : StreamClientError)
  | round (error : ScopedStreamToolRoundError)
deriving DecidableEq, Repr

structure ProcessedScopedRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (before : Model)
    (body : String)
    (after : Model) where
  wire : DeepSeekStream.ValidatedSseStream body
  round : ScopedStreamToolRound registry approval before body after

def executeWith
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (config : ProcessConfig)
    (request : HttpRequest)
    (before : Model) :
    IO (Except ProcessScopedRoundError
      (Sigma fun body : String =>
        Sigma fun after : Model =>
          ProcessedScopedRound registry approval before body after)) := do
  match ← executeSse config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, wire⟩ =>
      match executeBodyScopedTools registry approval before body with
      | .error error => pure (.error (.round error))
      | .ok ⟨after, round⟩ => pure (.ok ⟨body, ⟨after, { wire, round }⟩⟩)

theorem ProcessedScopedRound.source_exact
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {body : String}
    {after : Model}
    (processed : ProcessedScopedRound registry approval before body after) :
    validateBody body = .ok processed.round.source :=
  processed.round.source_eq

theorem ProcessedScopedRound.calls_exact
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {before : Model}
    {body : String}
    {after : Model}
    (processed : ProcessedScopedRound registry approval before body after) :
    processed.round.calls = toFunctionCalls processed.round.source.assembly.result :=
  processed.round.calls_eq

namespace Example

open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekScopedRegistry.Example
open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekToolSchema

def scopedDualProcess : ProcessConfig := dualToolStreamProcess

def scopedDualRequest : HttpRequest := DeepSeekCurlTransport.fixtureRequest.request

def scopedDualRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except ProcessScopedRoundError
      (Sigma fun body : String =>
        Sigma fun after : Nat =>
          ProcessedScopedRound
            (scopedRegistry weatherCertificate clockCertificate)
            approvalPolicy 0 body after)) :=
  executeWith (scopedRegistry weatherCertificate clockCertificate) approvalPolicy
    scopedDualProcess scopedDualRequest 0

def scopedDualProcessSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← scopedDualRun weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok ⟨_, ⟨after, processed⟩⟩ =>
          let session := appendRound (Session.Session.empty Session.noExtensions) 1 0
            processed.round [] (by simp) (by simp)
          pure (after == 0 && processed.round.calls.length == 2 &&
            session.messages.length == 3 && session.nextSeq == 3)
  | _, _ => pure false

end Example

end Cordis.DeepSeekProcessScopedStreamToolRound
