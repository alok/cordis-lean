import Cordis.DeepSeekCurlStream
import Cordis.DeepSeekStreamToolRound

/-!
# Process-backed provider assembly and dependent stream round

This module closes the process boundary above `DeepSeekProviderStreamAssembly`: a configured
process returns a complete HTTP body, the status/SSE adapter certifies that body, and the exact
wire-backed provider/dependent round then reuses the same proof-carrying execution and session
append path.  The process witness and semantic round remain separate fields.

The fixture is deterministic and local.  It does not claim network reachability, credential or
provider authenticity, incremental delivery, backpressure, cancellation, persistence, external
tool effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProcessStreamToolRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekAssemblerToolRound
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProviderStreamAssembly
open Cordis.DeepSeekStreamToolRound

inductive ProcessRoundError where
  | transport (error : StreamClientError)
  | round (error : StreamToolRoundError)
deriving DecidableEq, Repr

structure ProcessedRound
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  wire : DeepSeekStream.ValidatedSseStream body
  round : ValidatedStreamToolRound cfg before body

def executeWith
    {Model Capability : Type}
    (config : ProcessConfig)
    (request : HttpRequest)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model) :
    IO (Except ProcessRoundError
      (Sigma fun body : String => ProcessedRound cfg before body)) := do
  match ← executeSse config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, wire⟩ =>
      match executeBodyTools cfg before body with
      | .error error => pure (.error (.round error))
      | .ok round => pure (.ok ⟨body, { wire, round }⟩)

theorem ProcessedRound.source_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (processed : ProcessedRound cfg before body) :
    validateBody body = .ok processed.round.source :=
  processed.round.source_eq

theorem ProcessedRound.execution_exact
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String}
    (processed : ProcessedRound cfg before body) :
    executeAssembledTools cfg before processed.round.source.assembly.result =
      .ok processed.round.execution :=
  processed.round.execution_eq

def counterProcess : ProcessConfig :=
  fixtureProcess counterBody

def counterRequest : HttpRequest :=
  DeepSeekCurlTransport.fixtureRequest.request

def counterRun : IO (Except ProcessRoundError
    (Sigma fun body : String =>
      ProcessedRound Cordis.Harness.counterConfig 2 body)) :=
  executeWith counterProcess counterRequest Cordis.Harness.counterConfig 2

def counterSummary : IO Bool := do
  match ← counterRun with
  | .error _ => pure false
  | .ok ⟨_, processed⟩ =>
      let session := appendRound (Session.Session.empty Session.noExtensions) 1 0
        processed.round [] (by simp) (by simp)
      pure (processed.round.execution.after == 5 &&
        processed.round.execution.calls.length == 1 &&
        processed.round.execution.executions.length == 1 &&
        session.messages.length == 2 && session.nextSeq == 2)

end Cordis.DeepSeekProcessStreamToolRound
