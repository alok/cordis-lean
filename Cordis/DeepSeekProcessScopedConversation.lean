import Cordis.DeepSeekProcessScopedStreamToolRound

/-!
# Process-backed scoped streamed conversation

This module lifts the process-backed scoped stream round to a finite dependent conversation.
Each process response is parsed and scoped-dispatched before its assistant/tool-result append;
the successor model and session are then the indices of the next process step.  A no-call body
is a typed terminal, while fuel exhaustion is retained separately from a transport or dispatch
failure.

The fixture is deterministic and local.  It does not claim network reachability, credentials,
provider obedience, incremental delivery, cancellation of blocked reads, persistence, external
tool effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProcessScopedConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekProcessScopedStreamToolRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekScopedStreamToolRound
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

abbrev RoundWitness
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg) :=
  Sigma fun before : Model =>
    Sigma fun body : String =>
      Sigma fun after : Model => ProcessedScopedRound registry approval before body after

inductive ConversationStop
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg) :
    Session.Session Session.noExtensions → Model → Type where
  | completed
      {session : Session.Session Session.noExtensions}
      {before after : Model}
      {body : String}
      (step : Nat)
      (processed : ProcessedScopedRound registry approval before body after)
      (noCalls : processed.round.calls = [])
      : ConversationStop registry approval
          (DeepSeekScopedStreamToolRound.appendRound session 1 step processed.round []
            (by simp) (by simp)) after
  | fuelExhausted
      (session : Session.Session Session.noExtensions)
      (model : Model) :
      ConversationStop registry approval session model

namespace ConversationStop

def isFuelExhausted
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {session : Session.Session Session.noExtensions}
    {model : Model} :
    ConversationStop registry approval session model → Bool
  | .completed _ _ _ => false
  | .fuelExhausted _ _ => true

end ConversationStop

structure ConversationResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg) where
  rounds : List (RoundWitness registry approval)
  session : Session.Session Session.noExtensions
  finalModel : Model
  stop : ConversationStop registry approval session finalModel

def conversationProcess
    (toolBody terminalBody : String)
    (index : Nat) : ProcessConfig :=
  let script :=
    "cat >/dev/null; if [ \"$1\" = 0 ]; then printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' " ++
      "\"$2\"; else printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$3\"; fi"
  {
    command := "sh"
    args := fun _ => #[
      "-c", script, "cordis-scoped-conversation-fixture", toString index, toolBody, terminalBody
    ]
  }

def runAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (fuel : Nat)
    (index : Nat)
    (config : Nat → ProcessConfig)
    (request : HttpRequest)
    (before : Model)
    (session : Session.Session Session.noExtensions)
    (history : List (RoundWitness registry approval)) :
    IO (Except ProcessScopedRoundError (ConversationResult registry approval)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        session
        finalModel := before
        stop := .fuelExhausted session before
      })
  | fuel + 1 =>
      match ← executeWith registry approval (config index) request before with
      | .error error => pure (.error error)
      | .ok ⟨body, ⟨after, processed⟩⟩ =>
          let nextSession := DeepSeekScopedStreamToolRound.appendRound session 1 index
            processed.round [] (by simp) (by simp)
          let witness : RoundWitness registry approval :=
            ⟨before, ⟨body, ⟨after, processed⟩⟩⟩
          if noCalls : processed.round.calls = [] then
            pure (.ok {
              rounds := history ++ [witness]
              session := nextSession
              finalModel := after
              stop := .completed index processed noCalls
            })
          else
            runAux registry approval fuel (index + 1) config request after nextSession
              (history ++ [witness])

def run
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (fuel : Nat)
    (config : Nat → ProcessConfig)
    (request : HttpRequest)
    (before : Model)
    (session : Session.Session Session.noExtensions) :
    IO (Except ProcessScopedRoundError (ConversationResult registry approval)) :=
  runAux registry approval fuel 0 config request before session []

namespace Example

open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekScopedRegistry.Example
open Cordis.DeepSeekSchemaRegistry.Example

def process (index : Nat) : ProcessConfig :=
  conversationProcess dualToolStreamBody DeepSeekRichStream.exampleTextStreamBody index

def request : HttpRequest := DeepSeekCurlTransport.fixtureRequest.request

def runTwoSteps
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except ProcessScopedRoundError
      (ConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy)) :=
  run (scopedRegistry weatherCertificate clockCertificate) approvalPolicy 2 process request 0
    (Session.Session.empty Session.noExtensions)

def runOneStep
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except ProcessScopedRoundError
      (ConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy)) :=
  run (scopedRegistry weatherCertificate clockCertificate) approvalPolicy 1 process request 0
    (Session.Session.empty Session.noExtensions)

def twoStepSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runTwoSteps weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          pure (result.rounds.length == 2 && result.finalModel == 0 &&
            result.session.messages.length == 4 && result.session.nextSeq == 4)
  | _, _ => pure false

def oneStepFuelSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runOneStep weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          pure (ConversationStop.isFuelExhausted result.stop &&
            result.rounds.length == 1 && result.session.messages.length == 3 &&
            result.session.nextSeq == 3)
  | _, _ => pure false

end Example

end Cordis.DeepSeekProcessScopedConversation
