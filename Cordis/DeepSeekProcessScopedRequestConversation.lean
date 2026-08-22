import Cordis.DeepSeekProcessScopedConversation
import Cordis.DeepSeekHarness
import Cordis.DeepSeekCurlStream

/-!
# Request-indexed process-backed scoped conversation

This module closes the request-provenance gap left by the body-only process conversation.  Each
round first builds a typed streaming request from the current session, then passes exactly that
request to the process/SSE/scoped/dependent round.  The prepared response is indexed by the same
`HttpRequest`, so a successful witness cannot silently pair a response with a different request.

The fixture is deterministic and local.  It proves request-plan construction, streaming-mode
selection, process/status/SSE evidence, scoped approval, dependent execution, exact session append,
and terminal-versus-fuel stops.  It does not claim network reachability, credential validity,
provider obedience, retries, cancellation, persistence, external effects, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProcessScopedRequestConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlStream
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProcessScopedConversation
open Cordis.DeepSeekProcessScopedStreamToolRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekScopedStreamToolRound
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-! ## Process result indexed by its exact request -/

structure PreparedProcessScopedRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (request : HttpRequest)
    (before : Model)
    (body : String)
    (after : Model) where
  wire : DeepSeekStream.ValidatedSseStream body
  round : ScopedStreamToolRound registry approval before body after

def executePrepared
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
          PreparedProcessScopedRound registry approval request before body after)) := do
  match ← executeSse config request with
  | .error error => pure (.error (.transport error))
  | .ok ⟨body, wire⟩ =>
      match executeBodyScopedTools registry approval before body with
      | .error error => pure (.error (.round error))
      | .ok ⟨after, round⟩ => pure (.ok ⟨body, ⟨after, { wire, round }⟩⟩)

/-! ## Session-indexed request witnesses -/

inductive RequestConversationError where
  | request (error : DeepSeekHarness.RequestError)
  | process (error : ProcessScopedRoundError)
deriving DecidableEq, Repr

structure PreparedScopedRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (session : Session.Session Session.noExtensions)
    (before : Model)
    (body : String)
    (after : Model) where
  plan : TypedRequestPlan .streaming
  plan_eq : buildTypedStreamingRequestPlan baseUrl apiKey source session = .ok plan
  prepared : PreparedProcessScopedRound registry approval plan.request before body after

theorem PreparedScopedRound.plan_source_stream
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {session : Session.Session Session.noExtensions}
    {before : Model}
    {body : String}
    {after : Model}
    (round : PreparedScopedRound registry approval baseUrl apiKey source session before body
      after) :
    round.plan.source.stream = true :=
  round.plan.streaming_source_stream

theorem PreparedScopedRound.plan_body_exact
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {session : Session.Session Session.noExtensions}
    {before : Model}
    {body : String}
    {after : Model}
    (round : PreparedScopedRound registry approval baseUrl apiKey source session before body
      after) :
    round.plan.request.body = Lean.Json.compress (round.plan.source.toJson) :=
  round.plan.body_eq

abbrev RoundWitness
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource) :=
  Sigma fun session : Session.Session Session.noExtensions =>
    Sigma fun before : Model =>
      Sigma fun body : String =>
        Sigma fun after : Model =>
          PreparedScopedRound registry approval baseUrl apiKey source session before body after

namespace RoundWitness

def requestBody
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    RoundWitness registry approval baseUrl apiKey source → String
  | ⟨_, ⟨_, ⟨_, ⟨_, round⟩⟩⟩⟩ => round.plan.request.body

def sourceIsStreaming
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    RoundWitness registry approval baseUrl apiKey source → Bool
  | ⟨_, ⟨_, ⟨_, ⟨_, round⟩⟩⟩⟩ => round.plan.source.stream

def allStreaming
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    List (RoundWitness registry approval baseUrl apiKey source) → Bool
  | [] => true
  | head :: tail => head.sourceIsStreaming && allStreaming tail

def firstTwoBodiesDistinct
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    List (RoundWitness registry approval baseUrl apiKey source) → Bool
  | first :: second :: _ => first.requestBody != second.requestBody
  | _ => false

end RoundWitness

inductive ConversationStop
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource) :
    Session.Session Session.noExtensions → Model → Type where
  | completed
      {session : Session.Session Session.noExtensions}
      {before after : Model}
      {body : String}
      (step : Nat)
      (prepared : PreparedScopedRound registry approval baseUrl apiKey source
        session before body after)
      (noCalls : prepared.prepared.round.calls = []) :
      ConversationStop registry approval baseUrl apiKey source
        (DeepSeekScopedStreamToolRound.appendRound session 1 step prepared.prepared.round []
          (by simp) (by simp)) after
  | fuelExhausted
      (session : Session.Session Session.noExtensions)
      (model : Model) :
      ConversationStop registry approval baseUrl apiKey source session model

namespace ConversationStop

def isFuelExhausted
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {session : Session.Session Session.noExtensions}
    {model : Model} :
    ConversationStop registry approval baseUrl apiKey source session model → Bool
  | .completed _ _ _ => false
  | .fuelExhausted _ _ => true

end ConversationStop

structure ConversationResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource) where
  rounds : List (RoundWitness registry approval baseUrl apiKey source)
  session : Session.Session Session.noExtensions
  finalModel : Model
  stop : ConversationStop registry approval baseUrl apiKey source session finalModel

def runAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (fuel : Nat)
    (index : Nat)
    (config : Nat → ProcessConfig)
    (before : Model)
    (session : Session.Session Session.noExtensions)
    (history : List (RoundWitness registry approval baseUrl apiKey source)) :
    IO (Except RequestConversationError
      (ConversationResult registry approval baseUrl apiKey source)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        session
        finalModel := before
        stop := .fuelExhausted session before
      })
  | fuel + 1 =>
      match planEq : buildTypedStreamingRequestPlan baseUrl apiKey source session with
      | .error error => pure (.error (.request error))
      | .ok plan =>
          match ← executePrepared registry approval (config index) plan.request before with
          | .error error => pure (.error (.process error))
          | .ok ⟨body, ⟨after, prepared⟩⟩ =>
              let witness : PreparedScopedRound registry approval baseUrl apiKey source
                  session before body after := {
                plan
                plan_eq := planEq
                prepared
              }
              let nextSession := DeepSeekScopedStreamToolRound.appendRound session 1 index
                prepared.round [] (by simp) (by simp)
              let packed : RoundWitness registry approval baseUrl apiKey source :=
                ⟨session, ⟨before, ⟨body, ⟨after, witness⟩⟩⟩⟩
              if noCalls : prepared.round.calls = [] then
                pure (.ok {
                  rounds := history ++ [packed]
                  session := nextSession
                  finalModel := after
                  stop := .completed index witness noCalls
                })
              else
                runAux registry approval baseUrl apiKey source fuel (index + 1) config after
                  nextSession (history ++ [packed])

def run
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (fuel : Nat)
    (config : Nat → ProcessConfig)
    (before : Model)
    (session : Session.Session Session.noExtensions) :
    IO (Except RequestConversationError
      (ConversationResult registry approval baseUrl apiKey source)) :=
  runAux registry approval baseUrl apiKey source fuel 0 config before session []

namespace Example

open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekScopedRegistry.Example
open Cordis.DeepSeekSchemaRegistry.Example

def baseUrl : String := "https://fixture.invalid"

def apiKey : ApiKey := { value := "fixture-key" }

def source : RequestSource where
  model := "fixture-model"
  system := some "You are a deterministic local fixture."
  tools := [DeepSeekApi.exampleTool, clockTool]

def process (index : Nat) : ProcessConfig :=
  conversationProcess dualToolStreamBody DeepSeekRichStream.exampleTextStreamBody index

def runTwoSteps
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except RequestConversationError
      (ConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy baseUrl apiKey
        source)) :=
  run (scopedRegistry weatherCertificate clockCertificate) approvalPolicy baseUrl apiKey source 2
    process 0 (Session.Session.empty Session.noExtensions)

def runOneStep
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except RequestConversationError
      (ConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy baseUrl apiKey
        source)) :=
  run (scopedRegistry weatherCertificate clockCertificate) approvalPolicy baseUrl apiKey source 1
    process 0 (Session.Session.empty Session.noExtensions)

def twoStepSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runTwoSteps weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          pure (result.rounds.length == 2 && RoundWitness.allStreaming result.rounds &&
            RoundWitness.firstTwoBodiesDistinct result.rounds && result.finalModel == 0 &&
            result.session.messages.length == 4 && result.session.nextSeq == 4)
  | _, _ => pure false

def oneStepFuelSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runOneStep weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          pure (ConversationStop.isFuelExhausted result.stop &&
            RoundWitness.allStreaming result.rounds && result.rounds.length == 1 &&
            result.session.messages.length == 3 && result.session.nextSeq == 3)
  | _, _ => pure false

end Example

end Cordis.DeepSeekProcessScopedRequestConversation
