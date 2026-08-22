import Cordis.DeepSeekProcessScopedRequestConversation
import Cordis.DeepSeekCurlBytePrefix
import Cordis.DeepSeekHarness
import Cordis.DeepSeekStreamByteFraming

/-!
# Request-indexed byte-prefix scoped conversation

This module extends the request-indexed complete-body conversation with arbitrary-byte process
ingress.  Every successful round retains the exact typed streaming request, byte chunks, pending
framing state, strict SSE certificate, scoped approval, dependent execution, and session append.
Prefix fuel is a typed nonterminal stop, so an incomplete byte prefix cannot be mistaken for a
completed assistant response.

The fixture is deterministic and local.  It does not claim network reachability, credential or
executable trust, blocked-read interruption, backpressure, reconnects, provider-complete assembly,
retries, cancellation delivery, persistence, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekProcessScopedRequestBytePrefixConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlBytePrefix
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekProcessScopedConversation
open Cordis.DeepSeekScopedRegistry
open Cordis.DeepSeekScopedStreamToolRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekStreamIncremental
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-! ## Completed byte evidence and typed prefix attempts -/

structure CompletedBytePrefix where
  response : BytePrefixResponse (LinePolicy.never)
  stream : DeepSeekStreamByteFraming.ValidatedByteStream
  stop_eq : response.stop = .completed stream

structure PreparedByteScopedRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (request : HttpRequest)
    (before : Model)
    (body : String)
    (after : Model) where
  bytes : CompletedBytePrefix
  body_eq : bytes.stream.text = body
  round : ScopedStreamToolRound registry approval before body after

inductive ByteScopedAttempt
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (request : HttpRequest)
    (before : Model) where
  | completed
      (body : String)
      (after : Model)
      (prepared : PreparedByteScopedRound registry approval request before body after) :
      ByteScopedAttempt registry approval request before
  | fuelExhausted
      (response : BytePrefixResponse (LinePolicy.never))
      (stop_eq : response.stop = .fuelExhausted) :
      ByteScopedAttempt registry approval request before
  | cancelled
      (response : BytePrefixResponse (LinePolicy.never))
      (line : Nat)
      (reason : String) :
      ByteScopedAttempt registry approval request before

inductive ByteScopedRoundError where
  | client (error : BytePrefixClientError)
  | round (error : ScopedStreamToolRoundError)

def executePrepared
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (maxReads chunkSize : Nat)
    (config : ProcessConfig)
    (request : HttpRequest)
    (before : Model) :
    IO (Except ByteScopedRoundError (ByteScopedAttempt registry approval request before)) := do
  match ← executeSseBytePrefix (LinePolicy.never) maxReads chunkSize config request with
  | .error error => pure (.error (.client error))
  | .ok response =>
      match stop_eq : response.stop with
      | .fuelExhausted => pure (.ok (.fuelExhausted response stop_eq))
      | .cancelled line reason _ =>
          pure (.ok (.cancelled response line reason))
      | .completed stream =>
          let body := stream.text
          match executeBodyScopedTools registry approval before body with
          | .error error => pure (.error (.round error))
          | .ok ⟨after, round⟩ =>
              pure (.ok (.completed body after {
                bytes := { response, stream, stop_eq := stop_eq }
                body_eq := rfl
                round
              }))

/-! ## Session-indexed request and byte witnesses -/

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
  prepared : PreparedByteScopedRound registry approval plan.request before body after

theorem PreparedScopedRound.plan_source_stream
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {session : Session.Session Session.noExtensions}
    {before after : Model}
    {body : String}
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
    {before after : Model}
    {body : String}
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

def allByteComplete
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    List (RoundWitness registry approval baseUrl apiKey source) → Bool
  | [] => true
  | head :: tail =>
      head.2.2.2.2.prepared.bytes.response.isCompleted && allByteComplete tail

def firstTwoBodiesDistinct
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    List (RoundWitness registry approval baseUrl apiKey source) → Bool
  | first :: second :: _ =>
      first.2.2.2.2.plan.request.body != second.2.2.2.2.plan.request.body
  | _ => false

def firstHasManyByteChunks
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : ScopedRegistry cfg}
    {approval : ApprovalPolicy cfg}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource} :
    List (RoundWitness registry approval baseUrl apiKey source) → Bool
  | first :: _ => decide (first.2.2.2.2.prepared.bytes.response.rawChunks.length > 1)
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
  | prefixFuelExhausted
      (session : Session.Session Session.noExtensions)
      (model : Model)
      (response : BytePrefixResponse (LinePolicy.never))
      (stop_eq : response.stop = .fuelExhausted) :
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
  | .fuelExhausted _ _ | .prefixFuelExhausted _ _ _ _ => true

def isPrefixFuelExhausted
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
  | .prefixFuelExhausted _ _ _ _ => true
  | .completed _ _ _ | .fuelExhausted _ _ => false

end ConversationStop

inductive RequestByteConversationError where
  | request (error : DeepSeekHarness.RequestError)
  | round (error : ByteScopedRoundError)

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
    (fuel maxReads chunkSize : Nat)
    (config : Nat → ProcessConfig)
    (index : Nat)
    (before : Model)
    (session : Session.Session Session.noExtensions)
    (history : List (RoundWitness registry approval baseUrl apiKey source)) :
    IO (Except RequestByteConversationError
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
          match ← executePrepared registry approval maxReads chunkSize (config index) plan.request
            before
          with
          | .error error => pure (.error (.round error))
          | .ok attempt =>
              match attempt with
              | .fuelExhausted response stop_eq =>
                  pure (.ok {
                    rounds := history
                    session
                    finalModel := before
                    stop := .prefixFuelExhausted session before response stop_eq
                  })
              | .cancelled _ _ _ =>
                  pure (.error (.round (.client (.readLimit 0))))
              | .completed body after prepared =>
                  let witness : PreparedScopedRound registry approval baseUrl apiKey source
                      session before body after := {
                    plan
                    plan_eq := planEq
                    prepared
                  }
                  let nextSession := DeepSeekScopedStreamToolRound.appendRound session 1 0
                    prepared.round [] (by simp) (by simp)
                  let packed : RoundWitness registry approval baseUrl apiKey source :=
                    ⟨session, ⟨before, ⟨body, ⟨after, witness⟩⟩⟩⟩
                  if noCalls : prepared.round.calls = [] then
                    pure (.ok {
                      rounds := history ++ [packed]
                      session := nextSession
                      finalModel := after
                      stop := .completed 0 witness noCalls
                    })
                  else
                    runAux registry approval baseUrl apiKey source fuel maxReads chunkSize config
                      (index + 1) after nextSession (history ++ [packed])
termination_by fuel

def run
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : ScopedRegistry cfg)
    (approval : ApprovalPolicy cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (fuel maxReads chunkSize : Nat)
    (config : Nat → ProcessConfig)
    (before : Model)
    (session : Session.Session Session.noExtensions) :
    IO (Except RequestByteConversationError
      (ConversationResult registry approval baseUrl apiKey source)) :=
  runAux registry approval baseUrl apiKey source fuel maxReads chunkSize config 0 before session []

namespace Example

open Cordis.DeepSeekProcessScopedRequestConversation.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekScopedRegistry.Example
open Cordis.DeepSeekSchemaRegistry.Example

def process (index : Nat) : ProcessConfig :=
  Cordis.DeepSeekProcessScopedConversation.conversationProcess
    dualToolStreamBody DeepSeekRichStream.exampleTextStreamBody index

def runTwoSteps
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except RequestByteConversationError
      (ConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy
          Cordis.DeepSeekProcessScopedRequestConversation.Example.baseUrl
          Cordis.DeepSeekProcessScopedRequestConversation.Example.apiKey
          Cordis.DeepSeekProcessScopedRequestConversation.Example.source)) :=
  run (scopedRegistry weatherCertificate clockCertificate) approvalPolicy
    Cordis.DeepSeekProcessScopedRequestConversation.Example.baseUrl
    Cordis.DeepSeekProcessScopedRequestConversation.Example.apiKey
    Cordis.DeepSeekProcessScopedRequestConversation.Example.source 2 4096 1 process 0
    (Session.Session.empty Session.noExtensions)

def runPrefixFuel
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except RequestByteConversationError
      (ConversationResult
        (scopedRegistry weatherCertificate clockCertificate) approvalPolicy
          Cordis.DeepSeekProcessScopedRequestConversation.Example.baseUrl
          Cordis.DeepSeekProcessScopedRequestConversation.Example.apiKey
          Cordis.DeepSeekProcessScopedRequestConversation.Example.source)) :=
  run (scopedRegistry weatherCertificate clockCertificate) approvalPolicy
    Cordis.DeepSeekProcessScopedRequestConversation.Example.baseUrl
    Cordis.DeepSeekProcessScopedRequestConversation.Example.apiKey
    Cordis.DeepSeekProcessScopedRequestConversation.Example.source 1 1 1 process 0
    (Session.Session.empty Session.noExtensions)

def twoStepSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runTwoSteps weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          pure (result.rounds.length == 2 && RoundWitness.allByteComplete result.rounds &&
            RoundWitness.firstTwoBodiesDistinct result.rounds &&
            RoundWitness.firstHasManyByteChunks result.rounds && result.finalModel == 0 &&
            result.session.messages.length == 4 && result.session.nextSeq == 4)
  | _, _ => pure false

def prefixFuelSummary : IO Bool := do
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← runPrefixFuel weatherCertificate clockCertificate with
      | .error _ => pure false
      | .ok result =>
          pure (ConversationStop.isPrefixFuelExhausted result.stop && result.rounds.isEmpty &&
            result.session.messages.length == 0 && result.session.nextSeq == 0)
  | _, _ => pure false

end Example

end Cordis.DeepSeekProcessScopedRequestBytePrefixConversation
