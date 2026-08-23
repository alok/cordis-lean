import Cordis.DeepSeekSchemaTrace

/-!
# Fuel-bounded transport-backed schema conversation

`DeepSeekSchemaConversation` proves one complete-body request/response round for a heterogeneous
schema registry. This module closes the adjacent control-flow boundary: successful tool rounds
advance the dependent model and append their certified results, while a validated assistant
response with no tool calls is retained as an explicit terminal witness. Fuel exhaustion remains
distinct from terminal completion and transport/schema/execution failures.

The loop is intentionally finite and caller-controlled. The transport is still an explicit effect
boundary, the response body is complete rather than incrementally assembled, and no claim is made
about remote credentials, provider obedience, call-ID authenticity, retries, cancellation,
persistence, external tool effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaConversationLoop

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaMultiRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaTrace
open Cordis.DeepSeekToolSchema

/-! ## One-step terminal/tool distinction -/

structure SchemaRegistryTerminalResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  plan : TypedRequestPlan .complete
  accepted : AcceptedApiResponse body
  noToolCalls : accepted.validated.response.choices.head.message.toolCalls = []

structure SchemaRegistryToolResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  accepted : AcceptedToolCalls body
  batch : RegistryExecutionBatch cfg before accepted.calls
  result : SchemaRegistryConversationResult registry runner before accepted batch

inductive SchemaRegistryConversationStep
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  | terminal (result : SchemaRegistryTerminalResult registry runner before body) :
      SchemaRegistryConversationStep registry runner before body
  | tools (result : SchemaRegistryToolResult registry runner before body) :
      SchemaRegistryConversationStep registry runner before body

def executeSchemaRegistryConversationStep
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaConversationError
      (Sigma fun body : String =>
        SchemaRegistryConversationStep registry runner before body)) := do
  match buildTypedCompleteRequestPlan baseUrl apiKey request.source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeComplete transport plan with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, _response⟩ =>
          match acceptResponse body with
          | .error error => pure (.error (.response error))
          | .ok accepted =>
              match calls_eq : accepted.validated.response.choices.head.message.toolCalls with
              | [] =>
                  pure (.ok ⟨body, .terminal {
                    plan
                    accepted
                    noToolCalls := calls_eq
                  }⟩)
              | _ :: _ =>
                  match executeSchemaRegistryRound runner registry before body sourceEventSeqs
                      sourcesNodup sourcesEarlier with
                  | .error (.response error) => pure (.error (.response error))
                  | .error .noToolCalls => pure (.error .noToolCalls)
                  | .error (.execution error) => pure (.error (.execution error))
                  | .ok ⟨acceptedCalls, ⟨batch, round⟩⟩ =>
                      pure (.ok ⟨body, .tools {
                        accepted := acceptedCalls
                        batch
                        result := {
                          accepted := acceptedCalls
                          batch
                          plan
                          response := _response
                          round
                        }
                      }⟩)

/-! ## Heterogeneous tool-round history -/

abbrev SchemaToolRoundWitness
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) :=
  Sigma fun runner : ConversationRunner =>
    Sigma fun before : Model =>
      Sigma fun body : String =>
        Sigma fun accepted : AcceptedToolCalls body =>
          Sigma fun batch : RegistryExecutionBatch cfg before accepted.calls =>
            SchemaRegistryConversationResult registry runner before accepted batch

inductive SchemaConversationStop
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) : ConversationRunner -> Model -> Type where
  | completed
      {runner : ConversationRunner}
      {before : Model}
      {body : String}
      (terminal : SchemaRegistryTerminalResult registry runner before body) :
      SchemaConversationStop registry runner before
  | fuelExhausted
      (runner : ConversationRunner)
      (before : Model) :
      SchemaConversationStop registry runner before

structure SchemaConversationRunResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) where
  initialRunner : ConversationRunner
  initialModel : Model
  rounds : List (SchemaToolRoundWitness registry)
  runner : ConversationRunner
  finalModel : Model
  stop : SchemaConversationStop registry runner finalModel
  trace : SchemaConversationTrace registry initialRunner initialModel runner finalModel
  trace_rounds_eq : trace.rounds = rounds

def runSchemaConversationAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (initialModel : Model)
    (initialRunner : ConversationRunner)
    (before : Model)
    (runner : ConversationRunner)
    (history : List (SchemaToolRoundWitness registry))
    (historyTrace : SchemaConversationTrace registry initialRunner initialModel runner before)
    (historyTrace_rounds_eq : historyTrace.rounds = history) :
    IO (Except SchemaConversationError (SchemaConversationRunResult registry)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        initialRunner
        initialModel
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted runner before
        trace := historyTrace
        trace_rounds_eq := historyTrace_rounds_eq
      })
  | fuel + 1 =>
      match ← executeSchemaRegistryConversationStep transport baseUrl apiKey request before runner
          sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨_body, .terminal terminal⟩ =>
          pure (.ok {
            initialRunner
            initialModel
            rounds := history
            runner
            finalModel := before
            stop := .completed terminal
            trace := historyTrace
            trace_rounds_eq := historyTrace_rounds_eq
          })
      | .ok ⟨body, .tools toolStep⟩ =>
          let witness : SchemaToolRoundWitness registry :=
            ⟨runner, ⟨before, ⟨body, ⟨toolStep.accepted,
              ⟨toolStep.batch, toolStep.result⟩⟩⟩⟩⟩
          runSchemaConversationAux fuel transport baseUrl apiKey request sourceEventSeqs
            sourcesNodup sourcesEarlier initialModel initialRunner
            toolStep.result.batch.finalModel toolStep.result.round.finalRunner
            (history ++ [witness]) (historyTrace.snoc toolStep.result) (by
              change historyTrace.rounds ++ [⟨runner, ⟨before, ⟨body, ⟨toolStep.accepted,
                ⟨toolStep.batch, toolStep.result⟩⟩⟩⟩⟩] = history ++ [witness]
              rw [historyTrace_rounds_eq])

def runSchemaConversation
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except SchemaConversationError (SchemaConversationRunResult registry)) :=
  runSchemaConversationAux fuel transport baseUrl apiKey request sourceEventSeqs sourcesNodup
    sourcesEarlier before runner before runner [] (SchemaConversationTrace.nil runner before)
    (by rfl)

/-! ## Executable two-request fixture -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example
open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaConversation.Example

def dualTerminalResponseBody : String := DeepSeekHarness.counterFinalResponseBody

def dualSequenceTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.set (index + 1)
    pure (.ok {
      status := 200
      body := if index = 0 then dualResponseBody else dualTerminalResponseBody
    })

def dualConversationRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaConversationError
      (SchemaConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate))) := do
  let calls ← IO.mkRef 0
  runSchemaConversation 2 (dualSequenceTransport calls) "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

def dualConversationExhausted
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaConversationError
      (SchemaConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate))) := do
  let calls ← IO.mkRef 0
  runSchemaConversation 1 (dualSequenceTransport calls) "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekSchemaConversationLoop
