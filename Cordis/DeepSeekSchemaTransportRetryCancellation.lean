import Cordis.DeepSeekHarnessTransportRetry
import Cordis.DeepSeekHarnessCancellation
import Cordis.DeepSeekSchemaConversation

/-!
# Retry and pre-round cancellation for heterogeneous schema tools

This module composes the proof-carrying retry boundary with the heterogeneous schema registry.
The successful retry attempt is validated once; that dependent response is then used directly
for terminal admission or registry lookup/execution.  A cancellation decision is checked before
the request round, and the indexed trace records the exact tool-round endpoints.

The boundary is intentionally explicit: complete-body transport and caller-controlled fuel are
injected.  This does not claim provider backoff, idempotency, in-flight cancellation, durable
persistence, external-effect correctness, credential/network trust, or deployed Harness
equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaTransportRetryCancellation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessCancellation
open Cordis.DeepSeekHarnessRetry
open Cordis.DeepSeekHarnessTransportRetry
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaMultiRound
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekToolSchema

/-! ## Indexed round results -/

inductive SchemaRetryRoundError (policy : RetryPolicy) where
  | request (error : RequestError)
  | client (history : RetryHistory policy) (error : ClientError)
  | response (history : RetryHistory policy) (error : ResponseError)
  | session (error : ApiSessionError)
  | noToolCalls
  | execution (error : RegistryExecutionError)
structure SchemaRetryTerminalResult
    (policy : RetryPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  plan : TypedRequestPlan .complete
  retryHistory : RetryHistory policy
  response : HttpResponse
  validated : ValidatedResponse body
  accepted : AcceptedApiResponse body
  accepted_eq : acceptValidated validated = .ok accepted
  noToolCalls : accepted.validated.response.choices.head.message.toolCalls = []
  finalRunner : ConversationRunner
  finalRunner_eq : finalRunner = ConversationRunner.appendAcceptedApi runner accepted
    sourceEventSeqs sourcesNodup (by
      intro source source_mem
      exact sourcesEarlier runner source source_mem)
  finalModel : Model
  finalModel_eq : finalModel = before

structure SchemaRetryToolResult
    (policy : RetryPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  plan : TypedRequestPlan .complete
  retryHistory : RetryHistory policy
  response : HttpResponse
  validated : ValidatedResponse body
  accepted : AcceptedToolCalls body
  batch : RegistryExecutionBatch cfg before accepted.calls
  batch_eq : executeSchemaRegistryCalls registry before accepted.calls = .ok batch
  round : SchemaRegistryRoundResult registry runner before accepted batch

inductive SchemaRetryStep
    (policy : RetryPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (runner : ConversationRunner)
    (before : Model) : String → Type where
  | terminal {body : String}
      (result : SchemaRetryTerminalResult policy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before body) :
      SchemaRetryStep policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
        sourcesEarlier runner before body
  | tools {body : String}
      (result : SchemaRetryToolResult policy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before body) :
      SchemaRetryStep policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
        sourcesEarlier runner before body

def executeSchemaRetryStep
    (policy : RetryPolicy)
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
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    IO (Except (SchemaRetryRoundError policy)
      (Sigma fun body : String =>
        SchemaRetryStep policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
          sourcesEarlier runner before body)) := do
  match built : buildTypedCompleteRequestPlan baseUrl apiKey request.source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeValidatedRetry policy transport plan with
      | .failed history error => pure (.error (.client history error))
      | .responseFailure history _response error => pure (.error (.response history error))
      | .succeeded history response validated =>
          match acceptedEq : acceptValidated validated with
          | .error error => pure (.error (.session error))
          | .ok accepted =>
              match callsEq : accepted.validated.response.choices.head.message.toolCalls with
              | [] =>
                  let finalRunner := ConversationRunner.appendAcceptedApi runner accepted
                    sourceEventSeqs sourcesNodup (by
                      intro source source_mem
                      exact sourcesEarlier runner source source_mem)
                  pure (.ok ⟨response.body, .terminal {
                    plan
                    retryHistory := history
                    response
                    validated
                    accepted
                    accepted_eq := acceptedEq
                    noToolCalls := callsEq
                    finalRunner
                    finalRunner_eq := rfl
                    finalModel := before
                    finalModel_eq := rfl
                  }⟩)
              | head :: tail =>
                  let acceptedTools : AcceptedToolCalls response.body := {
                    accepted
                    calls := head :: tail
                    calls_eq := callsEq
                    nonempty := by simp
                  }
                  match batchEq : executeSchemaRegistryCalls registry before
                      acceptedTools.calls with
                  | .error error => pure (.error (.execution error))
                  | .ok batch =>
                      let assistantSeq := runner.session.nextSeq
                      let assistantRunner := ConversationRunner.appendAcceptedApi runner
                        accepted sourceEventSeqs sourcesNodup (by
                          intro source source_mem
                          exact sourcesEarlier runner source source_mem)
                      have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
                        rw [ConversationRunner.appendAcceptedApi_nextSeq]
                        exact Nat.lt_succ_self _
                      let finalRunner := appendSchemaRegistryResultsToRunner assistantRunner
                        runner.nextCall assistantSeq batch.executions assistantSeqEarlier
                      let round : SchemaRegistryRoundResult registry runner before acceptedTools
                          batch := {
                        assistantRunner
                        assistantSeq
                        assistantSeq_eq := by
                          change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                          rw [ConversationRunner.appendAcceptedApi_nextSeq]
                        assistantSeqEarlier
                        finalRunner
                        finalRunner_eq := rfl
                      }
                      pure (.ok ⟨response.body, .tools {
                        plan
                        retryHistory := history
                        response
                        validated
                        accepted := acceptedTools
                        batch
                        batch_eq := batchEq
                        round
                      }⟩)

/-! ## Trace, stop, and fuel-bounded execution -/

structure SchemaRetryToolRoundBox
    (policy : RetryPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (runner : ConversationRunner)
    (before : Model) where
  body : String
  round : SchemaRetryToolResult policy registry baseUrl apiKey request sourceEventSeqs
    sourcesNodup sourcesEarlier runner before body

inductive SchemaRetryTrace
    (policy : RetryPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    ConversationRunner → Model → ConversationRunner → Model → Type where
  | nil (runner : ConversationRunner) (before : Model) :
      SchemaRetryTrace policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
        sourcesEarlier runner before runner before
  | terminal
      {runner : ConversationRunner} {before : Model} {body : String}
      (round : SchemaRetryTerminalResult policy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before body) :
      SchemaRetryTrace policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
        sourcesEarlier runner before round.finalRunner round.finalModel
  | cons
      {runner : ConversationRunner} {before : Model}
      {finalRunner : ConversationRunner} {finalModel : Model}
      (head : SchemaRetryToolRoundBox policy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before)
      (tail : SchemaRetryTrace policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
        sourcesEarlier head.round.round.finalRunner head.round.batch.finalModel finalRunner finalModel) :
      SchemaRetryTrace policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
        sourcesEarlier runner before finalRunner finalModel

namespace SchemaRetryTrace

def length
    {policy : RetryPolicy}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {baseUrl : String} {apiKey : ApiKey}
    {request : RegistryRequestSource registry}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq}
    {runner finalRunner : ConversationRunner} {before finalModel : Model} :
    SchemaRetryTrace policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
      sourcesEarlier runner before finalRunner finalModel → Nat
  | .nil _ _ | .terminal _ => 0
  | .cons _ tail => Nat.succ tail.length

end SchemaRetryTrace

inductive SchemaRetryStop
    (policy : RetryPolicy)
    (cancellationPolicy : CancellationPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq) :
    ConversationRunner → Model → Type where
  | completed
      {runner : ConversationRunner} {before : Model} {body : String}
      {finalRunner : ConversationRunner} {finalModel : Model}
      (terminal : SchemaRetryTerminalResult policy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before body)
      (runner_eq : terminal.finalRunner = finalRunner)
      (model_eq : terminal.finalModel = finalModel)
      : SchemaRetryStop policy cancellationPolicy registry baseUrl apiKey request sourceEventSeqs
          sourcesNodup sourcesEarlier finalRunner finalModel
  | fuelExhausted {runner : ConversationRunner} {before : Model} :
      SchemaRetryStop policy cancellationPolicy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before
  | cancelled
      {runner : ConversationRunner} {before : Model}
      (round : Nat) (reason : CancelReason)
      (decided : cancellationPolicy.decide round runner = true) :
      SchemaRetryStop policy cancellationPolicy registry baseUrl apiKey request sourceEventSeqs
        sourcesNodup sourcesEarlier runner before

structure SchemaRetryRunResult
    (policy : RetryPolicy)
    (cancellationPolicy : CancellationPolicy)
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (initialRunner : ConversationRunner)
    (initialModel : Model)
    (finalRunner : ConversationRunner)
    (finalModel : Model) where
  trace : SchemaRetryTrace policy registry baseUrl apiKey request sourceEventSeqs sourcesNodup
    sourcesEarlier initialRunner initialModel finalRunner finalModel
  stop : SchemaRetryStop policy cancellationPolicy registry baseUrl apiKey request sourceEventSeqs
    sourcesNodup sourcesEarlier finalRunner finalModel

def runAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (cancellationPolicy : CancellationPolicy)
    (retryPolicy : RetryPolicy)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (round : Nat)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (SchemaRetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          SchemaRetryRunResult retryPolicy cancellationPolicy registry baseUrl apiKey request
            sourceEventSeqs sourcesNodup sourcesEarlier runner before finalRunner finalModel)) := do
  match fuel with
  | 0 =>
      pure (.ok ⟨runner, ⟨before, {
        trace := .nil runner before
        stop := .fuelExhausted
      }⟩⟩)
  | fuel + 1 =>
      if decided : cancellationPolicy.decide round runner then
        pure (.ok ⟨runner, ⟨before, {
          trace := .nil runner before
          stop := .cancelled round cancellationPolicy.reason decided
        }⟩⟩)
      else
        match ← executeSchemaRetryStep retryPolicy transport baseUrl apiKey request before runner
            sourceEventSeqs sourcesNodup sourcesEarlier with
        | .error error => pure (.error error)
        | .ok ⟨_body, .terminal terminal⟩ =>
            pure (.ok ⟨terminal.finalRunner, ⟨terminal.finalModel, {
              trace := .terminal terminal
              stop := .completed terminal rfl rfl
            }⟩⟩)
        | .ok ⟨body, .tools tools⟩ =>
            let head : SchemaRetryToolRoundBox retryPolicy registry baseUrl apiKey request
                sourceEventSeqs sourcesNodup sourcesEarlier runner before := {
              body
              round := tools
            }
            match ← runAux fuel cancellationPolicy retryPolicy transport baseUrl apiKey request
                sourceEventSeqs sourcesNodup sourcesEarlier (round + 1) tools.batch.finalModel
                tools.round.finalRunner with
            | .error error => pure (.error error)
            | .ok ⟨finalRunner, ⟨finalModel, tail⟩⟩ =>
                pure (.ok ⟨finalRunner, ⟨finalModel, {
                  trace := .cons head tail.trace
                  stop := tail.stop
                }⟩⟩)

def run
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (cancellationPolicy : CancellationPolicy)
    (retryPolicy : RetryPolicy)
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except (SchemaRetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Model =>
          SchemaRetryRunResult retryPolicy cancellationPolicy registry baseUrl apiKey request
            sourceEventSeqs sourcesNodup sourcesEarlier runner before finalRunner finalModel)) :=
  runAux fuel cancellationPolicy retryPolicy transport baseUrl apiKey request sourceEventSeqs
    sourcesNodup sourcesEarlier 0 before runner

/-! ## Executable heterogeneous retry/cancellation fixtures -/

namespace Example

open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaRegistry.Example

def dualTerminalResponseBody : String := DeepSeekHarness.counterFinalResponseBody

def retryPolicy : RetryPolicy where
  maxRetries := 1
  retryTransport := true
  retryTransientHttp := true

def cancellationPolicy : CancellationPolicy :=
  CancellationPolicy.atRound 0 .timeout

def neverCancellation : CancellationPolicy :=
  CancellationPolicy.never .user

def retryTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.set (index + 1)
    pure (.ok {
      status := if index = 0 then 503 else 200
      body := if index = 0 then "busy"
        else if index = 1 then dualResponseBody
        else dualTerminalResponseBody
    })

def cancellationRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except (SchemaRetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          SchemaRetryRunResult retryPolicy cancellationPolicy
            (dualRegistryEntries weatherCertificate clockCertificate)
            "https://fixture.invalid" { value := "fixture-key" }
            (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp)
            DeepSeekSchemaHarness.Example.counterRunner 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  run cancellationPolicy retryPolicy 2 (retryTransport calls) "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp) 0
    DeepSeekSchemaHarness.Example.counterRunner

def successRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except (SchemaRetryRoundError retryPolicy)
      (Sigma fun finalRunner : ConversationRunner =>
        Sigma fun finalModel : Nat =>
          SchemaRetryRunResult retryPolicy neverCancellation
            (dualRegistryEntries weatherCertificate clockCertificate)
            "https://fixture.invalid" { value := "fixture-key" }
            (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp)
            DeepSeekSchemaHarness.Example.counterRunner 0 finalRunner finalModel)) := do
  let calls ← IO.mkRef 0
  run neverCancellation retryPolicy 2 (retryTransport calls) "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate) [] (by simp) (by simp) 0
    DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekSchemaTransportRetryCancellation
