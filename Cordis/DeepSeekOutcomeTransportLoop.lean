import Cordis.DeepSeekOutcomeConversation
import Cordis.DeepSeekRequestMode
import Cordis.DeepSeekApiErrorEnvelope

/-!
# Transport-backed terminal-outcome conversation loop

`DeepSeekOutcomeConversationLoop` is deliberately pure over a script of already-observed
complete bodies. This module closes the adjacent effect boundary for rich terminal outcomes:
each round builds a type-indexed streaming request, sends it through the generic `Transport`,
validates the complete SSE body, and executes the dependent tool calls before the next request.

The loop keeps provider failures separate from transport, HTTP-status, terminal-validation, and
tool-execution errors. It is still a complete-body adapter: incremental reads, reconnects,
backpressure, cancellation, retry policy, credential trust, and deployed-provider equivalence
remain outside this proof-carrying kernel.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekOutcomeTransportLoop

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiErrorEnvelope
open Cordis.DeepSeekHarness
open Cordis.DeepSeekOutcomeConversation
open Cordis.DeepSeekStreamFailure
open Cordis.DeepSeekTerminalOutcome

inductive OutcomeTransportError where
  | request (error : RequestError)
  | transport (message : String)
  | httpStatus (status : Nat) (body : String)
  | outcome (error : TerminalOutcomeError)
  | apiEnvelope
      (status : Nat)
      (body : String)
      (error : DeepSeekApiErrorEnvelope.ValidationError)
  | execution (error : ExecutionError)
deriving DecidableEq, Repr

structure OutcomeTransportAssistant
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    {body : String} where
  plan : TypedRequestPlan .streaming
  outcome : TerminalOutcome body
  round : ExecutedRound cfg before body

inductive OutcomeTransportResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (body : String) where
  | providerFailure
      (plan : TypedRequestPlan .streaming)
      (validated : ValidatedFailureStream body)
      (runner : ConversationRunner)
  | apiFailure
      (plan : TypedRequestPlan .streaming)
      (status : Nat)
      (validated : ValidatedApiError body)
      (runner : ConversationRunner)
  | assistant (result : OutcomeTransportAssistant cfg before (body := body))

private def successfulStatus (status : Nat) : Bool := 200 ≤ status && status < 300

def executeOutcomeTransportRound
    {Model Capability : Type}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except OutcomeTransportError
      (Sigma fun body : String => OutcomeTransportResult cfg before body)) := do
  match buildTypedStreamingRequestPlan baseUrl apiKey source runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← transport.send plan.requestPlan.request with
      | .error message => pure (.error (.transport message))
      | .ok response =>
          if successfulStatus response.status then
            match validateTerminalOutcome response.body with
            | .error error => pure (.error (.outcome error))
            | .ok outcome =>
                match executeOutcomeWithTools cfg before runner outcome sourceEventSeqs
                    sourcesNodup sourcesEarlier with
                | .error error => pure (.error (.execution error))
                | .ok (.providerFailure validated failureRunner) =>
                    pure (.ok ⟨response.body, .providerFailure plan validated failureRunner⟩)
                | .ok (.assistant round) =>
                    pure (.ok ⟨response.body, .assistant {
                      plan
                      outcome
                      round
                    }⟩)
          else
            match validateApiError response.body with
            | .error error =>
                pure (.error (.apiEnvelope response.status response.body error))
            | .ok validated =>
                pure (.ok ⟨response.body, .apiFailure plan response.status validated runner⟩)

abbrev OutcomeTransportWitness
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) :=
  Sigma fun before : Model =>
    Sigma fun body : String => OutcomeTransportAssistant cfg before (body := body)

inductive OutcomeTransportStop
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  | completed (last : OutcomeTransportWitness cfg)
      (noCalls : last.2.2.round.executions.length = 0)
  | providerFailure
      {body : String}
      (validated : ValidatedFailureStream body)
      (runner : ConversationRunner)
  | apiFailure
      {body : String}
      (status : Nat)
      (validated : ValidatedApiError body)
      (runner : ConversationRunner)
  | fuelExhausted

structure OutcomeTransportRunResult
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability) where
  rounds : List (OutcomeTransportWitness cfg)
  runner : ConversationRunner
  finalModel : Model
  stop : OutcomeTransportStop cfg

def runOutcomeTransportAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner)
    (history : List (OutcomeTransportWitness cfg)) :
    IO (Except OutcomeTransportError (OutcomeTransportRunResult cfg)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeOutcomeTransportRound transport baseUrl apiKey source cfg before runner
          sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨_body, .providerFailure _ validated failureRunner⟩ =>
          pure (.ok {
            rounds := history
            runner := failureRunner
            finalModel := before
            stop := .providerFailure validated failureRunner
          })
      | .ok ⟨_body, .apiFailure _ status validated failureRunner⟩ =>
          pure (.ok {
            rounds := history
            runner := failureRunner
            finalModel := before
            stop := .apiFailure status validated failureRunner
          })
      | .ok ⟨body, .assistant assistant⟩ =>
          let witness : OutcomeTransportWitness cfg := ⟨before, ⟨body, assistant⟩⟩
          let nextHistory := history ++ [witness]
          if noCalls : assistant.round.executions.length = 0 then
            pure (.ok {
              rounds := nextHistory
              runner := assistant.round.runner
              finalModel := assistant.round.finalModel
              stop := .completed witness noCalls
            })
          else
            runOutcomeTransportAux fuel transport baseUrl apiKey source sourceEventSeqs
              sourcesNodup sourcesEarlier assistant.round.finalModel assistant.round.runner
              nextHistory

def runOutcomeTransport
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (fuel : Nat)
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except OutcomeTransportError (OutcomeTransportRunResult cfg)) :=
  runOutcomeTransportAux fuel transport baseUrl apiKey source sourceEventSeqs sourcesNodup
    sourcesEarlier before runner []

namespace Example

def sequenceTransport (calls : IO.Ref Nat) : Transport where
  send _request := do
    let index ← calls.get
    calls.set (index + 1)
    pure (.ok {
      status := 200
      body := if index = 0 then counterToolStreamBody
        else DeepSeekRichStream.exampleTextStreamBody
    })

def run : IO (Except OutcomeTransportError
    (OutcomeTransportRunResult Cordis.Harness.counterConfig)) := do
  let calls ← IO.mkRef 0
  runOutcomeTransport 2 (sequenceTransport calls) "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by simp) 0
    (ConversationRunner.empty 1)

def apiFailureTransport : Transport where
  send _request := pure (.ok {
    status := 429
    body := DeepSeekApiErrorEnvelope.exampleBody
  })

def apiFailureRun : IO (Except OutcomeTransportError
    (OutcomeTransportRunResult Cordis.Harness.counterConfig)) := do
  runOutcomeTransport 2 apiFailureTransport "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp) (by simp) 0
    (ConversationRunner.empty 1)

end Example

end Cordis.DeepSeekOutcomeTransportLoop
