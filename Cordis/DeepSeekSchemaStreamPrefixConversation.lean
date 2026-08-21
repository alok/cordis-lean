import Cordis.DeepSeekSchemaStreamConversation
import Cordis.DeepSeekCurlPrefix

/-!
# Line-prefix heterogeneous streamed schema conversation

This module carries the dependent schema registry through the existing line-oriented process
prefix boundary. Every complete response line is parsed before the next read; a line policy or
read budget returns its exact typed prefix instead of pretending that a terminal response was
received. Only a completed `[DONE]` body is projected through the rich-stream/session validator
and dispatched through the heterogeneous registry.

The adapter remains deliberately bounded. It does not claim byte framing, blocked-read
interruption, backpressure, reconnects, provider-complete assembly, call-ID authenticity,
persistence, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaStreamPrefixConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaConversationLoop
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamIncremental
open Cordis.DeepSeekToolSchema

inductive SchemaPrefixConversationError where
  | request (error : RequestError)
  | client (error : PrefixClientError)
  | response (error : DeepSeekSessionRunner.ResponseError)
  | execution (error : RegistryExecutionError)
deriving DecidableEq, Repr

structure SchemaPrefixCompleted
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (policy : LinePolicy)
    (runner : ConversationRunner)
    (before : Model) where
  observed : PrefixResponse policy
  step : SchemaStreamConversationStep registry runner before observed.state.body

inductive SchemaPrefixRoundOutcome
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (policy : LinePolicy)
    (runner : ConversationRunner)
    (before : Model) where
  | completed (result : SchemaPrefixCompleted registry policy runner before) :
      SchemaPrefixRoundOutcome registry policy runner before
  | fuelExhausted (observed : PrefixResponse policy) :
      SchemaPrefixRoundOutcome registry policy runner before
  | cancelled
      (observed : PrefixResponse policy)
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true) :
      SchemaPrefixRoundOutcome registry policy runner before

def executeSchemaStreamPrefixRound
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (policy : LinePolicy)
    (maxReads : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except SchemaPrefixConversationError
      (SchemaPrefixRoundOutcome registry policy runner before)) := do
  match CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
      (registryCertifiedRequestSource request) runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeSsePrefix policy maxReads config plan.request with
      | .error error => pure (.error (.client error))
      | .ok observed =>
          match observed.stop with
          | .fuelExhausted => pure (.ok (.fuelExhausted observed))
          | .cancelled line reason decided =>
              pure (.ok (.cancelled observed line reason decided))
          | .completed wire =>
              match finishMulti observed.state.body with
              | .error error => pure (.error (.response error))
              | .ok finished =>
                  let processed : ProcessedResponse observed.state.body := {
                    wire
                    finished
                  }
                  let calls := finishedFunctionCalls finished
                  if noToolCalls : calls = [] then
                    pure (.ok (.completed {
                      observed
                      step := .terminal {
                        processed
                        noToolCalls
                      }
                    }))
                  else
                    let assistantSeq := runner.session.nextSeq
                    let assistantRunner := ConversationRunner.appendFinished runner finished
                      sourceEventSeqs sourcesNodup sourcesEarlier
                    have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
                      rw [ConversationRunner.appendFinished_nextSeq]
                      exact Nat.lt_succ_self _
                    match executeSchemaRegistryCalls registry before calls with
                    | .error error => pure (.error (.execution error))
                    | .ok batch =>
                        let finalRunner := appendSchemaRegistryResultsToRunner assistantRunner
                          runner.nextCall assistantSeq batch.executions assistantSeqEarlier
                        pure (.ok (.completed {
                          observed
                          step := .tools {
                            processed
                            calls
                            batch
                            assistantRunner
                            runner := finalRunner
                            finalModel := batch.finalModel
                            assistantSeq
                            assistantSeq_eq := by
                              rw [ConversationRunner.appendFinished_nextSeq]
                            finalRunner_nextSeq := by
                              change (appendSchemaRegistryResultsToRunner assistantRunner
                                runner.nextCall assistantSeq batch.executions assistantSeqEarlier
                                ).session.nextSeq = _
                              rw [appendSchemaRegistryResultsToRunner_nextSeq]
                              rw [ConversationRunner.appendFinished_nextSeq]
                              simp [batch.length_eq]
                          }
                        }))

abbrev SchemaPrefixRoundWitness
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) :=
  Sigma fun runner : ConversationRunner =>
    Sigma fun before : Model =>
      Sigma fun body : String =>
        SchemaStreamToolResult registry runner before body

inductive SchemaPrefixConversationStop
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (policy : LinePolicy) : ConversationRunner → Model → Type where
  | completed
      {runner : ConversationRunner}
      {before : Model}
      {body : String}
      (observed : PrefixResponse policy)
      (terminal : SchemaStreamTerminalResult registry runner before body) :
      SchemaPrefixConversationStop registry policy runner before
  | fuelExhausted
      (runner : ConversationRunner)
      (before : Model) :
      SchemaPrefixConversationStop registry policy runner before
  | cancelled
      (runner : ConversationRunner)
      (before : Model)
      (observed : PrefixResponse policy)
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true) :
      SchemaPrefixConversationStop registry policy runner before

structure SchemaPrefixConversationRunResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (policy : LinePolicy) where
  rounds : List (SchemaPrefixRoundWitness registry)
  runner : ConversationRunner
  finalModel : Model
  stop : SchemaPrefixConversationStop registry policy runner finalModel

def runSchemaStreamPrefixConversationAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (policy : LinePolicy)
    (fuel : Nat)
    (maxReads : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner)
    (history : List (SchemaPrefixRoundWitness registry)) :
    IO (Except SchemaPrefixConversationError
      (SchemaPrefixConversationRunResult registry policy)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted runner before
      })
  | fuel + 1 =>
      match ← executeSchemaStreamPrefixRound policy maxReads config baseUrl apiKey request before
          runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok (.fuelExhausted _observed) =>
          pure (.ok {
            rounds := history
            runner
            finalModel := before
            stop := .fuelExhausted runner before
          })
      | .ok (.cancelled observed line reason decided) =>
          pure (.ok {
            rounds := history
            runner
            finalModel := before
            stop := .cancelled runner before observed line reason decided
          })
      | .ok (.completed completed) =>
          match completed.step with
          | .terminal terminal =>
              pure (.ok {
                rounds := history
                runner
                finalModel := before
                stop := .completed completed.observed terminal
              })
          | .tools toolStep =>
              let witness : SchemaPrefixRoundWitness registry :=
                ⟨runner, ⟨before, ⟨completed.observed.state.body, toolStep⟩⟩⟩
              runSchemaStreamPrefixConversationAux policy fuel maxReads config baseUrl apiKey
                request sourceEventSeqs sourcesNodup sourcesEarlier toolStep.finalModel
                toolStep.runner (history ++ [witness])

def runSchemaStreamPrefixConversation
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (policy : LinePolicy)
    (fuel maxReads : Nat)
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ current : ConversationRunner,
      ∀ source ∈ sourceEventSeqs, source < current.session.nextSeq)
    (before : Model)
    (runner : ConversationRunner) :
    IO (Except SchemaPrefixConversationError
      (SchemaPrefixConversationRunResult registry policy)) :=
  runSchemaStreamPrefixConversationAux policy fuel maxReads config baseUrl apiKey request
    sourceEventSeqs sourcesNodup sourcesEarlier before runner []

namespace Example

open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaConversationLoop.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekSchemaHarness.Example

def dualToolPrefixRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (SchemaPrefixConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate) (LinePolicy.never))) := do
  runSchemaStreamPrefixConversation (LinePolicy.never) 1 64 dualToolStreamProcess
    "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

def dualToolPrefixCancelled
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (SchemaPrefixConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate)
        (LinePolicy.atLine 1 "cancelled:prefix"))) := do
  runSchemaStreamPrefixConversation (LinePolicy.atLine 1 "cancelled:prefix") 1 64
    dualToolStreamProcess "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

def textTerminalPrefixRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (SchemaPrefixConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate) (LinePolicy.never))) := do
  runSchemaStreamPrefixConversation (LinePolicy.never) 1 64 fixtureTextProcess
    "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekSchemaStreamPrefixConversation
