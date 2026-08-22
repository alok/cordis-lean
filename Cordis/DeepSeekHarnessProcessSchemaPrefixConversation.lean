import Cordis.DeepSeekHarnessProcessSchemaPrefix

/-!
# Fuel-bounded prefix conversation provenance

`DeepSeekHarnessProcessSchemaPrefix` retains one prepared registry plan through a line-oriented
prefix round. This module lifts that result through the existing caller-fueled conversation loop:
each completed tool round carries its own prepared plan and accepted prefix, while fuel exhaustion
and cancellation retain the plan of the attempted round when one exists.

The result remains a local line-oriented certificate. It does not claim byte framing, blocked-read
interruption, reconnects, provider schema obedience, persistence, external tool trust, or deployed
Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessProcessSchemaPrefixConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlPrefix
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessProcessSchema
open Cordis.DeepSeekHarnessProcessSchemaPrefix
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSchemaStreamPrefixConversation
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekStreamIncremental
open Cordis.DeepSeekToolSchema

structure PreparedSchemaPrefixToolWitness
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (policy : LinePolicy)
    (runner : ConversationRunner) where
  prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner
  source_stream : prepared.plan.source.stream = true
  before : Model
  observed : PrefixResponse policy
  step : SchemaStreamToolResult registry runner before observed.state.body

abbrev PreparedSchemaPrefixRoundWitness
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (policy : LinePolicy) :=
  Sigma fun runner : ConversationRunner =>
    PreparedSchemaPrefixToolWitness baseUrl apiKey request policy runner

inductive PreparedSchemaPrefixConversationStop
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (policy : LinePolicy) : ConversationRunner → Model → Type where
  | completed
      {runner : ConversationRunner}
      {before : Model}
      {observed : PrefixResponse policy}
      (_prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
      (terminal : SchemaStreamTerminalResult registry runner before observed.state.body) :
      PreparedSchemaPrefixConversationStop baseUrl apiKey request policy runner before
  | fuelExhausted
      (runner : ConversationRunner)
      (before : Model) :
      PreparedSchemaPrefixConversationStop baseUrl apiKey request policy runner before
  | roundFuelExhausted
      {runner : ConversationRunner}
      {before : Model}
      (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
      (observed : PrefixResponse policy) :
      PreparedSchemaPrefixConversationStop baseUrl apiKey request policy runner before
  | cancelled
      {runner : ConversationRunner}
      {before : Model}
      (prepared : PreparedRegistryStreamingRequest registry baseUrl apiKey request runner)
      (observed : PrefixResponse policy)
      (line : Nat)
      (reason : String)
      (decided : policy.decide line = true) :
      PreparedSchemaPrefixConversationStop baseUrl apiKey request policy runner before

structure PreparedSchemaPrefixConversationRunResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (baseUrl : String)
    (apiKey : ApiKey)
    (request : RegistryRequestSource registry)
    (policy : LinePolicy) where
  rounds : List (PreparedSchemaPrefixRoundWitness baseUrl apiKey request policy)
  runner : ConversationRunner
  finalModel : Model
  stop : PreparedSchemaPrefixConversationStop baseUrl apiKey request policy runner finalModel

def runPreparedSchemaPrefixConversationAux
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
    (history : List (PreparedSchemaPrefixRoundWitness baseUrl apiKey request policy)) :
    IO (Except SchemaPrefixConversationError
      (PreparedSchemaPrefixConversationRunResult baseUrl apiKey request policy)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted runner before
      })
  | fuel + 1 =>
      match ← executeRegistrySchemaPrefixRound policy maxReads config baseUrl apiKey request
          before runner sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨prepared, round⟩ =>
          match round.outcome with
          | .fuelExhausted observed =>
              pure (.ok {
                rounds := history
                runner
                finalModel := before
                stop := .roundFuelExhausted prepared observed
              })
          | .cancelled observed line reason decided =>
              pure (.ok {
                rounds := history
                runner
                finalModel := before
                stop := .cancelled prepared observed line reason decided
              })
          | .completed completed =>
              match completed.step with
              | .terminal terminal =>
                  pure (.ok {
                    rounds := history
                    runner
                    finalModel := before
                    stop := .completed prepared terminal
                  })
              | .tools toolStep =>
                  let witness : PreparedSchemaPrefixRoundWitness baseUrl apiKey request policy :=
                    ⟨runner, {
                      prepared
                      source_stream := prepared.source_stream
                      before
                      observed := completed.observed
                      step := toolStep
                    }⟩
                  runPreparedSchemaPrefixConversationAux policy fuel maxReads config baseUrl apiKey
                    request sourceEventSeqs sourcesNodup sourcesEarlier toolStep.finalModel
                    toolStep.runner (history ++ [witness])

def runPreparedSchemaPrefixConversation
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
      (PreparedSchemaPrefixConversationRunResult baseUrl apiKey request policy)) :=
  runPreparedSchemaPrefixConversationAux policy fuel maxReads config baseUrl apiKey request
    sourceEventSeqs sourcesNodup sourcesEarlier before runner []

namespace Example

open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekSchemaHarness.Example

def dualToolPrefixConversationProvenanceRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (PreparedSchemaPrefixConversationRunResult
        "https://fixture.invalid" { value := "fixture-key" }
        (dualRequestSource weatherCertificate clockCertificate) (LinePolicy.never))) := do
  runPreparedSchemaPrefixConversation (LinePolicy.never) 1 64 dualToolStreamProcess
    "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

def dualToolPrefixConversationCancelled
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaPrefixConversationError
      (PreparedSchemaPrefixConversationRunResult
        "https://fixture.invalid" { value := "fixture-key" }
        (dualRequestSource weatherCertificate clockCertificate)
        (LinePolicy.atLine 1 "cancelled:prefix"))) := do
  runPreparedSchemaPrefixConversation (LinePolicy.atLine 1 "cancelled:prefix") 1 64
    dualToolStreamProcess "https://fixture.invalid" { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekHarnessProcessSchemaPrefixConversation
