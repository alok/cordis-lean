import Cordis.DeepSeekSchemaConversationLoop
import Cordis.DeepSeekStreamHarness

/-!
# Process-backed heterogeneous streamed schema conversation

`DeepSeekSchemaConversationLoop` covers a complete-body non-streaming registry round. This module
composes the same dependent registry with the existing strict SSE/rich-stream/session boundary:
the registry supplies a validated tool-list certificate, the request is indexed as streaming, a
complete process body is projected to a terminal rich response, and each streamed function call
is dispatched through entry-specific schema and generic bindings.

The loop is still deliberately finite and caller-fueled. It does not claim incremental reader
semantics, backpressure, cancellation of blocked reads, reconnects, provider-complete assembly,
call-ID authenticity, external effects, persistence, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaStreamConversation

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaConversationLoop
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekToolSchema

/-! ## Registry-derived provider schema certificate -/

def registryValidatedTools
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability} :
    (registry : SchemaToolRegistry cfg) →
      ValidatedToolList (registryToolDefinitions registry)
  | { entries := [], names_nodup := _ } => .nil
  | { entries := entry :: entries, names_nodup := names_nodup } =>
      .cons entry.binding.certificate (registryValidatedTools {
        entries := entries
        names_nodup := by
          exact (List.nodup_cons.mp names_nodup).2
      })

def registryCertifiedRequestSource
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (request : RegistryRequestSource registry) :
    CertifiedRequestSource request.source where
  tools := by
    simpa [registryToolDefinitions, request.tools_eq] using registryValidatedTools registry
  names_nodup := by
    simp only [request.tools_eq, registryToolDefinitions, List.map_map]
    have h := registry.names_nodup
    change (List.map (fun entry : SchemaToolEntry cfg => entry.tool.function.name)
      registry.entries).Nodup at h
    exact h

/-! ## One streamed registry round -/

inductive SchemaStreamConversationError where
  | request (error : RequestError)
  | client (error : SessionClientError)
  | execution (error : RegistryExecutionError)
deriving BEq, DecidableEq, Repr

structure SchemaStreamTerminalResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  processed : ProcessedResponse body
  noToolCalls : finishedFunctionCalls processed.finished = []

structure SchemaStreamToolResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  processed : ProcessedResponse body
  calls : List FunctionCall := finishedFunctionCalls processed.finished
  batch : RegistryExecutionBatch cfg before calls
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  finalModel : Model
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq
  finalRunner_nextSeq : runner.session.nextSeq = assistantRunner.session.nextSeq + calls.length

inductive SchemaStreamConversationStep
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  | terminal (result : SchemaStreamTerminalResult registry runner before body) :
      SchemaStreamConversationStep registry runner before body
  | tools (result : SchemaStreamToolResult registry runner before body) :
      SchemaStreamConversationStep registry runner before body

def executeSchemaStreamConversationStep
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
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
    IO (Except SchemaStreamConversationError
      (Sigma fun body : String =>
        SchemaStreamConversationStep registry runner before body)) := do
  match CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
      (registryCertifiedRequestSource request) runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeTypedStreamingWith finishMulti config plan with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, processed⟩ =>
          let calls := finishedFunctionCalls processed.finished
          if noToolCalls : calls = [] then
            pure (.ok ⟨body, .terminal {
              processed
              noToolCalls
            }⟩)
          else
            let assistantSeq := runner.session.nextSeq
            let assistantRunner := ConversationRunner.appendFinished runner processed.finished
              sourceEventSeqs sourcesNodup sourcesEarlier
            have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
              rw [ConversationRunner.appendFinished_nextSeq]
              exact Nat.lt_succ_self _
            match batchResult : executeSchemaRegistryCalls registry before calls with
            | .error error => pure (.error (.execution error))
            | .ok batch =>
                let finalRunner := appendSchemaRegistryResultsToRunner assistantRunner
                  runner.nextCall assistantSeq batch.executions assistantSeqEarlier
                pure (.ok ⟨body, .tools {
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
                    change (appendSchemaRegistryResultsToRunner assistantRunner runner.nextCall
                      assistantSeq batch.executions assistantSeqEarlier).session.nextSeq = _
                    rw [appendSchemaRegistryResultsToRunner_nextSeq]
                    rw [ConversationRunner.appendFinished_nextSeq]
                    simp [batch.length_eq]
                }⟩)

/-! ## Fuel-bounded streamed history -/

abbrev SchemaStreamRoundWitness
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) :=
  Sigma fun runner : ConversationRunner =>
    Sigma fun before : Model =>
      Sigma fun body : String =>
        SchemaStreamToolResult registry runner before body

inductive SchemaStreamConversationStop
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) : ConversationRunner → Model → Type where
  | completed
      {runner : ConversationRunner}
      {before : Model}
      {body : String}
      (terminal : SchemaStreamTerminalResult registry runner before body) :
      SchemaStreamConversationStop registry runner before
  | fuelExhausted
      (runner : ConversationRunner)
      (before : Model) :
      SchemaStreamConversationStop registry runner before

structure SchemaStreamConversationRunResult
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (registry : SchemaToolRegistry cfg) where
  rounds : List (SchemaStreamRoundWitness registry)
  runner : ConversationRunner
  finalModel : Model
  stop : SchemaStreamConversationStop registry runner finalModel

def runSchemaStreamConversationAux
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (fuel : Nat)
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
    (history : List (SchemaStreamRoundWitness registry)) :
    IO (Except SchemaStreamConversationError
      (SchemaStreamConversationRunResult registry)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted runner before
      })
  | fuel + 1 =>
      match ← executeSchemaStreamConversationStep config baseUrl apiKey request before runner
          sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨_body, .terminal terminal⟩ =>
          pure (.ok {
            rounds := history
            runner
            finalModel := before
            stop := .completed terminal
          })
      | .ok ⟨body, .tools toolStep⟩ =>
          let witness : SchemaStreamRoundWitness registry :=
            ⟨runner, ⟨before, ⟨body, toolStep⟩⟩⟩
          runSchemaStreamConversationAux fuel config baseUrl apiKey request sourceEventSeqs
            sourcesNodup sourcesEarlier toolStep.finalModel toolStep.runner
            (history ++ [witness])

def runSchemaStreamConversation
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    (fuel : Nat)
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
    IO (Except SchemaStreamConversationError
      (SchemaStreamConversationRunResult registry)) :=
  runSchemaStreamConversationAux fuel config baseUrl apiKey request sourceEventSeqs sourcesNodup
    sourcesEarlier before runner []

/-! ## Executable heterogeneous streamed fixtures -/

namespace Example

open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaConversation.Example
open Cordis.DeepSeekSchemaHarness.Example

def dualToolStartJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-schema-stream"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 0)),
          ("id", .str "schema-stream-weather"),
          ("type", .str "function"),
          ("function", .mkObj [
            ("name", .str "get_weather"),
            ("arguments", .str "{\"city\":\"San Francisco\"}")
          ])
        ],
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 1)),
          ("id", .str "schema-stream-clock"),
          ("type", .str "function"),
          ("function", .mkObj [
            ("name", .str "get_time"),
            ("arguments", .str "{\"city\":\"New York\"}")
          ])
        ]
      ])
    ]),
    ("finish_reason", .null)
  ]]),
  ("usage", .null)
]

def dualToolFinishJson : Lean.Json := .mkObj [
  ("id", .str "chatcmpl-schema-stream"),
  ("model", .str "deepseek-reasoner"),
  ("choices", .arr #[.mkObj [
    ("index", .num (Lean.JsonNumber.fromNat 0)),
    ("delta", .mkObj [
      ("tool_calls", .arr #[
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 0)),
          ("function", .mkObj [("arguments", .str "")])
        ],
        .mkObj [
          ("index", .num (Lean.JsonNumber.fromNat 1)),
          ("function", .mkObj [("arguments", .str "")])
        ]
      ])
    ]),
    ("finish_reason", .str "tool_calls")
  ]]),
  ("usage", .mkObj [
    ("prompt_tokens", .num (Lean.JsonNumber.fromNat 5)),
    ("completion_tokens", .num (Lean.JsonNumber.fromNat 7)),
    ("total_tokens", .num (Lean.JsonNumber.fromNat 12))
  ])
]

def dualToolStreamBody : String :=
  "data: " ++ Lean.Json.compress dualToolStartJson ++ "\n\n" ++
  "data: " ++ Lean.Json.compress dualToolFinishJson ++ "\n\n" ++
  "data: [DONE]\n\n"

def dualToolStreamProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-schema-stream-fixture",
    dualToolStreamBody
  ]

def dualToolStreamRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaStreamConversationError
      (SchemaStreamConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate))) := do
  runSchemaStreamConversation 1 dualToolStreamProcess "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

def textTerminalRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaStreamConversationError
      (SchemaStreamConversationRunResult
        (dualRegistryEntries weatherCertificate clockCertificate))) := do
  runSchemaStreamConversation 1 DeepSeekCurlSession.fixtureTextProcess "https://fixture.invalid"
    { value := "fixture-key" }
    (dualRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekSchemaStreamConversation
