import Cordis.DeepSeekSchemaMultiRound

/-!
# A heterogeneous schema-tool registry

`DeepSeekSchemaMultiRound` deliberately fixes one `SchemaToolBinding` for every call. This module
adds the next type-level seam: a finite registry whose entries may bind different provider
`ToolDefinition`s to different generic catalog operations. Name lookup returns the dependent
entry and the exact name equality used for admission; the registry also carries name uniqueness,
so a successful lookup is deterministic.

The execution and runner result are still pure and bounded. Unknown names, schema/admission
failures, policy failures, and provider failures remain typed. This module does not claim a
provider-complete registry, remote transport, call-ID authenticity, model obedience, persistence,
or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaRegistry

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekHarness
open Cordis.DeepSeekSchemaExecution
open Cordis.DeepSeekSchemaHarness
open Cordis.DeepSeekSchemaMultiRound
open Cordis.DeepSeekToolAdmission
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-! ## Dependent registry data and lookup -/

structure SchemaToolEntry
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  tool : ToolDefinition
  binding : SchemaToolBinding cfg tool

namespace SchemaToolEntry

def name
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (entry : SchemaToolEntry cfg) : String :=
  entry.tool.function.name

end SchemaToolEntry

structure SchemaToolRegistry
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  entries : List (SchemaToolEntry cfg)
  names_nodup : (entries.map SchemaToolEntry.name).Nodup

def resolveSchemaTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (name : String) :
    Option { entry : SchemaToolEntry cfg // name = entry.name } :=
  let rec loop : List (SchemaToolEntry cfg) ->
      Option { entry : SchemaToolEntry cfg // name = entry.name }
    | [] => none
    | entry :: rest =>
        if equality : name = entry.name then
          some ⟨entry, equality⟩
        else
          loop rest
  loop registry.entries

theorem resolveSchemaTool_sound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (name : String)
    {entry : SchemaToolEntry cfg}
    (equality : name = entry.name)
    (_resolved : resolveSchemaTool registry name = some ⟨entry, equality⟩) :
    name = entry.name :=
  equality

theorem resolveSchemaTool_unique_name
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (name : String)
    {left right : SchemaToolEntry cfg}
    {leftEq : name = left.name}
    {rightEq : name = right.name}
    (_leftResolved : resolveSchemaTool registry name = some ⟨left, leftEq⟩)
    (_rightResolved : resolveSchemaTool registry name = some ⟨right, rightEq⟩) :
    left.name = right.name := by
  exact leftEq.symm.trans rightEq

/-! ## Heterogeneous execution -/

inductive RegistryExecutionError where
  | unknownTool (index : Nat) (name : String)
  | execution (index : Nat) (error : ExecutionError)
deriving BEq, DecidableEq, Repr

inductive AnyRegistryExecutedTool
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  | mk
      {entry : SchemaToolEntry cfg}
      (raw : FunctionCall)
      (before : Model)
      (call : cfg.Call)
      (executed : SchemaExecutedTool entry.binding raw before call)
      (name_eq : raw.name = entry.name)
      (execution_eq :
        executeCertifiedFunctionCall entry.binding before raw =
          .ok ⟨call, executed⟩) :
      AnyRegistryExecutedTool cfg

namespace AnyRegistryExecutedTool

def after
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (attempt : AnyRegistryExecutedTool cfg) : Model :=
  match attempt with
  | .mk _ _ _ executed _ _ => executed.executed.reply.value.after

def toExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (attempt : AnyRegistryExecutedTool cfg) : DeepSeekHarness.ExecutedTool cfg :=
  match attempt with
  | .mk _ _ _ executed _ _ => executed.toExecutedTool

end AnyRegistryExecutedTool

structure RegistryExecutionBatch
    {Model Capability : Type}
    (cfg : Config Model Capability)
    (before : Model)
    (calls : List FunctionCall) where
  finalModel : Model
  executions : List (AnyRegistryExecutedTool cfg)
  length_eq : executions.length = calls.length

def toExecutedTools
    {Model Capability : Type}
    {cfg : Config Model Capability} :
    List (AnyRegistryExecutedTool cfg) -> List (DeepSeekHarness.ExecutedTool cfg)
  | [] => []
  | attempt :: rest => attempt.toExecutedTool :: toExecutedTools rest

@[simp] theorem toExecutedTools_length
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (executions : List (AnyRegistryExecutedTool cfg)) :
    (toExecutedTools executions).length = executions.length := by
  induction executions with
  | nil => rfl
  | cons head tail inductionHypothesis => simp [toExecutedTools, inductionHypothesis]

def executeSchemaRegistryCallsAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (before : Model)
    (index : Nat) :
    (calls : List FunctionCall) ->
      Except RegistryExecutionError (RegistryExecutionBatch cfg before calls)
  | [] => .ok {
      finalModel := before
      executions := []
      length_eq := rfl
    }
  | raw :: rest =>
      match resolved : resolveSchemaTool registry raw.name with
      | none => .error (.unknownTool index raw.name)
      | some ⟨entry, name_eq⟩ =>
          match execution_eq : executeCertifiedFunctionCall entry.binding before raw with
          | .error error => .error (.execution index error)
          | .ok ⟨call, executed⟩ =>
              let head : AnyRegistryExecutedTool cfg :=
                .mk raw before call executed (name_eq ▸ rfl) execution_eq
              match executeSchemaRegistryCallsAux registry head.after (index + 1) rest with
              | .error error => .error error
              | .ok suffix => .ok {
                  finalModel := suffix.finalModel
                  executions := head :: suffix.executions
                  length_eq := by
                    simp only [List.length_cons]
                    rw [suffix.length_eq]
                }

def executeSchemaRegistryCalls
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (before : Model)
    (calls : List FunctionCall) :
    Except RegistryExecutionError (RegistryExecutionBatch cfg before calls) :=
  executeSchemaRegistryCallsAux registry before 0 calls

/-! ## Runner bridge -/

def appendSchemaRegistryResultsToRunner
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (AnyRegistryExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    ConversationRunner :=
  ConversationRunner.appendToolResults runner baseCall assistantSeq
    (toExecutedTools executions) assistantSeqEarlier

theorem appendSchemaRegistryResultsToRunner_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (AnyRegistryExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendSchemaRegistryResultsToRunner runner baseCall assistantSeq executions
      assistantSeqEarlier).session.nextSeq =
      runner.session.nextSeq + executions.length := by
  change (DeepSeekHarness.appendExecutedToolResults runner.session runner.turn runner.step
      baseCall assistantSeq (toExecutedTools executions) assistantSeqEarlier).nextSeq = _
  rw [DeepSeekHarness.appendExecutedToolResults_nextSeq]
  rw [toExecutedTools_length]

theorem appendSchemaRegistryResultsToRunner_session_messages
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (AnyRegistryExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendSchemaRegistryResultsToRunner runner baseCall assistantSeq executions
      assistantSeqEarlier).session.messages =
      runner.session.messages ++ DeepSeekHarness.executedToolMessages baseCall
        (toExecutedTools executions) := by
  exact ConversationRunner.appendToolResults_session_messages runner baseCall assistantSeq
    (toExecutedTools executions) assistantSeqEarlier

/-! ## Complete heterogeneous registry round -/

structure SchemaRegistryRoundResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    {body : String}
    (accepted : AcceptedToolCalls body)
    (batch : RegistryExecutionBatch cfg before accepted.calls) where
  assistantRunner : ConversationRunner
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq
  assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq
  finalRunner : ConversationRunner
  finalRunner_eq :
    finalRunner = appendSchemaRegistryResultsToRunner assistantRunner runner.nextCall
      assistantSeq batch.executions assistantSeqEarlier

inductive RegistryRoundError where
  | response (error : ApiSessionError)
  | noToolCalls
  | execution (error : RegistryExecutionError)
deriving BEq, DecidableEq, Repr

def executeSchemaRegistryRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (registry : SchemaToolRegistry cfg)
    (before : Model)
    (body : String)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    Except RegistryRoundError
      (Sigma fun accepted : AcceptedToolCalls body =>
        Sigma fun batch : RegistryExecutionBatch cfg before accepted.calls =>
          SchemaRegistryRoundResult registry runner before accepted batch) :=
  match acceptToolCalls body with
  | .error (.response error) => .error (.response error)
  | .error .noToolCalls => .error .noToolCalls
  | .error (.execution index error) => .error (.execution (.execution index error))
  | .ok accepted =>
      let assistantSeq := runner.session.nextSeq
      let assistantRunner := ConversationRunner.appendAcceptedApi runner accepted.accepted
        sourceEventSeqs sourcesNodup sourcesEarlier
      have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
        rw [ConversationRunner.appendAcceptedApi_nextSeq]
        exact Nat.lt_succ_self _
      match executeSchemaRegistryCalls registry before accepted.calls with
      | .error error => .error (.execution error)
      | .ok batch =>
          let finalRunner := appendSchemaRegistryResultsToRunner assistantRunner runner.nextCall
            assistantSeq batch.executions assistantSeqEarlier
          .ok ⟨accepted, ⟨batch, {
            assistantRunner
            assistantSeq
            assistantSeq_eq := by
              change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
              rw [ConversationRunner.appendAcceptedApi_nextSeq]
            assistantSeqEarlier
            finalRunner
            finalRunner_eq := rfl
          }⟩⟩

theorem SchemaRegistryRoundResult.finalRunner_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {registry : SchemaToolRegistry cfg}
    {runner : ConversationRunner}
    {before : Model}
    {body : String}
    {accepted : AcceptedToolCalls body}
    {batch : RegistryExecutionBatch cfg before accepted.calls}
    (result : SchemaRegistryRoundResult registry runner before accepted batch) :
    result.finalRunner.session.nextSeq =
      result.assistantRunner.session.nextSeq + batch.executions.length := by
  rw [result.finalRunner_eq]
  exact appendSchemaRegistryResultsToRunner_nextSeq result.assistantRunner runner.nextCall
    result.assistantSeq batch.executions result.assistantSeqEarlier

/-! ## Executable heterogeneous registry fixture -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example

inductive DualOperation where
  | weather
  | clock
deriving BEq, DecidableEq, Repr

def dualWeatherSpec : ToolSpec Nat Capability where
  name := "get_weather"
  description := "Accept a certified weather request"
  Input := Lean.Json
  Output _ := String
  Failure _ := String
  pre _ _ := True
  post _ before _ after := after = before
  required _ capability := capability = .invoke
  emission := .externalIdempotent

def dualClockSpec : ToolSpec Nat Capability where
  name := "get_time"
  description := "Accept a certified clock request"
  Input := Lean.Json
  Output _ := String
  Failure _ := String
  pre _ _ := True
  post _ before _ after := after = before
  required _ capability := capability = .invoke
  emission := .externalIdempotent

def dualCatalog : ToolCatalog Nat Capability where
  Tool := DualOperation
  toolDecEq := inferInstance
  spec
    | .weather => dualWeatherSpec
    | .clock => dualClockSpec

def dualWeatherImplementation :
    ToolSpec.VerifiedTool (dualCatalog.spec .weather) where
  execute invocation := {
    result := .ok "weather"
    after := invocation.before
    postcondition := rfl
  }

def dualClockImplementation :
    ToolSpec.VerifiedTool (dualCatalog.spec .clock) where
  execute invocation := {
    result := .ok "clock"
    after := invocation.before
    postcondition := rfl
  }

def dualWeatherProvider : Provider dualCatalog.signature .weather :=
  dualCatalog.provider .weather
    { domain := "example.deepseek"
      name := "weather"
      major := 1 }
    dualWeatherImplementation

def dualClockProvider : Provider dualCatalog.signature .clock :=
  dualCatalog.provider .clock
    { domain := "example.deepseek"
      name := "clock"
      major := 1 }
    dualClockImplementation

def dualRegistry : Registry dualCatalog.signature
  | .weather => some dualWeatherProvider
  | .clock => some dualClockProvider

def dualView : View dualCatalog.signature dualRegistry
    (fun _ => True) where
  resolve operation _ := by
    cases operation
    · exact { provider := dualWeatherProvider, present := rfl }
    · exact { provider := dualClockProvider, present := rfl }

def dualWire : ToolWire dualCatalog where
  resolve
    | "get_weather" => some .weather
    | "get_time" => some .clock
    | _ => none
  resolve_name tool := by cases tool <;> rfl
  inputCodec
    | .weather => jsonObjectCodec
    | .clock => jsonObjectCodec
  outputCodec
    | .weather, _ => Codec.string
    | .clock, _ => Codec.string
  failureCodec
    | .weather, _ => Codec.string
    | .clock, _ => Codec.string
  certifyAdmission tool _ _ granted grantedDecidable := by
    cases tool
    · match grantedDecidable .invoke with
      | .isFalse _ => exact .error "invoke capability is not granted"
      | .isTrue hasInvoke =>
          exact .ok {
            precondition := trivial
            authorized := by
              intro capability required
              change capability = Capability.invoke at required
              subst capability
              exact hasInvoke
          }
    · match grantedDecidable .invoke with
      | .isFalse _ => exact .error "invoke capability is not granted"
      | .isTrue hasInvoke =>
          exact .ok {
            precondition := trivial
            authorized := by
              intro capability required
              change capability = Capability.invoke at required
              subst capability
              exact hasInvoke
          }

def dualConfig : GenericHarness.Config Nat Capability where
  catalog := dualCatalog
  wire := dualWire
  needs := fun _ => True
  needsDecidable := fun _ => isTrue trivial
  registry := dualRegistry
  view := dualView
  granted := fun _ _ _ => True
  grantedDecidable := fun _ _ _ => isTrue trivial
  PolicyRejected := fun _ => String
  renderPolicyRejected := fun _ reason => reason
  decide := fun _ _ _ => .allow

def clockTool : ToolDefinition where
  function := {
    name := "get_time"
    description := some "Read the local time for a city."
    parameters := .mkObj [
      ("type", .str "object"),
      ("properties", .mkObj [("city", .mkObj [("type", .str "string")])]),
      ("required", .arr #[.str "city"]),
      ("additionalProperties", .bool false)
    ]
    strict := some true
  }

def clockToolCertificate :
    Except ToolSchemaError (ValidatedToolDefinition clockTool) :=
  validateToolDefinition clockTool

def dualWeatherBinding
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    SchemaToolBinding dualConfig DeepSeekApi.exampleTool where
  certificate := certificate
  genericTool := .weather
  name_eq := rfl

def dualClockBinding
    (certificate : ValidatedToolDefinition clockTool) :
    SchemaToolBinding dualConfig clockTool where
  certificate := certificate
  genericTool := .clock
  name_eq := rfl

def dualRegistryEntries
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    SchemaToolRegistry dualConfig where
  entries := [
    { tool := DeepSeekApi.exampleTool
      binding := dualWeatherBinding weatherCertificate },
    { tool := clockTool
      binding := dualClockBinding clockCertificate }
  ]
  names_nodup := by
    simp [SchemaToolEntry.name, DeepSeekApi.exampleTool, clockTool]

def dualResponseBody : String :=
  Lean.Json.compress
    (DeepSeekSchemaMultiRound.Example.twoWeatherResponseJson
      "get_time" "{\"city\":\"New York\"}")

def dualRound
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    Except RegistryRoundError
      (Sigma fun accepted : AcceptedToolCalls dualResponseBody =>
        Sigma fun batch : RegistryExecutionBatch dualConfig 0 accepted.calls =>
          SchemaRegistryRoundResult (dualRegistryEntries weatherCertificate clockCertificate)
            DeepSeekSchemaHarness.Example.counterRunner 0 accepted batch) :=
  executeSchemaRegistryRound DeepSeekSchemaHarness.Example.counterRunner
    (dualRegistryEntries weatherCertificate clockCertificate) 0 dualResponseBody []
    (by simp) (by simp)

def dualRoundAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match dualRound weatherCertificate clockCertificate with
      | .ok ⟨_, ⟨batch, _⟩⟩ => batch.executions.length == 2
      | .error _ => false
  | _, _ => false

def dualRoundFinalNextSeq : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match dualRound weatherCertificate clockCertificate with
      | .ok ⟨_, ⟨batch, result⟩⟩ =>
          result.finalRunner.session.nextSeq ==
              DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3 &&
            batch.finalModel == 0
      | .error _ => false
  | _, _ => false

def unknownToolRejected : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      let registry := dualRegistryEntries weatherCertificate clockCertificate
      let body := Lean.Json.compress
        (DeepSeekSchemaMultiRound.Example.twoWeatherResponseJson
          "unknown_weather" "{\"city\":\"New York\"}")
      match acceptToolCalls body with
      | .error _ => false
      | .ok accepted =>
          match executeSchemaRegistryCalls registry 0 accepted.calls with
          | .error (.unknownTool 1 "unknown_weather") => true
          | _ => false
  | _, _ => false

end Example

end Cordis.DeepSeekSchemaRegistry
