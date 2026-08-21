import Cordis.DeepSeekHarnessErrors
import Cordis.DeepSeekSchemaStreamConversation

/-!
# Recoverable provider failures in the heterogeneous streamed schema harness

`DeepSeekSchemaStreamConversation` dispatches every admitted call through a dependent registry,
but its ordinary execution path is fail-closed: a provider failure aborts the round.  This module
adds the explicit opt-in continuation policy for that path.  A failed entry retains its schema,
generic admission, policy, exact error string, and unchanged model; it is then converted to the
existing proof-carrying `ProviderFailedTool` surface so the session appends an `isError` result.

The loop is complete-body after the strict SSE process boundary.  It does not claim byte framing,
blocked-read interruption, backpressure, reconnects, retries, persistence, provider-complete
assembly, call-ID authenticity, external effects, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekSchemaStreamErrors

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekCurlSession
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessErrors
open Cordis.DeepSeekGenericBridge
open Cordis.DeepSeekSchemaConversation
open Cordis.DeepSeekSchemaRegistry
open Cordis.DeepSeekSchemaStreamConversation
open Cordis.DeepSeekSchemaHarness
open Cordis.DeepSeekSessionRunner
open Cordis.DeepSeekStreamHarness
open Cordis.DeepSeekToolSchema
open Cordis.GenericHarness

/-! ## Dependent recoverable attempts -/

structure RegistryExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (entry : SchemaToolEntry cfg)
    (raw : FunctionCall)
    (before : Model)
    (call : cfg.Call) where
  executed : SchemaExecutedTool entry.binding raw before call
  name_eq : raw.name = entry.name

namespace RegistryExecutedTool

def after
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {entry : SchemaToolEntry cfg}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : RegistryExecutedTool entry raw before call) : Model :=
  executed.executed.executed.reply.value.after

def toExecutedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {entry : SchemaToolEntry cfg}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (executed : RegistryExecutedTool entry raw before call) :
    DeepSeekHarness.ExecutedTool cfg :=
  executed.executed.toExecutedTool

end RegistryExecutedTool

structure RegistryProviderFailedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (entry : SchemaToolEntry cfg)
    (raw : FunctionCall)
    (before : Model)
    (call : cfg.Call) where
  beforeModel : Model := before
  checked : SchemaCheckedCall entry.binding raw before call
  policy : cfg.decide before {
      name := raw.name
      arguments := checked.provider.arguments.json
    } call = .allow
  message : String
  execution : cfg.view.execute call = .error message
  name_eq : raw.name = entry.name

namespace RegistryProviderFailedTool

def toProviderFailedTool
    {Model Capability : Type}
    {cfg : Config Model Capability}
    {entry : SchemaToolEntry cfg}
    {raw : FunctionCall}
    {before : Model}
    {call : cfg.Call}
    (failed : RegistryProviderFailedTool entry raw before call) :
    ProviderFailedTool cfg :=
  {
    raw := raw
    before := before
    parsed := failed.checked.provider.arguments.json
    parsed_eq := failed.checked.provider.arguments.parsed_eq
    call := call
    validation := failed.checked.validation
    policy := failed.policy
    message := failed.message
    execution := failed.execution
  }

end RegistryProviderFailedTool

inductive RegistryRecoverableAttempt
    {Model Capability : Type}
    (cfg : Config Model Capability) where
  | succeeded
      {entry : SchemaToolEntry cfg}
      {raw : FunctionCall}
      {before : Model}
      {call : cfg.Call}
      (executed : RegistryExecutedTool entry raw before call) :
      RegistryRecoverableAttempt cfg
  | providerFailed
      {entry : SchemaToolEntry cfg}
      {raw : FunctionCall}
      {before : Model}
      {call : cfg.Call}
      (failed : RegistryProviderFailedTool entry raw before call) :
      RegistryRecoverableAttempt cfg

namespace RegistryRecoverableAttempt

def after
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (attempt : RegistryRecoverableAttempt cfg) : Model :=
  match attempt with
  | .succeeded executed => executed.after
  | .providerFailed failed => failed.beforeModel

def toRecoverableToolAttempt
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (attempt : RegistryRecoverableAttempt cfg) : RecoverableToolAttempt cfg :=
  match attempt with
  | .succeeded executed => .succeeded executed.toExecutedTool
  | .providerFailed failed => .providerFailed failed.toProviderFailedTool

end RegistryRecoverableAttempt

structure RegistryRecoverableBatch
    {Model Capability : Type}
    (cfg : Config Model Capability)
    (before : Model)
    (calls : List FunctionCall) where
  finalModel : Model
  attempts : List (RegistryRecoverableAttempt cfg)
  length_eq : attempts.length = calls.length

def executeSchemaRegistryFunctionCallRecoverable
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (before : Model)
    (index : Nat)
    (raw : FunctionCall) :
    Except RegistryExecutionError (RegistryRecoverableAttempt cfg) :=
  match _resolved : resolveSchemaTool registry raw.name with
  | none => .error (.unknownTool index raw.name)
  | some ⟨entry, name_eq⟩ =>
      match _admission_eq : validateAndAdmit entry.binding before raw with
      | .error error => .error (.execution index (.admission error))
      | .ok ⟨call, checked⟩ =>
          let genericRaw : RawCall := {
            name := raw.name
            arguments := checked.provider.arguments.json
          }
          match policy_eq : cfg.decide before genericRaw call with
          | .reject decision _ reason =>
              .error (.execution index (.policy decision
                (cfg.renderPolicyRejected call reason)))
          | .allow =>
              match execution_eq : cfg.view.execute call with
              | .error message =>
                  .ok (.providerFailed {
                    checked
                    policy := policy_eq
                    message
                    execution := execution_eq
                    name_eq
                  })
              | .ok reply =>
                  .ok (.succeeded {
                    executed := {
                      executed := {
                        checked
                        reply
                        policy := policy_eq
                        execution := execution_eq
                      }
                    }
                    name_eq
                  })

def executeSchemaRegistryCallsRecoverableAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (before : Model)
    (index : Nat) :
    (calls : List FunctionCall) →
      Except RegistryExecutionError (RegistryRecoverableBatch cfg before calls)
  | [] => .ok {
      finalModel := before
      attempts := []
      length_eq := rfl
    }
  | raw :: rest =>
      match executeSchemaRegistryFunctionCallRecoverable registry before index raw with
      | .error error => .error error
      | .ok attempt =>
          match executeSchemaRegistryCallsRecoverableAux registry attempt.after
              (index + 1) rest with
          | .error error => .error error
          | .ok suffix => .ok {
              finalModel := suffix.finalModel
              attempts := attempt :: suffix.attempts
              length_eq := by
                simp only [List.length_cons]
                rw [suffix.length_eq]
            }

def executeSchemaRegistryCallsRecoverable
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (before : Model)
    (calls : List FunctionCall) :
    Except RegistryExecutionError (RegistryRecoverableBatch cfg before calls) :=
  executeSchemaRegistryCallsRecoverableAux registry before 0 calls

/-! ## Session/runner conversion -/

def registryRecoverableAttempts
    {Model Capability : Type}
    {cfg : Config Model Capability} :
    List (RegistryRecoverableAttempt cfg) → List (RecoverableToolAttempt cfg)
  | [] => []
  | attempt :: rest =>
      attempt.toRecoverableToolAttempt :: registryRecoverableAttempts rest

@[simp] theorem registryRecoverableAttempts_length
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (attempts : List (RegistryRecoverableAttempt cfg)) :
    (registryRecoverableAttempts attempts).length = attempts.length := by
  induction attempts with
  | nil => rfl
  | cons head tail inductionHypothesis => simp [registryRecoverableAttempts, inductionHypothesis]

def appendSchemaRegistryRecoverableResultsToRunner
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (attempts : List (RegistryRecoverableAttempt cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    ConversationRunner :=
  ConversationRunner.appendRecoverableToolResults runner baseCall assistantSeq
    (registryRecoverableAttempts attempts) assistantSeqEarlier

theorem appendSchemaRegistryRecoverableResultsToRunner_session_messages
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (attempts : List (RegistryRecoverableAttempt cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendSchemaRegistryRecoverableResultsToRunner runner baseCall assistantSeq attempts
      assistantSeqEarlier).session.messages =
      runner.session.messages ++
        recoverableToolMessages baseCall (registryRecoverableAttempts attempts) := by
  exact ConversationRunner.appendRecoverableToolResults_session_messages runner baseCall
    assistantSeq (registryRecoverableAttempts attempts) assistantSeqEarlier

theorem appendSchemaRegistryRecoverableResultsToRunner_nextSeq
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (runner : ConversationRunner)
    (baseCall assistantSeq : Nat)
    (attempts : List (RegistryRecoverableAttempt cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendSchemaRegistryRecoverableResultsToRunner runner baseCall assistantSeq attempts
      assistantSeqEarlier).session.nextSeq =
      runner.session.nextSeq + attempts.length := by
  rw [appendSchemaRegistryRecoverableResultsToRunner]
  rw [ConversationRunner.appendRecoverableToolResults_nextSeq]
  rw [registryRecoverableAttempts_length]

/-! ## One streamed recoverable round and fuel-bounded continuation -/

inductive SchemaStreamRecoverableConversationError where
  | request (error : RequestError)
  | client (error : SessionClientError)
  | execution (error : RegistryExecutionError)
deriving DecidableEq, Repr

structure SchemaStreamRecoverableRoundResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg)
    (runner : ConversationRunner)
    (before : Model)
    (body : String) where
  processed : ProcessedResponse body
  assistantRunner : ConversationRunner
  runner : ConversationRunner
  batch : RegistryRecoverableBatch cfg before (finishedFunctionCalls processed.finished)
  attempts_eq :
    executeSchemaRegistryCallsRecoverable registry before
      (finishedFunctionCalls processed.finished) = .ok batch
  assistantSeq : Nat
  assistantSeq_eq : assistantSeq + 1 = assistantRunner.session.nextSeq

def executeSchemaStreamRecoverableRound
    {Model Capability : Type}
    {cfg : Config Model Capability}
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
    IO (Except SchemaStreamRecoverableConversationError
      (Sigma fun body : String =>
        SchemaStreamRecoverableRoundResult registry runner before body)) := do
  match CertifiedRequestSource.buildTypedStreamingRequestPlan baseUrl apiKey
      (registryCertifiedRequestSource request) runner.session with
  | .error error => pure (.error (.request error))
  | .ok plan =>
      match ← executeTypedStreamingWith finishMulti config plan with
      | .error error => pure (.error (.client error))
      | .ok ⟨body, processed⟩ =>
          let assistantSeq := runner.session.nextSeq
          let assistantRunner := ConversationRunner.appendFinished runner processed.finished
            sourceEventSeqs sourcesNodup sourcesEarlier
          have assistantSeqEarlier : assistantSeq < assistantRunner.session.nextSeq := by
            rw [ConversationRunner.appendFinished_nextSeq]
            exact Nat.lt_succ_self _
          match attemptEq : executeSchemaRegistryCallsRecoverable registry before
              (finishedFunctionCalls processed.finished) with
          | .error error => pure (.error (.execution error))
          | .ok batch =>
              let finalRunner := appendSchemaRegistryRecoverableResultsToRunner assistantRunner
                runner.nextCall assistantSeq batch.attempts assistantSeqEarlier
              pure (.ok ⟨body, {
                processed
                assistantRunner
                runner := finalRunner
                batch
                attempts_eq := attemptEq
                assistantSeq
                assistantSeq_eq := by
                  change runner.session.nextSeq + 1 = assistantRunner.session.nextSeq
                  rw [ConversationRunner.appendFinished_nextSeq]
              }⟩)

structure SchemaStreamRecoverableRoundWitness
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg) where
  sourceRunner : ConversationRunner
  before : Model
  body : String
  result : SchemaStreamRecoverableRoundResult registry sourceRunner before body

inductive SchemaStreamRecoverableStop
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg) where
  | completed
      (last : SchemaStreamRecoverableRoundWitness registry)
      (noToolCalls : finishedFunctionCalls last.result.processed.finished = []) :
      SchemaStreamRecoverableStop registry
  | fuelExhausted : SchemaStreamRecoverableStop registry

structure SchemaStreamRecoverableRunResult
    {Model Capability : Type}
    {cfg : Config Model Capability}
    (registry : SchemaToolRegistry cfg) where
  rounds : List (SchemaStreamRecoverableRoundWitness registry)
  runner : ConversationRunner
  finalModel : Model
  stop : SchemaStreamRecoverableStop registry

def runSchemaStreamRecoverableAux
    {Model Capability : Type}
    {cfg : Config Model Capability}
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
    (history : List (SchemaStreamRecoverableRoundWitness registry)) :
    IO (Except SchemaStreamRecoverableConversationError
      (SchemaStreamRecoverableRunResult registry)) := do
  match fuel with
  | 0 =>
      pure (.ok {
        rounds := history
        runner
        finalModel := before
        stop := .fuelExhausted
      })
  | fuel + 1 =>
      match ← executeSchemaStreamRecoverableRound config baseUrl apiKey request before runner
          sourceEventSeqs sourcesNodup (sourcesEarlier runner) with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ =>
          let witness : SchemaStreamRecoverableRoundWitness registry := {
            sourceRunner := runner
            before
            body
            result := round
          }
          if noTools : finishedFunctionCalls round.processed.finished = [] then
            pure (.ok {
              rounds := history ++ [witness]
              runner := round.runner
              finalModel := round.batch.finalModel
              stop := .completed witness noTools
            })
          else
            runSchemaStreamRecoverableAux fuel config baseUrl apiKey request sourceEventSeqs
              sourcesNodup sourcesEarlier round.batch.finalModel round.runner (history ++ [witness])
termination_by fuel

def runSchemaStreamRecoverable
    {Model Capability : Type}
    {cfg : Config Model Capability}
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
    IO (Except SchemaStreamRecoverableConversationError
      (SchemaStreamRecoverableRunResult registry)) :=
  runSchemaStreamRecoverableAux fuel config baseUrl apiKey request sourceEventSeqs sourcesNodup
    sourcesEarlier before runner []

/-! ## Executable heterogeneous failure and continuation fixture -/

namespace Example

open Cordis.DeepSeekGenericBridge.Example
open Cordis.DeepSeekSchemaRegistry.Example
open Cordis.DeepSeekSchemaStreamConversation.Example
open Cordis.DeepSeekToolAdmission

def dualWeatherFailureProvider : Provider dualCatalog.signature .weather :=
  {
    id := {
      domain := "example.deepseek"
      name := "weather-failure"
      major := 1
    }
    handle := fun _ => .error "weather unavailable"
  }

def dualClockFailureProvider : Provider dualCatalog.signature .clock :=
  {
    id := {
      domain := "example.deepseek"
      name := "clock-failure"
      major := 1
    }
    handle := fun _ => .error "clock unavailable"
  }

def dualFailureRegistry : Registry dualCatalog.signature
  | .weather => some dualWeatherFailureProvider
  | .clock => some dualClockFailureProvider

def dualFailureView : View dualCatalog.signature dualFailureRegistry
    (fun _ => True) where
  resolve operation _ := by
    cases operation
    · exact { provider := dualWeatherFailureProvider, present := rfl }
    · exact { provider := dualClockFailureProvider, present := rfl }

def dualFailureConfig : GenericHarness.Config Nat Capability where
  catalog := dualCatalog
  wire := dualWire
  needs := fun _ => True
  needsDecidable := fun _ => isTrue trivial
  registry := dualFailureRegistry
  view := dualFailureView
  granted := fun _ _ _ => True
  grantedDecidable := fun _ _ _ => isTrue trivial
  PolicyRejected := fun _ => String
  renderPolicyRejected := fun _ reason => reason
  decide := fun _ _ _ => .allow

def dualWeatherFailureBinding
    (certificate : ValidatedToolDefinition DeepSeekApi.exampleTool) :
    SchemaToolBinding dualFailureConfig DeepSeekApi.exampleTool where
  certificate := certificate
  genericTool := .weather
  name_eq := rfl

def dualClockFailureBinding
    (certificate : ValidatedToolDefinition clockTool) :
    SchemaToolBinding dualFailureConfig clockTool where
  certificate := certificate
  genericTool := .clock
  name_eq := rfl

def dualFailureRegistryEntries
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    SchemaToolRegistry dualFailureConfig where
  entries := [
    { tool := DeepSeekApi.exampleTool
      binding := dualWeatherFailureBinding weatherCertificate },
    { tool := clockTool
      binding := dualClockFailureBinding clockCertificate }
  ]
  names_nodup := by
    simp [SchemaToolEntry.name, DeepSeekApi.exampleTool, clockTool]

def dualFailureRequestSource
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    RegistryRequestSource (dualFailureRegistryEntries weatherCertificate clockCertificate) where
  source := {
    model := "deepseek-reasoner"
    system := some "Recover provider failures as model-visible error results."
    tools := [DeepSeekApi.exampleTool, clockTool]
    toolChoice := some .auto
    errorToolResults := .include
  }
  tools_eq := by rfl

def dualFailureBatchAccepted : Bool :=
  match DeepSeekToolSchema.weatherToolCertificate, clockToolCertificate with
  | .ok weatherCertificate, .ok clockCertificate =>
      match executeSchemaRegistryCallsRecoverable
          (dualFailureRegistryEntries weatherCertificate clockCertificate) 0
          [weatherCall, {
            id := "call-clock-0"
            name := "get_time"
            arguments := "{\"city\":\"New York\"}"
          }] with
      | .error _ => false
      | .ok batch =>
          match batch.attempts with
          | .providerFailed weather :: .providerFailed clock :: [] =>
              batch.finalModel == 0 && weather.message == "weather unavailable" &&
                clock.message == "clock unavailable" &&
                (registryRecoverableAttempts batch.attempts).length == 2
          | _ => false
  | _, _ => false

def dualFailureLoopProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "request=$(cat); case \"$request\" in " ++
      "*'weather unavailable'*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
      "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
    "cordis-schema-stream-error-loop-fixture",
    dualToolStreamBody,
    DeepSeekRichStream.exampleTextStreamBody
  ]

def dualFailureContinuationRun
    (weatherCertificate : ValidatedToolDefinition DeepSeekApi.exampleTool)
    (clockCertificate : ValidatedToolDefinition clockTool) :
    IO (Except SchemaStreamRecoverableConversationError
      (SchemaStreamRecoverableRunResult
        (dualFailureRegistryEntries weatherCertificate clockCertificate))) := do
  runSchemaStreamRecoverable 2 dualFailureLoopProcess "https://fixture.invalid"
    { value := "fixture-key" }
    (dualFailureRequestSource weatherCertificate clockCertificate)
    [] (by simp) (by simp) 0 DeepSeekSchemaHarness.Example.counterRunner

end Example

end Cordis.DeepSeekSchemaStreamErrors
