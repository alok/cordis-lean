import Cordis.DeepSeekOutcomeConversation
import Cordis.DeepSeekRequestMode

/-!
# Typed process-backed rich outcome rounds

`DeepSeekHarnessProcess` retains a typed request source through a text-only process round.  This
module carries the same source provenance through the richer terminal-outcome path: a streaming
request plan is built from the `RequestSource`, a complete process body is classified as text,
tool, mixed, multi-call, or provider failure, and successful calls are dispatched through the
dependent `GenericHarness.Config` before the `ConversationRunner` endpoint is returned.

The result is indexed by the source, request plan, model, source-event evidence, and body.  The
execution equality prevents a process response from being detached from the dependent tool
execution that produced its model and runner endpoint.  Request, process/status/stream, and tool
execution failures remain separate.

This is still a complete-body local process adapter.  It does not claim provider schema or
credential authenticity, incremental delivery, cancellation of blocked reads, persistence,
external tool trust, or deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessProcessOutcome

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekCurlOutcome
open Cordis.DeepSeekCurlTransport
open Cordis.DeepSeekHarness
open Cordis.DeepSeekOutcomeConversation

/-! ## Streaming request provenance -/

/-- A streaming request plan tied to the typed source and exact conversation runner session. -/
structure PreparedStreamingRequest
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : ConversationRunner) where
  plan : TypedRequestPlan .streaming
  build_eq : buildTypedStreamingRequestPlan baseUrl apiKey source runner.session = .ok plan

namespace PreparedStreamingRequest

theorem build_exact
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl apiKey source runner) :
    buildTypedStreamingRequestPlan baseUrl apiKey source runner.session = .ok prepared.plan :=
  prepared.build_eq

theorem source_stream
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl apiKey source runner) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

theorem body_eq_source
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl apiKey source runner) :
    prepared.plan.request.body =
      Lean.Json.compress prepared.plan.source.toJson :=
  prepared.plan.body_eq

end PreparedStreamingRequest

/-- Build a streaming plan while retaining the dependent success equation. -/
def prepareStreamingRequest
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (runner : ConversationRunner) :
    Except RequestError (PreparedStreamingRequest baseUrl apiKey source runner) :=
  match built : buildTypedStreamingRequestPlan baseUrl apiKey source runner.session with
  | .error error => .error error
  | .ok plan => .ok { plan, build_eq := built }

/-! ## Process outcome and dependent endpoint -/

inductive RoundError where
  | request (error : RequestError)
  | client (error : OutcomeClientError)
  | execution (error : DeepSeekOutcomeConversation.ExecutionError)
deriving DecidableEq, Repr

def executionEndpoint
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {body : String} :
    ExecutionResult cfg before body → ConversationRunner
  | .providerFailure _ runner => runner
  | .assistant round => round.runner

/-- A classified process body tied to dependent execution and its exact conversation endpoint. -/
structure ProcessOutcomeRound
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : ConversationRunner}
    (prepared : PreparedStreamingRequest baseUrl apiKey source runner)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq)
    (body : String) where
  processed : ProcessedOutcome body
  result : ExecutionResult cfg before body
  result_eq :
    executeOutcomeWithTools cfg before runner processed.outcome sourceEventSeqs
        sourcesNodup sourcesEarlier =
      .ok result
  after : ConversationRunner
  after_eq : after = executionEndpoint result

namespace ProcessOutcomeRound

theorem result_exact
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner}
    {prepared : PreparedStreamingRequest baseUrl apiKey source runner}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : ProcessOutcomeRound prepared cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    executeOutcomeWithTools cfg before runner round.processed.outcome sourceEventSeqs
        sourcesNodup sourcesEarlier =
      .ok round.result :=
  round.result_eq

theorem endpoint_exact
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner}
    {prepared : PreparedStreamingRequest baseUrl apiKey source runner}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (round : ProcessOutcomeRound prepared cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    round.after = executionEndpoint round.result :=
  round.after_eq

theorem stream_flag
    {baseUrl : String} {apiKey : ApiKey} {source : RequestSource}
    {runner : ConversationRunner}
    {prepared : PreparedStreamingRequest baseUrl apiKey source runner}
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (_round : ProcessOutcomeRound prepared cfg before sourceEventSeqs sourcesNodup
      sourcesEarlier body) :
    prepared.plan.source.stream = true :=
  prepared.plan.streaming_source_stream

end ProcessOutcomeRound

/-! ## Typed process execution -/

def executePreparedOutcome
    (config : ProcessConfig)
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : ConversationRunner}
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (prepared : PreparedStreamingRequest baseUrl apiKey source runner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun body : String =>
        ProcessOutcomeRound prepared cfg before sourceEventSeqs sourcesNodup
          sourcesEarlier body)) := do
  match ← executeOutcome config prepared.plan.request with
  | .error error => pure (.error (.client error))
  | .ok ⟨body, processed⟩ =>
      match executionEq : executeOutcomeWithTools cfg before runner processed.outcome
          sourceEventSeqs sourcesNodup sourcesEarlier with
      | .error error => pure (.error (.execution error))
      | .ok result =>
          pure (.ok ⟨body, {
            processed
            result
            result_eq := executionEq
            after := executionEndpoint result
            after_eq := rfl
          }⟩)

def executeSourceOutcome
    (config : ProcessConfig)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    {Model Capability : Type}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : ConversationRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except RoundError
      (Sigma fun prepared : PreparedStreamingRequest baseUrl apiKey source runner =>
        Sigma fun body : String =>
          ProcessOutcomeRound prepared cfg before sourceEventSeqs sourcesNodup
            sourcesEarlier body)) := do
  match prepareStreamingRequest baseUrl apiKey source runner with
  | .error error => pure (.error (.request error))
  | .ok prepared =>
      match ← executePreparedOutcome config cfg before prepared sourceEventSeqs sourcesNodup
          sourcesEarlier with
      | .error error => pure (.error error)
      | .ok ⟨body, round⟩ => pure (.ok ⟨prepared, ⟨body, round⟩⟩)

/-! ## Executable process/provenance fixtures -/

namespace Example

def source : RequestSource where
  model := "fixture-model"
  system := some "Execute only certified local tools."

def toolSource : RequestSource where
  model := "fixture-model"
  system := some "Execute only certified local tools."
  tools := [counterReadTool]
  toolChoice := some .auto

def textProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-harness-outcome-text-fixture",
    DeepSeekRichStream.exampleTextStreamBody
  ]

def toolProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-harness-outcome-tool-fixture",
    counterToolStreamBody
  ]

def failureProcess : ProcessConfig where
  command := "sh"
  args := fun _ => #[
    "-c",
    "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
    "cordis-harness-outcome-failure-fixture",
    DeepSeekStreamFailure.exampleContentFilterBody
  ]

private theorem emptySourcesNodup : ([] : List Nat).Nodup := by simp

private theorem emptySourcesEarlier
    (runner : ConversationRunner) :
    ∀ source ∈ ([] : List Nat), source < runner.session.nextSeq := by
  simp

def text : IO (Except RoundError
    (Sigma fun prepared : PreparedStreamingRequest "https://fixture.invalid"
      { value := "fixture-key" } source (ConversationRunner.empty 1) =>
      Sigma fun body : String =>
        ProcessOutcomeRound prepared Cordis.Harness.counterConfig 0 [] (by simp) (by simp) body)) :=
  executeSourceOutcome textProcess "https://fixture.invalid" { value := "fixture-key" }
    source Cordis.Harness.counterConfig 0 (ConversationRunner.empty 1) [] (by simp) (by simp)

def tool : IO (Except RoundError
    (Sigma fun prepared : PreparedStreamingRequest "https://fixture.invalid"
      { value := "fixture-key" } toolSource (ConversationRunner.empty 1) =>
      Sigma fun body : String =>
        ProcessOutcomeRound prepared Cordis.Harness.counterConfig 0 [] (by simp) (by simp) body)) :=
  executeSourceOutcome toolProcess "https://fixture.invalid" { value := "fixture-key" }
    toolSource Cordis.Harness.counterConfig 0 (ConversationRunner.empty 1) [] (by simp) (by simp)

def failure : IO (Except RoundError
    (Sigma fun prepared : PreparedStreamingRequest "https://fixture.invalid"
      { value := "fixture-key" } source (ConversationRunner.empty 1) =>
      Sigma fun body : String =>
        ProcessOutcomeRound prepared Cordis.Harness.counterConfig 0 [] (by simp) (by simp) body)) :=
  executeSourceOutcome failureProcess "https://fixture.invalid" { value := "fixture-key" }
    source Cordis.Harness.counterConfig 0 (ConversationRunner.empty 1) [] (by simp) (by simp)

end Example

end Cordis.DeepSeekHarnessProcessOutcome
