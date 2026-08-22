import Cordis.DeepSeekHarnessTransportContract

/-!
# Single-decoder transport-backed DeepSeek tool round

`DeepSeekHarnessTransportContract` ties a prepared request to one HTTP response, one
`ValidatedResponse`, one `acceptValidated` admission, and the assistant append endpoint.  This
module carries that same dependent certificate into the generic tool executor without parsing or
admitting the response a second time.  Tool results are appended to the session-runner state with
the sequence and tool-count invariants reconstructed in the type.

The transport is still injected and the response body is complete.  The executable fixture uses
the process-backed local transport; live network reachability, credentials, provider obedience,
external effects, retries, persistence, cancellation, and deployed Harness equivalence remain
outside this contract.
-/

set_option autoImplicit false

namespace Cordis.DeepSeekHarnessTransportToolRound

open Cordis
open Cordis.DeepSeekApi
open Cordis.DeepSeekApiSession
open Cordis.DeepSeekHarness
open Cordis.DeepSeekHarnessProcess
open Cordis.DeepSeekHarnessTransportContract
open Cordis.DeepSeekSessionRunner

abbrev SessionRunner := Cordis.DeepSeekSessionRunner.Runner

/-! ## Tool-result append for the session runner -/

def appendToolResults
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : SessionRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    SessionRunner :=
  let session := DeepSeekHarness.appendExecutedToolResults runner.session runner.turn runner.step
    baseCall assistantSeq executions assistantSeqEarlier
  {
    session
    turn := runner.turn
    step := runner.step + executions.length
    nextCall := runner.nextCall
    nextSeq_eq_step := by
      change session.nextSeq = runner.step + executions.length
      rw [DeepSeekHarness.appendExecutedToolResults_nextSeq]
      rw [runner.nextSeq_eq_step]
    toolCallCount_eq_nextCall := by
      have messages_eq := DeepSeekHarness.appendExecutedToolResults_messages
        runner.session runner.turn runner.step baseCall assistantSeq executions
          assistantSeqEarlier
      have count_eq :
          DeepSeekSessionRunner.toolCallCount session.messages =
            DeepSeekSessionRunner.toolCallCount runner.session.messages := by
        change DeepSeekSessionRunner.toolCallCount
          (DeepSeekHarness.appendExecutedToolResults runner.session runner.turn runner.step
            baseCall assistantSeq executions assistantSeqEarlier).messages = _
        rw [messages_eq]
        simp [DeepSeekHarness.executedToolMessages_toolCallCount]
      rw [count_eq]
      exact runner.toolCallCount_eq_nextCall
  }

theorem appendToolResults_messages
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : SessionRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendToolResults runner baseCall assistantSeq executions
      assistantSeqEarlier).session.messages =
      runner.session.messages ++ DeepSeekHarness.executedToolMessages baseCall executions := by
  exact DeepSeekHarness.appendExecutedToolResults_messages runner.session runner.turn runner.step
    baseCall assistantSeq executions assistantSeqEarlier

theorem appendToolResults_nextSeq
    {Model Capability : Type}
    {cfg : GenericHarness.Config Model Capability}
    (runner : SessionRunner)
    (baseCall assistantSeq : Nat)
    (executions : List (ExecutedTool cfg))
    (assistantSeqEarlier : assistantSeq < runner.session.nextSeq) :
    (appendToolResults runner baseCall assistantSeq executions
      assistantSeqEarlier).session.nextSeq =
      runner.session.nextSeq + executions.length := by
  change (DeepSeekHarness.appendExecutedToolResults runner.session runner.turn runner.step
      baseCall assistantSeq executions assistantSeqEarlier).nextSeq = _
  exact DeepSeekHarness.appendExecutedToolResults_nextSeq runner.session runner.turn runner.step
    baseCall assistantSeq executions assistantSeqEarlier

/-! ## Single-decoder tool-round certificate -/

structure ToolTransportRound
    {Model Capability : Type}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : SessionRunner}
    (prepared : PreparedRequest baseUrl apiKey source runner)
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    where
  transportRound : TransportRound prepared sourceEventSeqs sourcesNodup sourcesEarlier body
  finalModel : Model
  executions : List (ExecutedTool cfg)
  executions_eq :
    executeFunctionCalls cfg before
        transportRound.accepted.validated.response.choices.head.message.toolCalls =
      .ok (finalModel, executions)

def ToolTransportRound.finalRunner
    {Model Capability : Type}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : SessionRunner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : ToolTransportRound (sourceEventSeqs := sourceEventSeqs)
      (sourcesNodup := sourcesNodup) (sourcesEarlier := sourcesEarlier) (body := body)
      prepared cfg before) :
    SessionRunner :=
  appendToolResults round.transportRound.after runner.nextCall runner.session.nextSeq
    round.executions (by
    rw [TransportRound.nextSeq round.transportRound]
    exact Nat.lt_succ_self _)

theorem ToolTransportRound.finalRunner_messages
    {Model Capability : Type}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : SessionRunner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : ToolTransportRound (sourceEventSeqs := sourceEventSeqs)
      (sourcesNodup := sourcesNodup) (sourcesEarlier := sourcesEarlier) (body := body)
      prepared cfg before) :
    (round.finalRunner).session.messages =
      round.transportRound.after.session.messages ++
        DeepSeekHarness.executedToolMessages runner.nextCall round.executions := by
  exact appendToolResults_messages round.transportRound.after runner.nextCall runner.session.nextSeq
    round.executions (by
      rw [TransportRound.nextSeq round.transportRound]
      exact Nat.lt_succ_self _)

theorem ToolTransportRound.finalRunner_nextSeq
    {Model Capability : Type}
    {baseUrl : String}
    {apiKey : ApiKey}
    {source : RequestSource}
    {runner : SessionRunner}
    {prepared : PreparedRequest baseUrl apiKey source runner}
    {sourceEventSeqs : List Nat}
    {sourcesNodup : sourceEventSeqs.Nodup}
    {sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq}
    {body : String}
    {cfg : GenericHarness.Config Model Capability}
    {before : Model}
    (round : ToolTransportRound (sourceEventSeqs := sourceEventSeqs)
      (sourcesNodup := sourcesNodup) (sourcesEarlier := sourcesEarlier) (body := body)
      prepared cfg before) :
    round.finalRunner.session.nextSeq =
      runner.session.nextSeq + 1 + round.executions.length := by
  rw [ToolTransportRound.finalRunner]
  rw [appendToolResults_nextSeq]
  rw [TransportRound.nextSeq round.transportRound]

/-! ## Typed transport/tool errors and execution -/

inductive ToolTransportError where
  | request (error : RequestError)
  | transport (message : String)
  | httpStatus (status : Nat) (body : String)
  | response (error : DeepSeekApi.ResponseError)
  | session (error : ApiSessionError)
  | tool (error : ToolRoundError)
deriving DecidableEq, Repr

private def mapRoundError : DeepSeekHarnessTransportContract.RoundError → ToolTransportError
  | .request error => .request error
  | .transport message => .transport message
  | .httpStatus status body => .httpStatus status body
  | .response error => .response error
  | .session error => .session error

def executeSource
    {Model Capability : Type}
    (transport : Transport)
    (baseUrl : String)
    (apiKey : ApiKey)
    (source : RequestSource)
    (cfg : GenericHarness.Config Model Capability)
    (before : Model)
    (runner : SessionRunner)
    (sourceEventSeqs : List Nat)
    (sourcesNodup : sourceEventSeqs.Nodup)
    (sourcesEarlier : ∀ source ∈ sourceEventSeqs, source < runner.session.nextSeq) :
    IO (Except ToolTransportError
      (Sigma fun prepared : PreparedRequest baseUrl apiKey source runner =>
        Sigma fun body : String =>
          ToolTransportRound (sourceEventSeqs := sourceEventSeqs)
            (sourcesNodup := sourcesNodup) (sourcesEarlier := sourcesEarlier) (body := body)
            prepared cfg before)) := do
  match ← DeepSeekHarnessTransportContract.executeSource transport baseUrl apiKey source runner
      sourceEventSeqs sourcesNodup sourcesEarlier with
  | .error error => pure (.error (mapRoundError error))
  | .ok ⟨prepared, ⟨body, transportRound⟩⟩ =>
      match execution_eq : executeFunctionCalls cfg before
          transportRound.accepted.validated.response.choices.head.message.toolCalls with
      | .error error => pure (.error (.tool error))
      | .ok (finalModel, executions) =>
          pure (.ok ⟨prepared, ⟨body, {
            transportRound := transportRound
            finalModel
            executions
            executions_eq := execution_eq
          }⟩⟩)

/-! ## Executable process-backed fixture -/

namespace Example

def source : RequestSource := DeepSeekHarness.counterRequestSource

def transport : Transport :=
  DeepSeekCurlTransport.fixtureTransport DeepSeekHarness.counterResponseBody

def round : IO (Except ToolTransportError
    (Sigma fun prepared : PreparedRequest "https://fixture.invalid" { value := "fixture-key" }
      source (DeepSeekSessionRunner.Runner.empty 1) =>
      Sigma fun body : String =>
        ToolTransportRound (sourceEventSeqs := []) (sourcesNodup := by simp)
          (sourcesEarlier := by simp) (body := body) prepared Cordis.Harness.counterConfig 0)) :=
  executeSource transport "https://fixture.invalid" { value := "fixture-key" }
    source Cordis.Harness.counterConfig 0 (DeepSeekSessionRunner.Runner.empty 1) []
      (by simp) (by simp)

def statusFailureTransport : Transport := {
  send := fun _ => pure (.ok { status := 503, body := "busy" })
}

def statusFailure : IO (Except ToolTransportError
    (Sigma fun prepared : PreparedRequest "https://fixture.invalid" { value := "fixture-key" }
      source (DeepSeekSessionRunner.Runner.empty 1) =>
      Sigma fun body : String =>
        ToolTransportRound (sourceEventSeqs := []) (sourcesNodup := by simp)
          (sourcesEarlier := by simp) (body := body) prepared Cordis.Harness.counterConfig 0)) :=
  executeSource statusFailureTransport "https://fixture.invalid" { value := "fixture-key" }
    source Cordis.Harness.counterConfig 0 (DeepSeekSessionRunner.Runner.empty 1) []
      (by simp) (by simp)

end Example

end Cordis.DeepSeekHarnessTransportToolRound
