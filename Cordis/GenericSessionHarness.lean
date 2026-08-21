import Cordis.GenericHarness
import Cordis.Session
import Lean.Data.Json.Printer

/-!
# Generic rich-session harness bridge

`GenericHarness.Runner` is deliberately structural: its log is the erased protocol trace needed
for phase-indexed replay. The counter example previously supplied the only rich `Session` wrapper
around that runner. This module factors that wrapper over an arbitrary coherent generic
configuration and a caller-supplied request header, so a non-counter catalog can carry the same
proof-producing model-request and surface/log projection certificates.

The bridge remains pure and finite. It does not add transport, persistence, external tool I/O,
asynchronous scheduling, or TypeScript/deployed Harness equivalence.
-/

set_option autoImplicit false

namespace Cordis.GenericSessionHarness

open Cordis

universe u

/-! ## Configuration and state -/

structure SessionConfig (Model Capability : Type u) where
  core : GenericHarness.Config Model Capability
  requestHeader : Session.RequestHeader
  userPrompt : String
  assistantPrompt : String

abbrev Core
    {Model Capability : Type u}
    (cfg : SessionConfig Model Capability) := cfg.core

inductive RunnerError where
  | notReady (state : RuntimeState)
  | notInTurn (state : RuntimeState)
  | notInStep (state : RuntimeState)
  | pendingCalls (pending : List CallId)
  | internal (error : GenericHarness.RunnerError)
deriving DecidableEq, Repr

structure RunnerState
    {Model Capability : Type u}
    (cfg : SessionConfig Model Capability) where
  phase : SessionState
  runner : GenericHarness.Runner cfg.core phase
  session : Session.Session Session.noExtensions
  projection_eq : Session.protocolProjection session.events = runner.log

namespace RunnerState

private def sessionToolCalls : Nat → List RawCall → List Session.ToolCall
  | _, [] => []
  | next, raw :: rest =>
      {
        id := { value := next }
        name := raw.name
        arguments := raw.arguments.compress
      } :: sessionToolCalls (next + 1) rest

def initial
    {Model Capability : Type u}
    (cfg : SessionConfig Model Capability)
    (model : Model) : RunnerState cfg :=
  {
    phase := .ready 0
    runner := GenericHarness.Runner.initial cfg.core model
    session := Session.Session.empty Session.noExtensions
    projection_eq := rfl
  }

def initialModel
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : Model :=
  state.runner.initialModel

def model
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : Model :=
  state.runner.model

def protocol
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : RuntimeState :=
  eraseState state.phase

def nextCall
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : Nat :=
  state.runner.nextCall

def leases
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : LeasePool :=
  state.runner.leases

def log
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : List RuntimeEvent :=
  state.runner.log

def records
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    List (GenericHarness.CallRecord cfg.core) :=
  state.runner.records

def messages
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : List Session.Message :=
  state.session.messages

/-- The request is reconstructed from the rich log, never from an independent snapshot. -/
def modelRequest
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : Option (Session.ModelRequest state.session) :=
  Session.mkRequest state.session

theorem protocolProjection_eq_log
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    Session.protocolProjection state.session.events = state.log :=
  state.projection_eq

theorem protocolProjection_replays
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    replayRaw (.ready 0) (Session.protocolProjection state.session.events) =
      .ok state.protocol := by
  rw [state.protocolProjection_eq_log]
  exact state.runner.replayProof

theorem records_length_eq_nextCall
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    (state.records).length = state.nextCall :=
  state.runner.records_length_eq_nextCall

theorem models_threaded
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    GenericHarness.ModelsThreaded state.initialModel state.records state.model :=
  state.runner.models_threaded

theorem leases_threaded
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    GenericHarness.LeasesThreaded .empty state.records state.leases :=
  state.runner.leases_threaded

theorem ids_eq_range
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    (state.records).map (fun record => record.id.value) = List.range state.nextCall :=
  state.runner.ids_eq_range

theorem callBoundaries_eq_records
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) :
    GenericHarness.callBoundaries state.log =
      GenericHarness.recordBoundaries state.records :=
  state.runner.callBoundaries_eq_records

private def recordRequestHeader
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : RunnerState cfg :=
  let nextSession := state.session.appendLogOnly .requestHeader cfg.requestHeader
  {
    state with
    session := nextSession
    projection_eq := by
      simpa [nextSession] using state.projection_eq
  }

private def recordUserMessage
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg)
    (content : String) : RunnerState cfg :=
  let nextSession := state.session.appendSurface .userMessage { content } [] (by simp) (by simp)
  {
    state with
    session := nextSession
    projection_eq := by
      simpa [nextSession] using state.projection_eq
  }

private def recordAssistantMessage
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg)
    (content : String)
    (calls : List RawCall) : RunnerState cfg :=
  let rawToolCalls := sessionToolCalls state.nextCall calls
  let nextSession := state.session.appendSurface .assistantMessage {
    turn := match state.phase with
      | .step turn _ _ => turn
      | _ => 0
    step := match state.phase with
      | .step _ step _ => step
      | _ => 0
    content
    rawToolCalls
  } [] (by simp) (by simp)
  {
    state with
    session := nextSession
    projection_eq := by
      simpa [nextSession] using state.projection_eq
  }

def beginTurn
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability} :
    RunnerState cfg -> Except RunnerError (RunnerState cfg)
  | ⟨.ready turn, runner, session, aligned⟩ =>
      let nextRunner := runner.beginTurn
      let nextSession := session.appendLogOnly .turnStart { turn }
      .ok {
        phase := .turn turn 0
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [GenericHarness.Runner.beginTurn_log]
          simpa [nextSession, Session.Session.appendLogOnly, Session.Session.append,
            Session.protocolProjection, Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.turnStart turn]) aligned
      }
  | ⟨phase, _, _, _⟩ => .error (.notReady (eraseState phase))

def beginStep
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability} :
    RunnerState cfg -> Except RunnerError (RunnerState cfg)
  | ⟨.turn turn step, runner, session, aligned⟩ =>
      let nextRunner := runner.beginStep
      let nextSession := session.appendLogOnly .stepStart { turn, step }
      .ok {
        phase := .step turn step []
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [GenericHarness.Runner.beginStep_log]
          simpa [nextSession, Session.Session.appendLogOnly, Session.Session.append,
            Session.protocolProjection, Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.stepStart turn step]) aligned
      }
  | ⟨phase, _, _, _⟩ => .error (.notInTurn (eraseState phase))

def beginSession
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : Except RunnerError (RunnerState cfg) := do
  let inTurn ← beginTurn state
  beginStep inTurn

def dispatch
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability} :
    RunnerState cfg -> RawCall -> Except RunnerError (RunnerState cfg)
  | ⟨.step turn step [], runner, session, aligned⟩, raw =>
      match runner.dispatch raw with
      | .error error => .error (.internal error)
      | .ok result =>
          let callSeq := session.nextSeq
          let call : Session.ToolCall := {
            id := result.record.id
            name := raw.name
            arguments := raw.arguments.compress
          }
          let called := session.appendLogOnly .toolCall { turn, step, call }
          let outcome := result.record.outcome
          let completed := called.appendSurface .toolResult {
            turn
            step
            callId := result.record.id
            content := reprStr outcome
            isError := match outcome with
              | .succeeded => false
              | _ => true
          } [callSeq] (by simp) (by
            intro source member
            simp only [List.mem_singleton] at member
            subst source
            simp [callSeq, called, Session.Session.appendLogOnly,
              Session.Session.append])
          .ok {
            phase := .step turn step []
            runner := result.runner
            session := completed
            projection_eq := by
              rw [result.log_eq]
              simpa [completed, called, call, Session.Session.appendSurface,
                Session.Session.appendLogOnly, Session.Session.append,
                Session.protocolProjection, Session.LoggedEvent.protocolEvent?] using
                congrArg (fun log => log ++ [
                  RuntimeEvent.toolCall turn step result.record.id,
                  RuntimeEvent.toolResult turn step result.record.id
                ]) aligned
          }
  | ⟨.step _ _ pending, _, _, _⟩, _ => .error (.pendingCalls pending)
  | ⟨phase, _, _, _⟩, _ => .error (.notInStep (eraseState phase))

def dispatchAll
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability} :
    RunnerState cfg -> List RawCall -> Except RunnerError (RunnerState cfg)
  | state, [] => .ok state
  | state, raw :: rest => do
      let next ← dispatch state raw
      dispatchAll next rest

def finishStep
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability} :
    RunnerState cfg -> Except RunnerError (RunnerState cfg)
  | ⟨.step turn step [], runner, session, aligned⟩ =>
      let nextRunner := runner.finishStep
      let nextSession := session.appendLogOnly .stepEnd { turn, step }
      .ok {
        phase := .turn turn (step + 1)
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [GenericHarness.Runner.finishStep_log]
          simpa [nextSession, Session.Session.appendLogOnly, Session.Session.append,
            Session.protocolProjection, Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.stepEnd turn step]) aligned
      }
  | ⟨.step _ _ pending, _, _, _⟩ => .error (.pendingCalls pending)
  | ⟨phase, _, _, _⟩ => .error (.notInStep (eraseState phase))

def finishTurn
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability} :
    RunnerState cfg -> Except RunnerError (RunnerState cfg)
  | ⟨.turn turn nextStep, runner, session, aligned⟩ =>
      let nextRunner := runner.finishTurn
      let nextSession := session.appendLogOnly .turnEnd {
        turn
        nextStep
        reason := .completed
      }
      .ok {
        phase := .ready (turn + 1)
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [GenericHarness.Runner.finishTurn_log]
          simpa [nextSession, Session.Session.appendLogOnly, Session.Session.append,
            Session.protocolProjection, Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.turnEnd turn nextStep]) aligned
      }
  | ⟨phase, _, _, _⟩ => .error (.notInTurn (eraseState phase))

def finishSession
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg) : Except RunnerError (RunnerState cfg) := do
  let inTurn ← finishStep state
  finishTurn inTurn

def runStep
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg)
    (calls : List RawCall) : Except RunnerError (RunnerState cfg) := do
  let started ← beginStep state
  let withHeader := recordRequestHeader started
  let withUser := recordUserMessage withHeader cfg.userPrompt
  let withAssistant := recordAssistantMessage withUser cfg.assistantPrompt calls
  let settled ← dispatchAll withAssistant calls
  finishStep settled

def runSteps
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    : RunnerState cfg -> List (List RawCall) -> Except RunnerError (RunnerState cfg)
  | state, [] => .ok state
  | state, calls :: rest => do
      let next ← runStep state calls
      runSteps next rest

def runTurn
    {Model Capability : Type u}
    {cfg : SessionConfig Model Capability}
    (state : RunnerState cfg)
    (steps : List (List RawCall)) :
    Except RunnerError (RunnerState cfg) := do
  let started ← beginTurn state
  let completed ← runSteps started steps
  finishTurn completed

def runScript
    {Model Capability : Type u}
    (cfg : SessionConfig Model Capability)
    (initialModel : Model)
    (steps : List (List RawCall)) :
    Except RunnerError (RunnerState cfg) := do
  let state := initial cfg initialModel
  runTurn state steps

end RunnerState

end Cordis.GenericSessionHarness
