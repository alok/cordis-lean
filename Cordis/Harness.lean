import Cordis.Examples.CounterWire
import Cordis.GenericHarness
import Cordis.Session
import Lean.Data.Json.Printer

/-!
# Counter instantiation of the generic proof-carrying harness

`Cordis.GenericHarness` owns the reusable, phase-indexed runner. This module supplies the
verified counter catalog as one concrete configuration and an erased convenience wrapper for the
demo and dynamic callers. Trusted internal transitions remain indexed by `SessionState`.
-/

namespace Cordis.Harness

open Cordis
open Cordis.Examples.Counter

/-- The counter example grants both declared capabilities and allows every admitted call. -/
def counterConfig : Cordis.GenericHarness.Config Nat Capability where
  catalog := catalog
  wire := wire
  needs := needs
  needsDecidable := fun _ => isTrue trivial
  registry := registry
  view := view
  granted := fun _ _ _ => True
  grantedDecidable := fun _ _ _ => isTrue trivial
  PolicyRejected := fun _ => String
  renderPolicyRejected := fun _ reason => reason
  decide := fun _ _ _ => .allow

def counterRequestHeader : Cordis.Session.RequestHeader where
  provider := "cordis-lean"
  model := "deterministic-counter"
  system := some "Execute only the supplied proof-carrying counter tools."
  toolSchemas := [
    {
      name := readSpec.name
      description := readSpec.description
      inputSchema := (wire.inputCodec .read).schema.compress
    },
    {
      name := incrementSpec.name
      description := incrementSpec.description
      inputSchema := (wire.inputCodec .increment).schema.compress
    }
  ]

abbrev CallOutcome := Cordis.GenericHarness.CallOutcome
abbrev CounterCall := counterConfig.Call
abbrev CounterCompletion (call : CounterCall) := counterConfig.Completion call

def completionAfter (before : Nat) {call : CounterCall} : CounterCompletion call → Nat :=
  Cordis.GenericHarness.completionAfter before

abbrev CallEvidence
    (id : CallId)
    (raw : RawCall)
    (before after : Nat)
    (leasesBefore leasesAfter : LeasePool) :=
  Cordis.GenericHarness.CallEvidence counterConfig id raw before after leasesBefore leasesAfter

abbrev CallRecord := Cordis.GenericHarness.CallRecord counterConfig

namespace CallRecord

def name (record : CallRecord) : String := Cordis.GenericHarness.CallRecord.name record

def outcome (record : CallRecord) : CallOutcome :=
  Cordis.GenericHarness.CallRecord.outcome record

def encodedResult (record : CallRecord) : Option Lean.Json :=
  Cordis.GenericHarness.CallRecord.encodedResult record

def policyDispatchCount (record : CallRecord) : Nat :=
  Cordis.GenericHarness.CallRecord.dispatchCount record

end CallRecord

def callOutcomeIsError : CallOutcome → Bool
  | .succeeded => false
  | _ => true

abbrev CallBoundary := Cordis.GenericHarness.CallBoundary

def callBoundaries (log : List RuntimeEvent) : List CallBoundary :=
  Cordis.GenericHarness.callBoundaries log

def recordBoundaries (records : List CallRecord) : List CallBoundary :=
  Cordis.GenericHarness.recordBoundaries records

abbrev ModelsThreaded (start : Nat) (records : List CallRecord) (finish : Nat) : Prop :=
  Cordis.GenericHarness.ModelsThreaded (cfg := counterConfig) start records finish

abbrev LeasesThreaded
    (start : LeasePool) (records : List CallRecord) (finish : LeasePool) : Prop :=
  Cordis.GenericHarness.LeasesThreaded (cfg := counterConfig) start records finish

abbrev RecordChain
    (initial : Nat)
    (nextCall : Nat)
    (records : List CallRecord)
    (final : Nat)
    (leases : LeasePool)
    (boundaries : List CallBoundary) : Prop :=
  Cordis.GenericHarness.RecordChain counterConfig initial nextCall records final leases boundaries

namespace RecordChain

theorem length_eq_nextCall
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    records.length = nextCall :=
  Cordis.GenericHarness.RecordChain.length_eq_nextCall history

theorem ids_eq_range
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    records.map (fun record ↦ record.id.value) = List.range nextCall :=
  Cordis.GenericHarness.RecordChain.ids_eq_range history

theorem boundaries_eq_records
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    boundaries = recordBoundaries records :=
  Cordis.GenericHarness.RecordChain.boundaries_eq_records history

theorem models_threaded
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    ModelsThreaded initial records final :=
  Cordis.GenericHarness.RecordChain.models_threaded history

theorem leases_threaded
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    LeasesThreaded .empty records leases :=
  Cordis.GenericHarness.RecordChain.leases_threaded history

end RecordChain

theorem replayRaw_append
    (start : RuntimeState)
    (first second : List RuntimeEvent) :
    replayRaw start (first ++ second) =
      match replayRaw start first with
      | .error error => .error error
      | .ok middle => replayRaw middle second :=
  Cordis.GenericHarness.replayRaw_append start first second

/-- Failures exposed only by the erased convenience wrapper. -/
inductive RunnerError where
  | notReady (state : RuntimeState)
  | notInTurn (state : RuntimeState)
  | notInStep (state : RuntimeState)
  | pendingCalls (pending : List CallId)
  | internal (error : Cordis.GenericHarness.RunnerError)
deriving DecidableEq, Repr

/-- Existential phase wrapper around the trusted phase-indexed counter runner. -/
structure RunnerState where
  phase : SessionState
  runner : Cordis.GenericHarness.Runner counterConfig phase
  session : Cordis.Session.Session Cordis.Session.noExtensions
  projection_eq : Cordis.Session.protocolProjection session.events = runner.log

namespace RunnerState

private def sessionToolCalls : Nat → List RawCall → List Cordis.Session.ToolCall
  | _, [] => []
  | next, raw :: rest =>
      {
        id := { value := next }
        name := raw.name
        arguments := raw.arguments.compress
      } :: sessionToolCalls (next + 1) rest

def initial (model : Nat) : RunnerState :=
  { phase := .ready 0,
    runner := Cordis.GenericHarness.Runner.initial counterConfig model
    session := Cordis.Session.Session.empty Cordis.Session.noExtensions
    projection_eq := rfl }

def initialModel (state : RunnerState) : Nat := state.runner.initialModel

def model (state : RunnerState) : Nat := state.runner.model

def protocol (state : RunnerState) : RuntimeState := eraseState state.phase

def nextCall (state : RunnerState) : Nat := state.runner.nextCall

def leases (state : RunnerState) : LeasePool := state.runner.leases

def log (state : RunnerState) : List RuntimeEvent := state.runner.log

def records (state : RunnerState) : List CallRecord := state.runner.records

def messages (state : RunnerState) : List Cordis.Session.Message := state.session.messages

def modelRequest (state : RunnerState) : Option (Cordis.Session.ModelRequest state.session) :=
  Cordis.Session.mkRequest state.session

private def recordRequestHeader (state : RunnerState) : RunnerState :=
  let nextSession := state.session.appendLogOnly .requestHeader counterRequestHeader
  {
    state with
    session := nextSession
    projection_eq := by
      simpa [nextSession] using state.projection_eq
  }

private def recordUserMessage (state : RunnerState) (content : String) : RunnerState :=
  let nextSession := state.session.appendSurface .userMessage { content } [] (by simp) (by simp)
  {
    state with
    session := nextSession
    projection_eq := by
      simpa [nextSession] using state.projection_eq
  }

private def recordAssistantMessage
    (state : RunnerState)
    (content : String)
    (calls : List RawCall) : RunnerState :=
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

theorem records_length_eq_nextCall (state : RunnerState) :
    state.records.length = state.nextCall :=
  state.runner.records_length_eq_nextCall

theorem ids_eq_range (state : RunnerState) :
    state.records.map (fun record ↦ record.id.value) = List.range state.nextCall :=
  state.runner.ids_eq_range

theorem models_threaded (state : RunnerState) :
    ModelsThreaded state.initialModel state.records state.model :=
  state.runner.models_threaded

theorem callBoundaries_eq_records (state : RunnerState) :
    callBoundaries state.log = recordBoundaries state.records :=
  state.runner.callBoundaries_eq_records

theorem protocolProjection_eq_log (state : RunnerState) :
    Cordis.Session.protocolProjection state.session.events = state.log :=
  state.projection_eq

theorem protocolProjection_replays (state : RunnerState) :
    replayRaw (.ready 0) (Cordis.Session.protocolProjection state.session.events) =
      .ok state.protocol := by
  rw [state.protocolProjection_eq_log]
  exact state.runner.replayProof

theorem leases_threaded (state : RunnerState) :
    LeasesThreaded .empty state.records state.leases :=
  state.runner.leases_threaded

def beginTurn : RunnerState → Except RunnerError RunnerState
  | ⟨.ready turn, runner, session, aligned⟩ =>
      let nextRunner := runner.beginTurn
      let nextSession := session.appendLogOnly .turnStart { turn }
      .ok {
        phase := .turn turn 0
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [Cordis.GenericHarness.Runner.beginTurn_log]
          simpa [nextSession, Cordis.Session.Session.appendLogOnly,
            Cordis.Session.Session.append, Cordis.Session.protocolProjection,
            Cordis.Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.turnStart turn]) aligned
      }
  | ⟨phase, _, _, _⟩ => .error (.notReady (eraseState phase))

def beginStep : RunnerState → Except RunnerError RunnerState
  | ⟨.turn turn step, runner, session, aligned⟩ =>
      let nextRunner := runner.beginStep
      let nextSession := session.appendLogOnly .stepStart { turn, step }
      .ok {
        phase := .step turn step []
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [Cordis.GenericHarness.Runner.beginStep_log]
          simpa [nextSession, Cordis.Session.Session.appendLogOnly,
            Cordis.Session.Session.append, Cordis.Session.protocolProjection,
            Cordis.Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.stepStart turn step]) aligned
      }
  | ⟨phase, _, _, _⟩ => .error (.notInTurn (eraseState phase))

def beginSession (state : RunnerState) : Except RunnerError RunnerState := do
  let inTurn ← state.beginTurn
  inTurn.beginStep

def dispatch : RunnerState → RawCall → Except RunnerError RunnerState
  | ⟨.step turn step [], runner, session, aligned⟩, raw =>
      match runner.dispatch raw with
      | .error error => .error (.internal error)
      | .ok result =>
          let callSeq := session.nextSeq
          let call : Cordis.Session.ToolCall := {
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
            isError := callOutcomeIsError outcome
          } [callSeq] (by simp) (by
            intro source member
            simp only [List.mem_singleton] at member
            subst source
            simp [callSeq, called, Cordis.Session.Session.appendLogOnly,
              Cordis.Session.Session.append])
          .ok {
            phase := .step turn step []
            runner := result.runner
            session := completed
            projection_eq := by
              rw [result.log_eq]
              simpa [completed, called, call, Cordis.Session.Session.appendSurface,
                Cordis.Session.Session.appendLogOnly, Cordis.Session.Session.append,
                Cordis.Session.protocolProjection,
                Cordis.Session.LoggedEvent.protocolEvent?] using
                congrArg (fun log => log ++ [
                  RuntimeEvent.toolCall turn step result.record.id,
                  RuntimeEvent.toolResult turn step result.record.id
                ]) aligned
          }
  | ⟨.step _ _ pending, _, _, _⟩, _ => .error (.pendingCalls pending)
  | ⟨phase, _, _, _⟩, _ => .error (.notInStep (eraseState phase))

def dispatchAll : RunnerState → List RawCall → Except RunnerError RunnerState
  | state, [] => .ok state
  | state, raw :: rest => do
      let next ← state.dispatch raw
      dispatchAll next rest

def finishStep : RunnerState → Except RunnerError RunnerState
  | ⟨.step turn step [], runner, session, aligned⟩ =>
      let nextRunner := runner.finishStep
      let nextSession := session.appendLogOnly .stepEnd { turn, step }
      .ok {
        phase := .turn turn (step + 1)
        runner := nextRunner
        session := nextSession
        projection_eq := by
          rw [Cordis.GenericHarness.Runner.finishStep_log]
          simpa [nextSession, Cordis.Session.Session.appendLogOnly,
            Cordis.Session.Session.append, Cordis.Session.protocolProjection,
            Cordis.Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.stepEnd turn step]) aligned
      }
  | ⟨.step _ _ pending, _, _, _⟩ => .error (.pendingCalls pending)
  | ⟨phase, _, _, _⟩ => .error (.notInStep (eraseState phase))

def finishTurn : RunnerState → Except RunnerError RunnerState
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
          rw [Cordis.GenericHarness.Runner.finishTurn_log]
          simpa [nextSession, Cordis.Session.Session.appendLogOnly,
            Cordis.Session.Session.append, Cordis.Session.protocolProjection,
            Cordis.Session.LoggedEvent.protocolEvent?] using
            congrArg (fun log => log ++ [.turnEnd turn nextStep]) aligned
      }
  | ⟨phase, _, _, _⟩ => .error (.notInTurn (eraseState phase))

def finishSession (state : RunnerState) : Except RunnerError RunnerState := do
  let inTurn ← state.finishStep
  inTurn.finishTurn

def runStep (state : RunnerState) (calls : List RawCall) : Except RunnerError RunnerState := do
  let started ← state.beginStep
  let withHeader := started.recordRequestHeader
  let withUser := withHeader.recordUserMessage "Execute the next certified counter step."
  let withAssistant := withUser.recordAssistantMessage "Dispatching certified tools." calls
  let settled ← withAssistant.dispatchAll calls
  settled.finishStep

def runSteps : RunnerState → List (List RawCall) → Except RunnerError RunnerState
  | state, [] => .ok state
  | state, calls :: rest => do
      let next ← state.runStep calls
      runSteps next rest

def runTurn
    (state : RunnerState)
    (steps : List (List RawCall)) : Except RunnerError RunnerState := do
  let started ← state.beginTurn
  let completed ← started.runSteps steps
  completed.finishTurn

def runTurns : RunnerState → List (List (List RawCall)) → Except RunnerError RunnerState
  | state, [] => .ok state
  | state, steps :: rest => do
      let next ← state.runTurn steps
      runTurns next rest

def runScript (initialModel : Nat) (calls : List RawCall) : Except RunnerError RunnerState :=
  (initial initialModel).runTurn [calls]

def runMultiTurn
    (initialModel : Nat)
    (turns : List (List (List RawCall))) : Except RunnerError RunnerState :=
  (initial initialModel).runTurns turns

end RunnerState

/-- A statically typed two-call trace exercising the intrinsic protocol API. -/
def certifiedTwoCallTrace : Trace (.ready 0) (.ready 1) :=
  .cons (.turnStart 0) <|
  .cons (.stepStart 0 0) <|
  .cons (.toolCall ⟨0⟩ (by simp)) <|
  .cons (.toolResult ⟨0⟩ (by simp)) <|
  .cons (.toolCall ⟨1⟩ (by simp)) <|
  .cons (.toolResult ⟨1⟩ (by simp)) <|
  .cons (.stepEnd 0 0) <|
  .cons (.turnEnd 0 1) .nil

theorem certifiedTwoCallTrace_replays :
    replayRaw (.ready 0) certifiedTwoCallTrace.erase = .ok (.ready 1) :=
  replayRaw_eraseTrace certifiedTwoCallTrace

def demoCalls : List RawCall := [
  rawRead,
  rawIncrement { amount := 3, limit := 10 },
  rawRead,
  rawUnknown
]

def demo : Except RunnerError RunnerState :=
  RunnerState.runScript 2 demoCalls

end Cordis.Harness
