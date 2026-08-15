import Cordis.Examples.CounterWire
import Cordis.Policy
import Cordis.Protocol

/-!
# Deterministic proof-carrying harness

The reference runner is deliberately pure and credential-free. It validates
raw counter calls, executes only admitted dependent calls, and emits the same
turn/step/call/result bracket used by DeepSeek Harness. Every `RunnerState`
stores a proof that replaying its emitted log from the initial state yields its
current protocol state.
-/

namespace Cordis.Harness

open Cordis
open Cordis.Examples.Counter

/-- The externally visible disposition of one settled call. -/
inductive CallOutcome where
  | succeeded
  | toolFailed
  | rejected (error : AdmissionError)
  | providerFailed (message : String)
deriving BEq, DecidableEq, Repr

abbrev CounterCall := AuthorizedCall catalog.signature allNeeds

/-- Provider execution outcome indexed by the exact authorized counter call. -/
abbrev CounterCompletion (call : CounterCall) := Except String (Reply call)

/-- The modeled counter after one provider execution or provider-level failure. -/
def completionAfter
    (before : Nat)
    {call : CounterCall} : CounterCompletion call → Nat
  | .error _ => before
  | .ok reply => reply.value.after

/--
Evidence connecting one raw call to either fail-closed admission or an exact-subject policy
trace ending in the provider result for that same dependent call.
-/
inductive CallEvidence
    (id : CallId)
    (raw : RawCall)
    (before : Nat) :
    (after : Nat) →
    (leasesBefore leasesAfter : LeasePool) → Type where
  | rejected
      {leases : LeasePool}
      (error : AdmissionError)
      (validation : validateRaw before raw = .error error) :
      CallEvidence id raw before before leases leases
  | admitted
      {leasesBefore leasesAfter : LeasePool}
      (call : CounterCall)
      (validation : validateRaw before raw = .ok call)
      (issued : LeasePool)
      (issuance : leasesBefore.issue id = some issued)
      (completion : CounterCompletion call)
      (execution : view.execute call = completion)
      (policy : SubjectPolicyTrace
        (Completed := CounterCompletion)
        (Rejected := fun _ => String)
        (.proposed id call issued)
        (.settled id call leasesAfter (.completed completion))) :
      CallEvidence id raw before (completionAfter before completion)
        leasesBefore leasesAfter

namespace CallEvidence

/-- User-facing disposition derived from the retained dependent evidence. -/
def outcome
    {id : CallId}
    {raw : RawCall}
    {before after : Nat}
    {leasesBefore leasesAfter : LeasePool} :
    CallEvidence id raw before after leasesBefore leasesAfter → CallOutcome
  | .rejected error _ => .rejected error
  | .admitted (completion := .error message) .. => .providerFailed message
  | .admitted (completion := .ok reply) .. =>
      match reply.value.result with
      | .error _ => .toolFailed
      | .ok _ => .succeeded

/-- Encoded request-indexed tool result, available only after provider execution succeeds. -/
def encodedResult
    {id : CallId}
    {raw : RawCall}
    {before after : Nat}
    {leasesBefore leasesAfter : LeasePool} :
    CallEvidence id raw before after leasesBefore leasesAfter → Option Lean.Json
  | .rejected _ _ => none
  | .admitted (completion := .error _) .. => none
  | .admitted (call := call) (completion := .ok reply) .. =>
      some (wire.encodeCertifiedResult call.op call.request reply.value)

/-- Dispatch edges retained by this call's exact-subject policy trace. -/
def dispatchCount
    {id : CallId}
    {raw : RawCall}
    {before after : Nat}
    {leasesBefore leasesAfter : LeasePool} :
    CallEvidence id raw before after leasesBefore leasesAfter → Nat
  | .rejected _ _ => 0
  | .admitted (policy := policy) .. => policy.dispatchCount

end CallEvidence

/-- Audit data retaining the raw call and proof-carrying evidence for its exact result. -/
structure CallRecord where
  id : CallId
  raw : RawCall
  before : Nat
  after : Nat
  leasesBefore : LeasePool
  leasesAfter : LeasePool
  evidence : CallEvidence id raw before after leasesBefore leasesAfter

namespace CallRecord

def name (record : CallRecord) : String :=
  record.raw.name

def outcome (record : CallRecord) : CallOutcome :=
  record.evidence.outcome

def encodedResult (record : CallRecord) : Option Lean.Json :=
  record.evidence.encodedResult

def policyDispatchCount (record : CallRecord) : Nat :=
  record.evidence.dispatchCount

end CallRecord

/-- The tool-boundary portion of a runtime log, with protocol coordinates erased. -/
inductive CallBoundary where
  | call (id : CallId)
  | result (id : CallId)
deriving BEq, DecidableEq, Repr

namespace RuntimeEvent

/-- Retain only tool calls and results from the full protocol event vocabulary. -/
def callBoundary? : RuntimeEvent → Option CallBoundary
  | .toolCall _ _ id => some (.call id)
  | .toolResult _ _ id => some (.result id)
  | _ => none

end RuntimeEvent

/-- The ordered call/result subsequence of a full runtime log. -/
def callBoundaries (log : List RuntimeEvent) : List CallBoundary :=
  log.filterMap RuntimeEvent.callBoundary?

/-- The exact call/result pair required by every settled record. -/
def recordBoundaries (records : List CallRecord) : List CallBoundary :=
  records.flatMap fun record => [.call record.id, .result record.id]

/-- Every record receives exactly the pool produced by its predecessor. -/
def LeasesThreaded (start : LeasePool) : List CallRecord → LeasePool → Prop
  | [], finish => finish = start
  | record :: records, finish =>
      record.leasesBefore = start ∧ LeasesThreaded record.leasesAfter records finish

private theorem leasesThreaded_snoc
    {start current : LeasePool}
    {records : List CallRecord}
    (threaded : LeasesThreaded start records current)
    (record : CallRecord)
    (starts : record.leasesBefore = current) :
    LeasesThreaded start (records ++ [record]) record.leasesAfter := by
  induction records generalizing start with
  | nil =>
      simp only [LeasesThreaded] at threaded
      simp only [List.nil_append, LeasesThreaded]
      exact ⟨starts.trans threaded, trivial⟩
  | cons first rest inductionHypothesis =>
      simp only [LeasesThreaded] at threaded
      simp only [List.cons_append, LeasesThreaded]
      exact ⟨threaded.1, inductionHypothesis threaded.2⟩

/--
Joint proof that records form one contiguous modeled history, lease ownership is threaded from
the empty pool to the final pool, and the projected runtime log is exactly the records' ordered
call/result pairs. The constructor is append-oriented because results are committed in model
order.
-/
inductive RecordChain :
    Nat → Nat → List CallRecord → Nat → LeasePool → List CallBoundary → Prop where
  | nil (initial : Nat) : RecordChain initial 0 [] initial .empty []
  | snoc
      {initial nextCall current : Nat}
      {records : List CallRecord}
      {currentLeases : LeasePool}
      {boundaries : List CallBoundary}
      (prior : RecordChain initial nextCall records current currentLeases boundaries)
      (record : CallRecord)
      (id_is_next : record.id.value = nextCall)
      (starts_at_current : record.before = current)
      (leases_start_at_current : record.leasesBefore = currentLeases) :
      RecordChain initial (nextCall + 1) (records ++ [record]) record.after
        record.leasesAfter (boundaries ++ [.call record.id, .result record.id])

namespace RecordChain

/-- A certified record history contains exactly one record per allocated call identifier. -/
theorem length_eq_nextCall
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    records.length = nextCall := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      simp [inductionHypothesis]

/-- A certified record history assigns identifiers `0, 1, ..., nextCall - 1` in order. -/
theorem ids_eq_range
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    records.map (fun record ↦ record.id.value) = List.range nextCall := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      simp [inductionHypothesis, id_is_next, List.range_succ]

/-- The boundary index of a certified history is exactly the records' ordered call/result pairs. -/
theorem boundaries_eq_records
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    boundaries = recordBoundaries records := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      simp [recordBoundaries, inductionHypothesis]

/-- A certified history threads leases from the empty initial pool to its indexed final pool. -/
theorem leases_threaded
    {initial nextCall final : Nat}
    {records : List CallRecord}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain initial nextCall records final leases boundaries) :
    LeasesThreaded .empty records leases := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      exact leasesThreaded_snoc inductionHypothesis record leases_start

end RecordChain

/-- Internal failures of the deterministic runner itself. -/
inductive RunnerError where
  | protocol (error : ValidationError)
  | notReady (state : RuntimeState)
  | notInTurn (state : RuntimeState)
  | notInStep (state : RuntimeState)
  | leaseInvariant (id : CallId)
deriving DecidableEq, Repr

/-- Replaying an appended suffix is the same as replaying in two stages. -/
theorem replayRaw_append
    (start : RuntimeState)
    (first second : List RuntimeEvent) :
    replayRaw start (first ++ second) =
      match replayRaw start first with
      | .error error => .error error
      | .ok middle => replayRaw middle second := by
  induction first generalizing start with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, replayRaw]
      cases applied : applyRaw start event with
      | error error => rfl
      | ok middle =>
          change
            replayRaw middle (rest ++ second) =
              match replayRaw middle rest with
              | .error error => .error error
              | .ok state => replayRaw state second
          exact inductionHypothesis middle

/--
Pure runtime state. `replayProof` rules out divergence between the in-memory
protocol state and the append-only event log.
-/
structure RunnerState where
  initialModel : Nat
  model : Nat
  protocol : RuntimeState
  nextCall : Nat
  leases : LeasePool
  log : List RuntimeEvent
  records : List CallRecord
  history : RecordChain initialModel nextCall records model leases (callBoundaries log)
  replayProof : replayRaw (.ready 0) log = .ok protocol

namespace RunnerState

def initial (model : Nat) : RunnerState where
  initialModel := model
  model := model
  protocol := .ready 0
  nextCall := 0
  leases := .empty
  log := []
  records := []
  history := .nil model
  replayProof := rfl

/-- No tool call or result exists in the log beyond the exact ordered pairs in `records`. -/
theorem callBoundaries_eq_records (state : RunnerState) :
    callBoundaries state.log = recordBoundaries state.records :=
  state.history.boundaries_eq_records

/-- Every record lease input is its predecessor's output, from empty to `state.leases`. -/
theorem leases_threaded (state : RunnerState) :
    LeasesThreaded .empty state.records state.leases :=
  state.history.leases_threaded

/-- Append one checked non-tool event while extending both state certificates. -/
private def emitNonBoundary
    (state : RunnerState)
    (event : RuntimeEvent)
    (notBoundary : RuntimeEvent.callBoundary? event = none) :
    Except RunnerError RunnerState :=
  match applied : applyRaw state.protocol event with
  | .error error => .error (.protocol error)
  | .ok next =>
      .ok {
        state with
        protocol := next
        log := state.log ++ [event]
        history := by
          simpa [callBoundaries, notBoundary] using state.history
        replayProof := by
          rw [replayRaw_append, state.replayProof]
          change replayRaw state.protocol [event] = .ok next
          simp only [replayRaw, applied]
          rfl
      }

/-- Open the next turn recorded by the protocol state. -/
def beginTurn (state : RunnerState) : Except RunnerError RunnerState :=
  match state.protocol with
  | .ready turn => emitNonBoundary state (.turnStart turn) rfl
  | protocol => .error (.notReady protocol)

/-- Open the next model step recorded by the current turn. -/
def beginStep (state : RunnerState) : Except RunnerError RunnerState :=
  match state.protocol with
  | .turn turn step => emitNonBoundary state (.stepStart turn step) rfl
  | protocol => .error (.notInTurn protocol)

/-- Backwards-compatible helper opening one turn and its first model step. -/
def beginSession (state : RunnerState) : Except RunnerError RunnerState := do
  let inTurn ← state.beginTurn
  inTurn.beginStep

private def settle
    (state : RunnerState)
    (turn step : Nat)
    (record : CallRecord)
    (id_is_next : record.id.value = state.nextCall)
    (starts_at_current : record.before = state.model)
    (leases_start_at_current : record.leasesBefore = state.leases) :
    Except RunnerError RunnerState :=
  let callEvent := RuntimeEvent.toolCall turn step record.id
  let resultEvent := RuntimeEvent.toolResult turn step record.id
  match called : applyRaw state.protocol callEvent with
  | .error error => .error (.protocol error)
  | .ok awaitingResult =>
      match resulted : applyRaw awaitingResult resultEvent with
      | .error error => .error (.protocol error)
      | .ok next =>
          .ok {
            state with
            model := record.after
            protocol := next
            nextCall := state.nextCall + 1
            leases := record.leasesAfter
            log := state.log ++ [callEvent, resultEvent]
            records := state.records ++ [record]
            history := by
              simpa [callEvent, resultEvent, callBoundaries, RuntimeEvent.callBoundary?] using
                RecordChain.snoc state.history record id_is_next starts_at_current
                  leases_start_at_current
            replayProof := by
              rw [replayRaw_append, state.replayProof]
              calc
                replayRaw state.protocol [callEvent, resultEvent] =
                    (do
                      let middle ← applyRaw state.protocol callEvent
                      let finish ← applyRaw middle resultEvent
                      Except.ok finish) := rfl
                _ =
                    (do
                      let finish ← applyRaw awaitingResult resultEvent
                      Except.ok finish) := by rw [called]; rfl
                _ = .ok next := by rw [resulted]; rfl
          }

/--
Dispatch one raw call. Rejections and provider failures still emit a matching
result, so no protocol obligation leaks from a failed tool boundary.
-/
def dispatch (state : RunnerState) (raw : RawCall) : Except RunnerError RunnerState :=
  match state.protocol with
  | .step turn step _ => do
      let assigned : CallId := { value := state.nextCall }
      match validation : validateRaw state.model raw with
      | .error error =>
          settle state turn step {
            id := assigned
            raw := raw
            before := state.model
            after := state.model
            leasesBefore := state.leases
            leasesAfter := state.leases
            evidence := .rejected error validation
          } rfl rfl rfl
      | .ok call =>
          match issuance : state.leases.issue assigned with
          | none => .error (.leaseInvariant assigned)
          | some issued =>
              match consumption : issued.consume assigned with
              | none => .error (.leaseInvariant assigned)
              | some remaining =>
                  match execution : view.execute call with
                  | .error message =>
                      let completion : CounterCompletion call := .error message
                      let policy : SubjectPolicyTrace
                          (Completed := CounterCompletion)
                          (Rejected := fun _ => String)
                          (.proposed assigned call issued)
                          (.settled assigned call remaining (.completed completion)) :=
                        .cons (.decide assigned call issued .allow) <|
                        .cons (.dispatch consumption) <|
                        .cons (.settle completion) (.nil _)
                      settle state turn step {
                        id := assigned
                        raw := raw
                        before := state.model
                        after := completionAfter state.model completion
                        leasesBefore := state.leases
                        leasesAfter := remaining
                        evidence := .admitted call validation issued issuance completion
                          execution policy
                      } rfl rfl rfl
                  | .ok reply =>
                      let completion : CounterCompletion call := .ok reply
                      let policy : SubjectPolicyTrace
                          (Completed := CounterCompletion)
                          (Rejected := fun _ => String)
                          (.proposed assigned call issued)
                          (.settled assigned call remaining (.completed completion)) :=
                        .cons (.decide assigned call issued .allow) <|
                        .cons (.dispatch consumption) <|
                        .cons (.settle completion) (.nil _)
                      settle state turn step {
                        id := assigned
                        raw := raw
                        before := state.model
                        after := completionAfter state.model completion
                        leasesBefore := state.leases
                        leasesAfter := remaining
                        evidence := .admitted call validation issued issuance completion
                          execution policy
                      } rfl rfl rfl
  | state => .error (.notInStep state)

/-- Dispatch calls in model order. -/
def dispatchAll : RunnerState -> List RawCall -> Except RunnerError RunnerState
  | state, [] => .ok state
  | state, call :: rest => do
      let next ← state.dispatch call
      dispatchAll next rest

/-- Close the current step after all calls have settled. -/
def finishStep (state : RunnerState) : Except RunnerError RunnerState :=
  match state.protocol with
  | .step turn step _ => emitNonBoundary state (.stepEnd turn step) rfl
  | protocol => .error (.notInStep protocol)

/-- Close the current turn after its final step. -/
def finishTurn (state : RunnerState) : Except RunnerError RunnerState :=
  match state.protocol with
  | .turn turn nextStep => emitNonBoundary state (.turnEnd turn nextStep) rfl
  | protocol => .error (.notInTurn protocol)

/-- Close the current step and turn after all calls have settled. -/
def finishSession (state : RunnerState) : Except RunnerError RunnerState := do
  let inTurn ← state.finishStep
  inTurn.finishTurn

/-- Run one complete model step from an open turn. -/
def runStep (state : RunnerState) (calls : List RawCall) : Except RunnerError RunnerState := do
  let started ← state.beginStep
  let settled ← started.dispatchAll calls
  settled.finishStep

/-- Run a finite list of model steps inside one open turn. -/
def runSteps : RunnerState -> List (List RawCall) -> Except RunnerError RunnerState
  | state, [] => .ok state
  | state, calls :: rest => do
      let next ← state.runStep calls
      runSteps next rest

/-- Run one turn containing an arbitrary finite list of model steps. -/
def runTurn
    (state : RunnerState)
    (steps : List (List RawCall)) : Except RunnerError RunnerState := do
  let started ← state.beginTurn
  let completed ← started.runSteps steps
  completed.finishTurn

/-- Run a finite list of turns while preserving one replay-certified session log. -/
def runTurns :
    RunnerState -> List (List (List RawCall)) -> Except RunnerError RunnerState
  | state, [] => .ok state
  | state, steps :: rest => do
      let next ← state.runTurn steps
      runTurns next rest

/-- Run one deterministic one-step turn from an initial counter state. -/
def runScript (initialModel : Nat) (calls : List RawCall) : Except RunnerError RunnerState :=
  (initial initialModel).runTurn [calls]

/-- Run a finite multi-turn script from an initial counter state. -/
def runMultiTurn
    (initialModel : Nat)
    (turns : List (List (List RawCall))) : Except RunnerError RunnerState :=
  (initial initialModel).runTurns turns

end RunnerState

/-- A statically typed two-call session used to exercise the intrinsic protocol API. -/
def certifiedTwoCallTrace : Trace (.ready 0) (.ready 1) :=
  .cons (.turnStart 0) <|
  .cons (.stepStart 0 0) <|
  .cons (.toolCall ⟨0⟩ (by simp)) <|
  .cons (.toolResult ⟨0⟩ (by simp)) <|
  .cons (.toolCall ⟨1⟩ (by simp)) <|
  .cons (.toolResult ⟨1⟩ (by simp)) <|
  .cons (.stepEnd 0 0) <|
  .cons (.turnEnd 0 1) .nil

/-- Erasing the static example yields a runtime log accepted to its exact endpoint. -/
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
