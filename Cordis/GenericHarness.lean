import Cordis.Policy
import Cordis.Protocol
import Cordis.ToolWire

/-!
# Generic proof-carrying harness

The runner in this module is generic over one coherent dependent tool configuration. Admission,
policy, provider execution, request-indexed encoding, lease accounting, model transitions, and
protocol replay are connected by types rather than by independently mutable runtime fields.
-/

namespace Cordis.GenericHarness

open Cordis

universe u v

/-- An exact-call policy answer: either allow, or retain a non-allow decision and its reason. -/
inductive PolicyDecision
    {Call : Type u}
    (Rejected : Call -> Type v)
    (call : Call) : Type (max u v) where
  | allow
  | reject
      (decision : Decision)
      (notAllowed : decision ≠ .allow)
      (reason : Rejected call)

/-- One coherent dependent catalog, admission boundary, provider view, and exact-call policy. -/
structure Config (Model Capability : Type u) where
  catalog : ToolCatalog Model Capability
  wire : ToolWire catalog
  needs : Needs catalog.signature
  needsDecidable : (tool : catalog.Tool) -> Decidable (needs tool)
  registry : Registry catalog.signature
  view : View catalog.signature registry needs
  granted : Model -> RawCall -> Capability -> Prop
  grantedDecidable :
    (model : Model) ->
    (raw : RawCall) ->
    (capability : Capability) ->
      Decidable (granted model raw capability)
  PolicyRejected : AuthorizedCall catalog.signature needs -> Type u
  renderPolicyRejected :
    (call : AuthorizedCall catalog.signature needs) -> PolicyRejected call -> String
  decide :
    (before : Model) ->
    (raw : RawCall) ->
    (call : AuthorizedCall catalog.signature needs) ->
      PolicyDecision PolicyRejected call

namespace Config

/-- The dependent call family selected by a configuration's exact catalog and needs predicate. -/
abbrev Call
    {Model Capability : Type u}
    (cfg : Config Model Capability) :=
  AuthorizedCall cfg.catalog.signature cfg.needs

/-- Provider completion indexed by the exact admitted call. -/
abbrev Completion
    {Model Capability : Type u}
    (cfg : Config Model Capability)
    (call : cfg.Call) :=
  Except String (Reply call)

/-- Admit a raw call using the configuration's call-dependent capability grant. -/
def validate
    {Model Capability : Type u}
    (cfg : Config Model Capability)
    (before : Model)
    (raw : RawCall) : Except AdmissionError cfg.Call :=
  ToolWire.validate cfg.wire cfg.needs cfg.needsDecidable before
    (cfg.granted before raw) (cfg.grantedDecidable before raw) raw

end Config

/-- Provider failure preserves the model; a certified reply selects its proved successor. -/
def completionAfter
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (before : Model)
    {call : cfg.Call} : cfg.Completion call -> Model
  | .error _ => before
  | .ok reply => reply.value.after

/-- The externally visible disposition of one settled generic call. -/
inductive CallOutcome where
  | admissionRejected (error : AdmissionError)
  | policyRejected (decision : Decision) (reason : String)
  | providerFailed (message : String)
  | toolFailed
  | succeeded
deriving BEq, DecidableEq, Repr

/--
Dependent evidence connecting raw admission to policy and, only when allowed, provider dispatch.
-/
inductive CallEvidence
    {Model Capability : Type u}
    (cfg : Config Model Capability)
    (id : CallId)
    (raw : RawCall)
    (before : Model) :
    (after : Model) ->
    (leasesBefore leasesAfter : LeasePool) -> Type u where
  | admissionRejected
      {leases : LeasePool}
      (error : AdmissionError)
      (validation : cfg.validate before raw = .error error) :
      CallEvidence cfg id raw before before leases leases
  | policyRejected
      {leases : LeasePool}
      (call : cfg.Call)
      (validation : cfg.validate before raw = .ok call)
      (decision : Decision)
      (notAllowed : decision ≠ .allow)
      (reason : cfg.PolicyRejected call)
      (decisionEvidence :
        cfg.decide before raw call = .reject decision notAllowed reason)
      (policy : SubjectPolicyTrace
        (Completed := cfg.Completion)
        (Rejected := cfg.PolicyRejected)
        (.proposed id call leases)
        (.settled id call leases (.rejected reason))) :
      CallEvidence cfg id raw before before leases leases
  | completed
      {leasesBefore leasesAfter : LeasePool}
      (call : cfg.Call)
      (validation : cfg.validate before raw = .ok call)
      (allowed : cfg.decide before raw call = .allow)
      (issued : LeasePool)
      (issuance : leasesBefore.issue id = some issued)
      (consumption : issued.consume id = some leasesAfter)
      (completion : cfg.Completion call)
      (execution : cfg.view.execute call = completion)
      (policy : SubjectPolicyTrace
        (Completed := cfg.Completion)
        (Rejected := cfg.PolicyRejected)
        (.proposed id call issued)
        (.settled id call leasesAfter (.completed completion))) :
      CallEvidence cfg id raw before (completionAfter before completion)
        leasesBefore leasesAfter

namespace CallEvidence

/-- User-facing disposition derived from the retained dependent evidence. -/
def outcome
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before after : Model}
    {leasesBefore leasesAfter : LeasePool} :
    CallEvidence cfg id raw before after leasesBefore leasesAfter -> CallOutcome
  | .admissionRejected error _ => .admissionRejected error
  | .policyRejected (call := call) (decision := decision) (reason := reason) .. =>
      .policyRejected decision (cfg.renderPolicyRejected call reason)
  | .completed (completion := .error message) .. => .providerFailed message
  | .completed (completion := .ok reply) .. =>
      match reply.value.result with
      | .error _ => .toolFailed
      | .ok _ => .succeeded

/-- Request-indexed result encoding exists exactly when the provider returned a certified reply. -/
def encodedResult
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before after : Model}
    {leasesBefore leasesAfter : LeasePool} :
    CallEvidence cfg id raw before after leasesBefore leasesAfter -> Option Lean.Json
  | .admissionRejected .. => none
  | .policyRejected .. => none
  | .completed (call := call) (completion := .error _) .. => none
  | .completed (call := call) (completion := .ok reply) .. =>
      some (cfg.wire.encodeCertifiedResult call.op call.request reply.value)

/-- Dispatch edges retained by the exact-subject policy trace. -/
def dispatchCount
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before after : Model}
    {leasesBefore leasesAfter : LeasePool} :
    CallEvidence cfg id raw before after leasesBefore leasesAfter -> Nat
  | .admissionRejected .. => 0
  | .policyRejected (policy := policy) .. => policy.dispatchCount
  | .completed (policy := policy) .. => policy.dispatchCount

private theorem dispatchCount_to_rejected
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type u}
    {id : CallId}
    {subject : Subject}
    {leases : LeasePool}
    {reason : Rejected subject}
    (trace : SubjectPolicyTrace (Completed := Completed) (Rejected := Rejected)
      (.proposed id subject leases)
      (.settled id subject leases (.rejected reason))) :
    trace.dispatchCount = 0 := by
  cases trace with
  | cons first rest =>
      cases first with
      | decide =>
          cases rest with
          | cons second suffix =>
              cases second with
              | dispatch consumed =>
                  cases suffix with
                  | cons third tail =>
                      cases third with
                      | settle result =>
                          cases tail with
                          | cons impossible _ => cases impossible
              | reject notAllowed rejected =>
                  simpa [SubjectPolicyTrace.dispatchCount,
                    SubjectPolicyTransition.isDispatch] using
                    SubjectPolicyTrace.dispatchCount_from_settled suffix

/-- Admission rejection performs no policy dispatch. -/
@[simp] theorem admissionRejected_dispatchCount_eq_zero
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before : Model}
    {leases : LeasePool}
    (error : AdmissionError)
    (validation : cfg.validate before raw = .error error) :
    dispatchCount
      (CallEvidence.admissionRejected (cfg := cfg) (id := id) (raw := raw)
        (before := before) (leases := leases) error validation) = 0 :=
  rfl

/-- Admitted policy rejection performs no dispatch for either `ask` or `deny`. -/
theorem policyRejected_dispatchCount_eq_zero
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before : Model}
    {leases : LeasePool}
    (call : cfg.Call)
    (validation : cfg.validate before raw = .ok call)
    (decision : Decision)
    (notAllowed : decision ≠ .allow)
    (reason : cfg.PolicyRejected call)
    (decisionEvidence : cfg.decide before raw call = .reject decision notAllowed reason)
    (policy : SubjectPolicyTrace
      (Completed := cfg.Completion)
      (Rejected := cfg.PolicyRejected)
      (.proposed id call leases)
      (.settled id call leases (.rejected reason))) :
    dispatchCount
      (CallEvidence.policyRejected (cfg := cfg) (id := id) (raw := raw)
        (before := before) call validation decision notAllowed reason decisionEvidence
          policy) = 0 :=
  dispatchCount_to_rejected policy

/-- Every admitted and completed call crosses the policy dispatch edge exactly once. -/
theorem completed_dispatchCount_eq_one
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before : Model}
    {leasesBefore leasesAfter issued : LeasePool}
    (call : cfg.Call)
    (validation : cfg.validate before raw = .ok call)
    (allowed : cfg.decide before raw call = .allow)
    (issuance : leasesBefore.issue id = some issued)
    (consumption : issued.consume id = some leasesAfter)
    (completion : cfg.Completion call)
    (execution : cfg.view.execute call = completion)
    (policy : SubjectPolicyTrace
      (Completed := cfg.Completion)
      (Rejected := cfg.PolicyRejected)
      (.proposed id call issued)
      (.settled id call leasesAfter (.completed completion))) :
    dispatchCount
      (CallEvidence.completed (cfg := cfg) (id := id) (raw := raw) (before := before)
        call validation allowed issued issuance consumption completion execution policy) = 1 :=
  SubjectPolicyTrace.dispatchCount_to_completed policy

/-- A completed call's consumed terminal lease is absent. -/
theorem completed_terminal_lease_absent
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before : Model}
    {leasesBefore leasesAfter issued : LeasePool}
    (call : cfg.Call)
    (_validation : cfg.validate before raw = .ok call)
    (_allowed : cfg.decide before raw call = .allow)
    (_issuance : leasesBefore.issue id = some issued)
    (consumption : issued.consume id = some leasesAfter)
    (completion : cfg.Completion call)
    (_execution : cfg.view.execute call = completion)
    (_policy : SubjectPolicyTrace
      (Completed := cfg.Completion)
      (Rejected := cfg.PolicyRejected)
      (.proposed id call issued)
      (.settled id call leasesAfter (.completed completion))) :
    id ∉ leasesAfter.available :=
  LeasePool.consumed_absent consumption

/-- Every settled branch restores the original lease pool. -/
theorem leases_restored
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {id : CallId}
    {raw : RawCall}
    {before after : Model}
    {leasesBefore leasesAfter : LeasePool}
    (evidence : CallEvidence cfg id raw before after leasesBefore leasesAfter) :
    leasesAfter = leasesBefore := by
  cases evidence with
  | admissionRejected => rfl
  | policyRejected => rfl
  | completed call validation allowed issued issuance consumption completion execution policy =>
      exact LeasePool.consume_after_issue_restores issuance consumption

end CallEvidence

/-- Audit data retaining raw input and exact dependent evidence for its settlement. -/
structure CallRecord
    {Model Capability : Type u}
    (cfg : Config Model Capability) where
  id : CallId
  raw : RawCall
  before : Model
  after : Model
  leasesBefore : LeasePool
  leasesAfter : LeasePool
  evidence : CallEvidence cfg id raw before after leasesBefore leasesAfter

namespace CallRecord

def name
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (record : CallRecord cfg) : String :=
  record.raw.name

def outcome
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (record : CallRecord cfg) : CallOutcome :=
  record.evidence.outcome

def encodedResult
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (record : CallRecord cfg) : Option Lean.Json :=
  record.evidence.encodedResult

def dispatchCount
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (record : CallRecord cfg) : Nat :=
  record.evidence.dispatchCount

end CallRecord

/-- Tool-boundary projection of the existing runtime protocol vocabulary. -/
inductive CallBoundary where
  | call (id : CallId)
  | result (id : CallId)
deriving BEq, DecidableEq, Repr

namespace RuntimeEvent

/-- Retain only tool calls and results while erasing turn and step coordinates. -/
def callBoundary? : Cordis.RuntimeEvent -> Option CallBoundary
  | .toolCall _ _ id => some (.call id)
  | .toolResult _ _ id => some (.result id)
  | _ => none

end RuntimeEvent

/-- Ordered tool-call and result projection of a runtime log. -/
def callBoundaries (log : List Cordis.RuntimeEvent) : List CallBoundary :=
  log.filterMap RuntimeEvent.callBoundary?

/-- Exact call/result pairs required by the settled record sequence. -/
def recordBoundaries
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (records : List (CallRecord cfg)) : List CallBoundary :=
  records.flatMap fun record ↦ [.call record.id, .result record.id]

/-- Record model inputs and outputs form one contiguous chain. -/
def ModelsThreaded
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (start : Model) : List (CallRecord cfg) -> Model -> Prop
  | [], finish => finish = start
  | record :: records, finish =>
      record.before = start ∧ ModelsThreaded record.after records finish

/-- Record lease inputs and outputs form one contiguous chain. -/
def LeasesThreaded
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    (start : LeasePool) : List (CallRecord cfg) -> LeasePool -> Prop
  | [], finish => finish = start
  | record :: records, finish =>
      record.leasesBefore = start ∧ LeasesThreaded record.leasesAfter records finish

private theorem modelsThreaded_snoc
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {start current : Model}
    {records : List (CallRecord cfg)}
    (threaded : ModelsThreaded start records current)
    (record : CallRecord cfg)
    (starts : record.before = current) :
    ModelsThreaded start (records ++ [record]) record.after := by
  induction records generalizing start with
  | nil =>
      simp only [ModelsThreaded] at threaded
      simp only [List.nil_append, ModelsThreaded]
      exact ⟨starts.trans threaded, trivial⟩
  | cons first rest inductionHypothesis =>
      simp only [ModelsThreaded] at threaded
      simp only [List.cons_append, ModelsThreaded]
      exact ⟨threaded.1, inductionHypothesis threaded.2⟩

private theorem leasesThreaded_snoc
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {start current : LeasePool}
    {records : List (CallRecord cfg)}
    (threaded : LeasesThreaded start records current)
    (record : CallRecord cfg)
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

/-- Joint model, lease, call-ID, record, and protocol-boundary history invariant. -/
inductive RecordChain
    {Model Capability : Type u}
    (cfg : Config Model Capability) :
    Model ->
    Nat ->
    List (CallRecord cfg) ->
    Model ->
    LeasePool ->
    List CallBoundary -> Prop where
  | nil (initial : Model) : RecordChain cfg initial 0 [] initial .empty []
  | snoc
      {initial current : Model}
      {nextCall : Nat}
      {records : List (CallRecord cfg)}
      {currentLeases : LeasePool}
      {boundaries : List CallBoundary}
      (prior : RecordChain cfg initial nextCall records current currentLeases boundaries)
      (record : CallRecord cfg)
      (id_is_next : record.id.value = nextCall)
      (starts_at_current : record.before = current)
      (leases_start_at_current : record.leasesBefore = currentLeases) :
      RecordChain cfg initial (nextCall + 1) (records ++ [record]) record.after
        record.leasesAfter (boundaries ++ [.call record.id, .result record.id])

namespace RecordChain

theorem length_eq_nextCall
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {initial final : Model}
    {nextCall : Nat}
    {records : List (CallRecord cfg)}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain cfg initial nextCall records final leases boundaries) :
    records.length = nextCall := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      simp [inductionHypothesis]

theorem ids_eq_range
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {initial final : Model}
    {nextCall : Nat}
    {records : List (CallRecord cfg)}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain cfg initial nextCall records final leases boundaries) :
    records.map (fun record ↦ record.id.value) = List.range nextCall := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      simp [inductionHypothesis, id_is_next, List.range_succ]

theorem boundaries_eq_records
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {initial final : Model}
    {nextCall : Nat}
    {records : List (CallRecord cfg)}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain cfg initial nextCall records final leases boundaries) :
    boundaries = recordBoundaries records := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      simp [recordBoundaries, inductionHypothesis]

theorem models_threaded
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {initial final : Model}
    {nextCall : Nat}
    {records : List (CallRecord cfg)}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain cfg initial nextCall records final leases boundaries) :
    ModelsThreaded initial records final := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      exact modelsThreaded_snoc inductionHypothesis record starts_at_current

theorem leases_threaded
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {initial final : Model}
    {nextCall : Nat}
    {records : List (CallRecord cfg)}
    {leases : LeasePool}
    {boundaries : List CallBoundary}
    (history : RecordChain cfg initial nextCall records final leases boundaries) :
    LeasesThreaded .empty records leases := by
  induction history with
  | nil => rfl
  | snoc prior record id_is_next starts_at_current leases_start inductionHypothesis =>
      exact leasesThreaded_snoc inductionHypothesis record leases_start

end RecordChain

/-- The only trusted runner failure is an internal violation of fresh lease issue or consume. -/
inductive RunnerError where
  | leaseInvariant (id : CallId)
deriving DecidableEq, Repr

/-- Replaying an appended suffix is equivalent to replaying it in two stages. -/
theorem replayRaw_append
    (start : RuntimeState)
    (first second : List Cordis.RuntimeEvent) :
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
Phase-indexed pure runner. The event log always replays to the erasure of its static phase.
-/
structure Runner
    {Model Capability : Type u}
    (cfg : Config Model Capability)
    (phase : SessionState) where
  initialModel : Model
  model : Model
  nextCall : Nat
  leases : LeasePool
  log : List Cordis.RuntimeEvent
  records : List (CallRecord cfg)
  history : RecordChain cfg initialModel nextCall records model leases (callBoundaries log)
  replayProof : replayRaw (.ready 0) log = .ok (eraseState phase)

namespace Runner

def initial
    {Model Capability : Type u}
    (cfg : Config Model Capability)
    (model : Model) : Runner cfg (.ready 0) where
  initialModel := model
  model := model
  nextCall := 0
  leases := .empty
  log := []
  records := []
  history := .nil model
  replayProof := rfl

theorem records_length_eq_nextCall
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {phase : SessionState}
    (state : Runner cfg phase) : state.records.length = state.nextCall :=
  state.history.length_eq_nextCall

theorem ids_eq_range
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {phase : SessionState}
    (state : Runner cfg phase) :
    state.records.map (fun record ↦ record.id.value) = List.range state.nextCall :=
  state.history.ids_eq_range

theorem models_threaded
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {phase : SessionState}
    (state : Runner cfg phase) :
    ModelsThreaded state.initialModel state.records state.model :=
  state.history.models_threaded

theorem leases_threaded
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {phase : SessionState}
    (state : Runner cfg phase) :
    LeasesThreaded .empty state.records state.leases :=
  state.history.leases_threaded

theorem callBoundaries_eq_records
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {phase : SessionState}
    (state : Runner cfg phase) :
    callBoundaries state.log = recordBoundaries state.records :=
  state.history.boundaries_eq_records

private def emitNonBoundary
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {start finish : SessionState}
    (state : Runner cfg start)
    (event : Event start finish)
    (notBoundary : RuntimeEvent.callBoundary? event.erase = none) : Runner cfg finish where
  initialModel := state.initialModel
  model := state.model
  nextCall := state.nextCall
  leases := state.leases
  log := state.log ++ [event.erase]
  records := state.records
  history := by
    simpa [callBoundaries, notBoundary] using state.history
  replayProof := by
    rw [replayRaw_append, state.replayProof]
    simpa [Trace.single, Trace.erase] using replayRaw_eraseTrace (Trace.single event)

/-- Open the statically known next turn. -/
def beginTurn
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn : Nat}
    (state : Runner cfg (.ready turn)) : Runner cfg (.turn turn 0) :=
  emitNonBoundary state (.turnStart turn) rfl

@[simp]
theorem beginTurn_log
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn : Nat}
    (state : Runner cfg (.ready turn)) :
    state.beginTurn.log = state.log ++ [.turnStart turn] := rfl

/-- Open the statically known next step with no pending calls. -/
def beginStep
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.turn turn step)) : Runner cfg (.step turn step []) :=
  emitNonBoundary state (.stepStart turn step) rfl

@[simp]
theorem beginStep_log
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.turn turn step)) :
    state.beginStep.log = state.log ++ [.stepStart turn step] := rfl

def settle
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.step turn step []))
    (record : CallRecord cfg)
    (id_is_next : record.id.value = state.nextCall)
    (starts_at_current : record.before = state.model)
    (leases_start_at_current : record.leasesBefore = state.leases) :
    Runner cfg (.step turn step []) :=
  let callEvent := Cordis.RuntimeEvent.toolCall turn step record.id
  let resultEvent := Cordis.RuntimeEvent.toolResult turn step record.id
  {
    initialModel := state.initialModel
    model := record.after
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
      simp [callEvent, resultEvent, replayRaw, applyRaw, eraseState, bind, Except.bind]
  }

/-- One settled dispatch exposes the exact appended record and log extension. -/
structure DispatchResult
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (before : Runner cfg (.step turn step [])) where
  record : CallRecord cfg
  runner : Runner cfg (.step turn step [])
  log_eq : runner.log = before.log ++ [
    .toolCall turn step record.id,
    .toolResult turn step record.id
  ]
  records_eq : runner.records = before.records ++ [record]

/--
Construct the completed branch when completion came from an external adapter.  The adapter must
still provide the exact generic `View.execute` equality; this constructor only centralizes the
lease, policy-trace, record-chain, and replay certificates rather than weakening them.
-/
def dispatchCompleted
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.step turn step []))
    (raw : RawCall)
    (call : cfg.Call)
    (validation : cfg.validate state.model raw = .ok call)
    (allowed : cfg.decide state.model raw call = .allow)
    (issued : LeasePool)
    (issuance : state.leases.issue { value := state.nextCall } = some issued)
    {remaining : LeasePool}
    (consumption : issued.consume { value := state.nextCall } = some remaining)
    (completion : cfg.Completion call)
    (execution : cfg.view.execute call = completion)
    (policy : SubjectPolicyTrace
      (Completed := cfg.Completion)
      (Rejected := cfg.PolicyRejected)
      (.proposed { value := state.nextCall } call issued)
      (.settled { value := state.nextCall } call remaining (.completed completion))) :
    DispatchResult state :=
  let record : CallRecord cfg := {
    id := { value := state.nextCall }
    raw := raw
    before := state.model
    after := completionAfter state.model completion
    leasesBefore := state.leases
    leasesAfter := remaining
    evidence := .completed call validation allowed issued issuance consumption
      completion execution policy
  }
  let next := settle state record rfl rfl rfl
  { record, runner := next, log_eq := rfl, records_eq := rfl }

/--
Settle one raw call in an empty-pending step. Policy is decided before lease issuance; non-allow
and admission rejection settle records without invoking the provider.
-/
def dispatch
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.step turn step []))
    (raw : RawCall) : Except RunnerError (DispatchResult state) :=
  let assigned : CallId := { value := state.nextCall }
  match validation : cfg.validate state.model raw with
  | .error error =>
      let record : CallRecord cfg := {
        id := assigned
        raw := raw
        before := state.model
        after := state.model
        leasesBefore := state.leases
        leasesAfter := state.leases
        evidence := .admissionRejected error validation
      }
      let next := settle state record rfl rfl rfl
      .ok { record, runner := next, log_eq := rfl, records_eq := rfl }
  | .ok call =>
      match decided : cfg.decide state.model raw call with
      | .reject decision notAllowed reason =>
          let policy : SubjectPolicyTrace
              (Completed := cfg.Completion)
              (Rejected := cfg.PolicyRejected)
              (.proposed assigned call state.leases)
              (.settled assigned call state.leases (.rejected reason)) :=
            .cons (.decide assigned call state.leases decision) <|
            .cons (.reject notAllowed reason) (.nil _)
          let record : CallRecord cfg := {
            id := assigned
            raw := raw
            before := state.model
            after := state.model
            leasesBefore := state.leases
            leasesAfter := state.leases
            evidence := .policyRejected call validation decision notAllowed reason decided policy
          }
          let next := settle state record rfl rfl rfl
          .ok { record, runner := next, log_eq := rfl, records_eq := rfl }
      | .allow =>
          match issuance : state.leases.issue assigned with
          | none => .error (.leaseInvariant assigned)
          | some issued =>
              match consumption : issued.consume assigned with
              | none => .error (.leaseInvariant assigned)
              | some remaining =>
                  let completion : cfg.Completion call := cfg.view.execute call
                  let policy : SubjectPolicyTrace
                      (Completed := cfg.Completion)
                      (Rejected := cfg.PolicyRejected)
                      (.proposed assigned call issued)
                      (.settled assigned call remaining (.completed completion)) :=
                    .cons (.decide assigned call issued .allow) <|
                    .cons (.dispatch consumption) <|
                    .cons (.settle completion) (.nil _)
                  let record : CallRecord cfg := {
                    id := assigned
                    raw := raw
                    before := state.model
                    after := completionAfter state.model completion
                    leasesBefore := state.leases
                    leasesAfter := remaining
                    evidence := .completed call validation decided issued issuance consumption
                      completion rfl policy
                  }
                  let next := settle state record rfl rfl rfl
                  .ok { record, runner := next, log_eq := rfl, records_eq := rfl }

/-- Dispatch a finite list in model order while retaining the same empty-pending phase. -/
def dispatchAll
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat} :
    Runner cfg (.step turn step []) ->
    List RawCall ->
    Except RunnerError (Runner cfg (.step turn step []))
  | state, [] => .ok state
  | state, raw :: rest => do
      let result ← state.dispatch raw
      dispatchAll result.runner rest

/-- Close an empty-pending step. -/
def finishStep
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.step turn step [])) : Runner cfg (.turn turn (step + 1)) :=
  emitNonBoundary state (.stepEnd turn step) rfl

@[simp]
theorem finishStep_log
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.step turn step [])) :
    state.finishStep.log = state.log ++ [.stepEnd turn step] := rfl

/-- Close the statically known turn. -/
def finishTurn
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn nextStep : Nat}
    (state : Runner cfg (.turn turn nextStep)) : Runner cfg (.ready (turn + 1)) :=
  emitNonBoundary state (.turnEnd turn nextStep) rfl

@[simp]
theorem finishTurn_log
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn nextStep : Nat}
    (state : Runner cfg (.turn turn nextStep)) :
    state.finishTurn.log = state.log ++ [.turnEnd turn nextStep] := rfl

/-- Run one complete step from an open turn. -/
def runStep
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn step : Nat}
    (state : Runner cfg (.turn turn step))
    (calls : List RawCall) : Except RunnerError (Runner cfg (.turn turn (step + 1))) := do
  let started := state.beginStep
  let settled ← started.dispatchAll calls
  pure settled.finishStep

/-- Run one complete one-step turn. -/
def runTurn
    {Model Capability : Type u}
    {cfg : Config Model Capability}
    {turn : Nat}
    (state : Runner cfg (.ready turn))
    (calls : List RawCall) : Except RunnerError (Runner cfg (.ready (turn + 1))) := do
  let started := state.beginTurn
  let completed ← started.runStep calls
  pure completed.finishTurn

end Runner

end Cordis.GenericHarness
