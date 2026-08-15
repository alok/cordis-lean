import Cordis.Tool
import Cordis.Protocol

/-!
# Proof-carrying tool policy

A policy decision and a single-use call lease must both authorize dispatch. The indexed
lifecycle prevents denied calls from reaching dispatch, while `LeasePool` provides the pure
checked boundary that a runtime harness can use for lease issue and consumption.

`SubjectPolicyState` is the stronger, request-preserving lifecycle. It carries the exact policy
subject through proposal, decision, and dispatch, then stores a terminal result indexed by that
same subject. The earlier ID-only `PolicyState` remains as a small compatibility layer.

Lean values are freely duplicable: neither a `LeasePool` nor a proof of successful consumption is
a linear capability. The at-most-once results below therefore apply to one explicitly threaded
`SubjectPolicyTrace`. Global exactly-once execution, atomic mutation, persistence, and exclusion
between duplicated external runners remain obligations of a runtime adapter.
-/

namespace Cordis

/-- The currently available, duplicate-free call leases. -/
structure LeasePool where
  available : List CallId
  unique : available.Nodup

namespace LeasePool

/-- A pool with no issued call leases. -/
def empty : LeasePool := ⟨[], List.nodup_nil⟩

/-- Issue or reissue a lease only when its identifier is currently fresh. -/
def issue (pool : LeasePool) (id : CallId) : Option LeasePool :=
  if fresh : id ∉ pool.available then
    some ⟨id :: pool.available, List.nodup_cons.mpr ⟨fresh, pool.unique⟩⟩
  else
    none

/-- Consume one available lease, returning the duplicate-free remainder. -/
def consume (pool : LeasePool) (id : CallId) : Option LeasePool :=
  if _leased : id ∈ pool.available then
    some ⟨pool.available.erase id, pool.unique.erase id⟩
  else
    none

/-- A successfully consumed lease is absent from the returned pool. -/
theorem consumed_absent
    {pool remaining : LeasePool}
    {id : CallId}
    (consumed : pool.consume id = some remaining) :
    id ∉ remaining.available := by
  unfold consume at consumed
  split at consumed
  · simp only [Option.some.injEq] at consumed
    subst remaining
    exact pool.unique.not_mem_erase
  · simp at consumed

/-- Without reissue, a lease cannot be consumed again after a successful consumption. -/
@[simp] theorem consume_after_consumed
    {pool remaining : LeasePool}
    {id : CallId}
    (consumed : pool.consume id = some remaining) :
    remaining.consume id = none := by
  simp [consume, consumed_absent consumed]

/-- Two successful consumptions of one lease are impossible without an intervening reissue. -/
theorem cannot_consume_twice
    {pool once twice : LeasePool}
    {id : CallId}
    (first : pool.consume id = some once)
    (second : once.consume id = some twice) :
    False := by
  rw [consume_after_consumed first] at second
  simp at second

end LeasePool

/-- Policy lifecycle for one proposed tool call and the lease pool carried alongside it. -/
inductive PolicyState where
  | proposed (id : CallId) (leases : LeasePool)
  | decided (id : CallId) (decision : Decision) (leases : LeasePool)
  | dispatched (id : CallId) (leases : LeasePool)
  | settled (id : CallId) (leases : LeasePool)

/--
One policy lifecycle transition. Dispatch exists only after `Decision.allow` and a successful
single-use consumption of the proposed call's lease.
-/
inductive PolicyTransition : PolicyState → PolicyState → Type where
  | decide (id : CallId) (leases : LeasePool) (decision : Decision) :
      PolicyTransition (.proposed id leases) (.decided id decision leases)
  | dispatch {id : CallId} {leases remaining : LeasePool}
      (consumed : leases.consume id = some remaining) :
      PolicyTransition (.decided id .allow leases) (.dispatched id remaining)
  | settle (id : CallId) (leases : LeasePool) :
      PolicyTransition (.dispatched id leases) (.settled id leases)

namespace PolicyTransition

/-- No transition can dispatch a call whose policy decision is denial. -/
theorem denied_cannot_dispatch
    {deniedId dispatchedId : CallId}
    {leases remaining : LeasePool}
    (transition :
      PolicyTransition (.decided deniedId .deny leases) (.dispatched dispatchedId remaining)) :
    False := by
  cases transition

/-- Dispatch consumes the exact lease belonging to the proposed and allowed call. -/
theorem dispatched_lease_absent
    {id : CallId}
    {leases remaining : LeasePool}
    (transition : PolicyTransition (.decided id .allow leases) (.dispatched id remaining)) :
    id ∉ remaining.available := by
  cases transition with
  | dispatch consumed => exact LeasePool.consumed_absent consumed

end PolicyTransition

/-!
## Exact-subject policy lifecycle

The generic parameters are deliberately suitable for a harness boundary:

* `Subject` can be an `AuthorizedCall` or an envelope containing its assigned `CallId`;
* `Completed subject` can be an encoded reply certified to belong to that exact call; and
* `Rejected subject` can retain a structured denial or approval-rejection reason.

The `CallId` remains separate because a harness commonly assigns it after decoding the dependent
call. Transition indices retain both the identifier and subject without requiring equality or
serialization instances for the subject.
-/

universe u v w

/-- A terminal policy disposition indexed by the exact subject that was proposed. -/
inductive SubjectPolicyResult
    {Subject : Type u}
    (Completed : Subject -> Type v)
    (Rejected : Subject -> Type w)
    (subject : Subject) : Type (max v w) where
  /-- The dispatched subject completed with its subject-indexed result. -/
  | completed (result : Completed subject) : SubjectPolicyResult Completed Rejected subject
  /-- The subject was rejected before dispatch. -/
  | rejected (reason : Rejected subject) : SubjectPolicyResult Completed Rejected subject

/--
Policy state retaining an exact subject and its subject-indexed terminal result family.

The same `subject` value occurs in every phase. A settled state additionally retains either a
successful result or a rejection reason whose type is selected by that exact subject.
-/
inductive SubjectPolicyState
    (Subject : Type u)
    (Completed : Subject -> Type v)
    (Rejected : Subject -> Type w) : Type (max u v w) where
  | proposed (id : CallId) (subject : Subject) (leases : LeasePool)
  | decided (id : CallId) (subject : Subject) (decision : Decision) (leases : LeasePool)
  | dispatched (id : CallId) (subject : Subject) (leases : LeasePool)
  | settled
      (id : CallId)
      (subject : Subject)
      (leases : LeasePool)
      (result : SubjectPolicyResult Completed Rejected subject)

/-- Observable phase of the exact-subject policy lifecycle. -/
inductive SubjectPolicyPhase where
  | proposed
  | decided
  | dispatched
  | settled
deriving BEq, DecidableEq, Repr

namespace SubjectPolicyState

/-- Forget policy data while retaining the lifecycle phase. -/
def phase
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w} :
    SubjectPolicyState Subject Completed Rejected -> SubjectPolicyPhase
  | .proposed _ _ _ => .proposed
  | .decided _ _ _ _ => .decided
  | .dispatched _ _ _ => .dispatched
  | .settled _ _ _ _ => .settled

/-- Numerical phase rank used to state strict phase monotonicity. -/
def phaseRank
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    (state : SubjectPolicyState Subject Completed Rejected) : Nat :=
  match state.phase with
  | .proposed => 0
  | .decided => 1
  | .dispatched => 2
  | .settled => 3

end SubjectPolicyState

/--
One exact-subject policy transition.

Dispatch consumes the lease for the same `CallId` and is available only from an `allow` state.
Any non-allow decision can instead terminate as a subject-indexed rejection without dispatch.
-/
inductive SubjectPolicyTransition
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w} :
    SubjectPolicyState Subject Completed Rejected ->
      SubjectPolicyState Subject Completed Rejected -> Type (max u v w) where
  | decide (id : CallId) (subject : Subject) (leases : LeasePool) (decision : Decision) :
      SubjectPolicyTransition
        (.proposed id subject leases)
        (.decided id subject decision leases)
  | dispatch {id : CallId} {subject : Subject} {leases remaining : LeasePool}
      (consumed : leases.consume id = some remaining) :
      SubjectPolicyTransition
        (.decided id subject .allow leases)
        (.dispatched id subject remaining)
  | reject
      {id : CallId}
      {subject : Subject}
      {decision : Decision}
      {leases : LeasePool}
      (notAllowed : decision ≠ .allow)
      (reason : Rejected subject) :
      SubjectPolicyTransition
        (.decided id subject decision leases)
        (.settled id subject leases (.rejected reason))
  | settle
      {id : CallId}
      {subject : Subject}
      {leases : LeasePool}
      (result : Completed subject) :
      SubjectPolicyTransition
        (.dispatched id subject leases)
        (.settled id subject leases (.completed result))

namespace SubjectPolicyTransition

/-- Whether this transition is the unique dispatch edge of the lifecycle. -/
def isDispatch
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start finish : SubjectPolicyState Subject Completed Rejected} :
    SubjectPolicyTransition start finish -> Bool
  | .dispatch _ => true
  | _ => false

/-- Every transition strictly advances the finite policy phase. -/
theorem phase_strict
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start finish : SubjectPolicyState Subject Completed Rejected}
    (transition : SubjectPolicyTransition start finish) :
    start.phaseRank < finish.phaseRank := by
  cases transition <;> simp [SubjectPolicyState.phaseRank, SubjectPolicyState.phase]

/-- Dispatch consumes the lease for the exact `CallId` retained beside the subject. -/
theorem dispatched_lease_absent
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {id : CallId}
    {subject : Subject}
    {leases remaining : LeasePool}
    (transition : SubjectPolicyTransition (Completed := Completed) (Rejected := Rejected)
      (.decided id subject .allow leases)
      (.dispatched id subject remaining)) :
    id ∉ remaining.available := by
  cases transition with
  | dispatch consumed => exact LeasePool.consumed_absent consumed

/-- A denied subject has no direct dispatch transition. -/
theorem denied_cannot_dispatch
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {deniedId dispatchedId : CallId}
    {deniedSubject dispatchedSubject : Subject}
    {leases remaining : LeasePool}
    (transition : SubjectPolicyTransition (Completed := Completed) (Rejected := Rejected)
      (.decided deniedId deniedSubject .deny leases)
      (.dispatched dispatchedId dispatchedSubject remaining)) : False := by
  cases transition

end SubjectPolicyTransition

/-- An intrinsically composed exact-subject policy execution. -/
inductive SubjectPolicyTrace
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w} :
    SubjectPolicyState Subject Completed Rejected ->
      SubjectPolicyState Subject Completed Rejected -> Type (max u v w) where
  | nil (state) : SubjectPolicyTrace state state
  | cons
      {start middle finish}
      (step : SubjectPolicyTransition start middle)
      (rest : SubjectPolicyTrace middle finish) :
      SubjectPolicyTrace start finish

namespace SubjectPolicyTrace

/-- Concatenate two exact-subject policy traces with a common boundary state. -/
def append
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start middle finish : SubjectPolicyState Subject Completed Rejected}
    (first : SubjectPolicyTrace start middle)
    (second : SubjectPolicyTrace middle finish) :
    SubjectPolicyTrace start finish :=
  match first with
  | .nil _ => second
  | .cons step rest => .cons step (append rest second)

/-- Lifecycle phase never decreases along an intrinsically composed trace. -/
theorem phase_monotone
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start finish : SubjectPolicyState Subject Completed Rejected}
    (trace : SubjectPolicyTrace start finish) :
    start.phaseRank <= finish.phaseRank := by
  induction trace with
  | nil => exact Nat.le_refl _
  | cons step rest inductionHypothesis =>
      exact Nat.le_trans
        (Nat.le_of_lt (SubjectPolicyTransition.phase_strict step))
        inductionHypothesis

/-- Count dispatch edges along one explicitly threaded policy trace. -/
def dispatchCount
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start finish : SubjectPolicyState Subject Completed Rejected} :
    SubjectPolicyTrace start finish -> Nat
  | .nil _ => 0
  | .cons step rest => (if step.isDispatch then 1 else 0) + dispatchCount rest

/-- A trace beginning after dispatch cannot dispatch again. -/
theorem dispatchCount_from_dispatched
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {id : CallId}
    {subject : Subject}
    {leases : LeasePool}
    {finish : SubjectPolicyState Subject Completed Rejected}
    (trace : SubjectPolicyTrace (.dispatched id subject leases) finish) :
    trace.dispatchCount = 0 := by
  cases trace with
  | nil => rfl
  | cons step rest =>
      cases step with
      | settle result =>
          cases rest with
          | nil => rfl
          | cons impossible _ => cases impossible

/-- A trace beginning from a settled state contains no dispatch edge. -/
theorem dispatchCount_from_settled
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {id : CallId}
    {subject : Subject}
    {leases : LeasePool}
    {result : SubjectPolicyResult Completed Rejected subject}
    {finish : SubjectPolicyState Subject Completed Rejected}
    (trace : SubjectPolicyTrace (.settled id subject leases result) finish) :
    trace.dispatchCount = 0 := by
  cases trace with
  | nil => rfl
  | cons impossible _ => cases impossible

/--
Within one threaded trace, a subject can cross the dispatch edge at most once.

This is a path property of the indexed phase machine. It is not a global exactly-once or atomicity
claim about duplicated pure states or external workers.
-/
theorem dispatchCount_le_one
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start finish : SubjectPolicyState Subject Completed Rejected}
    (trace : SubjectPolicyTrace start finish) :
    trace.dispatchCount <= 1 := by
  induction trace with
  | nil => simp [dispatchCount]
  | cons step rest inductionHypothesis =>
      cases step with
      | decide => simpa [dispatchCount, SubjectPolicyTransition.isDispatch]
          using inductionHypothesis
      | dispatch consumed =>
          simp [dispatchCount, SubjectPolicyTransition.isDispatch,
            dispatchCount_from_dispatched rest]
      | reject notAllowed reason =>
          simp [dispatchCount, SubjectPolicyTransition.isDispatch,
            dispatchCount_from_settled rest]
      | settle result =>
          simp [dispatchCount, SubjectPolicyTransition.isDispatch,
            dispatchCount_from_settled rest]

/-- Two dispatch edges cannot occur in one explicitly threaded trace. -/
theorem cannot_dispatch_twice
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {start finish : SubjectPolicyState Subject Completed Rejected}
    (trace : SubjectPolicyTrace start finish) :
    Not (2 <= trace.dispatchCount) := by
  intro twice
  have atMostOne := dispatchCount_le_one trace
  omega

/-- A trace starting from a denied decision cannot contain a dispatch edge. -/
theorem denied_dispatchCount_eq_zero
    {Subject : Type u}
    {Completed : Subject -> Type v}
    {Rejected : Subject -> Type w}
    {id : CallId}
    {subject : Subject}
    {leases : LeasePool}
    {finish : SubjectPolicyState Subject Completed Rejected}
    (trace : SubjectPolicyTrace (.decided id subject .deny leases) finish) :
    trace.dispatchCount = 0 := by
  cases trace with
  | nil => rfl
  | cons step rest =>
      cases step with
      | reject notAllowed reason =>
          simpa [dispatchCount, SubjectPolicyTransition.isDispatch] using
            dispatchCount_from_settled rest

end SubjectPolicyTrace

end Cordis
