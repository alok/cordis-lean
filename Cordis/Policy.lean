import Cordis.Tool
import Cordis.Protocol

/-!
# Proof-carrying tool policy

A policy decision and a single-use call lease must both authorize dispatch. The indexed
lifecycle prevents denied calls from reaching dispatch, while `LeasePool` provides the pure
checked boundary that a runtime harness can use for lease issue and consumption.
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

end Cordis
