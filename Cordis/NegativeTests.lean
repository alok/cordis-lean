import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Protocol

/-!
# Static rejection tests

These checks complement executable tests by asserting that representative illegal values fail
to elaborate. Each nested command is expected to produce the indicated error; if a later change
makes the invalid construction type-check, `#guard_msgs` fails the build.
-/

set_option autoImplicit false

namespace Cordis.NegativeTests

open Cordis.Examples.Counter

private inductive RequestIndexedOperation where
  | choose
deriving DecidableEq

private def requestIndexedSignature : Signature where
  Op := RequestIndexedOperation
  opDecEq := inferInstance
  Request
    | .choose => Bool
  Response
    | .choose, true => Nat
    | .choose, false => String

private def requestIndexedNeeds : Needs requestIndexedSignature := fun _ ↦ True

private def trueRequest : AuthorizedCall requestIndexedSignature requestIndexedNeeds where
  op := .choose
  request := true
  declared := trivial

/-! The request value itself selects the response type: `true` requires a natural number. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : Reply trueRequest where
  value := "not a natural number"

/-! A result cannot be emitted when no call identifier is pending. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : Event (.step 0 0 []) (.step 0 0 []) :=
  .toolResult ⟨0⟩ (by simp)

/-! A call identifier already pending cannot be called again. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : Event (.step 0 0 [⟨0⟩]) (.step 0 0 [⟨0⟩, ⟨0⟩]) :=
  .toolCall ⟨0⟩ (by simp)

/-! A denied subject has no dispatch constructor. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example
    (id : CallId)
    (subject : Nat)
    (leases remaining : LeasePool)
    (consumed : leases.consume id = some remaining) :
    SubjectPolicyTransition
      (Completed := fun _ : Nat ↦ Unit)
      (Rejected := fun _ : Nat ↦ String)
      (.decided id subject .deny leases)
      (.dispatched id subject remaining) :=
  .dispatch consumed

private def relyingView : Lifecycle.CommittedView Unit Nat where
  resolve _ := some 1

private def installedConsumer : Lifecycle.Consumer Unit Nat where
  fiber := 2
  installed := true
  view := relyingView

/-! An installed consumer relying on provider `1` prevents withdrawal of provider `1`. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : Lifecycle.Withdrawable [installedConsumer] 1 := by
  simp [Lifecycle.Withdrawable, installedConsumer, relyingView,
    Lifecycle.CommittedView.ReliesOn]

private def rejectedRecordZero : Harness.CallRecord where
  id := ⟨0⟩
  raw := rawUnknown
  before := 0
  after := 0
  leasesBefore := .empty
  leasesAfter := .empty
  evidence := .rejected (.unknownTool rawUnknown.name) rfl

private theorem historyZero : Harness.RecordChain 0 1 [rejectedRecordZero] 0 .empty
    [.call ⟨0⟩, .result ⟨0⟩] :=
  .snoc (.nil 0) rejectedRecordZero rfl rfl rfl

private def logNinetyNine : List RuntimeEvent := [
  .turnStart 0,
  .stepStart 0 0,
  .toolCall 0 0 ⟨99⟩,
  .toolResult 0 0 ⟨99⟩,
  .stepEnd 0 0,
  .turnEnd 0 1
]

/-!
A replay-valid log for call `99` cannot be paired with a record/history certificate for call `0`.
-/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : Harness.RunnerState where
  initialModel := 0
  model := 0
  protocol := .ready 1
  nextCall := 1
  leases := .empty
  log := logNinetyNine
  records := [rejectedRecordZero]
  history := historyZero
  replayProof := by decide

/-! A dependent structure update cannot replace the final lease pool without new history proof. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (state : Harness.RunnerState) : Harness.RunnerState := {
  state with leases := .empty
}

end Cordis.NegativeTests
