import Cordis.Harness
import Cordis.Coeffect
import Cordis.ContextualEquivalence
import Cordis.Examples.DependentChoice
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Protocol
import Cordis.RichStream
import Cordis.RuntimeRefinement
import Cordis.Schedule
import Cordis.Session
import Cordis.StreamSession
import Cordis.UnifiedContext

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
  evidence := .admissionRejected (.unknownTool rawUnknown.name) rfl

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
  phase := .ready 1
  runner := {
    initialModel := 0
    model := 0
    nextCall := 1
    leases := .empty
    log := logNinetyNine
    records := [rejectedRecordZero]
    history := historyZero
    replayProof := by decide
  }

/-! A dependent structure update cannot replace the final lease pool without new history proof. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example {phase : SessionState}
    (state : GenericHarness.Runner Harness.counterConfig phase) :
    GenericHarness.Runner Harness.counterConfig phase := {
  state with leases := .empty
}

/-! Log-only event kinds cannot carry surface placement metadata. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : Session.LoggedEvent Session.noExtensions where
  visibility := .logOnly
  seq := 0
  kind := .turnStart
  payload := { turn := 0 }
  intent := Session.SurfaceIntent.append []

/-! A model request cannot substitute a message list that was not derived from its session. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : Session.ModelRequest Session.certifiedSession where
  header := Session.exampleHeader
  messages := []
  messages_eq := by simp [Session.certifiedSession_messages]
  latestHeader_eq := rfl
  logLength := 5
  logLength_eq := rfl
  nextSeq_eq := rfl

/-! A rich session with tool boundaries cannot be paired with an empty structural runner log. -/

/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs (substring := true) in
example : Harness.RunnerState where
  phase := .ready 0
  runner := GenericHarness.Runner.initial Harness.counterConfig 0
  session := Session.certifiedSession
  projection_eq := by decide

/-! The trusted phase-indexed runner cannot close a step while it is ready. -/

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
example : GenericHarness.Runner Harness.counterConfig (.turn 0 1) :=
  (GenericHarness.Runner.initial Harness.counterConfig 0).finishStep

/-! A runner for the structured dependent-choice model cannot be replaced by a counter runner. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : GenericHarness.Runner Examples.DependentChoice.config (.ready 0) :=
  GenericHarness.Runner.initial Harness.counterConfig 0

/-! A dependent coeffect key cannot be populated with another key's value type. -/

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
example : Coeffect.Context Coeffect.Example.Key Coeffect.Example.Value :=
  Coeffect.setAt Coeffect.Example.initial .counter "not a Nat"

/-! A text delta cannot inhabit the tool-call-indexed delta family. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : RichStream.Delta .toolCall := .text "wrong block kind"

/-! A schedule that drops the third effect cannot construct the required permutation proof. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : Schedule.CertifiedSchedule Schedule.exampleCanonical where
  scheduled := [Schedule.exampleX, Schedule.exampleY]
  permutation := by simp [Schedule.exampleCanonical]
  commuting := Schedule.exampleCommuting

/-! Provider tool calls cannot enter a session with the wrong number of local call IDs. -/

/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs (substring := true) in
example : StreamSession.CallIdAssignment StreamSession.interleavedView where
  ids := []
  length_eq := by decide
  nodup := by decide

/-! Presence cannot be observationally related to absence at the same dependent key. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : Coeffect.Observational.Related
    Coeffect.Observational.Example.equivalences
    Coeffect.Observational.Example.left Coeffect.empty := by
  intro key
  cases key with
  | counter => exact Coeffect.Observational.OptionRelated.none
  | label => exact Coeffect.Observational.OptionRelated.none

/-! Isolation selects the stored value type through the resolved realm. -/

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
example : Cordis.Applied UnifiedContext.Example.Isolation.Context
    UnifiedContext.Example.Isolation.blank :=
  UnifiedContext.Example.Isolation.blank.setEffect .counter "not a Nat"
    UnifiedContext.Example.Isolation.blankCounterAbsent

/-! An intercepted provider must return the value type selected by its exact key. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : Cordis.Applied UnifiedContext.Example.Interception.Context
    UnifiedContext.Example.Interception.blank :=
  UnifiedContext.Example.Interception.blank.setEffect .count
    (fun _ ↦ "not a Nat") UnifiedContext.Example.Interception.blankCountAbsent

/-! Runtime JSON indices cannot fabricate a proof beyond JavaScript's exact integer range. -/

/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs (substring := true) in
example : RuntimeRefinement.SafeNat where
  value := 9007199254740992
  safe := by decide

end Cordis.NegativeTests
