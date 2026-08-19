import Cordis.Batch
import Cordis.Codec
import Cordis.Coeffect
import Cordis.CoeffectQuotient
import Cordis.ContextualEquivalence
import Cordis.Effect
import Cordis.Examples.Counter
import Cordis.Examples.CounterWire
import Cordis.Examples.DependentChoice
import Cordis.GlobalCalculus
import Cordis.GlobalDynamics
import Cordis.GlobalLifecycle
import Cordis.GlobalRegistry
import Cordis.GlobalTemporal
import Cordis.GlobalTraceFacts
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.MediatedIndependence
import Cordis.MediatedTheorem
import Cordis.OperationIndependence
import Cordis.OperationalEquivalence
import Cordis.PartialTransformation
import Cordis.Policy
import Cordis.Protocol
import Cordis.QuotientEffect
import Cordis.Registry
import Cordis.Removal
import Cordis.RichStream
import Cordis.RuntimeRefinement
import Cordis.Schedule
import Cordis.Session
import Cordis.SessionRefinement
import Cordis.SessionValidation
import Cordis.Stream
import Cordis.StreamSession
import Cordis.Transformation
import Cordis.UnifiedContext

/-!
# Executable adversarial and integration tests

The tests in this module exercise both successful proof-carrying paths and the dynamic
boundaries that must fail closed. `run` is intentionally independent of the repository's
executable entry points so another test runner can call it without importing an umbrella module.
-/

set_option autoImplicit false

namespace Cordis.TestSuite

open Cordis.Examples.Counter

private def rejectingCounterConfig : GenericHarness.Config Nat Capability := {
  Harness.counterConfig with
  decide := fun _ raw _ =>
    if raw.name = incrementSpec.name then
      .reject .deny (by decide) "counter increments are denied by this policy"
    else
      .allow
}

private def fail {alpha : Type} (message : String) : IO alpha :=
  throw <| IO.userError message

private def assertEqual {alpha : Type} [DecidableEq alpha] [Repr alpha]
    (label : String) (actual expected : alpha) : IO Unit :=
  if actual = expected then
    pure ()
  else
    fail s!"{label}: expected {reprStr expected}, got {reprStr actual}"

private def assertRoundtrip {alpha : Type} [DecidableEq alpha] [Repr alpha]
    (label : String) (codec : Codec alpha) (value : alpha) : IO Unit :=
  match codec.decode (codec.encode value) with
  | .ok decoded => assertEqual label decoded value
  | .error error => fail s!"{label}: encoded value was rejected with {reprStr error}"

private def assertRuntimeStateEqual
    (label : String) (actual expected : RuntimeState) : IO Unit :=
  match actual, expected with
  | .ready actualTurn, .ready expectedTurn =>
      assertEqual label actualTurn expectedTurn
  | .turn actualTurn actualStep, .turn expectedTurn expectedStep =>
      assertEqual label (actualTurn, actualStep) (expectedTurn, expectedStep)
  | .step actualTurn actualStep actualPending,
      .step expectedTurn expectedStep expectedPending =>
      assertEqual label
        (actualTurn, actualStep, actualPending)
        (expectedTurn, expectedStep, expectedPending)
  | _, _ => fail s!"{label}: expected {reprStr expected}, got {reprStr actual}"

private def addTwo : Effect Nat := fun before ↦
  { after := before + 2
    undo := fun current ↦ current - 2
    undo_after := Nat.add_sub_cancel before 2 }

private def triple : Effect Nat := fun before ↦
  { after := before * 3
    undo := fun current ↦ current / 3
    undo_after := Nat.mul_div_cancel before (by decide) }

private def incrementLeft : Effect (Nat × Nat) := fun before ↦
  { after := (before.1 + 1, before.2)
    undo := fun current ↦ (current.1 - 1, current.2)
    undo_after := by simp }

private def incrementRight : Effect (Nat × Nat) := fun before ↦
  { after := (before.1, before.2 + 1)
    undo := fun current ↦ (current.1, current.2 - 1)
    undo_after := by simp }

private abbrev LifecycleView := Lifecycle.CommittedView Nat Nat

private abbrev LifecycleState := Lifecycle.State Nat LifecycleView Unit

private def testEffects : IO Unit := do
  let first := addTwo 4
  let second := triple first.after
  let combined := Effect.seq addTwo triple 4
  assertEqual "effect successor" combined.after 18
  let afterNewestUndo := second.undo combined.after
  assertEqual "newest inverse runs first" afterNewestUndo 6
  assertEqual "older inverse completes recovery" (first.undo afterNewestUndo) 4
  assertEqual "the deliberately wrong inverse order differs" (second.undo (first.undo 18)) 5
  assertEqual "composed effect exactly recovers" (combined.undo combined.after) 4
  let stack := UndoStack.push (UndoStack.singleton first) second
  assertEqual "indexed undo stack exactly recovers" (stack.recover second.after) 4
  assertEqual "compiled accumulator agrees with stack"
    (stack.toAccumulator.recover second.after) 4

private def testCertifiedBatch : IO Unit := do
  let batch : TwoBatch (Nat × Nat) Nat Nat := {
    first := { effect := incrementLeft, result := Prod.fst }
    second := { effect := incrementRight, result := Prod.snd }
  }
  let independent : batch.IndependentAt (2, 3) := {
    effects := {
      successor_eq := rfl
      recovery_eq := by intro current; rfl
    }
    first_result_stable := rfl
    second_result_stable := rfl
  }
  let certified : CertifiedTwoBatch (Nat × Nat) Nat Nat (2, 3) := {
    batch := batch
    independent := independent
  }
  let model := certified.execute .model
  let swapped := certified.execute .swapped
  assertEqual "certified batch reaches the same successor"
    model.applied.after swapped.applied.after
  assertEqual "certified batch commits outputs in model order"
    model.outputs swapped.outputs
  assertEqual "certified batch successor" swapped.applied.after (3, 4)
  assertEqual "certified batch ordered outputs" swapped.outputs (2, 3)
  assertEqual "certified swapped batch recovers" (swapped.applied.undo swapped.applied.after)
    (2, 3)

private def testCodecs : IO Unit := do
  assertRoundtrip "boolean codec roundtrip" Codec.bool true
  assertRoundtrip "string codec roundtrip" Codec.string "cordis"
  assertRoundtrip "natural codec roundtrip" Codec.nat 42
  assertRoundtrip "product codec roundtrip" (Codec.prod Codec.nat Codec.string) (7, "seven")
  assertRoundtrip "list codec roundtrip" (Codec.list Codec.nat) [1, 2, 3, 5, 8]

  let nested := Codec.list (Codec.prod Codec.nat Codec.bool)
  let malformed : Lean.Json := .arr #[
    .arr #[Codec.nat.encode 1, Codec.bool.encode true],
    .arr #[Codec.nat.encode 2, .str "not-a-boolean"]
  ]
  let expected : DecodeError :=
    .typeMismatch [.index 1, .index 1] "boolean" .string
  match nested.decode malformed with
  | .error error => assertEqual "nested codec reports the complete path" error expected
  | .ok value =>
      fail s!"nested codec accepted malformed JSON as {reprStr value}"

private def testStream : IO Unit := do
  let chunks := ["proof-", "carrying", " stream"]
  assertEqual "stream assembly is deterministic"
    (Stream.assemble chunks) "proof-carrying stream"
  match Stream.replayRaw (Stream.RuntimeState.initial 3)
      [.text "proof-", .text "carrying", .text " stream", .finish] with
  | .error error => fail s!"valid assistant stream failed with {reprStr error}"
  | .ok state =>
      assertEqual "assistant stream reconstructs its exact terminal text" state
        (.finished { text := "proof-carrying stream" })
  match Stream.applyRaw (.open 0 "full") (.text "overflow") with
  | .error .budgetExhausted => pure ()
  | .error error => fail s!"expected stream budgetExhausted, got {reprStr error}"
  | .ok state => fail s!"over-budget stream chunk reached {reprStr state}"
  let finished : Stream.RuntimeState := .finished { text := "done" }
  match Stream.applyRaw finished (.text "late") with
  | .error (.alreadyFinished (.text "late")) => pure ()
  | .error error => fail s!"expected late stream text to be rejected, got {reprStr error}"
  | .ok state => fail s!"post-finish stream text reached {reprStr state}"
  match Stream.applyRaw finished .finish with
  | .error (.alreadyFinished .finish) => pure ()
  | .error error => fail s!"expected stream alreadyFinished, got {reprStr error}"
  | .ok state => fail s!"double stream finish reached {reprStr state}"

private def providerIdentityAt
    (providers : Registry catalog.signature)
    (operation : Operation) : Option ProviderId :=
  match providers operation with
  | none => none
  | some selected => some selected.id

private def testRegistry : IO Unit := do
  let removedRead :=
    (Registry.setEffect (sig := catalog.signature) Operation.read none) registry
  assertEqual "registry update removes its target"
    (providerIdentityAt removedRead.after .read) none
  assertEqual "registry update preserves a distinct key"
    (providerIdentityAt removedRead.after .increment) (some (providerId .increment))
  let restored := removedRead.undo removedRead.after
  assertEqual "registry inverse restores the overwritten provider"
    (providerIdentityAt restored .read) (some (providerId .read))
  assertEqual "registry inverse preserves the other provider"
    (providerIdentityAt restored .increment) (some (providerId .increment))

  let readThenIncrement :=
    Effect.seq
      (Registry.setEffect (sig := catalog.signature) Operation.read none)
      (Registry.setEffect (sig := catalog.signature) Operation.increment none)
      registry
  let incrementThenRead :=
    Effect.seq
      (Registry.setEffect (sig := catalog.signature) Operation.increment none)
      (Registry.setEffect (sig := catalog.signature) Operation.read none)
      registry
  for operation in [Operation.read, Operation.increment] do
    assertEqual "distinct-key registry updates commute"
      (providerIdentityAt readThenIncrement.after operation)
      (providerIdentityAt incrementThenRead.after operation)
    assertEqual "either distinct-key order recovers the original registry"
      (providerIdentityAt (readThenIncrement.undo readThenIncrement.after) operation)
      (providerIdentityAt registry operation)
    assertEqual "reversed distinct-key order also recovers the original registry"
      (providerIdentityAt (incrementThenRead.undo incrementThenRead.after) operation)
      (providerIdentityAt registry operation)

private def testLifecycle : IO Unit := do
  let committed : LifecycleView := {
    resolve := fun _ ↦ some 1
  }
  let applied := addTwo 4
  let undo := UndoStack.singleton applied
  let began : Lifecycle.Transition (Key := Nat) (Fiber := Nat) 1 []
      (.inactive 4 .stopped : LifecycleState)
      (.reloading 4 4 (.nil 4) () committed) :=
    .begin .stopped 4 () committed
  let iterated : Lifecycle.Transition (Key := Nat) (Fiber := Nat) 1 []
      (.reloading 4 4 (.nil 4) () committed : LifecycleState)
      (.reloading 4 applied.after undo () committed) :=
    .iterate addTwo ()
  let finished : Lifecycle.Transition (Key := Nat) (Fiber := Nat) 1 []
      (.reloading 4 applied.after undo () committed : LifecycleState)
      (.active 4 applied.after undo committed) :=
    .finish
  let left : Lifecycle.Transition (Key := Nat) (Fiber := Nat) 1 []
      (.active 4 applied.after undo committed : LifecycleState)
      (.unloading 4 applied.after undo committed .stopped) :=
    .leave .stopped
  let unloaded : Lifecycle.Transition (Key := Nat) (Fiber := Nat) 1 []
      (.unloading 4 applied.after undo committed .stopped : LifecycleState)
      (.inactive 4 .stopped) :=
    .unload (Lifecycle.withdrawable_empty 1)
  let trace : Lifecycle.Trace (Key := Nat) (Fiber := Nat) 1 []
      (.inactive 4 .stopped : LifecycleState) (.inactive 4 .stopped) :=
    .cons began <| .cons iterated <| .cons finished <| .cons left <|
      .cons unloaded (.nil _)
  let _ := trace
  assertEqual "lifecycle unload stack recovers the recorded inactive model"
    (undo.recover applied.after) 4

private def testProtocolFailures : IO Unit := do
  match applyRaw (.ready 0) (.turnStart 1) with
  | .error (.turnMismatch expected actual) =>
      assertEqual "protocol reports the mismatched turn" (expected, actual) (0, 1)
  | .error error => fail s!"expected turnMismatch, got {reprStr error}"
  | .ok state => fail s!"mismatched turn was accepted into {reprStr state}"

  match applyRaw (.turn 0 2) (.stepStart 0 3) with
  | .error (.stepMismatch expected actual) =>
      assertEqual "protocol reports the mismatched step" (expected, actual) (2, 3)
  | .error error => fail s!"expected stepMismatch, got {reprStr error}"
  | .ok state => fail s!"mismatched step was accepted into {reprStr state}"

  match applyRaw (.ready 0) (.stepEnd 0 0) with
  | .error (.wrongPhase _ _) => pure ()
  | .error error => fail s!"expected wrongPhase, got {reprStr error}"
  | .ok state => fail s!"wrong-phase event was accepted into {reprStr state}"

  let coordinateId : CallId := ⟨12⟩
  match applyRaw (.step 0 1 []) (.toolCall 9 1 coordinateId) with
  | .error (.turnMismatch expected actual) =>
      assertEqual "tool call reports its mismatched turn" (expected, actual) (0, 9)
  | .error error => fail s!"expected tool-call turnMismatch, got {reprStr error}"
  | .ok state => fail s!"wrong-turn tool call was accepted into {reprStr state}"

  match applyRaw (.step 0 1 []) (.toolCall 0 9 coordinateId) with
  | .error (.stepMismatch expected actual) =>
      assertEqual "tool call reports its mismatched step" (expected, actual) (1, 9)
  | .error error => fail s!"expected tool-call stepMismatch, got {reprStr error}"
  | .ok state => fail s!"wrong-step tool call was accepted into {reprStr state}"

  match applyRaw (.turn 0 2) (.turnEnd 0 1) with
  | .error (.stepMismatch expected actual) =>
      assertEqual "turn end reports its mismatched next step" (expected, actual) (2, 1)
  | .error error => fail s!"expected turn-end stepMismatch, got {reprStr error}"
  | .ok state => fail s!"wrong-coordinate turn end was accepted into {reprStr state}"

  let orphan : CallId := ⟨9⟩
  match applyRaw (.step 0 0 []) (.toolResult 0 0 orphan) with
  | .error (.orphanResult actual) =>
      assertEqual "protocol rejects the expected orphan call" actual orphan
  | .error error => fail s!"expected orphanResult, got {reprStr error}"
  | .ok state => fail s!"orphan result was accepted into {reprStr state}"

  let duplicate : CallId := ⟨4⟩
  match applyRaw (.step 0 0 [duplicate]) (.toolCall 0 0 duplicate) with
  | .error (.duplicateCall actual) =>
      assertEqual "protocol rejects the expected duplicate call" actual duplicate
  | .error error => fail s!"expected duplicateCall, got {reprStr error}"
  | .ok state => fail s!"duplicate call was accepted into {reprStr state}"

  let pending : CallId := ⟨6⟩
  match applyRaw (.step 0 0 [pending]) (.stepEnd 0 0) with
  | .error (.pendingCallsRemain actual) =>
      assertEqual "protocol reports the expected pending call" actual [pending]
  | .error error => fail s!"expected pendingCallsRemain, got {reprStr error}"
  | .ok state => fail s!"step with pending calls was closed into {reprStr state}"

private def testPolicy : IO Unit := do
  let id : CallId := ⟨7⟩
  let issued ←
    match LeasePool.empty.issue id with
    | none => fail "fresh policy lease was not issued"
    | some issued => pure issued
  assertEqual "policy lease is issued exactly once" issued.available [id]
  match issued.issue id with
  | some duplicate =>
      fail s!"duplicate live policy lease was issued as {reprStr duplicate.available}"
  | none => pure ()
  match consumed : issued.consume id with
  | none => fail "issued policy lease could not be consumed"
  | some remaining =>
      let allowed :
          PolicyTransition (.proposed id issued) (.decided id .allow issued) :=
        .decide id issued .allow
      let dispatched :
          PolicyTransition (.decided id .allow issued) (.dispatched id remaining) :=
        .dispatch consumed
      let settled :
          PolicyTransition (.dispatched id remaining) (.settled id remaining) :=
        .settle id remaining
      let _ := allowed
      let _ := dispatched
      let _ := settled
      assertEqual "dispatch consumes its exact lease" remaining.available []
      match remaining.consume id with
      | none => pure ()
      | some twice =>
          fail s!"consumed policy lease was reused as {reprStr twice.available}"

private def testSubjectPolicyRejection : IO Unit := do
  let id : CallId := ⟨8⟩
  let issued ←
    match LeasePool.empty.issue id with
    | none => fail "fresh exact-subject policy lease was not issued"
    | some issued => pure issued
  let decided : SubjectPolicyTransition
      (Completed := fun _ : Nat ↦ Unit)
      (Rejected := fun _ : Nat ↦ String)
      (.proposed id 42 issued)
      (.decided id 42 .deny issued) :=
    .decide id 42 issued .deny
  let rejected : SubjectPolicyTransition
      (Completed := fun _ : Nat ↦ Unit)
      (Rejected := fun _ : Nat ↦ String)
      (.decided id 42 .deny issued)
      (.settled id 42 issued (.rejected "denied")) :=
    .reject
      (Completed := fun _ : Nat ↦ Unit)
      (Rejected := fun _ : Nat ↦ String)
      (id := id)
      (subject := 42)
      (leases := issued)
      (decision := .deny)
      (by decide)
      "denied"
  let trace : SubjectPolicyTrace
      (Completed := fun _ : Nat ↦ Unit)
      (Rejected := fun _ : Nat ↦ String)
      (.proposed id 42 issued)
      (.settled id 42 issued (.rejected "denied")) :=
    .cons decided <| .cons rejected (.nil _)
  assertEqual "denied exact-subject trace never dispatches" trace.dispatchCount 0

private def testGenericRunnerPolicy : IO Unit := do
  let started :=
    (GenericHarness.Runner.initial rejectingCounterConfig 2).beginTurn.beginStep
  let afterRead ←
    match started.dispatch rawRead with
    | .error error => fail s!"generic read dispatch failed with {reprStr error}"
    | .ok result => pure result.runner
  let afterDenied ←
    match afterRead.dispatch (rawIncrement { amount := 3, limit := 10 }) with
    | .error error => fail s!"generic policy rejection failed with {reprStr error}"
    | .ok result => pure result.runner
  assertEqual "generic allowed call updates no read-only model" afterRead.model 2
  assertEqual "generic denied call preserves the model" afterDenied.model 2
  assertEqual "generic runner restores every modeled lease" afterDenied.leases.available []
  assertEqual "generic runner keeps session-wide ids"
    (afterDenied.records.map fun record ↦ record.id.value) [0, 1]
  assertEqual "generic runner records allowed then policy-rejected outcomes"
    (afterDenied.records.map GenericHarness.CallRecord.outcome)
    [.succeeded,
      .policyRejected .deny "counter increments are denied by this policy"]
  assertEqual "generic runner dispatches only the allowed call"
    (afterDenied.records.map GenericHarness.CallRecord.dispatchCount) [1, 0]
  let _models :
      GenericHarness.ModelsThreaded afterDenied.initialModel afterDenied.records
        afterDenied.model := afterDenied.models_threaded
  let _leases : GenericHarness.LeasesThreaded .empty afterDenied.records afterDenied.leases :=
    afterDenied.leases_threaded
  pure ()

private def testSessionLog : IO Unit := do
  assertEqual "session surface derives only model-visible messages"
    Session.certifiedSession.messages
    [.user "What is the answer?",
      .assistant "I will look it up." [Session.exampleCall],
      .toolResult Session.exampleCall.id "42" false]
  match Session.mkRequest Session.certifiedSession with
  | none => fail "certified session did not reconstruct a model request"
  | some request =>
      assertEqual "request reconstructs the latest full header"
        request.header Session.exampleHeader
      assertEqual "request reconstructs the exact session surface"
        request.messages Session.certifiedSession.messages
      assertEqual "request records its exact log length" request.logLength 5
  assertEqual "surface replacement shadows exactly the certified interval"
    Session.replacementSession.messages
    [.user "What is the answer?", .assistant "The answer is 42." []]
  match replayRaw (.step 0 0 [])
      (Session.protocolProjection Session.certifiedSession.events) with
  | .error error => fail s!"rich session protocol projection failed with {reprStr error}"
  | .ok state =>
      assertRuntimeStateEqual "rich session projection returns to an empty-pending step"
        state (.step 0 0 [])

private def testDependentChoiceHarness : IO Unit := do
  match Examples.DependentChoice.allowedEncodedResult with
  | none => fail "dependent choice allowed branch lost its typed encoding"
  | some encoded =>
      let codec : Codec (Except String Nat) :=
        Examples.DependentChoice.wire.resultCodec
          Examples.DependentChoice.Operation.choose true
      match codec.decode encoded with
      | .ok (.ok revision) =>
          assertEqual "dependent choice decodes the Nat-selected branch"
            revision Examples.DependentChoice.initialWorkspace.revision
      | .ok (.error message) => fail s!"dependent choice tool failed with {message}"
      | .error error => fail s!"dependent choice result failed to decode: {reprStr error}"
  assertEqual "dependent choice reaches exact-call policy rejection"
    Examples.DependentChoice.rejectedOutcome
    (some (.policyRejected .deny "label output rejected by exact-call policy"))
  assertEqual "dependent choice rejection never dispatches"
    Examples.DependentChoice.rejectedDispatchCount (some 0)
  assertEqual "dependent choice rejection preserves the structured model"
    Examples.DependentChoice.rejectedModel
    (some Examples.DependentChoice.initialWorkspace)

private def testSessionValidation : IO Unit := do
  match Session.validateAppend Session.certifiedSession Session.replacementEvent with
  | .error error => fail s!"valid surface replacement was rejected with {reprStr error}"
  | .ok validated =>
      assertEqual "validated replacement reconstructs the exact intrinsic surface"
        validated.apply.messages Session.replacementSession.messages
  match Session.validateAppend Session.certifiedSession Session.wrongSequenceEvent with
  | .error error =>
      assertEqual "rich validator reports the exact wrong sequence"
        error (.wrongPhysicalSeq 5 99)
  | .ok _ => fail "wrong-sequence rich event was accepted"
  match Session.validateAppend Session.certifiedSession Session.incompleteCoverageEvent with
  | .error error =>
      assertEqual "rich validator rejects incomplete replacement provenance"
        error (.incompleteShadowCoverage [2, 4] [2])
  | .ok _ => fail "incomplete replacement provenance was accepted"
  match Session.validateLog (Session.Session.empty Session.noExtensions) Session.shortRawLog with
  | .error error => fail s!"valid rich suffix was rejected with {reprStr error}"
  | .ok validated =>
      let _eventsEq :
          validated.final.events =
            (Session.Session.empty Session.noExtensions).events ++ Session.shortRawLog :=
        validated.events_eq
      assertEqual "validated rich suffix preserves the physical event count"
        validated.final.events.length Session.shortRawLog.length
      assertEqual "validated rich suffix derives the expected message"
        validated.final.messages [.user "What is the answer?"]

private def testReactiveCoeffects : IO Unit := do
  assertEqual "installing the last heterogeneous dependency activates"
    (Coeffect.notify Coeffect.Example.dependencies Coeffect.Example.counterOnly
      Coeffect.Example.installLabel.after) .activating
  assertEqual "removing the required dependency deactivates"
    (Coeffect.notify Coeffect.Example.dependencies Coeffect.Example.installLabel.after
      (Coeffect.removeAt Coeffect.Example.installLabel.after .label)) .deactivating
  let counter : Nat :=
    Coeffect.get Coeffect.Example.counterOnly .counter Coeffect.Example.counterPresent
  assertEqual "typed counter dependency remains Nat" counter 7
  let label : String :=
    Coeffect.get Coeffect.Example.installLabel.after .label Coeffect.Example.labelPresent
  assertEqual "typed label dependency remains String" label "ready"
  let recoveredLabel : Option String :=
    Coeffect.Example.installLabel.undo Coeffect.Example.installLabel.after .label
  let originalLabel : Option String := Coeffect.Example.counterOnly .label
  assertEqual "concrete coeffect inverse removes only the inserted binding"
    recoveredLabel originalLabel

private def testFiniteSchedules : IO Unit := do
  let expected : Schedule.Triple := { x := 11, y := 22, z := 33 }
  let reverse := Schedule.reverseSchedule.execute Schedule.exampleBefore
  let rotate := Schedule.rotateSchedule.execute Schedule.exampleBefore
  assertEqual "reverse finite schedule reaches the canonical successor" reverse.after expected
  assertEqual "rotated finite schedule reaches the canonical successor" rotate.after expected
  assertEqual "all finite schedules retain the same captured undo behavior"
    (reverse.undo { x := 100, y := 200, z := 300 })
    (rotate.undo { x := 100, y := 200, z := 300 })
  assertEqual "reverse schedule recovers its exact predecessor"
    (reverse.undo reverse.after) Schedule.exampleBefore

private def testRichStream : IO Unit := do
  match RichStream.validateTrace RichStream.State.initial RichStream.interleavedRaw with
  | .error error => fail s!"valid interleaved rich stream was rejected with {reprStr error}"
  | .ok validated =>
      assertEqual "rich stream validator preserves exact raw chunk count"
        validated.trace.erase.length RichStream.interleavedRaw.length
  match RichStream.replayRaw RichStream.RuntimeState.initial RichStream.interleavedRaw with
  | .error error => fail s!"valid rich stream replay failed with {reprStr error}"
  | .ok (.active _ _) => fail "complete rich stream remained active"
  | .ok (.terminal blocks usage reason replay) =>
      assertEqual "rich stream retains first-seen block order"
        blocks RichStream.interleavedBlocks
      assertEqual "rich stream retains usage before finish" usage RichStream.interleavedUsage
      assertEqual "rich stream retains terminal reason" reason .stop
      assertEqual "rich stream retains aligned replay metadata"
        replay (some RichStream.interleavedReplay.erase)
  let view := RichStream.toAssistantMessageView RichStream.interleavedBlocks
  assertEqual "rich stream projects visible text without private reasoning"
    view.content "Hello world"
  assertEqual "rich stream projects both raw tool calls" view.rawToolCalls.length 2
  match RichStream.applyRaw RichStream.RuntimeState.initial (.textDelta 0 "orphan") with
  | .error error => assertEqual "rich stream rejects missing block index" error (.missingIndex 0)
  | .ok _ => fail "rich stream accepted an orphan delta"
  match RichStream.applyRaw
      (.active [.closed (.text "done")] (some RichStream.interleavedUsage))
      (.finish .stop (some { responseId := none, perBlock := [none, none] })) with
  | .error error =>
      assertEqual "rich stream rejects misaligned replay metadata"
        error (.metadataLengthMismatch 1 2)
  | .ok _ => fail "rich stream accepted misaligned replay metadata"

private def testStreamSessionBridge : IO Unit := do
  assertEqual "stream bridge preserves visible assistant text"
    StreamSession.interleavedPayload.content "Hello world"
  assertEqual "stream bridge assigns both provider calls"
    StreamSession.interleavedPayload.rawToolCalls.length 2
  assertEqual "stream bridge preserves the first raw argument string"
    (Option.map (fun (call : Session.ToolCall) => call.arguments)
      StreamSession.interleavedPayload.rawToolCalls.head?)
    (some "{\"q\":\"lean\"}")
  assertEqual "stream bridge enters one canonical assistant surface message"
    StreamSession.bridgedSession.messages.length 1

private def testContextualEquivalence : IO Unit := do
  let leftCounter : Option Nat :=
    Coeffect.Observational.Example.left Coeffect.Example.Key.counter
  let rightCounter : Option Nat :=
    Coeffect.Observational.Example.right Coeffect.Example.Key.counter
  assertEqual "observationally related contexts may have different exact values"
    (leftCounter, rightCounter) (some 1, some 3)
  let leftAfter := Coeffect.removeAt Coeffect.Observational.Example.left
    Coeffect.Example.Key.label
  let rightAfter := Coeffect.removeAt Coeffect.Observational.Example.right
    Coeffect.Example.Key.label
  assertEqual "related endpoints induce the same notification"
    (Coeffect.notify Coeffect.Example.dependencies
      Coeffect.Observational.Example.left leftAfter)
    (Coeffect.notify Coeffect.Example.dependencies
      Coeffect.Observational.Example.right rightAfter)
  assertEqual "the related satisfied contexts both deactivate after label removal"
    (Coeffect.notify Coeffect.Example.dependencies
      Coeffect.Observational.Example.left leftAfter)
    .deactivating

private def testUnifiedContexts : IO Unit := do
  let isolationRoot := UnifiedContext.Example.Isolation.root
  let isolationTenant := UnifiedContext.Example.Isolation.tenant
  assertEqual "root isolation resolves the logical counter to its own realm"
    (isolationRoot.resolve .counter)
    UnifiedContext.Example.Isolation.Realm.counterBase
  assertEqual "derived isolation redirects the same logical counter"
    (isolationTenant.resolve .counter)
    UnifiedContext.Example.Isolation.Realm.counterTenant
  let rootCounter : Nat := isolationRoot.get .counter
    UnifiedContext.Example.Isolation.rootCounterPresent
  let tenantCounter : Nat := isolationTenant.get .counter
    UnifiedContext.Example.Isolation.tenantCounterPresent
  assertEqual "realm-dependent gets retain their exact Nat values"
    (rootCounter, tenantCounter) (1, 99)
  let counted := UnifiedContext.Example.Interception.counted
  let countResult : Nat := counted.get UnifiedContext.Example.Interception.algebra .count
    UnifiedContext.Example.Interception.declaredCount
    UnifiedContext.Example.Interception.countPresent
  assertEqual "interception merges declared then inherited metadata" countResult 14
  let texted := UnifiedContext.Example.Interception.texted
  let textResult : String := texted.get UnifiedContext.Example.Interception.algebra .text
    UnifiedContext.Example.Interception.declaredText
    UnifiedContext.Example.Interception.textPresent
  assertEqual "heterogeneous interception uses the String metadata monoid"
    textResult "value:declared-outer"
  let recorded := UnifiedContext.Example.Unified.layer.record
    UnifiedContext.Example.Unified.replacement
  assertEqual "finite unified layer records and recovers in LIFO order"
    (recorded.recover recorded.current) 10

private def testRuntimeRefinement : IO Unit := do
  match RuntimeRefinement.validateJsonTrace RuntimeRefinement.exampleJson with
  | .error error => fail s!"current Harness stream JSON was rejected with {reprStr error}"
  | .ok validated =>
      assertEqual "JSON refinement preserves every supported chunk"
        validated.chunks.length RuntimeRefinement.exampleChunks.length
      match validated.validated.finish with
      | .active _ _ => fail "complete current-Harness stream remained active"
      | .terminal blocks usage reason replay =>
          assertEqual "JSON refinement reaches the exact assembled text block"
            blocks [.text "hello"]
          assertEqual "JSON refinement performs only the named optional-usage normalization"
            usage RuntimeRefinement.exampleUsage.toLocal
          assertEqual "JSON refinement preserves the successful finish reason" reason .stop
          assertEqual "absent replay state remains absent" replay.isSome false
  let noncontiguous : List Lean.Json := [Lean.Json.mkObj [
    ("type", .str "block-start"),
    ("index", .num 1),
    ("blockType", .str "text")
  ]]
  match RuntimeRefinement.validateJsonTrace noncontiguous with
  | .error error =>
      assertEqual "JSON shape success cannot bypass semantic stream validation"
        error (.stream (.wrongStartIndex 0 1))
  | .ok _ => fail "noncontiguous current-Harness stream was accepted"
  match RuntimeRefinement.decodeChunk (Lean.Json.mkObj [
    ("type", .str "finish"),
    ("reason", Lean.Json.mkObj [("kind", .str "stop")]),
    ("replayState", Lean.Json.mkObj [("response", .null)])
  ]) with
  | .error error =>
      assertEqual "opaque upstream replay state fails closed"
        error (.unsupportedField [] "replayState")
  | .ok _ => fail "opaque upstream replay state was silently discarded"

private def testQuotientEffects : IO Unit := do
  let applied := Observational.Quotient.Example.program.run
    Observational.Quotient.Example.initial
  let expected : Observational.Quotient.Example.Model := { visible := 5, hidden := 11 }
  assertEqual "admissible quotient program retains its concrete successor"
    applied.after expected
  assertEqual "the concrete example's accumulated observational inverse recovers exactly"
    (applied.undo applied.after) Observational.Quotient.Example.initial

private def testCoeffectQuotientLift : IO Unit := do
  let result := Coeffect.Quotient.Example.counterCoeffect.lift
    Coeffect.Quotient.Example.counterOp Coeffect.Quotient.Example.counterAmount
    Coeffect.Quotient.Example.left Coeffect.Quotient.Example.leftCounter trivial
  let outcome : Nat := result.2
  assertEqual "quotient-preserving coeffect lift retains its typed outcome" outcome 3
  let afterCounter : Option Nat := result.1.after Coeffect.Quotient.Example.ExampleKey.counter
  assertEqual "quotient-preserving coeffect lift changes only the selected Nat binding"
    afterCounter (some 7)
  let recoveredCounter : Option Nat :=
    result.1.undo result.1.after Coeffect.Quotient.Example.ExampleKey.counter
  assertEqual "lifted local inverse restores the selected dependent binding"
    recoveredCounter (some 3)

private def testOperationalEquivalence : IO Unit := do
  match OperationalEquivalence.observe OperationalEquivalence.Example.coeffect
      OperationalEquivalence.Example.mixedTest OperationalEquivalence.Example.initial with
  | none => fail "enabled heterogeneous operational test became undefined"
  | some outcomes =>
      assertEqual "heterogeneous operational test records both forward outcomes"
        outcomes.length 2
  match OperationalEquivalence.observe OperationalEquivalence.Example.coeffect
      [.forward .bump ()] OperationalEquivalence.Example.blocked with
  | none => pure ()
  | some _ => fail "operational test ignored a failed operation precondition"

private def testSessionRefinement : IO Unit := do
  match SessionRefinement.validateJsonLog SessionRefinement.exampleJson with
  | .error error => fail s!"supported current-Harness session prefix failed: {reprStr error}"
  | .ok validated =>
      assertRuntimeStateEqual "stateful session refinement reaches the derived turn endpoint"
        (eraseState validated.final.protocol) (.ready 2)
      assertEqual "stateful session refinement preserves physical sequence continuity"
        validated.final.session.nextSeq 6
      assertEqual "stateful session refinement derives one tool-result surface message"
        validated.final.session.messages [.toolResult { value := 0 } "result" false]
      assertEqual "stateful session refinement retains the exact structural event sequence"
        validated.sequence.runtimeEvents [
          .turnStart 1,
          .stepStart 1 0,
          .toolCall 1 0 { value := 0 },
          .toolResult 1 0 { value := 0 },
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
      let _projectionCertificate :
          Session.protocolProjection validated.final.session.events =
            validated.sequence.protocolTrace.erase :=
        validated.projection_exact

private def testTransformationIndependence : IO Unit := do
  let modelOrder := Effect.seq Transformation.Example.bumpLeft
    Transformation.Example.bumpRight Transformation.Example.initial
  let swappedOrder := Effect.seq Transformation.Example.bumpRight
    Transformation.Example.bumpLeft Transformation.Example.initial
  assertEqual "full transformation-monoid independence reaches the same successor"
    modelOrder.after swappedOrder.after
  assertEqual "full transformation-monoid independence retains the same recovery map"
    (modelOrder.undo { left := 20, right := 30 })
    (swappedOrder.undo { left := 20, right := 30 })
  assertEqual "independent coordinate effects still recover their predecessor"
    (modelOrder.undo modelOrder.after) Transformation.Example.initial

open OperationIndependence.Example.DistinctKeys in
private def testOperationIndependence : IO Unit := do
  let coeffectFamily := Coeffect.Quotient.Example.coeffects
  let base := Coeffect.Quotient.Example.left
  let counterThenLabel :=
    (OperationIndependence.transformAt coeffectFamily
      Coeffect.Quotient.Example.ExampleKey.counter counterWord base).bind
      (OperationIndependence.transformAt coeffectFamily
        Coeffect.Quotient.Example.ExampleKey.label labelWord)
  let labelThenCounter :=
    (OperationIndependence.transformAt coeffectFamily
      Coeffect.Quotient.Example.ExampleKey.label labelWord base).bind
      (OperationIndependence.transformAt coeffectFamily
        Coeffect.Quotient.Example.ExampleKey.counter counterWord)
  match counterThenLabel, labelThenCounter with
  | some first, some second =>
      let firstCounter : Option Nat := first Coeffect.Quotient.Example.ExampleKey.counter
      let secondCounter : Option Nat := second Coeffect.Quotient.Example.ExampleKey.counter
      let firstLabel : Option String := first Coeffect.Quotient.Example.ExampleKey.label
      let secondLabel : Option String := second Coeffect.Quotient.Example.ExampleKey.label
      assertEqual "distinct-key finite operation words preserve the counter"
        firstCounter secondCounter
      assertEqual "distinct-key finite operation words preserve the label"
        firstLabel secondLabel
  | _, _ => fail "enabled distinct-key operation words became undefined"
  let mediated := OperationIndependence.Example.Mediated.applied
  let mediatedCounter : Option Nat :=
    mediated.after Coeffect.Quotient.Example.ExampleKey.counter
  let mediatedLabel : Option String :=
    mediated.after Coeffect.Quotient.Example.ExampleKey.label
  assertEqual "Definition 41 continuation consumes the prior typed Nat outcome"
    mediatedCounter (some 7)
  assertEqual "Definition 41 continuation selects the matching String argument"
    mediatedLabel (some "a-three")

private def testArbitraryRemoval : IO Unit := do
  let final := Removal.runState Removal.Example.effects Removal.Example.initial
  assertEqual "arbitrary inverse order recovers the exact initial state"
    (Removal.applyMaps Removal.Example.inverseOrder final) Removal.Example.initial
  let originalWithMiddle :=
    Removal.runState [Schedule.exampleZ]
      (Schedule.exampleY Removal.Example.afterX).after
  let omittedMiddle := Removal.runState [Schedule.exampleZ] Removal.Example.afterX
  assertEqual "removing the middle effect preserves the later independent contribution"
    (Removal.Example.inverseY originalWithMiddle) omittedMiddle

private def testGlobalRegistry : IO Unit := do
  assertEqual "global registry insertions advance the proof-only birth clock"
    GlobalRegistry.Example.withConsumer.nextBirth 2
  assertEqual "inserted provider remains registered"
    (GlobalRegistry.Example.withConsumer.registry 0).isSome true
  assertEqual "retire then remove makes the child name absent"
    (GlobalRegistry.Example.withoutConsumer.registry 1).isSome false
  match GlobalRegistry.Example.retiredConsumer.registry 1 with
  | none => fail "retirement removed the fiber instead of retaining it"
  | some fiber =>
      assertEqual "retirement sets only the request flag before removal" fiber.retired true
      match fiber.phase with
      | .inactive _ => pure ()
      | _ => fail "orchestration retirement changed the lifecycle phase"

private def testMediatedIndependenceBoundary : IO Unit := do
  assertEqual "realized Definition 41 path retains both outcome-selected stages"
    MediatedIndependence.BranchExample.path.stages.length 2
  let selectedLabel : Option String :=
    MediatedIndependence.BranchExample.applied.after
      Coeffect.Quotient.Example.ExampleKey.label
  assertEqual "realized path retains the Nat-selected String continuation"
    selectedLabel (some "a-three")
  let falseThenTrue : Option MediatedIndependence.Counterexample.Cell :=
    MediatedIndependence.Counterexample.falseThenTrue.after .cell
  let trueThenFalse : Option MediatedIndependence.Counterexample.Cell :=
    MediatedIndependence.Counterexample.trueThenFalse.after .cell
  assertEqual "quotient-related orders may choose different exact representatives"
    (falseThenTrue.map MediatedIndependence.Counterexample.Cell.hidden,
      trueThenFalse.map MediatedIndependence.Counterexample.Cell.hidden)
    (some true, some false)

open MediatedTheorem.Example.IndependentBranching in
private def testMediatedWholeRun : IO Unit := do
  match MediatedTheorem.runSequential leftComputation rightComputation initial,
      MediatedTheorem.runSequential rightComputation leftComputation initial with
  | some leftThenRight, some rightThenLeft =>
      let leftCounter : Option Nat := leftThenRight.after .counter
      let rightCounter : Option Nat := rightThenLeft.after .counter
      let leftLabel : Option String := leftThenRight.after .label
      let rightLabel : Option String := rightThenLeft.after .label
      let leftFlag : Option Bool := leftThenRight.after .flag
      let rightFlag : Option Bool := rightThenLeft.after .flag
      assertEqual "mediated tree swap preserves the counter" leftCounter rightCounter
      assertEqual "mediated tree swap preserves the Nat-selected String branch"
        (leftLabel, rightLabel) (some "a-three", some "a-three")
      assertEqual "mediated tree swap preserves the foreign Boolean result"
        (leftFlag, rightFlag) (some true, some true)
  | none, none => fail "non-vacuous mediated example made both orders undefined"
  | _, _ => fail "mediated example disagreed on composite definedness"

private def testPartialTransformation : IO Unit := do
  let falseThenTrue : Option Bool :=
    PartialTransformation.WholeRunGap.falseResult.undo
      (PartialTransformation.WholeRunGap.trueResult.undo
        PartialTransformation.WholeRunGap.falseContext) .cell
  let trueThenFalse : Option Bool :=
    PartialTransformation.WholeRunGap.trueResult.undo
      (PartialTransformation.WholeRunGap.falseResult.undo
        PartialTransformation.WholeRunGap.falseContext) .cell
  assertEqual "whole-run equality can hide noncommuting cross-seed inverses"
    (falseThenTrue, trueThenFalse) (some false, some true)

open GlobalDynamics.Example in
private def testGlobalDynamics : IO Unit := do
  assertEqual "fueled global iterator executes ordinary then registration steps"
    (summarize (GlobalDynamics.runFuel dynamics oracle 2 start 0))
    (some { ambient := 4, childPresent := true, undoCount := 2, completed := true })
  assertEqual "fuel exhaustion retains the exact continuation code"
    (exhaustedCode (GlobalDynamics.runFuel dynamics oracle 1 start 0)) (some (some 1))
  assertEqual "mixed external/retirement accumulation recovers the ambient observation"
    (recoveredAmbient (GlobalDynamics.runFuel dynamics oracle 2 start 0)) (some start.ambient)

open GlobalLifecycle.Example in
private def testGlobalLifecycle : IO Unit := do
  assertEqual "global lifecycle exposes the exact five-rule path around retirement"
    [beginTransition.rule, iterTransition.rule, finishTransition.rule,
      leaveTransition.rule, unloadTransition.rule]
    [.begin, .iter, .finish, .leave, .unload]
  assertEqual "global lifecycle recovery restores the exact ambient observation"
    unloadedState.ambient start.ambient
  match finishState.registry 0 with
  | none => fail "global lifecycle finish lost the owner fiber"
  | some fiber =>
      match fiber.phase with
      | .active undos _ =>
          assertEqual "global lifecycle retained both newest-first inverses" undos.length 2
      | _ => fail "global lifecycle finish did not reach the active phase"
  match unloadedState.registry 0 with
  | none => fail "global lifecycle unload removed the owner instead of deactivating it"
  | some fiber =>
      match fiber.phase with
      | .inactive none => pure ()
      | _ => fail "global lifecycle unload reached the wrong phase"

open GlobalCalculus.Example in
private def testGlobalCalculus : IO Unit := do
  assertEqual "unified global calculus has the paper's ten-name inventory"
    GlobalCalculus.allRules.length 10
  assertEqual "unified global trace projects exact rule names"
    unifiedTrace.rules
    [.oInsert, .lBegin, .lIter, .lFinish, .oRetire, .lLeave, .lUnload, .oRemove]
  assertEqual "unified global trace separates Equation 51 state maps from edits"
    unifiedTrace.stateMaps
    [.identity, .identity, .iterator, .iterator, .identity, .identity,
      .accumulatedRecovery, .identity]
  assertEqual "unified global trace restores its ambient observation"
    removedState.ambient emptyStart.ambient
  assertEqual "unified global trace returns to an empty registry"
    (removedState.registry 0).isNone true

private def testGlobalTraceFacts : IO Unit := do
  let states := GlobalTraceFacts.Trace.states GlobalCalculus.Example.unifiedTrace
  let records := GlobalTraceFacts.Trace.records GlobalCalculus.Example.unifiedTrace
  assertEqual "global trace state projection has one more endpoint than records"
    states.length (records.length + 1)
  let beforeForeign : Option Nat :=
    (GlobalTraceFacts.Counterexample.state 7).registry true >>= fun fiber ↦ fiber.table ()
  let afterForeign : Option Nat :=
    GlobalTraceFacts.Counterexample.inactiveAfter.registry true >>= fun fiber ↦ fiber.table ()
  assertEqual "bare unload admission can mutate a foreign table in the kernel countermodel"
    (beforeForeign, afterForeign) (some 7, some 8)

private def testGlobalTemporal : IO Unit := do
  assertEqual "exact iterator map can fail when re-executed off-source"
    (GlobalTemporal.Step.partialMap GlobalCalculus.Example.iterStep
      GlobalCalculus.Example.emptyStart).isNone true
  let recovered := GlobalDynamics.Example.dynamics.recover [.external 0]
    GlobalTemporal.Counterexample.interleavedState
  assertEqual "structural recovery confinement alone misses foreign ambient commutation"
    (recovered.ambient, GlobalTemporal.Counterexample.foreignReplayState.ambient) (7, 6)

private def testHarnessPhaseFailures : IO Unit := do
  let initial := Harness.RunnerState.initial 0
  match initial.beginStep with
  | .error (.notInTurn (.ready 0)) => pure ()
  | .error error => fail s!"expected beginStep notInTurn, got {reprStr error}"
  | .ok state => fail s!"beginStep accepted ready state as {reprStr state.protocol}"
  match initial.dispatch rawRead with
  | .error (.notInStep (.ready 0)) => pure ()
  | .error error => fail s!"expected dispatch notInStep, got {reprStr error}"
  | .ok state => fail s!"dispatch accepted ready state as {reprStr state.protocol}"
  match initial.finishStep with
  | .error (.notInStep (.ready 0)) => pure ()
  | .error error => fail s!"expected finishStep notInStep, got {reprStr error}"
  | .ok state => fail s!"finishStep accepted ready state as {reprStr state.protocol}"
  let inTurn ←
    match initial.beginTurn with
    | .error error => fail s!"valid beginTurn failed with {reprStr error}"
    | .ok state => pure state
  match inTurn.beginTurn with
  | .error (.notReady (.turn 0 0)) => pure ()
  | .error error => fail s!"expected repeated beginTurn notReady, got {reprStr error}"
  | .ok state => fail s!"repeated beginTurn reached {reprStr state.protocol}"
  match inTurn.dispatch rawRead with
  | .error (.notInStep (.turn 0 0)) => pure ()
  | .error error => fail s!"expected in-turn dispatch notInStep, got {reprStr error}"
  | .ok state => fail s!"in-turn dispatch reached {reprStr state.protocol}"
  let inStep ←
    match inTurn.beginStep with
    | .error error => fail s!"valid beginStep failed with {reprStr error}"
    | .ok state => pure state
  match inStep.finishTurn with
  | .error (.notInTurn (.step 0 0 [])) => pure ()
  | .error error => fail s!"expected in-step finishTurn notInTurn, got {reprStr error}"
  | .ok state => fail s!"in-step finishTurn reached {reprStr state.protocol}"

private def testCounterAdmission : IO Unit := do
  let admittedRaw := rawIncrement { amount := 3, limit := 10 }
  match validateRaw 2 admittedRaw with
  | .error error =>
      fail s!"valid counter increment was rejected with {reprStr error}"
  | .ok call =>
      match view.execute call with
      | .error message => fail s!"admitted counter provider failed with {message}"
      | .ok reply => assertEqual "admitted counter increment reaches five" reply.value.after 5

  match validateRaw 2 rawUnknown with
  | .error error =>
      assertEqual "unknown counter tool is rejected"
        error (.unknownTool rawUnknown.name)
  | .ok _ => fail "unknown counter tool unexpectedly crossed the admission boundary"

  let overLimit := rawIncrement { amount := 9, limit := 10 }
  match validateRaw 2 overLimit with
  | .error error =>
      assertEqual "counter contract rejects an over-limit increment" error
        (.contractRejected incrementSpec.name
          "counter_increment would cross the request limit")
  | .ok _ => fail "over-limit counter increment unexpectedly crossed admission"

private def testHarnessDemo : IO Unit := do
  let state ←
    match Harness.demo with
    | .error error => fail s!"Harness.demo failed with {reprStr error}"
    | .ok state => pure state
  assertEqual "Harness.demo final model" state.model 5
  assertEqual "Harness.demo final protocol" state.protocol (.ready 1)
  assertEqual "Harness.demo leaves no live dispatch lease" state.leases.available []
  assertEqual "Harness.demo settled record count" state.records.length 4
  assertEqual "Harness.demo assigns monotonically increasing call ids"
    (state.records.map fun record ↦ record.id.value) [0, 1, 2, 3]
  assertEqual "Harness.demo log has exactly one adjacent call/result pair per record"
    (Harness.callBoundaries state.log) (Harness.recordBoundaries state.records)
  assertEqual "Harness.demo derives its structural protocol from the rich canonical log"
    (Session.protocolProjection state.session.events) state.log
  assertEqual "Harness.demo rich session records every request and settlement event"
    state.session.events.length 15
  assertEqual "Harness.demo rich surface contains user, assistant, and four tool results"
    state.messages.length 6
  match state.modelRequest with
  | none => fail "Harness.demo did not reconstruct a model request from its rich log"
  | some request =>
      assertEqual "Harness.demo request uses the latest recorded header"
        request.header Harness.counterRequestHeader
      assertEqual "Harness.demo request history is the exact current surface"
        request.messages state.messages
      assertEqual "Harness.demo request records the canonical log length"
        request.logLength state.session.events.length
  let _leaseCertificate :
      Harness.LeasesThreaded .empty state.records state.leases :=
    state.leases_threaded
  match state.records with
  | [first, incremented, secondRead, unknown] =>
      assertEqual "first read succeeds" first.outcome .succeeded
      assertEqual "increment succeeds" incremented.outcome .succeeded
      assertEqual "second read succeeds" secondRead.outcome .succeeded
      assertEqual "unknown tool is settled as a rejection" unknown.outcome
        (.admissionRejected (.unknownTool rawUnknown.name))
      assertEqual "admitted calls each retain exactly one policy dispatch"
        [first.policyDispatchCount, incremented.policyDispatchCount,
          secondRead.policyDispatchCount] [1, 1, 1]
      assertEqual "rejected call retains no policy dispatch" unknown.policyDispatchCount 0
      assertEqual "unknown rejection leaves the model unchanged" (unknown.before, unknown.after)
        (5, 5)
      let readResultCodec : Codec (Except String Nat) := wire.resultCodec .read ()
      match first.encodedResult with
      | none => fail "first read lost its request-indexed encoded result"
      | some encoded =>
          match readResultCodec.decode encoded with
          | .ok (.ok value) => assertEqual "first read encoded result" value 2
          | .ok (.error message) => fail s!"first read encoded tool failure: {message}"
          | .error error => fail s!"first read encoded result failed to decode: {reprStr error}"
      let incrementInput : Increment := { amount := 3, limit := 10 }
      let incrementResultCodec : Codec (Except String Nat) :=
        wire.resultCodec .increment incrementInput
      match incremented.encodedResult with
      | none => fail "increment lost its request-indexed encoded result"
      | some encoded =>
          match incrementResultCodec.decode encoded with
          | .ok (.ok value) => assertEqual "increment encoded result" value 5
          | .ok (.error message) => fail s!"increment encoded tool failure: {message}"
          | .error error => fail s!"increment encoded result failed to decode: {reprStr error}"
      match secondRead.encodedResult with
      | none => fail "second read lost its request-indexed encoded result"
      | some encoded =>
          match readResultCodec.decode encoded with
          | .ok (.ok value) => assertEqual "second read encoded result" value 5
          | .ok (.error message) => fail s!"second read encoded tool failure: {message}"
          | .error error =>
              fail s!"second read encoded result failed to decode: {reprStr error}"
      match unknown.encodedResult with
      | none => pure ()
      | some _ => fail "rejected call fabricated an encoded provider result"
  | records => fail s!"expected four ordered records, got {records.length}"
  match replayRaw (.ready 0) state.log with
  | .error error => fail s!"Harness.demo log replay failed with {reprStr error}"
  | .ok replayed =>
      assertRuntimeStateEqual
        "Harness.demo stored protocol equals replayed log" replayed state.protocol
  match validateRuntimeTrace (.ready 0) state.log with
  | .error error => fail s!"Harness.demo typed reconstruction failed with {reprStr error}"
  | .ok validated =>
      assertRuntimeStateEqual
        "Harness.demo raw log reconstructs an intrinsic typed trace"
        (eraseState validated.finish) state.protocol

  let multiTurn ←
    match Harness.RunnerState.runMultiTurn 1 [
      [[rawRead], [rawIncrement { amount := 2, limit := 10 }]],
      [[rawRead]]
    ] with
    | .error error => fail s!"multi-turn harness failed with {reprStr error}"
    | .ok state => pure state
  assertEqual "multi-turn harness final model" multiTurn.model 3
  assertEqual "multi-turn harness advances exact turn and step counters"
    multiTurn.protocol (.ready 2)
  assertEqual "multi-turn harness assigns session-wide call ids"
    (multiTurn.records.map fun record ↦ record.id.value) [0, 1, 2]
  assertEqual "multi-turn harness routes every admitted call through policy"
    (multiTurn.records.map Harness.CallRecord.policyDispatchCount) [1, 1, 1]
  assertEqual "multi-turn log has no unrecorded call or result"
    (Harness.callBoundaries multiTurn.log)
    (Harness.recordBoundaries multiTurn.records)
  let _leaseCertificate :
      Harness.LeasesThreaded .empty multiTurn.records multiTurn.leases :=
    multiTurn.leases_threaded
  match validateRuntimeTrace (.ready 0) multiTurn.log with
  | .error error => fail s!"multi-turn typed reconstruction failed with {reprStr error}"
  | .ok validated =>
      assertRuntimeStateEqual "multi-turn log reconstructs its terminal protocol"
        (eraseState validated.finish) multiTurn.protocol

/-- Run all executable adversarial and integration tests. -/
def run : IO Unit := do
  testEffects
  testCertifiedBatch
  testCodecs
  testStream
  testRegistry
  testLifecycle
  testProtocolFailures
  testPolicy
  testSubjectPolicyRejection
  testGenericRunnerPolicy
  testSessionLog
  testDependentChoiceHarness
  testSessionValidation
  testReactiveCoeffects
  testFiniteSchedules
  testRichStream
  testStreamSessionBridge
  testContextualEquivalence
  testUnifiedContexts
  testRuntimeRefinement
  testQuotientEffects
  testCoeffectQuotientLift
  testOperationalEquivalence
  testSessionRefinement
  testTransformationIndependence
  testOperationIndependence
  testArbitraryRemoval
  testGlobalRegistry
  testMediatedIndependenceBoundary
  testMediatedWholeRun
  testPartialTransformation
  testGlobalDynamics
  testGlobalLifecycle
  testGlobalCalculus
  testGlobalTraceFacts
  testGlobalTemporal
  testHarnessPhaseFailures
  testCounterAdmission
  testHarnessDemo
  IO.println "CORDIS adversarial and integration tests passed"

end Cordis.TestSuite
