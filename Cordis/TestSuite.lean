import Cordis.Batch
import Cordis.Codec
import Cordis.Effect
import Cordis.Examples.Counter
import Cordis.Examples.CounterWire
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Protocol
import Cordis.Registry
import Cordis.Stream

/-!
# Executable adversarial and integration tests

The tests in this module exercise both successful proof-carrying paths and the dynamic
boundaries that must fail closed. `run` is intentionally independent of the repository's
executable entry points so another test runner can call it without importing an umbrella module.
-/

set_option autoImplicit false

namespace Cordis.TestSuite

open Cordis.Examples.Counter

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
  let _leaseCertificate :
      Harness.LeasesThreaded .empty state.records state.leases :=
    state.leases_threaded
  match state.records with
  | [first, incremented, secondRead, unknown] =>
      assertEqual "first read succeeds" first.outcome .succeeded
      assertEqual "increment succeeds" incremented.outcome .succeeded
      assertEqual "second read succeeds" secondRead.outcome .succeeded
      assertEqual "unknown tool is settled as a rejection" unknown.outcome
        (.rejected (.unknownTool rawUnknown.name))
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
  testCounterAdmission
  testHarnessDemo
  IO.println "CORDIS adversarial and integration tests passed"

end Cordis.TestSuite
