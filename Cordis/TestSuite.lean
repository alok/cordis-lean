import Cordis.Codec
import Cordis.Effect
import Cordis.Examples.Counter
import Cordis.Examples.CounterWire
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Protocol
import Cordis.Registry

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

private def testProtocolFailures : IO Unit := do
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
  assertEqual "Harness.demo settled record count" state.records.length 4
  assertEqual "Harness.demo assigns monotonically increasing call ids"
    (state.records.map fun record ↦ record.id.value) [0, 1, 2, 3]
  match state.records with
  | [first, incremented, secondRead, unknown] =>
      assertEqual "first read succeeds" first.outcome .succeeded
      assertEqual "increment succeeds" incremented.outcome .succeeded
      assertEqual "second read succeeds" secondRead.outcome .succeeded
      assertEqual "unknown tool is settled as a rejection" unknown.outcome
        (.rejected (.unknownTool rawUnknown.name))
      assertEqual "unknown rejection leaves the model unchanged" (unknown.before, unknown.after)
        (5, 5)
  | records => fail s!"expected four ordered records, got {reprStr records}"
  match replayRaw (.ready 0) state.log with
  | .error error => fail s!"Harness.demo log replay failed with {reprStr error}"
  | .ok replayed =>
      assertRuntimeStateEqual
        "Harness.demo stored protocol equals replayed log" replayed state.protocol

/-- Run all executable adversarial and integration tests. -/
def run : IO Unit := do
  testEffects
  testCodecs
  testRegistry
  testProtocolFailures
  testCounterAdmission
  testHarnessDemo
  IO.println "CORDIS adversarial and integration tests passed"

end Cordis.TestSuite
