import Cordis.Batch
import Cordis.Codec
import Cordis.Coeffect
import Cordis.CoeffectQuotient
import Cordis.ContextualEquivalence
import Cordis.DeepSeekApi
import Cordis.DeepSeekApiErrorEnvelope
import Cordis.DeepSeekCurlTransport
import Cordis.DeepSeekCurlStream
import Cordis.DeepSeekCurlSession
import Cordis.DeepSeekHarnessProcess
import Cordis.DeepSeekHarnessProcessOutcome
import Cordis.DeepSeekHarnessTransportContract
import Cordis.DeepSeekHarnessTransportToolRound
import Cordis.DeepSeekHarnessProcessSchema
import Cordis.DeepSeekHarnessProcessSchemaPrefix
import Cordis.DeepSeekHarnessProcessSchemaPrefixConversation
import Cordis.DeepSeekCurlIncremental
import Cordis.DeepSeekCurlPrefix
import Cordis.DeepSeekCurlPrefixSession
import Cordis.DeepSeekCurlOutcome
import Cordis.DeepSeekOutcomeSession
import Cordis.DeepSeekOutcomeConversation
import Cordis.DeepSeekOutcomeConversationLoop
import Cordis.DeepSeekOutcomeTransportLoop
import Cordis.DeepSeekAsyncHarness
import Cordis.DeepSeekAsyncStreamHarness
import Cordis.DeepSeekAsyncStreamCancellation
import Cordis.DeepSeekStream
import Cordis.DeepSeekStreamFailure
import Cordis.DeepSeekTerminalOutcome
import Cordis.DeepSeekStreamIncremental
import Cordis.DeepSeekStreamByteFraming
import Cordis.DeepSeekCurlByteFraming
import Cordis.DeepSeekCurlBytePrefix
import Cordis.DeepSeekRichStream
import Cordis.DeepSeekRichToolStream
import Cordis.DeepSeekRichMixedStream
import Cordis.DeepSeekRichMultiStream
import Cordis.DeepSeekSessionBridge
import Cordis.DeepSeekSessionRunner
import Cordis.DeepSeekApiSession
import Cordis.DeepSeekHarness
import Cordis.DeepSeekHarnessExtensions
import Cordis.DeepSeekToolSchema
import Cordis.DeepSeekToolAdmission
import Cordis.DeepSeekGenericBridge
import Cordis.DeepSeekSchemaExecution
import Cordis.DeepSeekSchemaHarness
import Cordis.DeepSeekSchemaRound
import Cordis.DeepSeekSchemaMultiRound
import Cordis.DeepSeekSchemaRegistry
import Cordis.DeepSeekScopedRegistry
import Cordis.DeepSeekSchemaConversation
import Cordis.DeepSeekSchemaConversationLoop
import Cordis.DeepSeekSchemaStreamConversation
import Cordis.DeepSeekSchemaStreamPrefixConversation
import Cordis.DeepSeekSchemaStreamErrors
import Cordis.DeepSeekHarnessPersistence
import Cordis.DeepSeekHarnessEventArchive
import Cordis.DeepSeekHarnessExtensionArchive
import Cordis.DeepSeekHarnessExtensionRequest
import Cordis.DeepSeekHarnessExtensionPersistence
import Cordis.DeepSeekHarnessMixedPersistence
import Cordis.DeepSeekHarnessSchemaLift
import Cordis.DeepSeekHarnessMixedReplay
import Cordis.DeepSeekHarnessEventText
import Cordis.DeepSeekHarnessEventProcessOutcome
import Cordis.LoaderHMR
import Cordis.DeepSeekHarnessPayloadText
import Cordis.DeepSeekHarnessPayloadPersistence
import Cordis.DeepSeekHarnessErrors
import Cordis.DeepSeekHarnessRetry
import Cordis.DeepSeekHarnessCancellation
import Cordis.DeepSeekStreamHarness
import Cordis.DeepSeekStreamHarnessByte
import Cordis.DeepSeekStreamHarnessBytePrefix
import Cordis.DeepSeekStreamHarnessCancellation
import Cordis.DeepSeekStreamHarnessPrefix
import Cordis.DeepSeekStreamHarnessErrors
import Cordis.DeepSeekStreamHarnessRetry
import Cordis.DeepSeekStreamHarnessRetryConversation
import Cordis.DurableCodec
import Cordis.DurableBytes
import Cordis.DurableIO
import Cordis.DurableSettlement
import Cordis.Effect
import Cordis.Examples.Counter
import Cordis.Examples.CounterWire
import Cordis.Examples.DependentChoice
import Cordis.Examples.DependentChoiceSession
import Cordis.GlobalActivationOrchestrationTransposition
import Cordis.GlobalActivationTransposition
import Cordis.GlobalCalculus
import Cordis.GlobalDeletion
import Cordis.GlobalDynamics
import Cordis.GlobalIteratorIndependence
import Cordis.GlobalTransposition
import Cordis.GlobalForeignPhase
import Cordis.GlobalLandingTransposition
import Cordis.GlobalLifecycle
import Cordis.GlobalLifecycleBisimulation
import Cordis.GlobalNameAction
import Cordis.GlobalNameLifecycle
import Cordis.GlobalPaperRelation
import Cordis.GlobalPaperTraceSimulation
import Cordis.GlobalPaperTraceDeletion
import Cordis.GlobalPaperTraceNormalization
import Cordis.GlobalProgress
import Cordis.GlobalProgressTermination
import Cordis.GlobalRelations
import Cordis.GlobalRegistry
import Cordis.GlobalRuleInvariance
import Cordis.GlobalRuleObservations
import Cordis.GlobalSpatial
import Cordis.GlobalSupport
import Cordis.GlobalTemporal
import Cordis.GlobalTraceFacts
import Cordis.GlobalTraceRewrite
import Cordis.GlobalVestigial
import Cordis.Harness
import Cordis.GenericSessionHarness
import Cordis.HarnessPersistenceRefinement
import Cordis.HarnessPersistenceBytes
import Cordis.HarnessPersistenceArchive
import Cordis.HarnessPersistenceIO
import Cordis.DeepSeekHarnessPersistenceIO
import Cordis.DeepSeekHarnessPersistenceTransportRound
import Cordis.DeepSeekHarnessTransportConversation
import Cordis.DeepSeekHarnessTransportRetry
import Cordis.DeepSeekHarnessTransportRetryConversation
import Cordis.DeepSeekHarnessOpaqueMetadata
import Cordis.DeepSeekHarnessMetadataArchive
import Cordis.Lifecycle
import Cordis.MediatedIndependence
import Cordis.MediatedTheorem
import Cordis.OperationIndependence
import Cordis.ObservationalPartialTransformation
import Cordis.OperationalEquivalence
import Cordis.ParallelHarness
import Cordis.ParallelSchedule
import Cordis.AsyncHarness
import Cordis.PartialTransformation
import Cordis.Policy
import Cordis.Protocol
import Cordis.QuotientEffect
import Cordis.Registry
import Cordis.Removal
import Cordis.RichStream
import Cordis.RuntimeRefinement
import Cordis.RuntimeFailureRefinement
import Cordis.RuntimeOutcomeRefinement
import Cordis.RuntimeOutcomeSession
import Cordis.Schedule
import Cordis.Session
import Cordis.SessionRefinement
import Cordis.SessionExtensionRefinement
import Cordis.SessionExtensionArchive
import Cordis.SessionOpaqueMetadata
import Cordis.SessionArchive
import Cordis.SessionEventArchive
import Cordis.SessionPayloadArchive
import Cordis.SessionValidation
import Cordis.Stream
import Cordis.StreamSession
import Cordis.TextRefinement
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

private def testDependentChoiceSessionHarness : IO Unit := do
  assertEqual "dependent-choice rich generic run succeeds"
    Examples.DependentChoiceSession.runSucceeded true
  assertEqual "dependent-choice rich generic run reconstructs a request"
    Examples.DependentChoiceSession.requestPresent true
  assertEqual "dependent-choice rich generic run retains both call records"
    Examples.DependentChoiceSession.retainedRecordCount 2
  match Examples.DependentChoiceSession.runState with
  | none => fail "dependent-choice rich generic run unexpectedly failed"
  | some state =>
      assertEqual "dependent-choice rich generic final workspace" state.model
        Examples.DependentChoice.initialWorkspace
      assertEqual "dependent-choice rich generic protocol endpoint"
        state.protocol (.ready 1)
      assertEqual "dependent-choice rich generic log projection"
        (Session.protocolProjection state.session.events) state.log
      assertEqual "dependent-choice rich generic surface message count"
        state.messages.length 4
      assertEqual "dependent-choice rich generic outcomes"
        (state.records.map GenericHarness.CallRecord.outcome)
        [.succeeded,
          .policyRejected .deny "label output rejected by exact-call policy"]
      match state.modelRequest with
      | none => fail "dependent-choice rich generic request disappeared"
      | some request =>
          assertEqual "dependent-choice rich generic request header"
            request.header Examples.DependentChoiceSession.requestHeader
          assertEqual "dependent-choice rich generic request surface"
            request.messages state.messages
          assertEqual "dependent-choice rich generic request log length"
            request.logLength state.session.events.length
      let _models :
          GenericHarness.ModelsThreaded state.initialModel state.records state.model :=
        state.models_threaded
      let _leases :
          GenericHarness.LeasesThreaded .empty state.records state.leases :=
        state.leases_threaded

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

private def testParallelHarness : IO Unit := do
  let window := ParallelHarness.WindowOutcome.execute
    ParallelHarness.exampleWindow ParallelHarness.exampleBefore
  assertEqual "parallel window reaches the canonical state"
    window.applied.after
    { x := 11, y := 22, z := 33 }
  assertEqual "parallel window commits results in model order"
    (window.committed.map fun result => (result.id, result.value))
    [(0, 10), (1, 20), (2, 30)]
  let plan := ParallelHarness.Plan.execute
    ParallelHarness.examplePlan ParallelHarness.exampleBefore
  assertEqual "exclusive barrier runs after the parallel window"
    plan.applied.after
    { x := 11, y := 22, z := 33 }
  match plan.barrierReport with
  | none => fail "parallel plan lost its exclusive barrier report"
  | some report =>
      assertEqual "exclusive barrier report retains its task id" report.id 3
      match report.status with
      | .cancelled reason => fail s!"exclusive barrier was cancelled: {reason}"
      | .completed value => assertEqual "exclusive barrier observes the committed state" value 66
  let drained := ParallelHarness.drain [ParallelHarness.taskX, ParallelHarness.taskY] .timeout
  assertEqual "cancellation drain preserves every pending task id"
    (drained.map ParallelHarness.Report.id) [0, 1]
  match drained with
  | first :: _ =>
      match first.status with
      | .completed _ => fail "cancellation drain fabricated a completed result"
      | .cancelled reason =>
          assertEqual "cancellation drain emits a synthetic abort reason" reason "cancelled:timeout"
  | [] => fail "cancellation drain emitted no synthetic reports"

private def testParallelSchedule : IO Unit := do
  let outcome := ParallelSchedule.Plan.execute
    ParallelSchedule.examplePlan ParallelSchedule.exampleBefore
  assertEqual "finite parallel schedule reaches the canonical endpoint"
    outcome.applied.after
    { x := 11, y := 22, z := 33 }
  assertEqual "finite parallel schedule retains all model-order report IDs"
    (outcome.reports.map ParallelHarness.Report.id) [0, 1, 2, 3]
  assertEqual "finite parallel schedule emits one report per segment task"
    outcome.reports.length 4
  match outcome.reports with
  | _ :: _ :: _ :: barrierReport :: [] =>
      match barrierReport.status with
      | .completed value =>
          assertEqual "finite schedule barrier observes prior segment endpoints" value 66
      | .cancelled reason => fail s!"finite schedule barrier was cancelled: {reason}"
  | reports => fail s!"finite schedule emitted unexpected report shape: {reports.length}"
  assertEqual "finite parallel schedule recovers its exact predecessor"
    (outcome.applied.undo outcome.applied.after)
    ParallelSchedule.exampleBefore

private def testAsyncHarness : IO Unit := do
  assertEqual "async race records completion order separately from declaration order"
    AsyncHarness.exampleRaceTrace.completionIds [1, 0]
  assertEqual "async race applies the completion-order pure effects"
    AsyncHarness.exampleAfterComplete0.model
    { x := 11, y := 22, z := 30 }
  assertEqual "async race terminalizes fiber zero"
    (AsyncHarness.exampleAfterComplete0.phase AsyncHarness.exampleIndex0).isTerminal true
  assertEqual "async race terminalizes fiber one"
    (AsyncHarness.exampleAfterComplete0.phase AsyncHarness.exampleIndex1).isTerminal true
  assertEqual "async cancellation leaves the model unchanged"
    (AsyncHarness.exampleCancelInitial.cancel AsyncHarness.exampleIndex1 "user").model
    AsyncHarness.exampleBefore

private def testDurableSettlement : IO Unit := do
  assertEqual "durable first commit reaches its indexed successor"
    (DurableSettlement.Spec.after DurableSettlement.Example.spec 3
      DurableSettlement.Example.initial)
    13
  assertEqual "durable second commit reaches its indexed successor"
    (DurableSettlement.Spec.after DurableSettlement.Example.spec 8
      (DurableSettlement.Spec.after DurableSettlement.Example.spec 3
        DurableSettlement.Example.initial))
    21
  assertEqual "crash cut retains the committed prefix state"
    (DurableSettlement.CrashPrefix.recoveredState DurableSettlement.Example.crash)
    13
  assertEqual "crash cut exposes exactly one discarded frame"
    DurableSettlement.Example.crash.discarded.length
    1
  assertEqual "resume commits after the recovered prefix"
    (DurableSettlement.Spec.after DurableSettlement.Example.spec 5
      (DurableSettlement.CrashPrefix.recoveredState DurableSettlement.Example.crash))
    18
  assertEqual "resumed durable log contains the retained and new frames"
    (DurableSettlement.Log.frames DurableSettlement.Example.spec
      DurableSettlement.Example.initial DurableSettlement.Example.resumed).length
    2

private def testDurableCodec : IO Unit := do
  match DurableCodec.scanJsonPrefix DurableCodec.Example.wire
      DurableSettlement.Example.initial DurableCodec.Example.validJson with
  | .error error => fail s!"valid durable JSON prefix was rejected with {reprStr error}"
  | .ok scanned =>
      assertEqual "durable JSON scanner reaches the typed successor"
        scanned.current 21
      assertEqual "durable JSON scanner advances the sequence"
        scanned.nextSequence 2
      assertEqual "durable JSON scanner retains both decoded entries"
        (scanned.log.entries DurableCodec.Example.wire.spec
          DurableSettlement.Example.initial).length 2
  match DurableCodec.scanJsonPrefix DurableCodec.Example.wire
      DurableSettlement.Example.initial DurableCodec.Example.tornJson with
  | .error (.inl _) => pure ()
  | .error (.inr error) => fail s!"torn durable JSON reached semantic scanning: {reprStr error}"
  | .ok _ => fail "torn durable JSON frame was accepted"
  match DurableCodec.scanPrefix DurableCodec.Example.wire
      DurableSettlement.Example.initial [DurableCodec.Example.noncontiguousRaw] with
  | .error (.sequenceMismatch expected actual) =>
      assertEqual "durable scanner reports a non-contiguous sequence" (expected, actual) (0, 4)
  | .error error => fail s!"wrong durable scanner error: {reprStr error}"
  | .ok _ => fail "non-contiguous durable frame was accepted"

private def testDurableBytes : IO Unit := do
  match DurableBytes.decodeFrame DurableBytes.rawFramePayloadCodec
      (DurableBytes.Example.firstBytes ++ DurableBytes.Example.secondBytes) with
  | .error error => fail s!"binary raw frame prefix was rejected with {reprStr error}"
  | .ok (frame, suffix) =>
      assertEqual "binary frame decoder preserves the first sequence"
        frame.sequence 0
      assertEqual "binary frame decoder leaves the second frame untouched"
        suffix DurableBytes.Example.secondBytes
  match DurableBytes.decodeFrames DurableBytes.rawFramePayloadCodec 2
      DurableBytes.Example.validBytes with
  | .error error => fail s!"binary frame list was rejected with {reprStr error}"
  | .ok (frames, suffix) =>
      assertEqual "binary frame list decodes both raw frames"
        frames [DurableCodec.Example.firstRaw, DurableCodec.Example.secondRaw]
      assertEqual "binary frame list has no unconsumed bytes" suffix []
  match DurableBytes.decodeFrames DurableBytes.rawFramePayloadCodec 3
      DurableBytes.Example.tornBytes with
  | .error _ => pure ()
  | .ok _ => fail "torn binary durable suffix was accepted"
  match DurableBytes.scanBytesPrefix DurableCodec.Example.wire
      DurableSettlement.Example.initial DurableBytes.rawFramePayloadCodec 2
      DurableBytes.Example.validBytes with
  | .error error => fail s!"binary durable scan was rejected with {reprStr error}"
  | .ok (scanned, discarded) =>
      assertEqual "binary durable scan reaches the typed successor"
        scanned.current 21
      assertEqual "binary durable scan advances the sequence"
        scanned.nextSequence 2
      assertEqual "binary durable scan discards no bytes on a complete prefix"
        discarded []

private def testDurableIO : IO Unit := do
  let memory ← DurableIO.Example.memoryResume
  assertEqual "memory durable adapter resumes from a typed prefix" memory true
  let torn ← DurableIO.Example.memoryTornPrefix
  assertEqual "memory durable adapter exposes a torn suffix" torn true
  let file ← DurableIO.Example.fileResume
  assertEqual "filesystem durable adapter resumes from a typed prefix" file true

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

private def testRuntimeFailureRefinement : IO Unit := do
  match RuntimeFailureRefinement.validateFailureTrace
      RuntimeFailureRefinement.exampleJson with
  | .error error => fail s!"in-band provider failure was rejected with {reprStr error}"
  | .ok validated =>
      assertEqual "failure refinement preserves the decoded ordinary prefix"
        validated.chunks RuntimeFailureRefinement.exampleChunks
      assertEqual "failure refinement preserves the in-band error discriminant"
        validated.terminal.kind RuntimeFailureRefinement.FailureKind.error
      assertEqual "failure refinement preserves every LlmFailure field"
        validated.terminal.failure RuntimeFailureRefinement.exampleFailure
      let _certificate :=
        RuntimeFailureRefinement.ValidatedFailureTrace.decoded_exact validated
      pure ()
  match RuntimeFailureRefinement.validateFailureTrace
      RuntimeFailureRefinement.abortedJson with
  | .error error => fail s!"in-band abort was rejected with {reprStr error}"
  | .ok validated =>
      assertEqual "abort refinement preserves the aborted discriminant"
        validated.terminal.kind RuntimeFailureRefinement.FailureKind.aborted
      assertEqual "abort refinement preserves the request id"
        validated.terminal.failure.requestId (some "req-abort")
      assertEqual "abort refinement preserves absent optional retry metadata"
        (validated.terminal.failure.status, validated.terminal.failure.providerRetryAfterMs)
        (none, none)
  match RuntimeFailureRefinement.decodeFailureTrace [Lean.Json.mkObj [
    ("type", .str "finish"),
    ("reason", Lean.Json.mkObj [("kind", .str "stop")])
  ]] with
  | .error error =>
      assertEqual "successful finishes stay outside the failure validator"
        error (.successfulFinish 0 .stop)
  | .ok _ => fail "successful finish was accepted as an in-band failure"
  match RuntimeFailureRefinement.decodeFailureTrace [Lean.Json.mkObj [
    ("type", .str "finish"),
    ("reason", Lean.Json.mkObj [
      ("kind", .str "error"),
      ("failure", Lean.Json.mkObj [
        ("message", .str "bad"),
        ("code", .str "E"),
        ("status", .str "not-a-number")
      ])
    ])
  ]] with
  | .error error =>
      assertEqual "malformed failure metadata reports its nested status path"
        error (.terminal 0 (.typeMismatch
          [.index 0, .field "reason", .field "failure", .field "status"]
          "nonnegative safe integer" .string))
  | .ok _ => fail "malformed failure metadata was accepted"

private def testRuntimeOutcomeRefinement : IO Unit := do
  match RuntimeOutcomeRefinement.validateOutcome RuntimeRefinement.exampleJson with
  | .error error => fail s!"successful outcome dispatch failed: {reprStr error}"
  | .ok outcome =>
      match outcome with
      | .success validated =>
          assertEqual "outcome dispatch retains successful chunk sequence"
            validated.chunks RuntimeRefinement.exampleChunks
          assertEqual "outcome dispatch reports the successful branch"
            outcome.kind RuntimeOutcomeRefinement.OutcomeKind.success
          let _certificate := validated.decode_eq
          pure ()
      | .failure _ => fail "successful stream was dispatched as a failure"
  match RuntimeOutcomeRefinement.validateOutcome RuntimeFailureRefinement.exampleJson with
  | .error error => fail s!"failure outcome dispatch failed: {reprStr error}"
  | .ok outcome =>
      match outcome with
      | .failure validated =>
          assertEqual "outcome dispatch retains the failure discriminant"
            validated.terminal.kind RuntimeFailureRefinement.FailureKind.error
          assertEqual "outcome dispatch reports the failure branch"
            outcome.kind RuntimeOutcomeRefinement.OutcomeKind.failure
          let _certificate := validated.decoded_exact
          pure ()
      | .success _ => fail "in-band failure was dispatched as a successful stream"
  match RuntimeOutcomeRefinement.validateOutcome RuntimeOutcomeRefinement.neitherExample with
  | .error (.neither successError failureError) =>
      assertEqual "outcome rejection retains the successful-language error"
        successError (.decode (.unsupportedTag
          [.index 0, .field "type"] "unsupported"))
      assertEqual "outcome rejection retains the failure-language error"
        failureError (.ordinary 0 (.unsupportedTag
          [.field "type"] "unsupported"))
  | .ok _ => fail "unsupported stream was accepted by the outcome dispatcher"

private def testRuntimeOutcomeSession : IO Unit := do
  match RuntimeOutcomeSession.fixtureFailureDispatch with
  | .error error => fail s!"failure session dispatch failed: {reprStr error}"
  | .ok (.failure validated runner) =>
      assertEqual "failure session dispatch preserves its terminal kind"
        validated.terminal.kind RuntimeFailureRefinement.FailureKind.error
      assertEqual "failure session dispatch leaves the runner sequence unchanged"
        runner.session.nextSeq 0
      assertEqual "failure session dispatch leaves the runner turn unchanged"
        runner.turn 1
  | .ok (.appended _ _) => fail "in-band failure was appended as an assistant message"
  match RuntimeOutcomeSession.fixtureSuccessDispatch with
  | .error error => fail s!"successful session dispatch failed: {reprStr error}"
  | .ok (.failure _ _) => fail "successful stream was preserved as a failure"
  | .ok (.appended finished runner) =>
      assertEqual "successful session dispatch preserves the decoded source"
        finished.source.chunks RuntimeRefinement.exampleChunks
      assertEqual "successful session dispatch advances the sequence"
        runner.session.nextSeq 1
      assertEqual "successful session dispatch appends the assistant text"
        runner.session.messages [.assistant "hello" []]
  match RuntimeOutcomeSession.fixtureTextSuccessDispatch with
  | .error error => fail s!"text outcome session dispatch failed: {reprStr error}"
  | .ok result =>
      assertEqual "text outcome session dispatch retains parsed line count"
        result.validated.parsed.lines.length RuntimeRefinement.exampleJson.length
      assertEqual "text outcome session dispatch retains canonical source"
        (TextRefinement.renderJsonLines result.validated.parsed.lines)
        TextRefinement.outcomeTextExample
      match result.dispatched with
      | .appended _ runner =>
          assertEqual "text outcome session dispatch advances the sequence"
            runner.session.nextSeq 1
      | .failure _ _ => fail "text success was preserved as a failure"
  match RuntimeOutcomeSession.fixtureBytesFailureDispatch with
  | .error error => fail s!"byte failure session dispatch failed: {reprStr error}"
  | .ok ⟨text, result⟩ =>
      assertEqual "byte failure session dispatch retains decoded source"
        text TextRefinement.failureTextExample
      match result.dispatched with
      | .failure validated runner =>
          assertEqual "byte failure session dispatch preserves failure kind"
            validated.terminal.kind RuntimeFailureRefinement.FailureKind.error
          assertEqual "byte failure session dispatch leaves sequence unchanged"
            runner.session.nextSeq 0
      | .appended _ _ => fail "byte failure was appended as an assistant message"

private def testTextRefinement : IO Unit := do
  let streamSource := TextRefinement.renderJsonLines RuntimeRefinement.exampleJson
  match TextRefinement.validateStreamText streamSource with
  | .error error => fail s!"JSONL stream refinement failed: {reprStr error}"
  | .ok validated =>
      assertEqual "JSONL stream parsing retains every source line"
        validated.parsed.lines.length RuntimeRefinement.exampleJson.length
      let _replayCertificate := TextRefinement.ValidatedStreamText.replay_eq validated
      pure ()
  let sessionBytes := TextRefinement.renderJsonLinesBytes SessionRefinement.exampleJson
  match TextRefinement.validateSessionBytes sessionBytes with
  | .error error => fail s!"UTF-8 session refinement failed: {reprStr error}"
  | .ok ⟨_, validated⟩ =>
      assertRuntimeStateEqual "UTF-8 session parsing reaches the exact derived endpoint"
        (eraseState validated.validated.final.protocol) (.ready 2)
      let _projectionCertificate := TextRefinement.ValidatedSessionText.projection_exact validated
      pure ()
  match TextRefinement.parseJsonLines "" with
  | .error .emptyInput => pure ()
  | .error error => fail s!"empty JSONL source returned the wrong error: {reprStr error}"
  | .ok _ => fail "empty JSONL source was accepted"
  match TextRefinement.parseJsonLinesBytes (ByteArray.mk #[255]) with
  | .error .invalidUtf8 => pure ()
  | .error error => fail s!"invalid UTF-8 returned the wrong error: {reprStr error}"
  | .ok _ => fail "invalid UTF-8 was accepted"
  match TextRefinement.validateFailureText TextRefinement.failureTextExample with
  | .error error => fail s!"failure JSONL refinement failed: {reprStr error}"
  | .ok validated =>
      assertEqual "failure JSONL preserves the typed in-band error"
        validated.validated.terminal.kind RuntimeFailureRefinement.FailureKind.error
      assertEqual "failure JSONL preserves the provider retry delay"
        (validated.validated.terminal.failure.providerRetryAfterMs.map
          RuntimeRefinement.SafeNat.value)
        (some 250)
      let _certificate := TextRefinement.ValidatedFailureText.decoded_exact validated
      pure ()
  match TextRefinement.validateFailureBytes TextRefinement.failureTextExample.toUTF8 with
  | .error error => fail s!"failure UTF-8 refinement failed: {reprStr error}"
  | .ok ⟨text, validated⟩ =>
      assertEqual "failure UTF-8 refinement retains the exact source text"
        text TextRefinement.failureTextExample
      assertEqual "failure UTF-8 refinement retains the failure request id"
        validated.validated.terminal.failure.requestId (some "req-42")
  match TextRefinement.validateFailureBytes (ByteArray.mk #[255]) with
  | .error (.inl .invalidUtf8) => pure ()
  | .error error => fail s!"failure UTF-8 returned the wrong error: {reprStr error}"
  | .ok _ => fail "invalid UTF-8 was accepted by failure refinement"
  match TextRefinement.validateOutcomeText TextRefinement.outcomeTextExample with
  | .error error => fail s!"unified JSONL outcome refinement failed: {reprStr error}"
  | .ok validated =>
      match validated.validated with
      | .success success =>
          assertEqual "unified JSONL outcome retains the successful prefix"
            success.chunks RuntimeRefinement.exampleChunks
      | .failure _ => fail "successful JSONL outcome was dispatched as a failure"
  match TextRefinement.validateOutcomeText TextRefinement.failureTextExample with
  | .error error => fail s!"unified failure JSONL outcome failed: {reprStr error}"
  | .ok validated =>
      match validated.validated with
      | .failure failure =>
          assertEqual "unified failure JSONL outcome retains its terminal kind"
            failure.terminal.kind RuntimeFailureRefinement.FailureKind.error
      | .success _ => fail "failure JSONL outcome was dispatched as a success"
  match TextRefinement.validateOutcomeBytes TextRefinement.failureTextExample.toUTF8 with
  | .error error => fail s!"unified failure UTF-8 outcome failed: {reprStr error}"
  | .ok ⟨text, _⟩ =>
      assertEqual "unified failure UTF-8 outcome retains source text"
        text TextRefinement.failureTextExample

private def testHarnessPersistence : IO Unit := do
  match HarnessPersistenceRefinement.validatePersistedJson
      HarnessPersistenceRefinement.packedPersistenceExample with
  | .error error => fail s!"packed Harness persistence example failed: {reprStr error}"
  | .ok validated =>
      assertEqual "packed persistence preserves the supported header version and expansion count"
        (HarnessPersistenceRefinement.persistenceSummary (.ok validated)) (some (0, 3, 3))
      assertEqual "packed persistence retains exactly one storage row"
        validated.storageRows.length 1
      assertEqual "packed persistence expands the packed row into three events"
        validated.expandedEvents.length 3
      assertEqual "packed persistence retains the source session id"
        validated.header.id "session-example"
      let _splitCertificate := validated.split_exact
      let _expansionCertificate := validated.expansion_exact
      let _projectionCertificate := validated.projection_exact
      pure ()
  match HarnessPersistenceRefinement.validatePersistedJson
      HarnessPersistenceRefinement.packedReasoningPersistenceExample with
  | .error error => fail s!"packed reasoning persistence example failed: {reprStr error}"
  | .ok validated =>
      assertEqual "packed reasoning rows remain log-only while expanding exactly"
        (HarnessPersistenceRefinement.persistenceSummary (.ok validated)) (some (0, 2, 2))
      pure ()
  match HarnessPersistenceRefinement.validatePersistedJson
      [HarnessPersistenceRefinement.headerExample,
        HarnessPersistenceRefinement.malformedPackedRow] with
  | .error (.storage (.malformed "text-chunks"
      "dt length must be payload length minus one")) => pure ()
  | .error error => fail s!"malformed packed persistence row returned {reprStr error}"
  | .ok _ => fail "malformed packed persistence row was accepted"
  match HarnessPersistenceRefinement.validatePersistedJson
      [HarnessPersistenceRefinement.foreignVersionHeader] with
  | .error (.header (.foreignVersion 1)) => pure ()
  | .error error => fail s!"foreign persistence version returned {reprStr error}"
  | .ok _ => fail "foreign persistence version was accepted"
  match HarnessPersistenceRefinement.validatePersistedJson
      [HarnessPersistenceRefinement.foreignHeaderTag] with
  | .error (.header (.unsupportedTag [.field "type"] "event")) => pure ()
  | .error error => fail s!"foreign persistence header tag returned {reprStr error}"
  | .ok _ => fail "foreign persistence header tag was accepted"
  match HarnessPersistenceRefinement.validatePersistedJson [] with
  | .error .missingHeader => pure ()
  | .error error => fail s!"missing persistence header returned {reprStr error}"
  | .ok _ => fail "missing persistence header was accepted"
  match HarnessPersistenceRefinement.validatePersistedText
      (TextRefinement.renderJsonLines HarnessPersistenceRefinement.packedPersistenceExample) with
  | .error error => fail s!"text persistence example failed: {reprStr error}"
  | .ok ⟨_, validated⟩ =>
      assertEqual "text persistence composes JSONL parsing with packed expansion"
        validated.expandedEvents.length 3

private def testHarnessPersistenceBytes : IO Unit := do
  if ← HarnessPersistenceBytes.packedPersistenceBytesRuntime then
    pure ()
  else
    fail "byte persistence fixture did not reach the validated summary"
  if ← HarnessPersistenceBytes.packedReasoningPersistenceBytesRuntime then
    pure ()
  else
    fail "byte reasoning persistence fixture did not reach the validated summary"
  if ← HarnessPersistenceBytes.malformedPackedRowBytesRuntime then
    pure ()
  else
    fail "malformed byte persistence row was accepted"
  if ← HarnessPersistenceBytes.emptyBytesRuntime then
    pure ()
  else
    fail "empty byte persistence input was accepted"
  match HarnessPersistenceBytes.validatePersistedBytes
      HarnessPersistenceBytes.packedPersistenceBytesExample with
  | .error error => fail s!"byte persistence certificate failed: {reprStr error}"
  | .ok validated =>
      assertEqual "byte persistence retains the decoded source text"
        validated.text
        (TextRefinement.renderJsonLines HarnessPersistenceRefinement.packedPersistenceExample)
      assertEqual "byte persistence retains the parsed header and storage rows"
        validated.input.length 2
      assertEqual "byte persistence expands the packed row exactly"
        validated.persisted.expandedEvents.length 3
      assertEqual "byte persistence reaches the expected next sequence"
        validated.persisted.validated.final.session.nextSeq 3
      let _decoded := validated.decoded_exact
      let _parsed := validated.parsed_exact
      let _projection := validated.projection_exact
      pure ()
  match HarnessPersistenceBytes.validatePersistedBytes (ByteArray.mk #[255]) with
  | .error (.inl .invalidUtf8) => pure ()
  | .error error => fail s!"invalid UTF-8 returned {reprStr error}"
  | .ok _ => fail "invalid UTF-8 byte persistence input was accepted"

private def testHarnessPersistenceArchive : IO Unit := do
  match HarnessPersistenceArchive.archivePersistedJson
      HarnessPersistenceArchive.archivePersistenceExample with
  | .error error => fail s!"lossless persisted archive failed: {reprStr error}"
  | .ok archived =>
      assertEqual "lossless persisted archive retains every storage row"
        archived.rows.length 3
      assertEqual "lossless persisted archive tags packed and opaque rows"
        (archived.rows.map HarnessPersistenceArchive.ArchivedStorageRow.tag)
        ["packed:text-chunks", "opaque-required", "opaque-ignorable"]
      assertEqual "lossless persisted archive preserves row ASTs"
        ((archived.rows.map HarnessPersistenceArchive.ArchivedStorageRow.raw) ==
          [HarnessPersistenceRefinement.packedTextExample,
            SessionArchive.requiredExtensionJson, SessionArchive.ignorableExtensionJson]) true
      assertEqual "lossless persisted archive preserves the typed session header"
        archived.header.id "session-example"
      let _split := archived.split_exact
      let _rows := archived.rows_raw_exact
      pure ()
  match HarnessPersistenceArchive.archivePersistedText
      HarnessPersistenceArchive.archivePersistenceTextExample with
  | .error error => fail s!"lossless persisted text archive failed: {reprStr error}"
  | .ok ⟨input, archived⟩ =>
      assertEqual "lossless persisted text archive retains parsed input"
        input.length 4
      assertEqual "lossless persisted text archive retains row count"
        archived.rows.length 3
  match HarnessPersistenceArchive.archivePersistedBytes
      HarnessPersistenceArchive.archivePersistenceTextExample.toUTF8 with
  | .error error => fail s!"lossless persisted byte archive failed: {reprStr error}"
  | .ok ⟨text, input, archived⟩ =>
      assertEqual "lossless persisted byte archive retains decoded text"
        text HarnessPersistenceArchive.archivePersistenceTextExample
      assertEqual "lossless persisted byte archive retains parsed rows"
        input.length 4
      assertEqual "lossless persisted byte archive retains packed and opaque rows"
        archived.rows.length 3
  match HarnessPersistenceArchive.archivePersistedJson
      [HarnessPersistenceRefinement.headerExample,
        HarnessPersistenceRefinement.packedTextExample,
        HarnessPersistenceArchive.malformedPersistedEnvelope] with
  | .error (.row 2 (.missingField [.index 2] "time")) => pure ()
  | .error error => fail s!"indexed persisted archive failure returned {reprStr error}"
  | .ok _ => fail "malformed persisted envelope was accepted"
  match HarnessPersistenceArchive.archivePersistedJson [] with
  | .error .missingHeader => pure ()
  | .error error => fail s!"empty persisted archive returned {reprStr error}"
  | .ok _ => fail "empty persisted archive was accepted"

private def testHarnessPersistenceIO : IO Unit := do
  match ← HarnessPersistenceIO.fixtureMemory with
  | .error error => fail s!"memory Harness JSONL adapter failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "memory Harness JSONL adapter retains the logical rows"
        certificate.input.length 2
      assertEqual "memory Harness JSONL adapter retains packed expansion"
        certificate.validated.expandedEvents.length 3
      assertEqual
        "memory Harness JSONL adapter reaches the validated session endpoint"
        certificate.validated.validated.final.session.nextSeq 3
      let _projection := HarnessPersistenceIO.ReadCertificate.projection_exact certificate
      let _split := HarnessPersistenceIO.ReadCertificate.split_exact certificate
      pure ()
  match ← HarnessPersistenceIO.fixtureAppend with
  | .error error => fail s!"append-only Harness JSONL adapter failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "append-only Harness JSONL adapter retains the appended row"
        certificate.input.length 2
      assertEqual "append-only Harness JSONL adapter expands the appended packed row"
        certificate.validated.expandedEvents.length 3
      pure ()
  match ← HarnessPersistenceIO.fixtureFile with
  | .error error => fail s!"filesystem Harness JSONL adapter failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "filesystem Harness JSONL adapter retains the source header"
        certificate.validated.header.id "session-example"
      pure ()
  match ← HarnessPersistenceIO.fixtureInvalidUtf8 with
  | .error (.text .invalidUtf8) => pure ()
  | .error error =>
      fail s!"invalid UTF-8 returned the wrong persistence adapter error: {reprStr error}"
  | .ok _ => fail "invalid UTF-8 was accepted by the persistence adapter"

private def testDeepSeekApi : IO Unit := do
  let plan := DeepSeekApi.buildRequest "https://api.deepseek.com"
    { value := "test-key" } DeepSeekApi.exampleRequest
  assertEqual "DeepSeek request uses POST" plan.request.method .post
  assertEqual "DeepSeek request targets chat completions"
    plan.request.url "https://api.deepseek.com/chat/completions"
  assertEqual "DeepSeek request carries content and authorization headers"
    plan.request.headers.length 2
  let _bodyCertificate := plan.body_eq
  match ← DeepSeekApi.execute DeepSeekApi.exampleTransport plan with
  | .error error => fail s!"DeepSeek fixture request failed: {reprStr error}"
  | .ok ⟨body, validated⟩ =>
      assertEqual "DeepSeek fixture body is preserved" body DeepSeekApi.exampleResponseBody
      assertEqual "DeepSeek response id" validated.response.id "chatcmpl-example"
      assertEqual "DeepSeek response model" validated.response.model "deepseek-reasoner"
      assertEqual "DeepSeek response has one tool call"
        validated.response.choices.head.message.toolCalls.length 1
      assertEqual "DeepSeek response tool name"
        (validated.response.choices.head.message.toolCalls.head?.map DeepSeekApi.FunctionCall.name)
        (some "get_weather")
      assertEqual "DeepSeek response finish reason"
        validated.response.choices.head.finishReason (some .toolCalls)
      let _parseCertificate := validated.parsed
      let _decodeCertificate := validated.decoded
  match DeepSeekApi.validateResponse "" with
  | .error (.invalidJson _) => pure ()
  | _ => fail "invalid DeepSeek JSON was accepted"
  let badStatusTransport : DeepSeekApi.Transport := {
    send := fun _request => pure <| .ok {
      status := 401
      body := "{\"error\":{\"message\":\"unauthorized\"}}"
    }
  }
  match ← DeepSeekApi.execute badStatusTransport plan with
  | .error (.httpStatus 401 _) => pure ()
  | _ => fail "HTTP status boundary was not preserved"
  let failingTransport : DeepSeekApi.Transport := {
    send := fun _request => pure (.error "offline")
  }
  match ← DeepSeekApi.execute failingTransport plan with
  | .error (.transport "offline") => pure ()
  | _ => fail "transport failure was not preserved"

private def testDeepSeekCurlTransport : IO Unit := do
  match ← DeepSeekCurlTransport.fixtureResponse with
  | .error error => fail s!"process-backed DeepSeek fixture failed: {reprStr error}"
  | .ok ⟨body, validated⟩ =>
      assertEqual "process-backed DeepSeek fixture preserves stdin body"
        body DeepSeekApi.exampleResponseBody
      assertEqual "process-backed DeepSeek fixture decodes response id"
        validated.response.id "chatcmpl-example"
      let _bodyCertificate := validated.parsed
      let _decodeCertificate := validated.decoded
  let malformedConfig : DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #["-c", "printf broken"]
  }
  match ← DeepSeekCurlTransport.runProcess malformedConfig
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.malformedOutput output) =>
      assertEqual "malformed process output is preserved" output "broken"
  | .error error => fail s!"malformed process output returned {reprStr error}"
  | .ok response => fail s!"malformed process output was accepted: {reprStr response}"

private def testDeepSeekCurlStream : IO Unit := do
  match ← DeepSeekCurlStream.fixtureResponse with
  | .error error => fail s!"process-backed DeepSeek SSE fixture failed: {reprStr error}"
  | .ok ⟨body, validated⟩ =>
      assertEqual "process-backed DeepSeek SSE fixture preserves body"
        body DeepSeekStream.exampleStreamBody
      assertEqual "process-backed DeepSeek SSE fixture retains data and done frames"
        validated.frames.length 2
  let malformedConfig : DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #[
      "-c",
      "printf 'event: bad\\n\\ndata: [DONE]\\n\\n__CORDIS_HTTP_STATUS__200\\n'"
    ]
  }
  match ← DeepSeekCurlStream.executeSse malformedConfig
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.stream (.unexpectedLine _ _)) => pure ()
  | .error error => fail s!"malformed SSE returned {reprStr error}"
  | .ok _ => fail "malformed SSE was accepted"
  let statusConfig : DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #["-c", "printf 'unavailable\\n__CORDIS_HTTP_STATUS__503\\n'"]
  }
  match ← DeepSeekCurlStream.executeSse statusConfig
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.httpStatus 503 "unavailable") => pure ()
  | .error error => fail s!"HTTP status returned {reprStr error}"
  | .ok _ => fail "non-success SSE status was accepted"

private def testDeepSeekCurlOutcome : IO Unit := do
  match ← DeepSeekCurlOutcome.fixtureContentFilter with
  | .error error => fail s!"process-backed terminal failure outcome failed: {reprStr error}"
  | .ok ⟨body, processed⟩ =>
      assertEqual "process-backed outcome preserves failure body"
        body DeepSeekStreamFailure.exampleContentFilterBody
      assertEqual "process-backed outcome classifies provider failure"
        (DeepSeekTerminalOutcome.TerminalOutcome.kind processed.outcome)
        .providerFailure
      match processed.outcome with
      | .failure validated =>
          assertEqual "process-backed outcome retains failure reason"
            validated.view.reason .contentFilter
      | _ => fail "process-backed outcome lost the failure certificate"
  match ← DeepSeekCurlOutcome.fixtureText with
  | .error error => fail s!"process-backed terminal text outcome failed: {reprStr error}"
  | .ok ⟨_, processed⟩ =>
      assertEqual "process-backed outcome classifies text"
        (DeepSeekTerminalOutcome.TerminalOutcome.kind processed.outcome) .text
  match ← DeepSeekCurlOutcome.fixtureTool with
  | .error error => fail s!"process-backed terminal tool outcome failed: {reprStr error}"
  | .ok ⟨_, processed⟩ =>
      assertEqual "process-backed outcome classifies tool"
        (DeepSeekTerminalOutcome.TerminalOutcome.kind processed.outcome) .tool
  match ← DeepSeekCurlOutcome.fixtureMixed with
  | .error error => fail s!"process-backed terminal mixed outcome failed: {reprStr error}"
  | .ok ⟨_, processed⟩ =>
      assertEqual "process-backed outcome classifies mixed"
        (DeepSeekTerminalOutcome.TerminalOutcome.kind processed.outcome) .mixed
  match ← DeepSeekCurlOutcome.fixtureMulti with
  | .error error => fail s!"process-backed terminal multi outcome failed: {reprStr error}"
  | .ok ⟨_, processed⟩ =>
      assertEqual "process-backed outcome classifies multi"
        (DeepSeekTerminalOutcome.TerminalOutcome.kind processed.outcome) .multi
  let malformedConfig : DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #["-c", "printf broken"]
  }
  match ← DeepSeekCurlOutcome.executeOutcome malformedConfig
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.process (.malformedOutput "broken")) => pure ()
  | .error error => fail s!"process-backed outcome malformed output returned {reprStr error}"
  | .ok _ => fail "process-backed outcome accepted malformed process output"
  let statusConfig : DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #["-c", "printf 'unavailable\\n__CORDIS_HTTP_STATUS__503\\n'"]
  }
  match ← DeepSeekCurlOutcome.executeOutcome statusConfig
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.httpStatus 503 "unavailable") => pure ()
  | .error error => fail s!"process-backed outcome status returned {reprStr error}"
  | .ok _ => fail "process-backed outcome accepted a non-success status"

private def testDeepSeekOutcomeSession : IO Unit := do
  match ← DeepSeekOutcomeSession.fixtureFailureDispatch with
  | .error error => fail s!"outcome session failure dispatch failed: {reprStr error}"
  | .ok ⟨_, .providerFailure validated runner⟩ =>
      assertEqual "outcome session preserves provider failure reason"
        validated.view.reason .contentFilter
      assertEqual "outcome session does not append a provider failure"
        runner.session.nextSeq 0
      assertEqual "outcome session failure leaves messages unchanged"
        runner.session.messages []
  | .ok _ => fail "outcome session turned a provider failure into an assistant message"
  match ← DeepSeekOutcomeSession.fixtureTextDispatch with
  | .error error => fail s!"outcome session text dispatch failed: {reprStr error}"
  | .ok ⟨_, .appended finished runner⟩ =>
      assertEqual "outcome session text dispatch advances the sequence"
        runner.session.nextSeq 1
      assertEqual "outcome session text dispatch stores the assistant"
        runner.session.messages [.assistant "Hello world" []]
      let _terminalCertificate := finished.finished.terminal_state
  | .ok _ => fail "outcome session text dispatch returned a non-appended result"
  match ← DeepSeekOutcomeSession.fixtureToolDispatch with
  | .error error => fail s!"outcome session tool dispatch failed: {reprStr error}"
  | .ok ⟨_, .appended _ runner⟩ =>
      assertEqual "outcome session tool dispatch advances the sequence"
        runner.session.nextSeq 1
      assertEqual "outcome session tool dispatch allocates one local call"
        runner.nextCall 1
  | .ok _ => fail "outcome session tool dispatch returned a non-appended result"
  match ← DeepSeekOutcomeSession.fixtureMixedDispatch with
  | .error error => fail s!"outcome session mixed dispatch failed: {reprStr error}"
  | .ok ⟨_, .appended _ runner⟩ =>
      assertEqual "outcome session mixed dispatch advances the sequence"
        runner.session.nextSeq 1
      assertEqual "outcome session mixed dispatch counts one local call"
        runner.nextCall 1
  | .ok _ => fail "outcome session mixed dispatch returned a non-appended result"
  match ← DeepSeekOutcomeSession.fixtureMultiDispatch with
  | .error error => fail s!"outcome session multi dispatch failed: {reprStr error}"
  | .ok ⟨_, .appended _ runner⟩ =>
      assertEqual "outcome session multi dispatch advances the sequence"
        runner.session.nextSeq 1
      assertEqual "outcome session multi dispatch counts both local calls"
        runner.nextCall 2
  | .ok _ => fail "outcome session multi dispatch returned a non-appended result"

private def testDeepSeekOutcomeConversation : IO Unit := do
  match ← DeepSeekOutcomeConversation.fixtureFailureDispatch with
  | .error error => fail s!"outcome conversation failure dispatch failed: {reprStr error}"
  | .ok ⟨_, .providerFailure validated runner⟩ =>
      assertEqual "outcome conversation preserves provider failure reason"
        validated.view.reason .contentFilter
      assertEqual "outcome conversation failure leaves sequence unchanged"
        runner.session.nextSeq 0
      assertEqual "outcome conversation failure leaves messages unchanged"
        runner.session.messages []
  | .ok _ => fail "outcome conversation turned a provider failure into an assistant"
  match ← DeepSeekOutcomeConversation.fixtureTextDispatch with
  | .error error => fail s!"outcome conversation text dispatch failed: {reprStr error}"
  | .ok ⟨_, .assistant finished runner⟩ =>
      assertEqual "outcome conversation text advances sequence" runner.session.nextSeq 1
      assertEqual "outcome conversation text stores assistant"
        runner.session.messages [.assistant "Hello world" []]
      assertEqual "outcome conversation text exposes no calls"
        (DeepSeekOutcomeConversation.projectedFunctionCalls finished.finished.view).length 0
  | .ok _ => fail "outcome conversation text returned a non-assistant result"
  match ← DeepSeekOutcomeConversation.fixtureToolDispatch with
  | .error error => fail s!"outcome conversation tool dispatch failed: {reprStr error}"
  | .ok ⟨_, .assistant finished runner⟩ =>
      assertEqual "outcome conversation tool advances sequence" runner.session.nextSeq 1
      assertEqual "outcome conversation tool allocates one call" runner.nextCall 1
      assertEqual "outcome conversation tool exposes one call"
        (DeepSeekOutcomeConversation.projectedFunctionCalls finished.finished.view).length 1
  | .ok _ => fail "outcome conversation tool returned a non-assistant result"
  match ← DeepSeekOutcomeConversation.fixtureMixedDispatch with
  | .error error => fail s!"outcome conversation mixed dispatch failed: {reprStr error}"
  | .ok ⟨_, .assistant finished runner⟩ =>
      assertEqual "outcome conversation mixed advances sequence" runner.session.nextSeq 1
      assertEqual "outcome conversation mixed allocates one call" runner.nextCall 1
      assertEqual "outcome conversation mixed exposes one call"
        (DeepSeekOutcomeConversation.projectedFunctionCalls finished.finished.view).length 1
  | .ok _ => fail "outcome conversation mixed returned a non-assistant result"
  match ← DeepSeekOutcomeConversation.fixtureMultiDispatch with
  | .error error => fail s!"outcome conversation multi dispatch failed: {reprStr error}"
  | .ok ⟨_, .assistant finished runner⟩ =>
      assertEqual "outcome conversation multi advances sequence" runner.session.nextSeq 1
      assertEqual "outcome conversation multi allocates two calls" runner.nextCall 2
      assertEqual "outcome conversation multi exposes two calls"
        (DeepSeekOutcomeConversation.projectedFunctionCalls finished.finished.view).length 2
  | .ok _ => fail "outcome conversation multi returned a non-assistant result"

private def testDeepSeekOutcomeConversationExecution : IO Unit := do
  match ← DeepSeekOutcomeConversation.fixtureFailureExecution with
  | .error error => fail s!"outcome conversation failure execution failed: {reprStr error}"
  | .ok ⟨_, .providerFailure validated runner⟩ =>
      assertEqual "outcome conversation execution preserves failure reason"
        validated.view.reason .contentFilter
      assertEqual "outcome conversation execution failure leaves sequence unchanged"
        runner.session.nextSeq 0
  | .ok _ => fail "outcome conversation execution ran a provider failure as a tool round"
  match ← DeepSeekOutcomeConversation.fixtureTextExecution with
  | .error error => fail s!"outcome conversation text execution failed: {reprStr error}"
  | .ok ⟨_, .assistant round⟩ =>
      assertEqual "outcome conversation text execution preserves model" round.finalModel 0
      assertEqual "outcome conversation text execution appends one assistant"
        round.runner.session.nextSeq 1
      assertEqual "outcome conversation text execution has no tools" round.executions.length 0
  | .ok _ => fail "outcome conversation text execution returned a failure"
  match ← DeepSeekOutcomeConversation.fixtureCounterToolExecution with
  | .error error => fail s!"outcome conversation counter execution failed: {reprStr error}"
  | .ok ⟨_, .assistant round⟩ =>
      assertEqual "outcome conversation counter execution preserves model" round.finalModel 0
      assertEqual "outcome conversation counter execution executes one tool"
        round.executions.length 1
      assertEqual "outcome conversation counter execution retains assistant sequence"
        round.assistantRunner.session.nextSeq 1
      assertEqual "outcome conversation counter execution appends tool result"
        round.runner.session.nextSeq 2
  | .ok _ => fail "outcome conversation counter execution returned a failure"

private def testDeepSeekOutcomeConversationLoop : IO Unit := do
  match DeepSeekOutcomeConversationLoop.exampleRun with
  | .error error => fail s!"outcome conversation loop failed: {reprStr error}"
  | .ok result =>
      assertEqual "outcome conversation loop executes two terminal rounds"
        result.rounds.length 2
      assertEqual "outcome conversation loop preserves final model"
        result.finalModel 0
      assertEqual "outcome conversation loop retains one tool call"
        result.runner.nextCall 1
      assertEqual "outcome conversation loop appends assistant/tool/assistant"
        result.runner.session.nextSeq 3
      match result.stop with
      | .completed _ noCalls =>
          let _completionEvidence := noCalls
          pure ()
      | .providerFailure _ _ => fail "outcome conversation loop stopped on provider failure"
      | .fuelExhausted => fail "outcome conversation loop exhausted before text completion"

private def testDeepSeekOutcomeTransportLoop : IO Unit := do
  match ← DeepSeekOutcomeTransportLoop.Example.run with
  | .error error => fail s!"outcome transport loop failed: {reprStr error}"
  | .ok result =>
      assertEqual "outcome transport loop executes two terminal rounds"
        result.rounds.length 2
      assertEqual "outcome transport loop preserves final model"
        result.finalModel 0
      assertEqual "outcome transport loop retains one tool call"
        result.runner.nextCall 1
      assertEqual "outcome transport loop appends assistant/tool/assistant"
        result.runner.session.nextSeq 3
      match result.rounds with
      | first :: _ =>
          assertEqual "outcome transport loop uses a streaming request"
            first.2.2.plan.source.stream true
      | [] => fail "outcome transport loop returned no successful rounds"
      match result.stop with
      | .completed _ noCalls =>
          let _completionEvidence := noCalls
          pure ()
      | .providerFailure _ _ => fail "outcome transport loop stopped on provider failure"
      | .apiFailure _ _ _ => fail "outcome transport loop stopped on API failure"
      | .fuelExhausted => fail "outcome transport loop exhausted before text completion"
  match ← DeepSeekOutcomeTransportLoop.Example.apiFailureRun with
  | .error error => fail s!"outcome transport API failure failed: {reprStr error}"
  | .ok result =>
      assertEqual "outcome transport API failure leaves rounds empty"
        result.rounds.length 0
      assertEqual "outcome transport API failure preserves runner"
        result.runner.session.nextSeq 0
      match result.stop with
      | .apiFailure status validated runner =>
          assertEqual "outcome transport API failure preserves status" status 429
          assertEqual "outcome transport API failure preserves message"
            validated.error.message "rate limited"
          assertEqual "outcome transport API failure keeps the same runner"
            runner.session.messages []
      | .completed _ _ => fail "outcome transport API failure completed"
      | .providerFailure _ _ => fail "outcome transport API failure became stream failure"
      | .fuelExhausted => fail "outcome transport API failure exhausted"

private def testDeepSeekCurlSession : IO Unit := do
  match ← DeepSeekCurlSession.fixtureTextResponse with
  | .error error => fail s!"process-backed DeepSeek session response failed: {reprStr error}"
  | .ok ⟨body, processed⟩ =>
      assertEqual "process-backed DeepSeek session preserves the source body"
        body DeepSeekRichStream.exampleTextStreamBody
      assertEqual "process-backed DeepSeek session extracts terminal text"
        processed.finished.finished.view.content "Hello world"
      assertEqual "process-backed DeepSeek session has no tool calls in text fixture"
        processed.finished.finished.view.rawToolCalls.length 0
  match ← DeepSeekCurlSession.fixtureTextAppend with
  | .error error => fail s!"process-backed DeepSeek session append failed: {reprStr error}"
  | .ok ⟨body, (processed, runner)⟩ =>
      assertEqual "process-backed DeepSeek append retains the source body"
        body DeepSeekRichStream.exampleTextStreamBody
      assertEqual "process-backed DeepSeek append advances the runner sequence"
        runner.session.nextSeq 1
      assertEqual "process-backed DeepSeek append retains the typed assistant message"
        runner.session.messages [.assistant "Hello world" []]
      let _wireCertificate := processed.wire
      let _finishedCertificate := processed.finished.finished.terminal_state
      let _nextSeqCertificate := DeepSeekCurlSession.appendProcessed_nextSeq
        runner processed [] (by simp) (by simp)
      let _nextCallCertificate := DeepSeekCurlSession.appendProcessed_nextCall
        runner processed [] (by simp) (by simp)
      pure ()

private def testDeepSeekHarnessProcess : IO Unit := do
  match DeepSeekHarnessProcess.fixturePrepared with
  | .error error => fail s!"request provenance preparation failed: {reprStr error}"
  | .ok prepared =>
      assertEqual "request provenance preserves the typed model"
        prepared.plan.source.model "fixture-model"
      let _buildCertificate :=
        DeepSeekHarnessProcess.PreparedRequest.build_exact prepared
      let _bodyCertificate :=
        DeepSeekHarnessProcess.PreparedRequest.body_eq_source prepared
      pure ()
  match ← DeepSeekHarnessProcess.fixtureText with
  | .error error => fail s!"request provenance process fixture failed: {reprStr error}"
  | .ok ⟨prepared, ⟨body, round⟩⟩ =>
      assertEqual "request provenance process preserves the source body"
        body DeepSeekRichStream.exampleTextStreamBody
      assertEqual "request provenance process appends one session event"
        round.after.session.nextSeq 1
      assertEqual "request provenance process retains the prepared model"
        prepared.plan.source.model "fixture-model"
      let _endpointCertificate :=
        DeepSeekHarnessProcess.ProcessRound.append_endpoint round
      let _nextSeqCertificate :=
        DeepSeekHarnessProcess.ProcessRound.nextSeq round
      let _nextCallCertificate :=
        DeepSeekHarnessProcess.ProcessRound.nextCall round
      pure ()

private def testDeepSeekHarnessProcessOutcome : IO Unit := do
  match ← DeepSeekHarnessProcessOutcome.Example.text with
  | .error error => fail s!"typed outcome text fixture failed: {reprStr error}"
  | .ok ⟨prepared, ⟨body, round⟩⟩ =>
      assertEqual "typed outcome process preserves text body"
        body DeepSeekRichStream.exampleTextStreamBody
      assertEqual "typed outcome process proves streaming mode"
        prepared.plan.source.stream true
      match round.result with
      | .providerFailure _ _ => fail "text outcome became a provider failure"
      | .assistant executed =>
          assertEqual "typed outcome text appends one assistant event"
            executed.runner.session.nextSeq 1
          assertEqual "typed outcome text executes no tools"
            executed.executions.length 0
          let _resultCertificate :=
            DeepSeekHarnessProcessOutcome.ProcessOutcomeRound.result_exact round
          let _endpointCertificate :=
            DeepSeekHarnessProcessOutcome.ProcessOutcomeRound.endpoint_exact round
          let _streamCertificate :=
            DeepSeekHarnessProcessOutcome.ProcessOutcomeRound.stream_flag round
          pure ()
  match ← DeepSeekHarnessProcessOutcome.Example.tool with
  | .error error => fail s!"typed outcome tool fixture failed: {reprStr error}"
  | .ok ⟨_prepared, ⟨body, round⟩⟩ =>
      assertEqual "typed outcome process preserves tool body"
        body DeepSeekOutcomeConversation.counterToolStreamBody
      match round.result with
      | .providerFailure _ _ => fail "tool outcome became a provider failure"
      | .assistant executed =>
          assertEqual "typed outcome tool executes one dependent call"
            executed.executions.length 1
          assertEqual "typed outcome tool appends assistant and tool result"
            executed.runner.session.nextSeq 2
          pure ()
  match ← DeepSeekHarnessProcessOutcome.Example.failure with
  | .error error => fail s!"typed outcome failure fixture failed: {reprStr error}"
  | .ok ⟨_prepared, ⟨body, round⟩⟩ =>
      assertEqual "typed outcome process preserves provider-failure body"
        body DeepSeekStreamFailure.exampleContentFilterBody
      match round.result with
      | .providerFailure validated runner =>
          assertEqual "typed outcome failure preserves provider failure kind"
            validated.view.reason DeepSeekStreamFailure.FailureReason.contentFilter
          assertEqual "typed outcome failure preserves the runner"
            runner.session.nextSeq 0
      | .assistant _ => fail "provider failure became an assistant"

private def testDeepSeekHarnessProcessSchema : IO Unit := do
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"process schema weather certificate failed: {reprStr error}"
  | _, .error error => fail s!"process schema clock certificate failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekHarnessProcessSchema.Example.dualToolStreamProvenanceRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"process schema tool fixture failed: {reprStr error}"
      | .ok ⟨prepared, ⟨body, round⟩⟩ =>
          assertEqual "process schema preserves the dual-tool body"
            body DeepSeekSchemaStreamConversation.Example.dualToolStreamBody
          assertEqual "process schema retains stream mode"
            prepared.plan.source.stream true
          assertEqual "process schema retains both certified tools"
            prepared.plan.source.tools.length 2
          let _processedCertificate :=
            DeepSeekHarnessProcessSchema.SchemaProcessRound.processed_exact round
          match round.step with
          | .terminal _ => fail "process schema tool fixture became terminal"
          | .tools toolStep =>
              assertEqual "process schema executes both registry calls"
                toolStep.batch.executions.length 2
              assertEqual "process schema appends assistant and two results"
                toolStep.runner.session.nextSeq
                (DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3)
      match ← DeepSeekHarnessProcessSchema.Example.textProvenanceRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"process schema text fixture failed: {reprStr error}"
      | .ok ⟨prepared, ⟨body, round⟩⟩ =>
          assertEqual "process schema preserves the terminal body"
            body DeepSeekRichStream.exampleTextStreamBody
          assertEqual "process schema text remains streamed"
            prepared.plan.source.stream true
          match round.step with
          | .terminal terminal =>
              assertEqual "process schema terminal has no tool calls"
                terminal.processed.finished.finished.view.rawToolCalls.length 0
          | .tools _ => fail "process schema text fixture unexpectedly dispatched tools"

private def testDeepSeekHarnessProcessSchemaPrefix : IO Unit := do
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"prefix process schema weather certificate failed: {reprStr error}"
  | _, .error error => fail s!"prefix process schema clock certificate failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekHarnessProcessSchemaPrefix.Example.dualToolPrefixProvenanceRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"prefix process schema tool fixture failed: {reprStr error}"
      | .ok ⟨prepared, round⟩ =>
          assertEqual "prefix process schema retains stream mode"
            prepared.plan.source.stream true
          assertEqual "prefix process schema retains both certified tools"
            prepared.plan.source.tools.length 2
          let _bodyCertificate :=
            DeepSeekHarnessProcessSchemaPrefix.PreparedSchemaPrefixRound.body_eq_source round
          match round.outcome with
          | .completed completed =>
              assertEqual "prefix process schema preserves the complete body prefix"
                (completed.observed.state.body.startsWith
                  DeepSeekSchemaStreamConversation.Example.dualToolStreamBody) true
              assertEqual "prefix process schema records all three SSE frames"
                completed.observed.state.frames.length 3
              assertEqual "prefix process schema marks the done frame"
                completed.observed.state.done true
              match completed.step with
              | .terminal _ => fail "prefix process schema tool fixture became terminal"
              | .tools toolStep =>
                  assertEqual "prefix process schema executes both registry calls"
                    toolStep.batch.executions.length 2
          | .fuelExhausted _ => fail "prefix process schema exhausted before completion"
          | .cancelled _ _ _ _ => fail "prefix process schema unexpectedly cancelled"
      match ← DeepSeekHarnessProcessSchemaPrefix.Example.dualToolPrefixCancelled
          weatherCertificate clockCertificate with
      | .error error => fail s!"prefix process schema cancellation failed: {reprStr error}"
      | .ok ⟨prepared, round⟩ =>
          assertEqual "prefix process schema cancellation retains stream mode"
            prepared.plan.source.stream true
          match round.outcome with
          | .cancelled _ line reason _ =>
              assertEqual "prefix process schema cancellation reports its line" line 1
              assertEqual "prefix process schema cancellation reports its reason"
                reason "cancelled:prefix"
          | .completed _ => fail "prefix process schema cancellation unexpectedly completed"
          | .fuelExhausted _ => fail "prefix process schema cancellation exhausted"

private def testDeepSeekHarnessProcessSchemaPrefixConversation : IO Unit := do
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ =>
      fail s!"prefix process schema conversation weather certificate failed: {reprStr error}"
  | _, .error error =>
      fail s!"prefix process schema conversation clock certificate failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekHarnessProcessSchemaPrefixConversation.Example.dualToolPrefixConversationProvenanceRun
          weatherCertificate clockCertificate with
      | .error error =>
          fail s!"prefix process schema conversation fixture failed: {reprStr error}"
      | .ok result =>
          assertEqual "prefix process schema conversation records one tool round"
            result.rounds.length 1
          assertEqual "prefix process schema conversation preserves the final model"
            result.finalModel 0
          assertEqual "prefix process schema conversation advances the runner"
            result.runner.session.nextSeq
            (DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3)
          match result.rounds with
          | [⟨_, witness⟩] =>
              assertEqual "prefix process schema conversation retains stream mode per round"
                witness.prepared.plan.source.stream true
              assertEqual "prefix process schema conversation retains the accepted prefix"
                witness.observed.state.frames.length 3
              assertEqual "prefix process schema conversation dispatches both tools"
                witness.step.batch.executions.length 2
          | _ => fail "prefix process schema conversation lost its round witness"
          match result.stop with
          | .fuelExhausted _ _ => pure ()
          | .completed _ _ => fail "prefix process schema conversation unexpectedly completed"
          | .roundFuelExhausted _ _ => fail "prefix process schema conversation round exhausted"
          | .cancelled _ _ _ _ _ => fail "prefix process schema conversation cancelled"
      match ← DeepSeekHarnessProcessSchemaPrefixConversation.Example.dualToolPrefixConversationCancelled
          weatherCertificate clockCertificate with
      | .error error =>
          fail s!"prefix process schema conversation cancellation failed: {reprStr error}"
      | .ok result =>
          assertEqual "prefix process schema conversation cancellation has no tool rounds"
            result.rounds.length 0
          match result.stop with
          | .cancelled prepared observed line reason _ =>
              assertEqual "prefix process schema conversation cancellation keeps stream mode"
                prepared.plan.source.stream true
              assertEqual "prefix process schema conversation cancellation keeps the prefix"
                observed.state.frames.length 1
              assertEqual "prefix process schema conversation cancellation reports its line"
                line 1
              assertEqual "prefix process schema conversation cancellation reports its reason"
                reason "cancelled:prefix"
          | .completed _ _ => fail "prefix process schema conversation cancellation completed"
          | .fuelExhausted _ _ => fail "prefix process schema conversation cancellation exhausted"
          | .roundFuelExhausted _ _ =>
              fail "prefix process schema conversation cancellation exhausted the round"

private def testDeepSeekCurlIncremental : IO Unit := do
  let seen ← IO.mkRef ([] : List (Nat × String))
  let result ← DeepSeekCurlIncremental.executeSseIncremental
    64 (DeepSeekCurlIncremental.fixtureProcess DeepSeekStream.exampleStreamBody)
    DeepSeekCurlTransport.fixtureRequest.request (fun index line => do
      seen.modify (fun lines => (index, line) :: lines))
  match result with
  | .error error => fail s!"incremental DeepSeek SSE fixture failed: {reprStr error}"
  | .ok ⟨body, response⟩ =>
      let callbackLines ← seen.get
      let callbackLines := callbackLines.reverse
      assertEqual "incremental DeepSeek SSE preserves the complete source body"
        body DeepSeekStream.exampleStreamBody
      assertEqual "incremental DeepSeek SSE callback indices are contiguous"
        (callbackLines.map (fun item => item.1))
        (List.range callbackLines.length)
      assertEqual "incremental DeepSeek SSE retains callback lines in the response"
        (callbackLines.map (fun item => item.2)) response.lines
      assertEqual "incremental DeepSeek SSE excludes the private status trailer"
        (response.lines.any (fun line => line.contains DeepSeekCurlTransport.statusMarker)) false
      let _wireCertificate := response.wire
      assertEqual "incremental DeepSeek SSE validates the same frame count"
        response.wire.frames.length 2
  match ← DeepSeekCurlIncremental.executeSseIncremental
      1 (DeepSeekCurlIncremental.fixtureProcess DeepSeekStream.exampleStreamBody)
      DeepSeekCurlTransport.fixtureRequest.request (fun _ _ => pure ()) with
  | .error (.lineLimit reads) =>
      assertEqual "incremental DeepSeek SSE exposes the read budget failure" reads 1
  | .error error => fail s!"unexpected incremental budget error: {reprStr error}"
  | .ok _ => fail "incremental DeepSeek SSE accepted an exhausted read budget"
  match ← DeepSeekCurlIncremental.executeSseIncremental
      64 (DeepSeekCurlIncremental.fixtureProcess DeepSeekStream.exampleStreamBody)
      DeepSeekCurlTransport.fixtureRequest.request (fun index _ => do
        if index == 0 then
          throw (IO.userError "stop callback")
        else
          pure ()) with
  | .error (.callback line _) =>
      assertEqual "incremental DeepSeek SSE preserves callback failure position" line 0
  | .error error => fail s!"unexpected incremental callback error: {reprStr error}"
  | .ok _ => fail "incremental DeepSeek SSE ignored a callback failure"

private def testDeepSeekCurlPrefix : IO Unit := do
  match ← DeepSeekCurlPrefix.fixtureResponse with
  | .error error => fail s!"process-backed prefix fixture failed: {reprStr error}"
  | .ok response =>
      assertEqual "process-backed prefix fixture preserves the raw response body"
        response.rawBody DeepSeekStream.exampleStreamBody
      assertEqual "process-backed prefix fixture preserves the HTTP status"
        response.status (some 200)
      assertEqual "process-backed prefix fixture retains both parsed frames"
        response.state.frames.length 2
      assertEqual "process-backed prefix fixture reaches completion"
        response.isCompleted true
      assertEqual "process-backed prefix fixture records the terminal marker"
        response.state.done true
  let cancelledPolicy := DeepSeekStreamIncremental.LinePolicy.atLine 1 "cancelled:user"
  match ← DeepSeekCurlPrefix.executeSsePrefix cancelledPolicy 64
      DeepSeekCurlPrefix.fixtureProcess DeepSeekCurlTransport.fixtureRequest.request with
  | .error error => fail s!"process-backed prefix cancellation failed: {reprStr error}"
  | .ok response =>
      assertEqual "process-backed prefix cancellation reports cancellation"
        response.isCancelled true
      assertEqual "process-backed prefix cancellation has no terminal status"
        response.status none
      assertEqual "process-backed prefix cancellation stops before the next body line"
        response.state.frames.length 1
      match DeepSeekStreamIncremental.finish response.state with
      | .error .missingDone => pure ()
      | .error error => fail s!"process-backed prefix cancellation had wrong error: {reprStr error}"
      | .ok _ => fail "process-backed prefix cancellation fabricated a complete stream"
  match ← DeepSeekCurlPrefix.executeSsePrefix (DeepSeekStreamIncremental.LinePolicy.never) 1
      DeepSeekCurlPrefix.fixtureProcess DeepSeekCurlTransport.fixtureRequest.request with
  | .error error => fail s!"process-backed prefix fuel fixture failed: {reprStr error}"
  | .ok response =>
      assertEqual "process-backed prefix fuel exhaustion is distinct"
        response.isFuelExhausted true
      assertEqual "process-backed prefix fuel exhaustion retains the first frame"
        response.state.frames.length 1
  let malformedConfig : DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #["-c", "printf 'event: bad\\n\\n__CORDIS_HTTP_STATUS__200\\n'"]
  }
  match ← DeepSeekCurlPrefix.executeSsePrefix (DeepSeekStreamIncremental.LinePolicy.never) 16
      malformedConfig DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.stream (.unexpectedLine _ "event: bad")) => pure ()
  | .error error => fail s!"malformed process-backed prefix returned {reprStr error}"
  | .ok _ => fail "malformed process-backed prefix was accepted"

private def testDeepSeekCurlPrefixSession : IO Unit := do
  match ← DeepSeekCurlPrefixSession.fixtureTextResponse with
  | .error error => fail s!"process-backed prefix session fixture failed: {reprStr error}"
  | .ok processed =>
      assertEqual "process-backed prefix session retains raw text body"
        processed.observed.rawBody DeepSeekRichStream.exampleTextStreamBody
      assertEqual "process-backed prefix session retains terminal status"
        processed.observed.status (some 200)
      assertEqual "process-backed prefix session retains normalized wire frames"
        processed.wire.frames.length 3
      assertEqual "process-backed prefix session extracts terminal text"
        processed.finished.finished.view.content "Hello world"
      let _wireCertificate := processed.wire.parsed
      let _finishCertificate := processed.finished.finished.terminal_state
  match ← DeepSeekCurlPrefixSession.fixtureTextAppend with
  | .error error => fail s!"process-backed prefix session append failed: {reprStr error}"
  | .ok (processed, runner) =>
      assertEqual "process-backed prefix session append advances the sequence"
        runner.session.nextSeq 1
      assertEqual "process-backed prefix session append stores the assistant"
        runner.session.messages [.assistant "Hello world" []]
      let _nextSeq := DeepSeekCurlPrefixSession.appendProcessed_nextSeq
        runner processed [] (by simp) (by simp)
      let _nextCall := DeepSeekCurlPrefixSession.appendProcessed_nextCall
        runner processed [] (by simp) (by simp)
  let cancelledPolicy := DeepSeekStreamIncremental.LinePolicy.atLine 1 "cancelled:user"
  match ← DeepSeekCurlPrefixSession.executeText cancelledPolicy 64
      DeepSeekCurlPrefixSession.fixtureTextProcess
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.cancelled 1 "cancelled:user") => pure ()
  | .error error => fail s!"prefix session cancellation returned {reprStr error}"
  | .ok _ => fail "prefix session cancellation fabricated a semantic response"
  match ← DeepSeekCurlPrefixSession.executeText (DeepSeekStreamIncremental.LinePolicy.never) 1
      DeepSeekCurlPrefixSession.fixtureTextProcess
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error .fuelExhausted => pure ()
  | .error error => fail s!"prefix session fuel stop returned {reprStr error}"
  | .ok _ => fail "prefix session fuel stop fabricated a semantic response"

private def testDeepSeekAsyncHarness : IO Unit := do
  let race ← DeepSeekAsyncHarness.exampleRace
  assertEqual "async DeepSeek fixture race reports success"
    race.successful true
  assertEqual "async DeepSeek fixture race reaches a terminal phase"
    race.phase.isTerminal true
  match race.winner with
  | some 0 | some 1 => pure ()
  | winner => fail s!"async DeepSeek fixture race returned invalid winner {reprStr winner}"
  match race.result with
  | some (.ok processed) =>
      assertEqual "async DeepSeek fixture race retains terminal status"
        processed.observed.status (some 200)
  | some (.error error) =>
      fail s!"async DeepSeek fixture race returned typed error {reprStr error}"
  | none => fail "async DeepSeek fixture race returned no winning result"

private def testDeepSeekAsyncStreamHarness : IO Unit := do
  let race ← DeepSeekAsyncStreamHarness.exampleRace
  assertEqual "async streamed DeepSeek race reports success"
    race.successful true
  assertEqual "async streamed DeepSeek race reaches a terminal phase"
    race.phase.isTerminal true
  match race with
  | .left (.ok result) | .right (.ok result) =>
      assertEqual "async streamed DeepSeek race retains both tool/text rounds"
        result.rounds.length 2
      assertEqual "async streamed DeepSeek race retains the final model"
        result.finalModel 0
      assertEqual "async streamed DeepSeek race retains the full local sequence"
        result.runner.session.nextSeq 5
  | .left (.error error) | .right (.error error) =>
      fail s!"async streamed DeepSeek race returned typed error {reprStr error}"
  | .waiting => fail "async streamed DeepSeek race returned no winning result"

private def testDeepSeekAsyncStreamCancellation : IO Unit := do
  let race ← DeepSeekAsyncStreamCancellation.exampleCancellationRace
  assertEqual "async streamed cancellation race returns an accepted result"
    race.successful true
  assertEqual "async streamed cancellation race reports cancellation"
    race.cancelled true
  assertEqual "async streamed cancellation race reaches a terminal phase"
    race.phase.isTerminal true
  match race with
  | .left result | .right result =>
      match result.result with
      | .ok run =>
          assertEqual "async streamed cancellation retains no dispatched rounds"
            run.rounds.length 0
          assertEqual "async streamed cancellation retains the unchanged model"
            run.finalModel 0
          assertEqual "async streamed cancellation retains the cancellation runner"
            run.runner.turn 99
      | .error error =>
          fail s!"async streamed cancellation returned typed error {reprStr error}"
  | .waiting => fail "async streamed cancellation returned no winning result"

private def testDeepSeekStream : IO Unit := do
  match DeepSeekStream.validateSse DeepSeekStream.exampleStreamBody with
  | .error error => fail s!"DeepSeek SSE fixture failed: {reprStr error}"
  | .ok validated =>
      assertEqual "DeepSeek SSE fixture has one data frame and a terminal marker"
        validated.frames.length 2
      match validated.frames with
      | [.data frame, .done] =>
          assertEqual "DeepSeek SSE frame id" frame.chunk.id "chatcmpl-stream-example"
          assertEqual "DeepSeek SSE frame model" frame.chunk.model "deepseek-reasoner"
          match frame.chunk.choices with
          | [choice] =>
              assertEqual "DeepSeek SSE delta role" choice.delta.role (some "assistant")
              assertEqual "DeepSeek SSE delta content" choice.delta.content (some "Hello")
              assertEqual "DeepSeek SSE delta is not terminal" choice.finishReason none
          | _ => fail "DeepSeek SSE fixture did not decode exactly one choice"
          let _parseCertificate := validated.parsed
          let _frameParseCertificate := frame.parsed
          let _frameDecodeCertificate := frame.decoded
          pure ()
      | _ => fail "DeepSeek SSE fixture did not retain the expected frame sequence"
  match DeepSeekStream.validateSse "data: [DONE]\n\ndata: {}\n\n" with
  | .error (.dataAfterDone _) => pure ()
  | _ => fail "data after DeepSeek SSE [DONE] was accepted"
  let missingDoneBody :=
    "data: " ++ Lean.Json.compress DeepSeekStream.exampleChunkJson ++ "\n\n"
  match DeepSeekStream.validateSse missingDoneBody with
  | .error .missingDone => pure ()
  | _ => fail "DeepSeek SSE body without [DONE] was accepted"
  match DeepSeekStream.validateSse "event: message\n\ndata: [DONE]\n\n" with
  | .error (.unexpectedLine _ "event: message") => pure ()
  | _ => fail "unsupported DeepSeek SSE field was accepted"
  match DeepSeekStream.validateSseBytes (ByteArray.mk #[255]) with
  | .error .invalidUtf8 => pure ()
  | _ => fail "invalid UTF-8 DeepSeek SSE input was accepted"

private def testDeepSeekStreamFailure : IO Unit := do
  match DeepSeekStreamFailure.exampleContentFilter with
  | .error error => fail s!"DeepSeek content-filter fixture failed: {reprStr error}"
  | .ok validated =>
      assertEqual "DeepSeek content-filter failure preserves the prefix frame count"
        validated.view.leading.length 1
      assertEqual "DeepSeek content-filter failure preserves its reason"
        validated.view.reason .contentFilter
      assertEqual "DeepSeek content-filter failure preserves terminal choice index"
        validated.view.info.choice.index 0
      assertEqual "DeepSeek content-filter failure preserves terminal raw content"
        validated.view.info.choice.delta.content (some "partial")
      assertEqual "DeepSeek content-filter failure retains the done frame"
        validated.wire.frames.length 3
      let _projectionCertificate := validated.projection
      let _reasonCertificate := DeepSeekStreamFailure.validateFailureStream_reason validated
      let _choiceCertificate :=
        DeepSeekStreamFailure.validateFailureStream_terminal_choice validated
  match DeepSeekStreamFailure.exampleInsufficientResource with
  | .error error => fail s!"DeepSeek resource-failure fixture failed: {reprStr error}"
  | .ok validated =>
      assertEqual "DeepSeek resource failure preserves its reason"
        validated.view.reason .insufficientSystemResource
      assertEqual "DeepSeek resource failure preserves optional terminal usage"
        validated.view.usage none
  match DeepSeekStreamFailure.validateFailureStream DeepSeekRichStream.exampleTextStreamBody with
  | .error (.inr (.unsupportedFinish .stop)) => pure ()
  | .error error => fail s!"ordinary DeepSeek finish returned {reprStr error}"
  | .ok _ => fail "ordinary DeepSeek stop was accepted as a provider failure"

private def testDeepSeekTerminalOutcome : IO Unit := do
  match Cordis.DeepSeekTerminalOutcome.exampleFailure with
  | .error error => fail s!"terminal failure outcome rejected: {reprStr error}"
  | .ok (.failure validated) =>
      assertEqual "terminal outcome classifies content-filter as provider failure"
        validated.view.reason .contentFilter
      assertEqual "terminal outcome preserves failure wire frames"
        validated.wire.frames.length 3
      assertEqual "terminal outcome failure kind"
        (Cordis.DeepSeekTerminalOutcome.TerminalOutcome.kind (.failure validated))
        .providerFailure
  | .ok _ => fail "terminal failure outcome was classified as a success language"
  match Cordis.DeepSeekTerminalOutcome.exampleText with
  | .error error => fail s!"terminal text outcome rejected: {reprStr error}"
  | .ok (.text validated) =>
      assertEqual "terminal outcome classifies text as text"
        (Cordis.DeepSeekTerminalOutcome.TerminalOutcome.kind (.text validated)) .text
      assertEqual "terminal outcome retains text rich trace"
        validated.raw.length 6
  | .ok _ => fail "terminal text outcome was classified as another language"
  match Cordis.DeepSeekTerminalOutcome.exampleTool with
  | .error error => fail s!"terminal tool outcome rejected: {reprStr error}"
  | .ok (.tool validated) =>
      assertEqual "terminal outcome classifies tool calls as tool"
        (Cordis.DeepSeekTerminalOutcome.TerminalOutcome.kind (.tool validated)) .tool
      assertEqual "terminal outcome retains tool rich trace"
        validated.raw.length 6
  | .ok _ => fail "terminal tool outcome was classified as another language"
  match Cordis.DeepSeekTerminalOutcome.exampleMixed with
  | .error error => fail s!"terminal mixed outcome rejected: {reprStr error}"
  | .ok (.mixed validated) =>
      assertEqual "terminal outcome classifies mixed blocks as mixed"
        (Cordis.DeepSeekTerminalOutcome.TerminalOutcome.kind (.mixed validated)) .mixed
      assertEqual "terminal outcome retains mixed rich trace"
        validated.raw.length 14
  | .ok _ => fail "terminal mixed outcome was classified as another language"
  match Cordis.DeepSeekTerminalOutcome.exampleMulti with
  | .error error => fail s!"terminal multi outcome rejected: {reprStr error}"
  | .ok (.multi validated) =>
      assertEqual "terminal outcome classifies multiple calls as multi"
        (Cordis.DeepSeekTerminalOutcome.TerminalOutcome.kind (.multi validated)) .multi
      assertEqual "terminal outcome retains multi wire frame count"
        validated.wire.frames.length 4
  | .ok _ => fail "terminal multi outcome was classified as another language"
  let malformedBody := "event: message\n\ndata: [DONE]\n\n"
  match Cordis.DeepSeekTerminalOutcome.validateTerminalOutcome malformedBody with
  | .error (.wire (.unexpectedLine 0 "event: message")) => pure ()
  | .error error => fail s!"terminal malformed wire returned {reprStr error}"
  | .ok _ => fail "terminal malformed wire was accepted"

private def testDeepSeekStreamIncremental : IO Unit := do
  match DeepSeekStreamIncremental.consumeBody
      (DeepSeekStreamIncremental.LinePolicy.never) 32 DeepSeekStream.exampleStreamBody with
  | .error error => fail s!"incremental prefix fixture failed: {reprStr error}"
  | .ok result =>
      assertEqual "incremental prefix fixture reaches the terminal marker"
        result.state.done true
      assertEqual "incremental prefix fixture retains the complete frame sequence"
        result.state.frames.length 2
      assertEqual "incremental prefix fixture reports completion"
        (DeepSeekStreamIncremental.StreamStop.isCompleted result.stop) true
  let lines := DeepSeekStream.exampleStreamBody.splitOn "\n"
  match DeepSeekStreamIncremental.consumeLines
      (DeepSeekStreamIncremental.LinePolicy.atLine 1 "cancelled:user") 32 lines with
  | .error error => fail s!"incremental cancellation fixture failed: {reprStr error}"
  | .ok result =>
      assertEqual "incremental line cancellation reports cancellation"
        (DeepSeekStreamIncremental.StreamStop.isCancelled result.stop) true
      assertEqual "incremental line cancellation stops before the second line"
        (DeepSeekStreamIncremental.StreamStop.cancelledLine result.stop) (some 1)
      assertEqual "incremental line cancellation retains only the first data frame"
        result.state.frames.length 1
      match DeepSeekStreamIncremental.finish result.state with
      | .error .missingDone => pure ()
      | .error error => fail s!"incremental cancellation finished with wrong error: {reprStr error}"
      | .ok _ => fail "incremental cancellation fabricated a complete stream"
  match DeepSeekStreamIncremental.consumeLines
      (DeepSeekStreamIncremental.LinePolicy.never) 4 ["event: message"] with
  | .error (.unexpectedLine 0 "event: message") => pure ()
  | .error error => fail s!"incremental malformed line had wrong error: {reprStr error}"
  | .ok _ => fail "incremental malformed line was accepted"
  match DeepSeekStreamIncremental.consumeBody
      (DeepSeekStreamIncremental.LinePolicy.never) 1 DeepSeekStream.exampleStreamBody with
  | .error error => fail s!"incremental fuel fixture failed: {reprStr error}"
  | .ok result =>
      assertEqual "incremental fuel exhaustion reports the distinct stop"
        (DeepSeekStreamIncremental.StreamStop.isFuelExhausted result.stop) true
      assertEqual "incremental fuel exhaustion retains the parsed prefix"
        result.state.frames.length 1

private def testDeepSeekStreamByteFraming : IO Unit := do
  assertEqual "byte-framing ASCII fixture succeeds"
    DeepSeekStreamByteFraming.exampleRuntime true
  assertEqual "byte-framing UTF-8 boundary fixture succeeds"
    DeepSeekStreamByteFraming.unicodeRuntime true
  match DeepSeekStreamByteFraming.validateChunks [ByteArray.mk #[255, 10]] with
  | .error (.invalidUtf8 0 bytes) =>
      assertEqual "byte-framing invalid UTF-8 retains the offending line bytes"
        bytes.size 1
  | .error _ => fail "byte-framing invalid UTF-8 returned the wrong typed error"
  | .ok _ => fail "byte-framing invalid UTF-8 was accepted"
  match DeepSeekStreamByteFraming.validateChunks [
      DeepSeekStreamByteFraming.exampleBytes.extract 0 1] with
  | .error (.incomplete bytes) =>
      assertEqual "byte-framing incomplete final line retains pending bytes"
        bytes.size 1
  | .error _ => fail "byte-framing incomplete input returned the wrong typed error"
  | .ok _ => fail "byte-framing incomplete input was accepted"
  match DeepSeekStreamByteFraming.validateChunks DeepSeekStreamByteFraming.exampleChunks with
  | .error _ => fail "byte-framing bridge rejected the valid chunked fixture"
  | .ok result =>
      assertEqual "byte-framing bridge retains both SSE frames"
        result.stream.frames.length 2
      let _sourceCertificate := result.state.framed
      let _decodedCertificate := result.decoded
      let _bodyCertificate := result.body_eq
      let _validatorCertificate :=
        DeepSeekStreamByteFraming.ValidatedByteStream.validateSseBytes_exact result

private def testDeepSeekCurlByteFraming : IO Unit := do
  match ← DeepSeekCurlByteFraming.fixtureResponse with
  | .error _ => fail "process byte-framing ASCII fixture failed"
  | .ok ⟨body, response⟩ =>
      assertEqual "process byte-framing status is retained" response.status 200
      assertEqual "process byte-framing reads multiple chunks"
        (decide (response.chunks.length > 1)) true
      assertEqual "process byte-framing body agrees with parser"
        response.framed.text body
      let _rawCertificate := response.rawDecoded
      let _parsedCertificate := response.parsed
      let _rawChunksCertificate := response.raw_chunks_eq
      let _bodyCertificate := response.body_chunks_eq
      let _framedCertificate := response.framed_text_eq
      let _validatorCertificate :=
        DeepSeekCurlByteFraming.ByteChunkResponse.validateSseBytes_exact response
  match ← DeepSeekCurlByteFraming.unicodeFixtureResponse with
  | .error _ => fail "process byte-framing UTF-8 fixture failed"
  | .ok ⟨_, response⟩ =>
      assertEqual "process byte-framing preserves split UTF-8 text"
        (response.framed.text.contains "hé") true
  match ← DeepSeekCurlByteFraming.executeSseBytes 8 0
      (DeepSeekCurlByteFraming.fixtureProcess DeepSeekStream.exampleStreamBody)
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error .chunkSize => pure ()
  | .error _ => fail "process byte-framing zero chunk size returned wrong error"
  | .ok _ => fail "process byte-framing accepted zero chunk size"
  match ← DeepSeekCurlByteFraming.executeSseBytes 1 3
      (DeepSeekCurlByteFraming.fixtureProcess DeepSeekStream.exampleStreamBody)
      DeepSeekCurlTransport.fixtureRequest.request with
  | .error (.readLimit 1) => pure ()
  | .error _ => fail "process byte-framing read budget returned wrong error"
  | .ok _ => fail "process byte-framing ignored the read budget"

private def testDeepSeekCurlBytePrefix : IO Unit := do
  match ← DeepSeekCurlBytePrefix.fixtureResponse with
  | .error _ => fail "process byte-prefix fixture failed"
  | .ok response =>
      assertEqual "process byte-prefix completes the typed stream"
        (DeepSeekCurlBytePrefix.BytePrefixResponse.isCompleted response) true
      assertEqual "process byte-prefix retains many one-byte reads"
        (decide (response.rawChunks.length > 1)) true
      assertEqual "process byte-prefix has no pending bytes at completion"
        response.pendingRaw []
      assertEqual "process byte-prefix typed body is exact"
        response.state.typed.body DeepSeekStream.exampleStreamBody
      assertEqual "process byte-prefix source is exact UTF-8"
        (decide (DeepSeekStreamByteFraming.bytesOfList response.state.source =
          DeepSeekStream.exampleStreamBody.toUTF8)) true
      let _rawCertificate := response.raw_chunks_eq
      match response.stop with
      | .completed stream =>
          assertEqual "process byte-prefix completion retains both SSE frames"
            stream.stream.frames.length 2
          let _sourceCertificate := stream.decoded
          let _bodyCertificate := stream.body_eq
      | .fuelExhausted => fail "process byte-prefix fixture exhausted"
      | .cancelled _ _ _ => fail "process byte-prefix fixture cancelled"
  match ← DeepSeekCurlBytePrefix.cancellationResponse with
  | .error _ => fail "process byte-prefix cancellation fixture failed"
  | .ok response =>
      assertEqual "process byte-prefix cancellation is typed"
        (DeepSeekCurlBytePrefix.BytePrefixResponse.isCancelled response) true
      assertEqual "process byte-prefix cancellation stops at line one"
        response.state.typed.line 1
      match response.stop with
      | .cancelled line reason _ =>
          assertEqual "process byte-prefix cancellation retains line" line 1
          assertEqual "process byte-prefix cancellation retains reason"
            reason "cancelled:byte-prefix"
      | .completed _ => fail "process byte-prefix cancellation completed"
      | .fuelExhausted => fail "process byte-prefix cancellation exhausted"

private def testDeepSeekRichStream : IO Unit := do
  match DeepSeekRichStream.validateTextStream DeepSeekRichStream.exampleTextStreamBody with
  | .error error => fail s!"DeepSeek rich-stream projection failed: {reprStr error}"
  | .ok validated =>
      assertEqual "DeepSeek text projection emits the expected local raw trace length"
        validated.raw.length 6
      match validated.rich.finish with
      | .terminal blocks usage .stop none =>
          assertEqual "DeepSeek text projection assembles one exact text block"
            blocks [.text "Hello world"]
          assertEqual "DeepSeek text projection retains input usage"
            usage.inputTokens 3
          assertEqual "DeepSeek text projection retains output usage"
            usage.outputTokens 2
      | _ => fail "DeepSeek text projection did not reach the expected terminal state"
      let _wireCertificate := validated.wire.parsed
      let _projectionCertificate := validated.projection
      let _richCertificate := validated.rich.erase_eq
      pure ()
  let unsupportedToolJson : Lean.Json := .mkObj [
    ("id", .str "tool-stream-example"),
    ("model", .str "deepseek-reasoner"),
    ("choices", .arr #[.mkObj [
      ("index", .num (Lean.JsonNumber.fromNat 0)),
      ("delta", .mkObj [("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("type", .str "function"),
        ("function", .mkObj [
          ("name", .str "lookup"),
          ("arguments", .str "{\\\"q\\\":")
        ])
      ]])]),
      ("finish_reason", .null)
    ]])
  ]
  let unsupportedToolBody :=
    "data: " ++ Lean.Json.compress unsupportedToolJson ++ "\n\ndata: [DONE]\n\n"
  match DeepSeekRichStream.validateTextStream unsupportedToolBody with
  | .error (.projection .toolCallsUnsupported) => pure ()
  | _ => fail "DeepSeek rich-stream projection accepted unsupported tool-call deltas"
  let incompleteBody :=
    "data: " ++ Lean.Json.compress DeepSeekStream.exampleChunkJson ++ "\n\ndata: [DONE]\n\n"
  match DeepSeekRichStream.validateTextStream incompleteBody with
  | .error (.projection .missingFinish) => pure ()
  | _ => fail "DeepSeek rich-stream projection accepted a stream without finish"

private def testDeepSeekRichToolStream : IO Unit := do
  match DeepSeekRichToolStream.validateToolStream
      DeepSeekRichToolStream.exampleToolStreamBody with
  | .error error => fail s!"DeepSeek rich-tool projection failed: {reprStr error}"
  | .ok validated =>
      assertEqual "DeepSeek rich-tool projection emits the expected local raw trace length"
        validated.raw.length 6
      match validated.rich.finish with
      | .terminal blocks usage .toolCalls none =>
          assertEqual "DeepSeek rich-tool projection assembles one exact tool block"
            blocks [.toolCall "call-a" "lookup" "{\\\"q\\\":lean\\\"}"]
          assertEqual "DeepSeek rich-tool projection retains input usage"
            usage.inputTokens 4
          assertEqual "DeepSeek rich-tool projection retains output usage"
            usage.outputTokens 3
      | _ => fail "DeepSeek rich-tool projection did not reach the expected terminal state"
      let _wireCertificate := validated.wire.parsed
      let _projectionCertificate := validated.projection
      let _richCertificate := validated.rich.erase_eq
      pure ()
  let multipleToolJson : Lean.Json := .mkObj [
    ("id", .str "tool-stream-example"),
    ("model", .str "deepseek-reasoner"),
    ("choices", .arr #[.mkObj [
      ("index", .num (Lean.JsonNumber.fromNat 0)),
      ("delta", .mkObj [("tool_calls", .arr #[
        .mkObj [("index", .num (Lean.JsonNumber.fromNat 0)),
          ("id", .str "a")],
        .mkObj [("index", .num (Lean.JsonNumber.fromNat 1)),
          ("id", .str "b")]
      ])]),
      ("finish_reason", .null)
    ]])
  ]
  let multipleToolBody :=
    "data: " ++ Lean.Json.compress multipleToolJson ++ "\n\ndata: [DONE]\n\n"
  match DeepSeekRichToolStream.validateToolStream multipleToolBody with
  | .error (.projection (.multipleToolCalls 2)) => pure ()
  | _ => fail "DeepSeek rich-tool projection accepted multiple tool calls"
  let missingIdJson : Lean.Json := .mkObj [
    ("id", .str "tool-stream-example"),
    ("model", .str "deepseek-reasoner"),
    ("choices", .arr #[.mkObj [
      ("index", .num (Lean.JsonNumber.fromNat 0)),
      ("delta", .mkObj [("tool_calls", .arr #[.mkObj [
        ("index", .num (Lean.JsonNumber.fromNat 0)),
        ("function", .mkObj [("name", .str "lookup")])
      ]])]),
      ("finish_reason", .null)
    ]])
  ]
  let missingIdBody :=
    "data: " ++ Lean.Json.compress missingIdJson ++ "\n\ndata: [DONE]\n\n"
  match DeepSeekRichToolStream.validateToolStream missingIdBody with
  | .error (.projection .missingToolId) => pure ()
  | _ => fail "DeepSeek rich-tool projection accepted a tool delta without an id"

private def testDeepSeekRichMixedStream : IO Unit := do
  match DeepSeekRichMixedStream.validateMixedStream
      DeepSeekRichMixedStream.mixedStreamBody with
  | .error error => fail s!"DeepSeek mixed rich-stream projection failed: {reprStr error}"
  | .ok validated =>
      assertEqual "DeepSeek mixed projection emits the expected local raw trace length"
        validated.raw.length 14
      match validated.rich.finish with
      | .terminal blocks usage .toolCalls none =>
          assertEqual "DeepSeek mixed projection assembles text, reasoning, and one tool block"
            blocks DeepSeekRichMixedStream.mixedBlocks
          assertEqual "DeepSeek mixed projection retains input usage"
            usage.inputTokens 4
          assertEqual "DeepSeek mixed projection retains output usage"
            usage.outputTokens 8
      | _ => fail "DeepSeek mixed projection did not reach the expected terminal state"
      let _wireCertificate := validated.wire.parsed
      let _projectionCertificate := validated.projection
      let _richCertificate := validated.rich.erase_eq
      pure ()
  match DeepSeekRichMixedStream.projectionErrorSummary
      DeepSeekRichMixedStream.mixedKindsBody with
  | some .mixedKinds => pure ()
  | result => fail s!"DeepSeek mixed projection accepted same-frame mixed kinds: {reprStr result}"

private def testDeepSeekRichMultiStream : IO Unit := do
  assertEqual "DeepSeek multi projection preserves interleaved raw chunks"
    (DeepSeekRichMultiStream.chunkRawSummary DeepSeekRichMultiStream.multiChunks)
    (some DeepSeekRichMultiStream.multiRaw)
  match DeepSeekRichMultiStream.jsonSummary DeepSeekRichMultiStream.multiBody with
  | some frameCount =>
      assertEqual "DeepSeek multi JSON fixture retains three data frames plus DONE"
        frameCount 4
  | none => fail "DeepSeek multi JSON fixture was rejected"
  let existingCall : DeepSeekRichMultiStream.MultiState := {
    DeepSeekRichMultiStream.MultiState.initial with
    tools := [{ providerIndex := 9, localIndex := 0, id := some "call-b", name := some "sum" }]
  }
  match DeepSeekRichMultiStream.projectChunks existingCall
      [DeepSeekRichMultiStream.mismatchedCallChunk] with
  | .error (.toolIdMismatch 9 "call-b" "other") => pure ()
  | result => fail s!"DeepSeek multi projection missed per-call ID mismatch: {reprStr result}"
  match DeepSeekRichMultiStream.projectChunks DeepSeekRichMultiStream.MultiState.initial
      [DeepSeekRichMultiStream.multiChoiceChunk] with
  | .error (.multipleChoices 2) => pure ()
  | result => fail s!"DeepSeek multi projection accepted multiple choices: {reprStr result}"

private def testDeepSeekSessionBridge : IO Unit := do
  match DeepSeekRichToolStream.validateToolStream
      DeepSeekRichToolStream.exampleToolStreamBody with
  | .error error => fail s!"DeepSeek session bridge source failed: {reprStr error}"
  | .ok validated =>
      match DeepSeekSessionBridge.finishAssistant validated.rich with
      | .error error => fail s!"DeepSeek session bridge terminal extraction failed: {reprStr error}"
      | .ok finished =>
          let assignment : StreamSession.CallIdAssignment finished.view := {
            ids := (List.range finished.view.rawToolCalls.length).map (fun value => {
              value
            })
            length_eq := by simp
            nodup := by
              apply List.nodup_iff_pairwise_ne.mpr
              exact List.Pairwise.map (R := fun left right : Nat => left ≠ right)
                (S := fun left right : CallId => left ≠ right)
                (fun value => { value := value })
                (by
                  intro left right different equal
                  exact different (by cases equal; rfl))
                (List.nodup_iff_pairwise_ne.mp (List.nodup_range))
          }
          let session := DeepSeekSessionBridge.appendFinishedAssistant
            (Session.Session.empty Session.noExtensions) 2 1 finished assignment []
            (by simp) (by simp)
          assertEqual "DeepSeek session bridge assigns a local numeric tool call ID"
            session.messages [
              .assistant "" [{
                id := { value := 0 }
                name := "lookup"
                arguments := "{\\\"q\\\":lean\\\"}"
              }]
            ]
          let _terminalCertificate := finished.terminal_state
          let _messageCertificate := DeepSeekSessionBridge.appendFinishedAssistant_messages
            (Session.Session.empty Session.noExtensions) 2 1 finished assignment []
            (by simp) (by simp)
          pure ()

private def testDeepSeekSessionRunner : IO Unit := do
  match DeepSeekSessionRunner.Runner.appendText
      (DeepSeekSessionRunner.Runner.empty 1)
      DeepSeekRichStream.exampleTextStreamBody [] (by simp) (by simp) with
  | .error error => fail s!"DeepSeek session runner text append failed: {reprStr error}"
  | .ok afterText =>
      assertEqual "DeepSeek session runner advances after a terminal text response"
        afterText.session.nextSeq 1
      assertEqual "DeepSeek session runner keeps the tool-call count at zero for text"
        afterText.nextCall 0
      match DeepSeekSessionRunner.Runner.appendTool afterText
          DeepSeekRichToolStream.exampleToolStreamBody [] (by simp) (by simp) with
      | .error error => fail s!"DeepSeek session runner tool append failed: {reprStr error}"
      | .ok final =>
          assertEqual "DeepSeek session runner advances a second terminal response"
            final.session.nextSeq 2
          assertEqual "DeepSeek session runner allocates the next local tool ID"
            final.nextCall 1
          assertEqual "DeepSeek session runner preserves model message order"
            final.session.messages [
            .assistant "Hello world" [],
            .assistant "" [{
              id := { value := 0 }
              name := "lookup"
              arguments := "{\\\"q\\\":lean\\\"}"
            }]
          ]
          let _countCertificate := final.toolCallCount_eq_nextCall
          match DeepSeekSessionRunner.Runner.appendMixed final
              DeepSeekRichMixedStream.mixedStreamBody [] (by simp) (by simp) with
          | .error error => fail s!"DeepSeek session runner mixed append failed: {reprStr error}"
          | .ok mixedFinal =>
              assertEqual "DeepSeek session runner advances a mixed terminal response"
                mixedFinal.session.nextSeq 3
              assertEqual "DeepSeek session runner counts the mixed response tool call"
                mixedFinal.nextCall 2
              assertEqual "DeepSeek session runner projects mixed visible text and tool order"
                mixedFinal.session.messages [
                .assistant "Hello world" [],
                .assistant "" [{
                  id := { value := 0 }
                  name := "lookup"
                  arguments := "{\\\"q\\\":lean\\\"}"
                }],
                .assistant "Hello world" [{
                  id := { value := 1 }
                  name := "lookup"
                  arguments := "{\"q\":\"lean\"}"
                }]
              ]
              match DeepSeekSessionRunner.Runner.appendMulti mixedFinal
                  DeepSeekRichMultiStream.multiBody [] (by simp) (by simp) with
              | .error error =>
                  fail s!"DeepSeek session runner multi append failed: {reprStr error}"
              | .ok multiFinal =>
                  assertEqual "DeepSeek session runner advances a multi-call response"
                    multiFinal.session.nextSeq 4
                  assertEqual "DeepSeek session runner counts both multi-call tools"
                    multiFinal.nextCall 4
                  assertEqual "DeepSeek session runner preserves multi-call order"
                    multiFinal.session.messages.getLast? (some (.assistant "" [
                      { id := { value := 2 }, name := "lookup",
                        arguments := "{\"q\":\"lean\"}" },
                      { id := { value := 3 }, name := "sum",
                        arguments := "{\"xs\":[1,2]}" }
                    ]))
                  pure ()

private def testDeepSeekApiSession : IO Unit := do
  match DeepSeekApiSession.acceptResponse "" with
  | .error (.response (.invalidJson _)) => pure ()
  | .error error => fail s!"DeepSeek API session returned the wrong rejection: {reprStr error}"
  | .ok _ => fail "DeepSeek API session accepted an empty response body"
  match DeepSeekApiSession.acceptResponse DeepSeekApi.exampleResponseBody with
  | .error error => fail s!"DeepSeek API session acceptance failed: {reprStr error}"
  | .ok accepted =>
      assertEqual "DeepSeek API session accepts the singleton indexed choice"
        accepted.validated.response.choices.head.index 0
      assertEqual "DeepSeek API session retains the provider tool call"
        accepted.validated.response.choices.head.message.toolCalls.length 1
      let final := DeepSeekApiSession.Runner.appendApi
        (DeepSeekSessionRunner.Runner.empty 2) accepted [] (by simp) (by simp)
      assertEqual "DeepSeek API session append advances the local sequence"
        final.session.nextSeq 1
      assertEqual "DeepSeek API session append allocates one local call ID"
        final.nextCall 1
      assertEqual "DeepSeek API session append projects the decoded assistant payload"
        final.session.messages [
          .assistant "I will check that." [{
            id := { value := 0 }
            name := "get_weather"
            arguments := "{\"city\":\"San Francisco\"}"
          }]
        ]
      let _messageCertificate := DeepSeekApiSession.Runner.appendApi_session_messages
        (DeepSeekSessionRunner.Runner.empty 2) accepted [] (by simp) (by simp)
      let _sequenceCertificate := DeepSeekApiSession.Runner.appendApi_nextSeq
        (DeepSeekSessionRunner.Runner.empty 2) accepted [] (by simp) (by simp)
      pure ()

private def testDeepSeekHarness : IO Unit := do
  match DeepSeekHarness.buildChatRequest { model := "empty-test" }
      (Session.Session.empty Session.noExtensions) with
  | .error .emptyMessages => pure ()
  | .error error =>
      fail s!"DeepSeek harness returned the wrong empty-request error: {reprStr error}"
  | .ok _ => fail "DeepSeek harness built a request without messages or a system prompt"
  match DeepSeekHarness.buildChatRequest DeepSeekHarness.counterRequestSource
      DeepSeekHarness.counterSession with
  | .error error => fail s!"DeepSeek harness request construction failed: {reprStr error}"
  | .ok request =>
      assertEqual "DeepSeek harness request keeps the configured model"
        request.model "deterministic-counter"
      assertEqual "DeepSeek harness request prepends its explicit system message"
        request.messages.head (.system "Use the supplied proof-carrying counter tool.")
  match DeepSeekHarness.buildTypedCompleteRequestPlan "https://fixture.invalid"
      { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      DeepSeekHarness.counterSession with
  | .error error => fail s!"DeepSeek typed complete request construction failed: {reprStr error}"
  | .ok plan =>
      assertEqual "DeepSeek typed complete request disables the provider stream flag"
        plan.source.stream false
      let _bodyCertificate := plan.body_eq
      let _modeCertificate := plan.complete_source_stream
  match DeepSeekHarness.buildTypedStreamingRequestPlan "https://fixture.invalid"
      { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      DeepSeekHarness.counterSession with
  | .error error => fail s!"DeepSeek typed streaming request construction failed: {reprStr error}"
  | .ok plan =>
      assertEqual "DeepSeek typed streaming request enables the provider stream flag"
        plan.source.stream true
      let _bodyCertificate := plan.body_eq
      let _modeCertificate := plan.streaming_source_stream
  match DeepSeekHarness.buildStreamingRequestPlan "https://fixture.invalid"
      { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      DeepSeekHarness.counterSession with
  | .error error => fail s!"DeepSeek streaming request construction failed: {reprStr error}"
  | .ok plan =>
      assertEqual "DeepSeek streaming request enables the provider stream flag"
        plan.source.stream true
      let _bodyCertificate := plan.body_eq
  match DeepSeekHarness.sessionMessageToChatMessage
      (.toolResult { value := 7 } "failed" true) with
  | .error (.errorToolResult { value := 7 }) => pure ()
  | .error error => fail s!"DeepSeek harness accepted the wrong tool-result error: {reprStr error}"
  | .ok _ => fail "DeepSeek harness silently erased an error tool result"
  match DeepSeekHarness.executeFunctionCall Cordis.Harness.counterConfig 0 {
    id := "bad-call", name := "counter_read", arguments := "{" } with
  | .error (.parseArguments "bad-call" "counter_read" _) => pure ()
  | .error error =>
      fail s!"DeepSeek harness returned the wrong malformed-call error: {reprStr error}"
  | .ok _ => fail "DeepSeek harness admitted malformed tool arguments"
  match DeepSeekHarness.executeFunctionCall Cordis.Harness.counterConfig 0 {
    id := "unknown-call", name := "counter_destroy", arguments := "null" } with
  | .error (.admission "unknown-call" "counter_destroy" (.unknownTool "counter_destroy")) =>
      pure ()
  | .error error => fail s!"DeepSeek harness returned the wrong unknown-call error: {reprStr error}"
  | .ok _ => fail "DeepSeek harness admitted an unknown tool"
  match ← DeepSeekHarness.counterFixture with
  | .error error => fail s!"DeepSeek harness process-backed round failed: {reprStr error}"
  | .ok ⟨body, result⟩ =>
      assertEqual "DeepSeek harness preserves the response body"
        body DeepSeekHarness.counterResponseBody
      assertEqual "DeepSeek harness appends the accepted assistant response"
        result.runner.session.messages [.assistant "I will read the counter." [
          { id := { value := 0 }, name := "counter_read", arguments := "null" }
        ]]
      assertEqual "DeepSeek harness allocates one local tool call ID"
        result.runner.nextCall 1
      assertEqual "DeepSeek harness executes the dependent provider reply"
        result.finalModel 0
      match result.executions with
      | [executed] =>
          assertEqual "DeepSeek harness retains the provider tool name"
            executed.raw.name "counter_read"
          assertEqual "DeepSeek harness retains the certified successor model"
            executed.reply.value.after 0
          assertEqual "DeepSeek harness encodes the typed tool result"
            (DeepSeekHarness.executedToolResultContent executed) "[true,0]"
          assertEqual "DeepSeek harness marks a successful tool result as non-error"
            (DeepSeekHarness.executedToolResultIsError executed) false
          let _resultCertificate := DeepSeekHarness.executedToolResultJson_decodes executed
          let completed := DeepSeekHarness.appendRoundToolResults result
          assertEqual "DeepSeek harness appends the typed tool result to the session"
            completed.messages [
              .assistant "I will read the counter." [
                { id := { value := 0 }, name := "counter_read", arguments := "null" }
              ],
              .toolResult { value := 0 } "[true,0]" false
            ]
          assertEqual "DeepSeek harness advances the session sequence for the tool result"
            completed.nextSeq 2
          assertEqual "DeepSeek harness projects the tool result to protocol"
            (Session.protocolProjection completed.events) [.toolResult 1 0 { value := 0 }]
          let _messagesCertificate := DeepSeekHarness.appendRoundToolResults_messages result
          let _projectionCertificate :=
            DeepSeekHarness.appendRoundToolResults_protocolProjection result
          let _policyCertificate := DeepSeekHarness.executedTool_policy_is_allow executed
          let _providerCertificate := DeepSeekHarness.executedTool_provider_reply executed
          pure ()
      | executions => fail s!"DeepSeek harness returned {executions.length} tool executions"

  let requestBodies ← IO.mkRef ([] : List String)
  let transport : Cordis.DeepSeekApi.Transport := {
    send := fun request => do
      requestBodies.modify (fun bodies => request.body :: bodies)
      let index ← requestBodies.get
      pure (.ok {
        status := 200
        body := if index.length = 1 then DeepSeekHarness.counterResponseBody
          else DeepSeekHarness.counterFinalResponseBody
      })
  }
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  match ← DeepSeekHarness.executeConversationRound transport "https://fixture.invalid"
      { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      Cordis.Harness.counterConfig 0 initialRunner [] (by simp) (by simp) with
  | .error error => fail s!"first continuation round failed: {reprStr error}"
  | .ok ⟨firstBody, first⟩ =>
      assertEqual "conversation runner preserves the first response body"
        firstBody DeepSeekHarness.counterResponseBody
      assertEqual "conversation runner appends the assistant tool call before results"
        first.assistantRunner.session.messages [
          .user "Read the counter.",
          .assistant "I will read the counter." [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }]
        ]
      assertEqual "conversation runner appends the typed result before the next request"
        first.runner.session.messages [
          .user "Read the counter.",
          .assistant "I will read the counter." [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "[true,0]" false
        ]
      assertEqual "conversation runner carries the tool successor into the next round"
        first.finalModel 0
      match ← DeepSeekHarness.executeConversationRound transport "https://fixture.invalid"
          { value := "fixture-key" } DeepSeekHarness.counterRequestSource
          Cordis.Harness.counterConfig first.finalModel first.runner [] (by simp) (by simp) with
      | .error error => fail s!"second continuation round failed: {reprStr error}"
      | .ok ⟨secondBody, second⟩ =>
          assertEqual "conversation runner accepts the second assistant response"
            secondBody DeepSeekHarness.counterFinalResponseBody
          assertEqual "conversation runner executes the two-response tool loop"
            second.runner.session.messages [
              .user "Read the counter.",
              .assistant "I will read the counter." [{
                id := { value := 0 }, name := "counter_read", arguments := "null"
              }],
              .toolResult { value := 0 } "[true,0]" false,
              .assistant "The counter is 0." []
            ]
          assertEqual "conversation runner advances through both assistant responses"
            second.runner.session.nextSeq 4
          let requestBodiesSnapshot ← requestBodies.get
          assertEqual "conversation runner makes exactly two transport requests"
            requestBodiesSnapshot.length 2
          match second.executions with
          | [] => pure ()
          | executions => fail s!"second continuation round executed {executions.length} tools"

  let loopBodies ← IO.mkRef ([] : List String)
  let loopTransport : Cordis.DeepSeekApi.Transport := {
    send := fun request => do
      loopBodies.modify (fun bodies => request.body :: bodies)
      let bodies ← loopBodies.get
      pure (.ok {
        status := 200
        body := if bodies.length = 1 then DeepSeekHarness.counterResponseBody
          else DeepSeekHarness.counterFinalResponseBody
      })
  }
  let loopResult :
      Except DeepSeekHarness.ConversationError
        (DeepSeekHarness.ConversationRunResult
          (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
          Cordis.Harness.counterConfig) ←
    DeepSeekHarness.runConversation (Model := Nat)
      (Capability := Cordis.Examples.Counter.Capability) 2 loopTransport
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp)
      (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner
  match loopResult with
  | .error error => fail s!"fuel-bounded conversation failed: {reprStr error}"
  | .ok result =>
      assertEqual "fuel-bounded conversation retains both round witnesses"
        result.rounds.length 2
      assertEqual "fuel-bounded conversation retains the final model"
        result.finalModel 0
      assertEqual "fuel-bounded conversation reaches the final sequence"
        result.runner.session.nextSeq 4
      assertEqual "fuel-bounded conversation reports completion"
        (DeepSeekHarness.ConversationStop.isCompleted result.stop) true
      let loopBodiesSnapshot ← loopBodies.get
      assertEqual "fuel-bounded conversation makes one request per round"
        loopBodiesSnapshot.length 2

  let exhaustedBodies ← IO.mkRef ([] : List String)
  let exhaustedTransport : Cordis.DeepSeekApi.Transport := {
    send := fun request => do
      exhaustedBodies.modify (fun bodies => request.body :: bodies)
      pure (.ok { status := 200, body := DeepSeekHarness.counterResponseBody })
  }
  let exhaustedResult :
      Except DeepSeekHarness.ConversationError
        (DeepSeekHarness.ConversationRunResult
          (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
          Cordis.Harness.counterConfig) ←
    DeepSeekHarness.runConversation (Model := Nat)
      (Capability := Cordis.Examples.Counter.Capability) 1 exhaustedTransport
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp)
      (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner
  match exhaustedResult with
  | .error error => fail s!"fuel exhaustion fixture failed: {reprStr error}"
  | .ok result =>
      assertEqual "fuel exhaustion retains the completed round prefix"
        result.rounds.length 1
      assertEqual "fuel exhaustion returns the post-tool runner"
        result.runner.session.nextSeq 3
      assertEqual "fuel exhaustion reports a non-completed stop"
        (DeepSeekHarness.ConversationStop.isCompleted result.stop) false
      let exhaustedBodiesSnapshot ← exhaustedBodies.get
      assertEqual "fuel exhaustion does not issue an unbudgeted second request"
        exhaustedBodiesSnapshot.length 1

private def testDeepSeekHarnessPersistence : IO Unit := do
  match DeepSeekHarnessPersistence.persistedToolArchive with
  | .error error => fail s!"persisted DeepSeek archive failed: {reprStr error}"
  | .ok archive =>
      assertEqual "persisted DeepSeek archive validates its event count"
        (Cordis.HarnessPersistenceRefinement.persistenceSummary
          DeepSeekHarnessPersistence.persistedToolArchive)
        (some (0, 8, 8))
      let restored := DeepSeekHarnessPersistence.restoreRunner archive 1 1
        (Cordis.DeepSeekSessionRunner.toolCallCount archive.validated.final.session.messages) rfl
      assertEqual "restored DeepSeek runner preserves the archive endpoint"
        restored.runner.session.nextSeq archive.validated.final.session.nextSeq
      assertEqual "restored DeepSeek runner preserves the archive surface"
        restored.runner.session.messages archive.validated.final.session.messages
      match DeepSeekHarnessPersistence.buildRequestCertificate restored
          DeepSeekHarnessPersistence.persistedToolSource with
      | .error error => fail s!"restored DeepSeek request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "restored DeepSeek request preserves persisted messages"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _buildCertificate := certificate.build_eq
          let _archiveCertificate :=
            DeepSeekHarnessPersistence.buildRequest_session_eq_archive restored
              DeepSeekHarnessPersistence.persistedToolSource certificate.build_eq
          pure ()

private def testDeepSeekHarnessPersistenceIO : IO Unit := do
  match ← DeepSeekHarnessPersistenceIO.fixtureMemory with
  | .error error => fail s!"byte-backed DeepSeek restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "byte-backed DeepSeek restore reaches the archive endpoint"
        restored.restored.runner.session.nextSeq 8
      assertEqual "byte-backed DeepSeek restore retains the exact typed surface"
        restored.restored.runner.session.messages [
          .user "look up lean",
          .assistant "I will look it up." [{
            id := { value := 0 }
            name := "lookup"
            arguments := "{\"q\":\"lean\"}"
          }],
          .toolResult { value := 0 } "result" false
        ]
      let _sessionCertificate :=
        DeepSeekHarnessPersistenceIO.RestoredRunner.session_eq_read restored
      let _rowsCertificate :=
        DeepSeekHarnessPersistenceIO.RestoredRunner.raw_rows_eq_input restored
      match DeepSeekHarnessPersistenceIO.buildRequestCertificate restored
          { model := "deepseek-reasoner", errorToolResults := .reject } with
      | .error error => fail s!"byte-backed DeepSeek request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "byte-backed DeepSeek request retains persisted messages"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _requestCertificate := certificate.build_eq
          let _archiveCertificate :=
            DeepSeekHarnessPersistenceIO.buildRequest_session_eq_read restored
              { model := "deepseek-reasoner", errorToolResults := .reject }
              certificate.build_eq
          pure ()
  match ← DeepSeekHarnessPersistenceIO.fixtureFile with
  | .error error => fail s!"file-backed DeepSeek restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "file-backed DeepSeek restore retains the archive row count"
        restored.read.input.length 9
  match ← DeepSeekHarnessPersistenceIO.fixtureAppend with
  | .error error => fail s!"byte-backed DeepSeek append restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "byte-backed DeepSeek append restore retains the appended archive"
        restored.read.input.length 2
      assertEqual "byte-backed DeepSeek append restore reaches the expanded endpoint"
        restored.restored.runner.session.nextSeq 3
  match ← DeepSeekHarnessPersistenceIO.fixtureRequest with
  | .error error => fail s!"byte-backed DeepSeek request fixture read failed: {reprStr error}"
  | .ok (.error error) => fail s!"byte-backed DeepSeek request fixture failed: {reprStr error}"
  | .ok (.ok request) =>
      assertEqual "byte-backed DeepSeek request fixture uses the persisted tool call"
        request.messages.toList [
          .user "look up lean",
          .assistant (some "I will look it up.") none [{
            id := "0"
            name := "lookup"
            arguments := "{\"q\":\"lean\"}"
          }],
          .tool "0" "result"
        ]
  match ← DeepSeekHarnessPersistenceIO.fixtureInvalidUtf8 with
  | .error (.text .invalidUtf8) => pure ()
  | .error error => fail s!"byte-backed DeepSeek invalid UTF-8 returned {reprStr error}"
  | .ok _ => fail "byte-backed DeepSeek invalid UTF-8 was accepted"

private def testDeepSeekHarnessPayloadPersistence : IO Unit := do
  match DeepSeekHarnessPayloadPersistence.persistedToolPayloadRestored with
  | .error (.inl error) => fail s!"payload persistence archive failed: {reprStr error}"
  | .error (.inr error) => fail s!"payload persistence restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload persistence restore reaches the archive endpoint"
        restored.runner.session.nextSeq 8
      assertEqual "payload persistence keeps one event per expanded event"
        restored.payload.events.length restored.archive.expandedEvents.length
      assertEqual "payload persistence keeps all supported payloads typed"
        restored.payload.typedCount 8
      let _sessionCertificate :=
        DeepSeekHarnessPayloadPersistence.RestoredRunner.session_eq_archive restored
      let _payloadCertificate :=
        DeepSeekHarnessPayloadPersistence.RestoredRunner.payload_raw_eq_expanded restored
      let _projectionCertificate :=
        DeepSeekHarnessPayloadPersistence.RestoredRunner.projection_exact restored
      match DeepSeekHarnessPayloadPersistence.buildRequestCertificate restored
          DeepSeekHarnessPersistence.persistedToolSource with
      | .error error => fail s!"payload persistence request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "payload persistence request preserves persisted messages"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
  match DeepSeekHarnessPayloadPersistence.persistedToolBytesRestored with
  | .error error => fail s!"payload persistence byte restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload persistence bytes decode the exact source"
        (String.fromUTF8? DeepSeekHarnessPayloadPersistence.persistedToolBytes)
        (some restored.validated.text)
      assertEqual "payload persistence bytes reach the same endpoint"
        restored.restored.runner.session.nextSeq 8
      let _decodedCertificate :=
        DeepSeekHarnessPayloadPersistence.RestoredBytesRunner.decoded_eq restored
      let _payloadCertificate :=
        DeepSeekHarnessPayloadPersistence.RestoredBytesRunner.payload_raw_eq_expanded restored
  match ← DeepSeekHarnessPayloadPersistence.fixtureMemory with
  | .error error => fail s!"payload persistence memory fixture failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload persistence memory read retains the event count"
        restored.restored.payload.events.length 8
      let _sessionCertificate :=
        DeepSeekHarnessPayloadPersistence.ReadRestoredRunner.session_eq_read restored
      let _payloadCertificate :=
        DeepSeekHarnessPayloadPersistence.ReadRestoredRunner.payload_raw_eq_expanded restored
  match ← DeepSeekHarnessPayloadPersistence.fixtureAppend with
  | .error error => fail s!"payload persistence append fixture failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload persistence append re-enters the payload archive"
        restored.restored.payload.events.length 3
  match ← DeepSeekHarnessPayloadPersistence.fixtureFile with
  | .error error => fail s!"payload persistence file fixture failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload persistence file read retains the archive rows"
        restored.read.input.length 9
  match ← DeepSeekHarnessPayloadPersistence.fixtureInvalidUtf8 with
  | .error (.store (.text .invalidUtf8)) => pure ()
  | .error error => fail s!"payload persistence invalid UTF-8 returned {reprStr error}"
  | .ok _ => fail "payload persistence invalid UTF-8 was accepted"

private def testDeepSeekHarnessOpaqueMetadata : IO Unit := do
  match DeepSeekHarnessOpaqueMetadata.metadataRestored with
  | .error error => fail s!"opaque metadata DeepSeek restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "opaque metadata restore reaches the sanitized session endpoint"
        restored.runner.session.nextSeq 8
      assertEqual "opaque metadata restore preserves the typed tool surface"
        restored.runner.session.messages [
          .user "look up lean",
          .assistant "I will look it up." [{
            id := { value := 0 }
            name := "lookup"
            arguments := "{\"q\":\"lean\"}"
          }],
          .toolResult { value := 0 } "result" false
        ]
      assertEqual "opaque metadata restore retains exact provider/tool fields"
        ((restored.log.metadata.filterMap (fun metadata =>
          metadata.map (fun value => (value.error, value.metaValue)))) == [
            (some (Lean.Json.mkObj [
                ("name", .str "ToolError"), ("code", .str "E_FIXTURE")]),
              some (Lean.Json.mkObj [("opaque", .str "tool-owned")]))]) true
      let _sessionCertificate :=
        DeepSeekHarnessOpaqueMetadata.RestoredRunner.session_eq_log restored
      let _metadataCertificate :=
        DeepSeekHarnessOpaqueMetadata.RestoredRunner.metadata_eq_source restored
      let _validCertificate := DeepSeekHarnessOpaqueMetadata.metadataRestored_valid
      let _exactCertificate := DeepSeekHarnessOpaqueMetadata.metadataRestored_metadata_exact
      match DeepSeekHarnessOpaqueMetadata.buildRequestCertificate restored
          DeepSeekHarnessOpaqueMetadata.metadataToolSource with
      | .error error => fail s!"opaque metadata request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "opaque metadata request excludes quarantined fields"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _requestCertificate := certificate.build_eq
          let _archiveCertificate :=
            DeepSeekHarnessOpaqueMetadata.buildRequest_session_eq_log restored
              DeepSeekHarnessOpaqueMetadata.metadataToolSource certificate.build_eq
          pure ()

private def testDeepSeekHarnessMetadataArchive : IO Unit := do
  match DeepSeekHarnessMetadataArchive.metadataRestored with
  | .error error => fail s!"metadata event archive restore failed: {reprStr error}"
  | .ok restored =>
      assertEqual "metadata event archive preserves every raw envelope"
        ((restored.log.archive.events.map SessionEventArchive.ArchivedEvent.raw) ==
          SessionOpaqueMetadata.metadataExampleJson) true
      assertEqual "metadata event archive retains one opaque known event"
        (restored.log.archive.events.countP SessionEventArchive.ArchivedEvent.isOpaque) 1
      assertEqual "metadata event archive restores the sanitized session"
        restored.runner.session.nextSeq 8
      assertEqual "metadata event archive retains the opaque metadata ledger"
        ((restored.log.retained.metadata.filterMap (fun metadata =>
          metadata.map (fun value => (value.error, value.metaValue)))) == [
            (some (Lean.Json.mkObj [
                ("name", .str "ToolError"), ("code", .str "E_FIXTURE")]),
              some (Lean.Json.mkObj [("opaque", .str "tool-owned")]))]) true
      let _rawCertificate :=
        DeepSeekHarnessMetadataArchive.AttachedLog.raw_exact restored.log
      let _metadataCertificate :=
        DeepSeekHarnessMetadataArchive.AttachedLog.metadata_eq_source restored.log
      let _sanitizedCertificate :=
        DeepSeekHarnessMetadataArchive.AttachedLog.sanitized_eq_source restored.log
      let _validCertificate := DeepSeekHarnessMetadataArchive.metadataAttached_valid
      let _opaqueCertificate :=
        DeepSeekHarnessMetadataArchive.metadataAttached_has_one_opaque_event
      let _exactCertificate := DeepSeekHarnessMetadataArchive.metadataRestored_metadata_exact
      match DeepSeekHarnessMetadataArchive.buildRequestCertificate restored
          DeepSeekHarnessMetadataArchive.metadataToolSource with
      | .error error => fail s!"metadata event archive request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "metadata event archive request uses sanitized messages"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _requestCertificate := certificate.build_eq
          let _archiveCertificate :=
            DeepSeekHarnessMetadataArchive.buildRequest_session_eq_log restored
              DeepSeekHarnessMetadataArchive.metadataToolSource certificate.build_eq
          let _messageCertificate :=
            DeepSeekHarnessMetadataArchive.metadataRestored_request_messages
          pure ()

private def testDeepSeekToolSchema : IO Unit := do
  match DeepSeekToolSchema.weatherCertificate with
  | .error error => fail s!"bounded weather schema was rejected: {reprStr error}"
  | .ok certificate =>
      assertEqual "bounded weather schema retains the certified tool count"
        DeepSeekToolSchema.weatherSource.tools.length 1
      match DeepSeekToolSchema.CertifiedRequestSource.buildRequestPlan
          "https://fixture.invalid" { value := "fixture-key" } certificate
          DeepSeekHarness.counterSession with
      | .error error => fail s!"certified tool request failed: {reprStr error}"
      | .ok plan =>
          assertEqual "certified tool request preserves the tool name"
            (plan.source.tools.head?.map (fun tool => tool.function.name)) (some "get_weather")
          assertEqual "certified tool request preserves the exact model"
            plan.source.model "deepseek-reasoner"
          match DeepSeekToolSchema.CertifiedRequestSource.buildTypedStreamingRequestPlan
              "https://fixture.invalid" { value := "fixture-key" } certificate
              DeepSeekHarness.counterSession with
          | .error error => fail s!"certified streaming tool request failed: {reprStr error}"
          | .ok streamPlan =>
              assertEqual "certified streaming request enables the provider stream flag"
                streamPlan.source.stream true
              let _streamCertificate := streamPlan.streaming_source_stream
          pure ()
  assertEqual "valid weather arguments are admitted"
    DeepSeekToolSchema.validWeatherArgumentsAccepted true
  assertEqual "wrong primitive weather arguments are rejected"
    DeepSeekToolSchema.wrongWeatherArgumentsRejected true
  assertEqual "missing required weather arguments are rejected"
    DeepSeekToolSchema.missingWeatherArgumentsRejected true
  assertEqual "unknown weather arguments are rejected"
    DeepSeekToolSchema.unknownWeatherArgumentsRejected true
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => fail s!"weather tool argument certificate setup failed: {reprStr error}"
  | .ok certificate =>
      match certificate.validateArguments "{\"city\":\"San Francisco\"}" with
      | .error error => fail s!"valid weather arguments were rejected: {reprStr error}"
      | .ok arguments =>
          assertEqual "validated weather arguments retain one source field"
            arguments.fields.length 1
          assertEqual "validated weather arguments retain the source field name"
            (arguments.fields.map Prod.fst) ["city"]
          let _parsed := arguments.parsed_eq
          let _shape := arguments.source_is_object
          let _unique := arguments.fields_nodup
          let _required := arguments.required_present
          let _properties := arguments.properties_valid
          let _unknown := arguments.unknown_properties_ok
      match certificate.validateArguments "{\"city\":3}" with
      | .error (.typeMismatch path "string" .number) =>
          assertEqual "wrong primitive argument reports its exact path"
            path [.field "city"]
      | .error error => fail s!"wrong primitive argument returned {reprStr error}"
      | .ok _ => fail "wrong primitive argument was accepted"
      match certificate.validateArguments "{}" with
      | .error (.missingRequired path "city") =>
          assertEqual "missing required argument reports its path"
            path [.field "required", .field "city"]
      | .error error => fail s!"missing required argument returned {reprStr error}"
      | .ok _ => fail "missing required argument was accepted"
      match certificate.validateArguments "{\"city\":\"SF\",\"extra\":true}" with
      | .error (.unknownProperty path "extra") =>
          assertEqual "unknown argument reports its exact path"
            path [.field "extra"]
      | .error error => fail s!"unknown argument returned {reprStr error}"
      | .ok _ => fail "unknown argument was accepted"
  assertEqual "certified provider tool calls are admitted"
    DeepSeekToolAdmission.weatherCallAccepted true
  assertEqual "provider calls for another tool are rejected"
    DeepSeekToolAdmission.weatherCallWrongNameRejected true
  assertEqual "provider calls with wrong argument kinds are rejected"
    DeepSeekToolAdmission.weatherCallWrongArgumentsRejected true
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => fail s!"weather tool call setup failed: {reprStr error}"
  | .ok certificate =>
      match DeepSeekToolAdmission.validateFunctionCall certificate
          DeepSeekToolAdmission.weatherCall with
      | .error error => fail s!"valid provider tool call was rejected: {reprStr error}"
      | .ok call =>
          assertEqual "certified provider call preserves its declared name"
            DeepSeekToolAdmission.weatherCall.name "get_weather"
          let _name := call.name_eq
          let _parsed := call.arguments_parse_eq
          let _source := call.arguments.source_is_object
          let _required := call.arguments.required_present
      match DeepSeekToolAdmission.validateFunctionCall certificate
          DeepSeekToolAdmission.weatherCallWrongName with
      | .error (.nameMismatch "call-weather-0" "wrong_tool" "get_weather") => pure ()
      | .error error => fail s!"wrong provider tool name returned {reprStr error}"
      | .ok _ => fail "wrong provider tool name was accepted"
      match DeepSeekToolAdmission.validateFunctionCall certificate
          DeepSeekToolAdmission.weatherCallWrongArguments with
      | .error (.arguments "call-weather-0" "get_weather"
          (.typeMismatch path "string" .number)) =>
          assertEqual "provider argument error retains its exact field path"
            path [.field "city"]
      | .error error => fail s!"wrong provider argument returned {reprStr error}"
      | .ok _ => fail "wrong provider argument was accepted"
  assertEqual "certified provider call reaches generic dependent admission"
    DeepSeekGenericBridge.Example.weatherAccepted true
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => fail s!"generic bridge setup failed: {reprStr error}"
  | .ok certificate =>
      match DeepSeekGenericBridge.Example.weatherAdmitted certificate with
      | .error error => fail s!"generic bridge rejected a certified call: {reprStr error}"
      | .ok ⟨call, checked⟩ =>
          assertEqual "generic bridge selects the bound catalog operation"
            (call.op == DeepSeekGenericBridge.Example.Operation.weather) true
          let _name := checked.provider_name_eq
          let _operation :=
            DeepSeekGenericBridge.validateAndAdmit_generic_tool_eq
              (DeepSeekGenericBridge.Example.weatherBinding certificate) checked
          let _validation := checked.validation
          pure ()
  assertEqual "schema-certified provider call reaches dependent execution"
    DeepSeekSchemaExecution.Example.weatherExecutionAccepted true
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => fail s!"schema execution setup failed: {reprStr error}"
  | .ok certificate =>
      match DeepSeekSchemaExecution.Example.weatherExecuted certificate with
      | .error error => fail s!"schema-certified execution failed: {reprStr error}"
      | .ok ⟨call, executed⟩ =>
          assertEqual "schema execution selects the bound operation"
            (call.op == DeepSeekGenericBridge.Example.Operation.weather) true
          let _operation := executed.generic_tool_eq
          let _policy := executed.policy
          let _execution := executed.execution
          pure ()
  assertEqual "schema-certified execution reifies on the existing harness surface"
    DeepSeekSchemaHarness.Example.weatherAppended true
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => fail s!"schema harness setup failed: {reprStr error}"
  | .ok certificate =>
      match DeepSeekSchemaHarness.Example.weatherSchemaExecuted certificate with
      | .error error => fail s!"schema harness execution failed: {reprStr error}"
      | .ok ⟨_, executed⟩ =>
          let session := DeepSeekSchemaHarness.appendCertifiedToolResult
            DeepSeekHarness.counterSession 1 0 { value := 0 } 0 executed (by
              decide)
          let _messages :=
            DeepSeekSchemaHarness.appendCertifiedToolResult_messages
              DeepSeekHarness.counterSession 1 0 { value := 0 } 0 executed (by decide)
          let _projection :=
            DeepSeekSchemaHarness.appendCertifiedToolResult_protocolProjection
              DeepSeekHarness.counterSession 1 0 { value := 0 } 0 executed (by decide)
          let _nextSeq :=
            DeepSeekSchemaHarness.appendCertifiedToolResult_nextSeq
              DeepSeekHarness.counterSession 1 0 { value := 0 } 0 executed (by decide)
          let _tool := executed.toExecutedTool
          let _operation := executed.toExecutedTool_generic_tool_eq
          assertEqual "schema harness append advances the existing session"
            session.nextSeq (DeepSeekHarness.counterSession.nextSeq + 1)
          pure ()
  assertEqual "schema-certified execution reaches the conversation runner"
    DeepSeekSchemaHarness.Example.weatherRunnerAppended true
  match DeepSeekToolSchema.weatherToolCertificate with
  | .error error => fail s!"schema runner setup failed: {reprStr error}"
  | .ok certificate =>
      match DeepSeekSchemaHarness.Example.weatherSchemaExecuted certificate with
      | .error error => fail s!"schema runner execution failed: {reprStr error}"
      | .ok ⟨_, executed⟩ =>
          let runner := DeepSeekSchemaHarness.appendCertifiedToolResultToRunner
            DeepSeekSchemaHarness.Example.counterRunner 0 0 executed (by decide)
          let _messages :=
            DeepSeekSchemaHarness.appendCertifiedToolResultToRunner_messages
              DeepSeekSchemaHarness.Example.counterRunner 0 0 executed (by decide)
          let _nextCall :=
            DeepSeekSchemaHarness.appendCertifiedToolResultToRunner_nextCall
              DeepSeekSchemaHarness.Example.counterRunner 0 0 executed (by decide)
          assertEqual "schema runner append preserves the local call allocator"
            runner.nextCall DeepSeekSchemaHarness.Example.counterRunner.nextCall
          pure ()
  assertEqual "accepted DeepSeek response reaches the schema-aware round"
    DeepSeekSchemaRound.Example.weatherRoundAccepted true
  assertEqual "schema-aware round reaches the exact two-append endpoint"
    DeepSeekSchemaRound.Example.weatherRoundFinalNextSeq true
  assertEqual "schema-aware round rejects an assistant response without a tool call"
    DeepSeekSchemaRound.Example.emptyResponseRejected true
  assertEqual "schema-aware multi-round executes two certified calls"
    DeepSeekSchemaMultiRound.Example.twoWeatherRoundAccepted true
  assertEqual "schema-aware multi-round accounts for assistant plus two results"
    DeepSeekSchemaMultiRound.Example.twoWeatherRoundFinalNextSeq true
  assertEqual "schema-aware multi-round rejects a later wrong tool name"
    DeepSeekSchemaMultiRound.Example.wrongSecondNameRejected true
  assertEqual "schema registry executes heterogeneous weather and clock tools"
    DeepSeekSchemaRegistry.Example.dualRoundAccepted true
  assertEqual "schema registry accounts for assistant plus heterogeneous results"
    DeepSeekSchemaRegistry.Example.dualRoundFinalNextSeq true
  assertEqual "schema registry rejects an unknown later tool name"
    DeepSeekSchemaRegistry.Example.unknownToolRejected true
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"transport-backed registry weather schema failed: {reprStr error}"
  | _, .error error => fail s!"transport-backed registry clock schema failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekSchemaConversation.Example.dualConversationRound
          weatherCertificate clockCertificate with
      | .error error => fail s!"transport-backed heterogeneous registry failed: {reprStr error}"
      | .ok ⟨_, ⟨_, ⟨batch, result⟩⟩⟩ =>
          assertEqual "transport-backed registry retains two certified executions"
            batch.executions.length 2
          assertEqual "transport-backed registry preserves the final model"
            batch.finalModel 0
          assertEqual "transport-backed registry accounts for assistant plus two results"
            result.round.finalRunner.session.nextSeq
            (DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3)
          assertEqual "transport-backed registry sends both declared tools"
            result.plan.source.tools.length 2
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"schema conversation loop weather schema failed: {reprStr error}"
  | _, .error error => fail s!"schema conversation loop clock schema failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekSchemaConversationLoop.Example.dualConversationRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"schema conversation loop failed: {reprStr error}"
      | .ok result =>
          assertEqual "schema conversation loop records one tool round"
            result.rounds.length 1
          assertEqual "schema conversation loop preserves the final model"
            result.finalModel 0
          assertEqual "schema conversation loop appends the tool round"
            result.runner.session.nextSeq
            (DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3)
          match result.stop with
          | .completed terminal =>
              assertEqual "schema conversation loop retains terminal no-tool response"
                terminal.accepted.validated.response.choices.head.message.toolCalls []
          | .fuelExhausted _ _ => fail "schema conversation loop exhausted before terminal response"
      match ← DeepSeekSchemaConversationLoop.Example.dualConversationExhausted
          weatherCertificate clockCertificate with
      | .error error => fail s!"schema conversation loop exhaustion fixture failed: {reprStr error}"
      | .ok result =>
          match result.stop with
          | .fuelExhausted _ _ =>
              assertEqual "schema conversation loop preserves its certified prefix on exhaustion"
                result.rounds.length 1
          | .completed _ => fail "schema conversation loop reported completion without fuel"
  match DeepSeekToolSchema.malformedToolResult with
  | .error (.unsupportedTag path "date") =>
      assertEqual "unsupported property type reports its exact path"
        path [.field "properties", .field "city", .field "type"]
  | .error error => fail s!"malformed tool returned the wrong error: {reprStr error}"
  | .ok _ => fail "malformed tool schema was accepted"
  match DeepSeekToolSchema.unknownRequiredResult with
  | .error (.unknownRequired path "missing") =>
      assertEqual "unknown required name reports its exact array path"
        path [.field "required", .index 0]
  | .error error => fail s!"unknown required name returned the wrong error: {reprStr error}"
  | .ok _ => fail "unknown required name was accepted"
  match DeepSeekToolSchema.duplicateNamesResult with
  | .error (.duplicateToolName "get_weather") => pure ()
  | .error error => fail s!"duplicate tool names returned the wrong error: {reprStr error}"
  | .ok _ => fail "duplicate tool names were accepted"

private def testDeepSeekScopedRegistry : IO Unit := do
  assertEqual "nearest scope shadows the global weather declaration"
    DeepSeekScopedRegistry.Example.shadowedWeather true
  assertEqual "a restricted nearest declaration blocks fallback"
    DeepSeekScopedRegistry.Example.restrictedWeather true
  assertEqual "global clock dispatch selects the review route"
    DeepSeekScopedRegistry.Example.globalClock true
  assertEqual "approval rejection happens before provider execution"
    DeepSeekScopedRegistry.Example.approvalRejected true
  assertEqual "unknown scoped names are rejected"
    DeepSeekScopedRegistry.Example.unknownRejected true

private def testDeepSeekHarnessExtensions : IO Unit := do
  have _logOnlyProof := DeepSeekHarnessExtensions.heartbeat_is_log_only
  pure ()
  assertEqual "generic extension session retains only its surface message"
    DeepSeekHarnessExtensions.extensionSession.messages [.user "hello"]
  assertEqual "generic extension request contains one model message"
    DeepSeekHarnessExtensions.extensionMessageCount 1
  assertEqual "generic extension request has the certified one-message shape"
    DeepSeekHarnessExtensions.extensionRequestHasOneMessage true
  match DeepSeekHarnessExtensions.extensionStreamingRequest with
  | .error error => fail s!"generic extension streaming request failed: {reprStr error}"
  | .ok plan =>
      assertEqual "generic extension streaming request carries stream=true"
        plan.source.stream true
  match DeepSeekHarnessExtensions.extensionTypedStreamingRequest with
  | .error error => fail s!"generic typed extension streaming request failed: {reprStr error}"
  | .ok plan =>
      assertEqual "generic typed extension request carries stream=true"
        plan.source.stream true
  assertEqual "schema-preserving assistant append keeps the extension session surface"
    DeepSeekHarnessExtensions.extensionWithAssistant.messages
    [.user "hello", .assistant "assistant" []]
  match DeepSeekHarnessExtensions.extensionRunnerText with
  | .error error => fail s!"generic extension runner text append failed: {reprStr error}"
  | .ok after =>
      assertEqual "generic extension runner preserves prior messages and appends rich text"
        after.session.messages [.user "hello", .assistant "Hello world" []]
      assertEqual "generic extension runner advances the physical sequence"
        after.session.nextSeq 4
      assertEqual "generic extension runner keeps the text tool-call count at zero"
        after.nextCall 0

private def testSessionExtensionRefinement : IO Unit := do
  have _heartbeatProof := SessionExtensionRefinement.Example.decode_heartbeat_exact
  have _bannerProof := SessionExtensionRefinement.Example.decode_banner_exact
  have _appendProof := SessionExtensionRefinement.Example.heartbeat_append_exact
  have _surfaceProof := SessionExtensionRefinement.Example.banner_append_messages
  have _replayProof := SessionExtensionRefinement.Example.validated_example_summary
  match SessionExtensionRefinement.Example.heartbeatSession with
  | .error error => fail s!"typed heartbeat extension failed: {reprStr error}"
  | .ok session =>
      assertEqual "typed log-only extension has no model message"
        session.messages []
      assertEqual "typed log-only extension advances the physical sequence"
        session.nextSeq 1
      assertEqual "typed log-only extension appends one event"
        session.events.length 1
  match SessionExtensionRefinement.Example.bannerSession with
  | .error error => fail s!"typed banner extension failed: {reprStr error}"
  | .ok session =>
      assertEqual "typed surface extension projects its schema message"
        session.messages [.user "extension:ready"]
      assertEqual "typed surface extension advances the physical sequence"
        session.nextSeq 1
  match SessionExtensionRefinement.decodeEvent SessionExtensionRefinement.Example.exampleCodec
      SessionExtensionRefinement.Example.wrongTagJson with
  | .error (.unsupportedTag _ "session/turn-start") => pure ()
  | .error error => fail s!"wrong extension tag returned the wrong error: {reprStr error}"
  | .ok _ => fail "wrong extension tag was accepted"
  match SessionExtensionRefinement.decodeEvent SessionExtensionRefinement.Example.exampleCodec
      SessionExtensionRefinement.Example.ignorableJson with
  | .error (.unsupportedField _ "ignorable") => pure ()
  | .error error => fail s!"ignorable extension returned the wrong error: {reprStr error}"
  | .ok _ => fail "ignorable extension was accepted"
  match SessionExtensionRefinement.decodeEvent SessionExtensionRefinement.Example.exampleCodec
      SessionExtensionRefinement.Example.malformedBannerJson with
  | .error (.typeMismatch _ "string" .number) => pure ()
  | .error error => fail s!"malformed extension payload returned the wrong error: {reprStr error}"
  | .ok _ => fail "malformed extension payload was accepted"
  match SessionExtensionRefinement.decodeAndAppend
      SessionExtensionRefinement.Example.exampleCodec
      (Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
      SessionExtensionRefinement.Example.staleHeartbeatJson with
  | .error (.sequenceMismatch _ 0 1) => pure ()
  | .error error => fail s!"stale extension sequence returned the wrong error: {reprStr error}"
  | .ok _ => fail "stale extension sequence was accepted"
  match SessionExtensionRefinement.Example.validatedExample with
  | .error error => fail s!"typed extension replay failed: {reprStr error}"
  | .ok log =>
      assertEqual "typed extension replay advances both records"
        log.final.nextSeq 2
      assertEqual "typed extension replay retains the surface projection"
        log.final.messages [.user "extension:ready"]
      assertEqual "typed extension replay retains both dependent events"
        log.replay.events.length 2
  have _archiveSummary := SessionExtensionArchive.Example.archived_example_summary
  have _archiveRaw := SessionExtensionArchive.Example.archived_example_raw_exact
  have _archiveExtensions :=
    SessionExtensionArchive.Example.archived_example_required_extensions
  match SessionExtensionArchive.Example.archivedExample with
  | .error error => fail s!"typed extension archive failed: {reprStr error}"
  | .ok archive =>
      assertEqual "typed extension archive retains both raw records"
        archive.archive.events.length 2
      assertEqual "typed extension archive reaches the replay endpoint"
        archive.validated.final.nextSeq 2
      assertEqual "typed extension archive retains both dependent records"
        archive.validated.replay.events.length 2
  match SessionExtensionArchive.validate SessionExtensionRefinement.Example.exampleCodec
      (Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
      [SessionExtensionArchive.Example.knownCoreJson] with
  | .error (.notExtension 0 (some .turnStart)) => pure ()
  | .error error => fail s!"known core archive returned the wrong error: {reprStr error}"
  | .ok _ => fail "known core event was accepted by extension-only archive"
  match SessionExtensionArchive.validate SessionExtensionRefinement.Example.exampleCodec
      (Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
      [SessionExtensionArchive.Example.ignorableExtensionJson] with
  | .error (.ignorable 0) => pure ()
  | .error error => fail s!"ignorable archive returned the wrong error: {reprStr error}"
  | .ok _ => fail "ignorable extension was accepted by required-extension archive"
  have _runnerSummary := DeepSeekHarnessExtensionArchive.Example.restored_example_summary
  have _runnerRequest := DeepSeekHarnessExtensionArchive.Example.restored_example_request
  match DeepSeekHarnessExtensionArchive.Example.restoredExample with
  | .error error => fail s!"schema extension runner restoration failed: {error}"
  | .ok restored =>
      assertEqual "schema extension runner retains the archived sequence endpoint"
        restored.runner.session.nextSeq 2
      assertEqual "schema extension runner aligns its step with the archived endpoint"
        restored.runner.step 2
      assertEqual "schema extension runner derives the archived tool-call count"
        restored.runner.nextCall 0
  match DeepSeekHarnessExtensionArchive.Example.exampleRequest with
  | .error error => fail s!"schema extension request construction failed: {reprStr error}"
  | .ok request =>
      assertEqual "schema extension request keeps the source model"
        request.model "deepseek-chat"
      assertEqual "schema extension request keeps the surface extension message"
        request.messages.toList [DeepSeekApi.ChatMessage.user "extension:ready"]
  match DeepSeekHarnessExtensionArchive.Example.restoredExample with
  | .error error => fail s!"certified extension request archive failed: {error}"
  | .ok restored =>
      match DeepSeekHarnessExtensionRequest.Example.certifiedExampleRequest restored with
      | .error error => fail s!"certified extension request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "certified extension request retains the source model"
            certificate.request.model "deepseek-chat"
          have _namesProof := certificate.tools.names_nodup
          let _archiveRequest :=
            DeepSeekHarnessExtensionRequest.CertifiedRequest.build_eq_archive certificate
          pure ()
  match DeepSeekHarnessExtensionArchive.Example.restoredExample with
  | .error error => fail s!"duplicate-tool archive setup failed: {error}"
  | .ok restored =>
      match DeepSeekHarnessExtensionRequest.Example.duplicateExampleRequest restored with
      | .error (.inl (.duplicateToolName "get_weather")) => pure ()
      | .error error => fail s!"duplicate tool source returned the wrong error: {reprStr error}"
      | .ok _ => fail "duplicate tool source was accepted"

private def testDeepSeekHarnessExtensionPersistence : IO Unit := do
  have _summary :=
    DeepSeekHarnessExtensionPersistence.Example.validated_example_summary
  have _rows := DeepSeekHarnessExtensionPersistence.Example.validated_example_rows_exact
  have _empty := DeepSeekHarnessExtensionPersistence.Example.reject_empty
  have _core := DeepSeekHarnessExtensionPersistence.Example.reject_known_core
  have _badHeader := DeepSeekHarnessExtensionPersistence.Example.reject_bad_header
  assertEqual "extension persistence text summary"
    DeepSeekHarnessExtensionPersistence.Example.textExampleSummary (some (0, 2))
  assertEqual "extension persistence byte summary"
    DeepSeekHarnessExtensionPersistence.Example.bytesExampleSummary (some 2)
  match DeepSeekHarnessExtensionPersistence.validate
      SessionExtensionRefinement.Example.exampleCodec
      (Session.Session.empty DeepSeekHarnessExtensions.exampleSchema)
      DeepSeekHarnessExtensionPersistence.Example.persistenceInput with
  | .error error => fail s!"extension persistence AST validation failed: {reprStr error}"
  | .ok validated =>
      assertEqual "extension persistence retains the header version"
        validated.header.version 0
      assertEqual "extension persistence retains the extension-row count"
        validated.storageRows.length 2
      assertEqual "extension persistence reaches the indexed endpoint"
        validated.extension.validated.final.nextSeq 2
      let restored := DeepSeekHarnessExtensionPersistence.restoreRunner
        SessionExtensionRefinement.Example.exampleCodec
        (Session.Session.empty DeepSeekHarnessExtensions.exampleSchema) validated 1
      have _session :=
        DeepSeekHarnessExtensionPersistence.RestoredRunner.session_eq_persisted restored
      match DeepSeekHarnessExtensionPersistence.buildRequestCertificate restored
          DeepSeekHarnessExtensionArchive.Example.exampleSource with
      | .error error => fail s!"extension persistence request failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "extension persistence request preserves the source model"
            certificate.request.model "deepseek-chat"
          have _names := certificate.tools.names_nodup
          pure ()
  match ← DeepSeekHarnessExtensionPersistence.Example.fixtureMemory with
  | .error error => fail s!"extension persistence memory read failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "extension persistence memory read reaches the endpoint"
        certificate.validated.extension.validated.final.nextSeq 2
  match ← DeepSeekHarnessExtensionPersistence.Example.fixtureAppend with
  | .error error => fail s!"extension persistence append failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "extension persistence append validates the new suffix"
        certificate.validated.extension.validated.final.nextSeq 1
  match ← DeepSeekHarnessExtensionPersistence.Example.fixtureFile with
  | .error error => fail s!"extension persistence file read failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "extension persistence file read preserves both rows"
        certificate.validated.storageRows.length 2
  match ← DeepSeekHarnessExtensionPersistence.Example.fixtureInvalidUtf8 with
  | .error (.text .invalidUtf8) => pure ()
  | .error error => fail s!"invalid extension persistence bytes returned {reprStr error}"
  | .ok _ => fail "invalid extension persistence bytes were accepted"

private def testDeepSeekHarnessMixedPersistence : IO Unit := do
  have _summary := DeepSeekHarnessMixedPersistence.Example.mixed_summary
  have _schedule := DeepSeekHarnessMixedPersistence.Example.mixed_schedule_exact
  match DeepSeekHarnessMixedPersistence.Example.mixedCertificate with
  | .error error => fail s!"mixed persistence validation failed: {reprStr error}"
  | .ok certificate =>
      assertEqual "mixed persistence archives every source row"
        certificate.archive.events.length 7
      assertEqual "mixed persistence core projection reaches its endpoint"
        certificate.core.final.session.nextSeq 6
      assertEqual "mixed persistence extension projection reaches its endpoint"
        certificate.extension.validated.final.nextSeq 1
      have _archive :=
        DeepSeekHarnessMixedPersistence.MixedCertificate.archive_raw_exact certificate
      have _core :=
        DeepSeekHarnessMixedPersistence.MixedCertificate.core_decode_exact certificate
      have _extension :=
        DeepSeekHarnessMixedPersistence.MixedCertificate.extension_raw_exact certificate
      pure ()

private def testDeepSeekHarnessSchemaLift : IO Unit := do
  have _eventProtocol :=
    DeepSeekHarnessSchemaLift.liftEvent_protocol
      (schema := DeepSeekHarnessExtensions.exampleSchema)
  have _sessionProtocol :=
    DeepSeekHarnessSchemaLift.Example.certifiedLift_protocol_exact
  assertEqual "arbitrary-schema core lift preserves the physical endpoint"
    DeepSeekHarnessSchemaLift.Example.certifiedLift.target.nextSeq 5
  assertEqual "arbitrary-schema core lift preserves the materialized surface"
    DeepSeekHarnessSchemaLift.Example.certifiedLift.target.surface.length 3
  assertEqual "arbitrary-schema core lift preserves the request header"
    DeepSeekHarnessSchemaLift.Example.certifiedLift.target.latestHeader.isSome true
  have _noCustom := DeepSeekHarnessSchemaLift.Example.lifted_extension_schema_is_not_custom
  pure ()
  assertEqual "arbitrary-schema core lift preserves the protocol trace"
    (Session.protocolProjection
      DeepSeekHarnessSchemaLift.Example.certifiedLift.target.events)
    Session.certifiedToolTrace.erase

private def testDeepSeekHarnessMixedReplay : IO Unit := do
  assertEqual "mixed replay accepts interleaved custom log-only rows"
    (match DeepSeekHarnessMixedReplay.Example.certificate with
    | .error _ => none
    | .ok log =>
        some (log.final.session.nextSeq, log.final.session.events.length,
          log.final.session.surface.length))
    (some (3, 3, 0))
  assertEqual "mixed replay preserves the core protocol projection"
    (match DeepSeekHarnessMixedReplay.Example.certificate with
    | .error _ => []
    | .ok log => Session.protocolProjection log.final.session.events)
    [.turnStart 1, .stepStart 1 0]
  have _surfaceRejected := DeepSeekHarnessMixedReplay.Example.surface_rejected
  have _staleRejected := DeepSeekHarnessMixedReplay.Example.stale_rejected
  pure ()

private def testDeepSeekHarnessTransportContract : IO Unit := do
  match ← DeepSeekHarnessTransportContract.Example.round with
  | .error error => fail s!"transport contract fixture failed: {reprStr error}"
  | .ok ⟨prepared, ⟨_body, round⟩⟩ =>
      assertEqual "transport contract keeps the successful HTTP status"
        round.response.status 200
      assertEqual "transport contract appends one accepted response"
        round.after.session.nextSeq 1
      assertEqual "transport contract retains the accepted tool call"
        round.accepted.validated.response.choices.head.message.toolCalls.length 1
      have _prepared := prepared.build_eq
      have _body := round.body_eq
      have _validated := DeepSeekHarnessTransportContract.TransportRound.validated_response_eq
        round
      have _accepted := DeepSeekHarnessTransportContract.TransportRound.accepted_response_eq round
      pure ()
  match ← DeepSeekHarnessTransportContract.Example.statusFailure with
  | .error (.httpStatus 503 "busy") => pure ()
  | .error error => fail s!"transport contract status error changed: {reprStr error}"
  | .ok _ => fail "transport contract accepted a 503 response"

private def testDeepSeekHarnessTransportToolRound : IO Unit := do
  match ← DeepSeekHarnessTransportToolRound.Example.round with
  | .error error => fail s!"transport tool-round fixture failed: {reprStr error}"
  | .ok ⟨prepared, ⟨_body, round⟩⟩ =>
      assertEqual "transport tool round keeps the accepted HTTP status"
        round.transportRound.response.status 200
      assertEqual "transport tool round executes one certified tool call"
        round.executions.length 1
      assertEqual "transport tool round preserves the final model"
        round.finalModel 0
      assertEqual "transport tool round advances the session by assistant plus results"
        round.finalRunner.session.nextSeq 2
      assertEqual "transport tool round advances the tool-call counter"
        round.finalRunner.nextCall 1
      have _prepared := prepared.build_eq
      have _messages :=
        DeepSeekHarnessTransportToolRound.ToolTransportRound.finalRunner_messages round
      have _nextSeq :=
        DeepSeekHarnessTransportToolRound.ToolTransportRound.finalRunner_nextSeq round
      pure ()
  match ← DeepSeekHarnessTransportToolRound.Example.statusFailure with
  | .error (.httpStatus 503 "busy") => pure ()
  | .error error => fail s!"transport tool-round status error changed: {reprStr error}"
  | .ok _ => fail "transport tool round accepted a 503 response"

private def testDeepSeekHarnessPersistenceTransportRound : IO Unit := do
  match ← DeepSeekHarnessPersistenceIO.fixtureMemory with
  | .error error => fail s!"persistence transport restore failed: {reprStr error}"
  | .ok restored =>
      let transport : DeepSeekApi.Transport :=
        DeepSeekCurlTransport.fixtureTransport DeepSeekHarness.counterResponseBody
      let result ← (DeepSeekHarnessPersistenceTransportRound.executeRestored
          (Model := Nat) (Capability := Capability) transport
          "https://fixture.invalid" { value := "fixture-key" } restored
          DeepSeekHarnessPersistence.persistedToolSource Cordis.Harness.counterConfig 0
          (sourceEventSeqs := []) (sourcesNodup := by simp) (sourcesEarlier := by simp) :
        IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
          (Sigma fun plan : DeepSeekApi.TypedRequestPlan .complete =>
            Sigma fun body : String =>
              DeepSeekHarnessPersistenceTransportRound.PersistedRound restored
                "https://fixture.invalid" { value := "fixture-key" }
                DeepSeekHarnessPersistence.persistedToolSource restored.restored.runner plan
                (sourceEventSeqs := []) (sourcesNodup := by simp)
                (sourcesEarlier := by simp) body Cordis.Harness.counterConfig 0)))
      let option : Option
          (Sigma fun plan : DeepSeekApi.TypedRequestPlan .complete =>
            Sigma fun body : String =>
              DeepSeekHarnessPersistenceTransportRound.PersistedRound restored
                "https://fixture.invalid" { value := "fixture-key" }
                DeepSeekHarnessPersistence.persistedToolSource restored.restored.runner plan
                (sourceEventSeqs := []) (sourcesNodup := by simp)
                (sourcesEarlier := by simp) body Cordis.Harness.counterConfig 0) :=
        result.toOption
      match option with
      | none => fail "persistence transport round failed"
      | some ⟨plan, ⟨body, round⟩⟩ =>
          assertEqual "persistence transport round preserves the response body"
            body DeepSeekHarness.counterResponseBody
          assertEqual "persistence transport round starts from the byte-backed archive"
            round.round.response.status 200
          assertEqual "persistence transport round executes the retained tool call"
            round.round.executions.length 1
          assertEqual "persistence transport round preserves the tool successor"
            round.round.finalModel 0
          assertEqual "persistence transport round advances archive plus assistant plus tool"
            round.round.finalRunner.session.nextSeq 10
          assertEqual "persistence transport round advances the local call allocator"
            round.round.finalRunner.nextCall 2
          have _read :=
            DeepSeekHarnessPersistenceTransportRound.PersistedRound.read_session restored
              "https://fixture.invalid" { value := "fixture-key" }
              DeepSeekHarnessPersistence.persistedToolSource restored.restored.runner plan
              (cfg := Cordis.Harness.counterConfig) (before := 0) round
          have _plan :=
            DeepSeekHarnessPersistenceTransportRound.PersistedRound.plan_build_archive restored
              "https://fixture.invalid" { value := "fixture-key" }
              DeepSeekHarnessPersistence.persistedToolSource restored.restored.runner plan
              (cfg := Cordis.Harness.counterConfig) (before := 0) round
          have _request :=
            DeepSeekHarnessPersistenceTransportRound.ConversationTransportToolRound.request_body_eq
              "https://fixture.invalid" { value := "fixture-key" }
              DeepSeekHarnessPersistence.persistedToolSource restored.restored.runner plan
              (cfg := Cordis.Harness.counterConfig) (before := 0) round.round
          pure ()

private def testDeepSeekHarnessTransportConversation : IO Unit := do
  let requestBodies ← IO.mkRef ([] : List String)
  let transport : Cordis.DeepSeekApi.Transport := {
    send := fun request => do
      requestBodies.modify (fun bodies => request.body :: bodies)
      let bodies ← requestBodies.get
      pure (.ok {
        status := 200
        body := if bodies.length = 1 then DeepSeekHarness.counterResponseBody
          else DeepSeekHarness.counterFinalResponseBody
      })
  }
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let result ← (DeepSeekHarnessTransportConversation.runTransport
      (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
      (cfg := Cordis.Harness.counterConfig) 2 transport "https://fixture.invalid"
      { value := "fixture-key" } DeepSeekHarness.counterRequestSource [] (by simp)
      (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner :
    IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
      (Sigma fun finalRunner : DeepSeekHarness.ConversationRunner =>
        Sigma fun finalModel : Nat =>
          DeepSeekHarnessTransportConversation.TransportConversationRunResult
            Cordis.Harness.counterConfig "https://fixture.invalid" { value := "fixture-key" }
            DeepSeekHarness.counterRequestSource [] (by simp) (by simp) initialRunner 0
            finalRunner finalModel)))
  let resultOption : Option
      (Sigma fun finalRunner : DeepSeekHarness.ConversationRunner =>
        Sigma fun finalModel : Nat =>
          DeepSeekHarnessTransportConversation.TransportConversationRunResult
            Cordis.Harness.counterConfig "https://fixture.invalid" { value := "fixture-key" }
            DeepSeekHarness.counterRequestSource [] (by simp) (by simp) initialRunner 0
            finalRunner finalModel) := result.toOption
  match resultOption with
  | none => fail "single-decoder transport conversation failed"
  | some ⟨finalRunner, ⟨finalModel, run⟩⟩ =>
      assertEqual "single-decoder conversation retains both typed round endpoints"
        run.trace.length 2
      assertEqual "single-decoder conversation preserves the final model" finalModel 0
      assertEqual "single-decoder conversation reaches the final session"
        finalRunner.session.nextSeq 4
      assertEqual "single-decoder conversation stops only after the final no-tool response"
        (DeepSeekHarnessTransportConversation.TransportStop.isCompleted run.stop) true
  let calls ← requestBodies.get
  assertEqual "single-decoder conversation makes exactly one request per typed round"
    calls.length 2

  let exhaustedResult ← (DeepSeekHarnessTransportConversation.runTransport
      (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
      (cfg := Cordis.Harness.counterConfig) 1
      (DeepSeekCurlTransport.fixtureTransport DeepSeekHarness.counterResponseBody)
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp)
      (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner :
    IO (Except DeepSeekHarnessPersistenceTransportRound.RoundError
      (Sigma fun finalRunner : DeepSeekHarness.ConversationRunner =>
        Sigma fun finalModel : Nat =>
          DeepSeekHarnessTransportConversation.TransportConversationRunResult
            Cordis.Harness.counterConfig "https://fixture.invalid" { value := "fixture-key" }
            DeepSeekHarness.counterRequestSource [] (by simp) (by simp) initialRunner 0
            finalRunner finalModel)))
  let exhaustedOption : Option
      (Sigma fun finalRunner : DeepSeekHarness.ConversationRunner =>
        Sigma fun finalModel : Nat =>
          DeepSeekHarnessTransportConversation.TransportConversationRunResult
            Cordis.Harness.counterConfig "https://fixture.invalid" { value := "fixture-key" }
            DeepSeekHarness.counterRequestSource [] (by simp) (by simp) initialRunner 0
            finalRunner finalModel) := exhaustedResult.toOption
  match exhaustedOption with
  | none => fail "single-decoder exhaustion fixture failed"
  | some ⟨_, ⟨_, run⟩⟩ =>
      assertEqual "single-decoder exhaustion retains the exact completed prefix"
        run.trace.length 1
      assertEqual "single-decoder exhaustion reports its bounded stop"
        (DeepSeekHarnessTransportConversation.TransportStop.isFuelExhausted run.stop) true

private def testDeepSeekHarnessTransportRetry : IO Unit := do
  let result ← DeepSeekHarnessTransportRetry.Example.retryRound
  match result.toOption with
  | none => fail "single-decoder retry transport fixture failed"
  | some ⟨_plan, ⟨body, round⟩⟩ =>
      assertEqual "single-decoder retry preserves the validated body"
        body DeepSeekHarness.counterResponseBody
      assertEqual "single-decoder retry retains one transient HTTP failure"
        round.retryHistory.failures.length 1
      assertEqual "single-decoder retry performs the initial attempt plus one retry"
        round.retryHistory.attemptCount 2
      assertEqual "single-decoder retry reaches the successful HTTP endpoint"
        round.round.response.status 200
      assertEqual "single-decoder retry executes the accepted tool call"
        round.round.executions.length 1
      assertEqual "single-decoder retry preserves the typed tool successor"
        round.round.finalModel 0
      assertEqual "single-decoder retry advances the session by assistant and tool result"
        round.round.finalRunner.session.nextSeq 2
      assertEqual "single-decoder retry advances the local call allocator"
        round.round.finalRunner.nextCall 1
      have _attemptBound :=
        DeepSeekHarnessTransportRetry.RetriedTransportRound.attemptCount_le_maxAttempts round
      have _finalEndpoint :=
        DeepSeekHarnessTransportRetry.RetriedTransportRound.final_endpoint round
      pure ()

private def testDeepSeekHarnessTransportRetryConversation : IO Unit := do
  let result ← DeepSeekHarnessTransportRetryConversation.Example.retryConversation
  match result.toOption with
  | none => fail "retry-aware transport conversation fixture failed"
  | some ⟨finalRunner, ⟨finalModel, run⟩⟩ =>
      assertEqual "retry-aware conversation records both typed rounds"
        run.trace.length 2
      assertEqual "retry-aware conversation preserves the final model"
        finalModel 0
      assertEqual "retry-aware conversation reaches the final session"
        finalRunner.session.nextSeq 3
      assertEqual "retry-aware conversation stops after the final no-tool response"
        (DeepSeekHarnessTransportRetryConversation.RetryTransportStop.isCompleted run.stop) true
      match run.trace with
      | .cons first (.cons second _) =>
          assertEqual "retry-aware conversation retains the first round retry history"
            first.round.retryHistory.failures.length 1
          assertEqual "retry-aware conversation bounds the first round attempts"
            first.round.retryHistory.attemptCount 2
          assertEqual "retry-aware conversation has no retry on the terminal round"
            second.round.retryHistory.failures.length 0
      | _ => fail "retry-aware conversation returned the wrong trace shape"

private def testDeepSeekSchemaStreamConversation : IO Unit := do
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"stream schema weather certificate failed: {reprStr error}"
  | _, .error error => fail s!"stream schema clock certificate failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekSchemaStreamConversation.Example.dualToolStreamRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"heterogeneous streamed schema run failed: {reprStr error}"
      | .ok result =>
          assertEqual "heterogeneous streamed schema loop records one tool round"
            result.rounds.length 1
          assertEqual "heterogeneous streamed schema loop preserves the final model"
            result.finalModel 0
          assertEqual "heterogeneous streamed schema loop appends assistant and two results"
            result.runner.session.nextSeq
            (DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 3)
          match result.stop with
          | .fuelExhausted _ _ => pure ()
          | .completed _ => fail "heterogeneous streamed schema loop unexpectedly completed"
      match ← DeepSeekSchemaStreamConversation.Example.textTerminalRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"stream text terminal run failed: {reprStr error}"
      | .ok result =>
          assertEqual "stream text terminal run has no tool rounds" result.rounds.length 0
          match result.stop with
          | .completed terminal =>
              assertEqual "stream text terminal run has no parsed tool calls"
                terminal.processed.finished.finished.view.rawToolCalls.length 0
          | .fuelExhausted _ _ => fail "stream text terminal run exhausted before completion"

private def testDeepSeekSchemaStreamPrefixConversation : IO Unit := do
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"prefix schema weather certificate failed: {reprStr error}"
  | _, .error error => fail s!"prefix schema clock certificate failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekSchemaStreamPrefixConversation.Example.dualToolPrefixRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"prefix heterogeneous schema run failed: {reprStr error}"
      | .ok result =>
          assertEqual "prefix heterogeneous schema loop records one tool round"
            result.rounds.length 1
          assertEqual "prefix heterogeneous schema loop preserves the final model"
            result.finalModel 0
          match result.stop with
          | .fuelExhausted _ _ => pure ()
          | .completed _ _ => fail "prefix heterogeneous schema loop unexpectedly completed"
          | .cancelled _ _ _ _ _ _ => fail "prefix schema fuel fixture reported cancellation"
      match ← DeepSeekSchemaStreamPrefixConversation.Example.dualToolPrefixCancelled
          weatherCertificate clockCertificate with
      | .error error => fail s!"prefix cancellation fixture failed: {reprStr error}"
      | .ok result =>
          assertEqual "prefix cancellation retains no completed rounds" result.rounds.length 0
          match result.stop with
          | .cancelled _ _ _ line reason _ =>
              assertEqual "prefix cancellation reports its line" line 1
              assertEqual "prefix cancellation reports its reason" reason "cancelled:prefix"
          | .completed _ _ => fail "prefix cancellation unexpectedly completed"
          | .fuelExhausted _ _ => fail "prefix cancellation unexpectedly exhausted"
      match ← DeepSeekSchemaStreamPrefixConversation.Example.textTerminalPrefixRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"prefix text terminal fixture failed: {reprStr error}"
      | .ok result =>
          assertEqual "prefix text terminal has no tool rounds" result.rounds.length 0
          match result.stop with
          | .completed _ terminal =>
              assertEqual "prefix text terminal has no parsed tool calls"
                terminal.processed.finished.finished.view.rawToolCalls.length 0
          | .fuelExhausted _ _ => fail "prefix text terminal exhausted"
          | .cancelled _ _ _ _ _ _ => fail "prefix text terminal was cancelled"

private def testDeepSeekSchemaStreamErrors : IO Unit := do
  assertEqual "heterogeneous recoverable batch fixture accepts two provider failures"
    DeepSeekSchemaStreamErrors.Example.dualFailureBatchAccepted true
  match DeepSeekToolSchema.weatherToolCertificate,
      DeepSeekSchemaRegistry.Example.clockToolCertificate with
  | .error error, _ => fail s!"recoverable schema weather certificate failed: {reprStr error}"
  | _, .error error => fail s!"recoverable schema clock certificate failed: {reprStr error}"
  | .ok weatherCertificate, .ok clockCertificate =>
      match ← DeepSeekSchemaStreamErrors.Example.dualFailureContinuationRun
          weatherCertificate clockCertificate with
      | .error error => fail s!"recoverable heterogeneous streamed run failed: {reprStr error}"
      | .ok result =>
          assertEqual "recoverable heterogeneous stream retains the failed tool round"
            result.rounds.length 2
          assertEqual "recoverable heterogeneous stream preserves the failed model"
            result.finalModel 0
          assertEqual
            "recoverable stream appends assistant, two errors, then terminal assistant"
            result.runner.session.nextSeq
            (DeepSeekSchemaHarness.Example.counterRunner.session.nextSeq + 4)
          match result.rounds with
          | first :: _ :: [] =>
              match first.result.batch.attempts with
              | .providerFailed _ :: .providerFailed _ :: [] => pure ()
              | _ => fail "recoverable stream did not retain both dependent provider failures"
          | _ => fail "recoverable stream returned an unexpected round history"
          match result.stop with
          | .completed last _ =>
              assertEqual "recoverable stream terminal response has no tool calls"
                last.result.processed.finished.finished.view.rawToolCalls.length 0
          | .fuelExhausted => fail "recoverable stream exhausted before its terminal continuation"

private def testDeepSeekHarnessEventArchive : IO Unit := do
  match DeepSeekHarnessEventArchive.toolRestored with
  | .error error => fail s!"current event archive restoration failed: {error}"
  | .ok restored =>
      assertEqual "current event archive restores the validated sequence endpoint"
        restored.runner.session.nextSeq 8
      assertEqual "current event archive restores the typed surface messages"
        restored.runner.session.messages [
          .user "look up lean",
          .assistant "I will look it up." [{
            id := { value := 0 }
            name := "lookup"
            arguments := "{\"q\":\"lean\"}"
          }],
          .toolResult { value := 0 } "result" false
        ]
      assertEqual "current event archive preserves every raw event in order"
        (restored.log.archive.events.map SessionEventArchive.ArchivedEvent.raw ==
          SessionRefinement.toolMessageExampleJson)
        true
      match DeepSeekHarnessEventArchive.buildRequestCertificate restored
          { model := "deepseek-reasoner", errorToolResults := .reject } with
      | .error error => fail s!"current event archive request construction failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "current event archive request preserves the restored messages"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _buildCertificate := certificate.build_eq
          let _archiveCertificate :=
            DeepSeekHarnessEventArchive.buildRequest_session_eq_archive restored
              { model := "deepseek-reasoner", errorToolResults := .reject }
              certificate.build_eq
          let _supportCertificate := restored.log.supported
          pure ()

private def testDeepSeekHarnessEventText : IO Unit := do
  match DeepSeekHarnessEventText.toolTextRestored with
  | .error error => fail s!"current event text restoration failed: {reprStr error}"
  | .ok restored =>
      assertEqual "current event text restores the validated sequence endpoint"
        restored.restored.runner.session.nextSeq 8
      assertEqual "current event text retains canonical source text"
        (TextRefinement.renderJsonLines restored.validated.parsed.lines)
        DeepSeekHarnessEventText.toolTextSource
      let _sourceCertificate := DeepSeekHarnessEventText.RestoredTextRunner.source_parse_eq restored
      let _sessionCertificate := DeepSeekHarnessEventText.RestoredTextRunner.session_eq restored
      let _archiveCertificate :=
        DeepSeekHarnessEventText.RestoredTextRunner.archive_raw_eq_lines restored
      match DeepSeekHarnessEventText.buildRequestCertificate restored
          { model := "deepseek-reasoner", errorToolResults := .reject } with
      | .error error => fail s!"current event text request construction failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "current event text request preserves restored messages"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _buildCertificate := certificate.build_eq
          pure ()
  match DeepSeekHarnessEventText.toolBytesRestored with
  | .error error => fail s!"current event bytes restoration failed: {reprStr error}"
  | .ok restored =>
      assertEqual "current event bytes retain decoded source text"
        restored.text DeepSeekHarnessEventText.toolTextSource
      assertEqual "current event bytes restore the same session endpoint"
        restored.restored.restored.runner.session.nextSeq 8
      let _decodedCertificate := DeepSeekHarnessEventText.RestoredBytesRunner.decoded_eq restored
  match DeepSeekHarnessEventText.restoreBytesRunner (ByteArray.mk #[255]) 1 1 with
  | .error (.text .invalidUtf8) => pure ()
  | .error error => fail s!"invalid event UTF-8 returned the wrong error: {reprStr error}"
  | .ok _ => fail "invalid event UTF-8 was accepted"

private def testDeepSeekHarnessEventProcessOutcome : IO Unit := do
  match ← DeepSeekHarnessEventProcessOutcome.Example.text with
  | .error error => fail s!"current event process outcome failed: {reprStr error}"
  | .ok body =>
      assertEqual "current event process outcome preserves the fixture body"
        body DeepSeekRichStream.exampleTextStreamBody
  match ← DeepSeekHarnessEventProcessOutcome.Example.bytes with
  | .error error => fail s!"current event byte process outcome failed: {reprStr error}"
  | .ok body =>
      assertEqual "current event byte process outcome preserves the fixture body"
        body DeepSeekRichStream.exampleTextStreamBody
  match ← DeepSeekHarnessEventProcessOutcome.Example.stream with
  | .error error => fail s!"restored streamed conversation failed: {reprStr error}"
  | .ok (rounds, nextSeq, completed) =>
      assertEqual "restored streamed conversation retains one round" rounds 1
      assertEqual "restored streamed conversation appends the tool result" nextSeq 10
      assertEqual "restored streamed conversation distinguishes fuel exhaustion" completed false
  match ← DeepSeekHarnessEventProcessOutcome.Example.bytesStream with
  | .error error => fail s!"restored byte streamed conversation failed: {reprStr error}"
  | .ok (rounds, nextSeq, completed) =>
      assertEqual "restored byte streamed conversation retains one round" rounds 1
      assertEqual "restored byte streamed conversation appends the tool result" nextSeq 10
      assertEqual "restored byte streamed conversation distinguishes fuel exhaustion" completed false

private def testLoaderHMR : IO Unit := do
  assertEqual "loader reconciliation dispatches config-only edits in place"
    (LoaderHMR.changeKind LoaderHMR.Example.entry LoaderHMR.Example.updatedEntry)
    .patchConfig
  assertEqual "loader reconciliation keys a surviving entry by its stable id"
    (LoaderHMR.reconcile [LoaderHMR.Example.entry] [LoaderHMR.Example.updatedEntry])
    [.update LoaderHMR.Example.entry LoaderHMR.Example.updatedEntry .patchConfig]
  assertEqual "HMR classification keeps the stashed module accepted"
    LoaderHMR.Example.classified.accepted ["changed.js"]
  assertEqual "HMR classification declines an unresolved cycle at the fuel boundary"
    LoaderHMR.Example.cycleClassified.declined ["right.js", "left.js"]
  assertEqual "stale-entry detection follows accepted transitive imports"
    LoaderHMR.Example.staleEntries [LoaderHMR.Example.entry]
  assertEqual "declined modules stop stale-entry dependency traversal"
    LoaderHMR.Example.declinedBoundaryEntries []
  assertEqual "transactional HMR success retains the exact ordered phase trace"
    (LoaderHMR.ReloadResult.phaseTrace
      (LoaderHMR.transactionalReload LoaderHMR.Example.loader LoaderHMR.Example.ready 8))
    [.ready, .invalidated, .imported, .disposed, .installed, .committed]
  match LoaderHMR.transactionalReload LoaderHMR.Example.badLoader LoaderHMR.Example.ready 8 with
  | .failure error result =>
      assertEqual "transactional HMR failure restores the old cache and fiber state"
        result.state LoaderHMR.Example.ready
      assertEqual "transactional HMR reports the import failure" error "syntax error"
  | .success _ => fail "transactional HMR failure unexpectedly committed a replacement"

private def testDeepSeekHarnessPayloadText : IO Unit := do
  match DeepSeekHarnessPayloadText.toolPayloadRestored with
  | .error error => fail s!"current payload text restoration failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload text retains the runner endpoint"
        restored.restored.restored.runner.session.nextSeq 8
      assertEqual "payload text retains every archived event"
        restored.payload.events.length 8
      assertEqual "payload text classifies every fixture payload"
        restored.payload.typedCount 8
      let _sessionCertificate :=
        DeepSeekHarnessPayloadText.RestoredPayloadRunner.session_eq restored
      let _rawLines :=
        DeepSeekHarnessPayloadText.RestoredPayloadRunner.payload_raw_eq_lines restored
      let _rawArchive :=
        DeepSeekHarnessPayloadText.RestoredPayloadRunner.payload_raw_exact restored
      match DeepSeekHarnessPayloadText.buildRequestCertificate restored
          { model := "deepseek-reasoner", errorToolResults := .reject } with
      | .error error => fail s!"payload text request construction failed: {reprStr error}"
      | .ok certificate =>
          assertEqual "payload text request uses the restored tool message"
            certificate.request.messages.toList [
              .user "look up lean",
              .assistant (some "I will look it up.") none [{
                id := "0"
                name := "lookup"
                arguments := "{\"q\":\"lean\"}"
              }],
              .tool "0" "result"
            ]
          let _buildCertificate := certificate.build_eq
          pure ()
  match DeepSeekHarnessPayloadText.toolPayloadBytesRestored with
  | .error error => fail s!"current payload bytes restoration failed: {reprStr error}"
  | .ok restored =>
      assertEqual "payload bytes retain decoded text"
        restored.text DeepSeekHarnessPayloadText.toolPayloadTextSource
      assertEqual "payload bytes retain the runner endpoint"
        restored.restored.restored.restored.runner.session.nextSeq 8
      let _decoded := DeepSeekHarnessPayloadText.RestoredBytesPayloadRunner.decoded_eq restored
      pure ()
  match DeepSeekHarnessPayloadText.restoreBytesPayloadRunner (ByteArray.mk #[255]) 1 1 with
  | .error (.restore (.text .invalidUtf8)) => pure ()
  | .error error => fail s!"invalid payload UTF-8 returned the wrong error: {reprStr error}"
  | .ok _ => fail "invalid payload UTF-8 was accepted"

private def testDeepSeekStreamHarness : IO Unit := do
  let process := DeepSeekStreamHarness.streamFlagFixtureProcess
    DeepSeekStreamHarness.counterToolStreamBody
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let streamResult :
      Except DeepSeekStreamHarness.StreamConversationError
        (Sigma fun body : String =>
          DeepSeekStreamHarness.StreamConversationRoundResult
            (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
            Cordis.Harness.counterConfig 0 body) ←
    DeepSeekStreamHarness.executeConversationStreamRound
      DeepSeekSessionRunner.finishTool process "https://fixture.invalid"
      { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      Cordis.Harness.counterConfig 0 initialRunner [] (by simp) (by simp)
  match streamResult with
  | .error error => fail s!"DeepSeek stream harness round failed: {reprStr error}"
  | .ok ⟨body, result⟩ =>
      assertEqual "DeepSeek stream harness preserves the complete SSE body"
        body DeepSeekStreamHarness.counterToolStreamBody
      assertEqual "DeepSeek stream harness appends the streamed assistant call"
        result.assistantRunner.session.messages [
          .user "Read the counter.",
          .assistant "" [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }]
        ]
      assertEqual "DeepSeek stream harness executes the streamed dependent call"
        result.finalModel 0
      assertEqual "DeepSeek stream harness appends the certified tool result"
        result.runner.session.messages [
          .user "Read the counter.",
          .assistant "" [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "[true,0]" false
        ]
      assertEqual "DeepSeek stream harness advances through assistant and tool events"
        result.runner.session.nextSeq 3
      match result.executions with
      | [executed] =>
          assertEqual "DeepSeek stream harness retains the streamed tool name"
            executed.raw.name "counter_read"
          assertEqual "DeepSeek stream harness retains the streamed tool successor"
            executed.reply.value.after 0
          let _resultCertificate := DeepSeekHarness.executedToolResultJson_decodes executed
          pure ()
      | executions =>
          fail s!"DeepSeek stream harness returned {executions.length} tool executions"

  let multiProcess : Cordis.DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #[
      "-c",
      "cat >/dev/null; printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\"",
      "cordis-stream-counter-multi-fixture",
      DeepSeekStreamHarness.counterMultiToolStreamBody
    ]
  }
  let multiResult :
      Except DeepSeekStreamHarness.StreamConversationError
        (Sigma fun body : String =>
          DeepSeekStreamHarness.StreamConversationRoundResult
            (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
            Cordis.Harness.counterConfig 0 body) ←
    DeepSeekStreamHarness.executeConversationMultiStreamRound
      multiProcess "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 0 initialRunner []
      (by simp) (by simp)
  match multiResult with
  | .error error => fail s!"DeepSeek multi-stream harness round failed: {reprStr error}"
  | .ok ⟨body, result⟩ =>
      assertEqual "DeepSeek multi-stream harness preserves the complete SSE body"
        body DeepSeekStreamHarness.counterMultiToolStreamBody
      assertEqual "DeepSeek multi-stream harness allocates both local call IDs"
        result.assistantRunner.session.messages [
          .user "Read the counter.",
          .assistant "" [
            { id := { value := 0 }, name := "counter_read", arguments := "null" },
            { id := { value := 1 }, name := "counter_read", arguments := "null" }
          ]
        ]
      assertEqual "DeepSeek multi-stream harness executes both dependent calls"
        result.finalModel 0
      assertEqual "DeepSeek multi-stream harness appends both certified results"
        result.runner.session.messages [
          .user "Read the counter.",
          .assistant "" [
            { id := { value := 0 }, name := "counter_read", arguments := "null" },
            { id := { value := 1 }, name := "counter_read", arguments := "null" }
          ],
          .toolResult { value := 0 } "[true,0]" false,
          .toolResult { value := 1 } "[true,0]" false
        ]
      assertEqual "DeepSeek multi-stream harness advances through all tool events"
        result.runner.session.nextSeq 4
      match result.executions with
      | [first, second] =>
          assertEqual "DeepSeek multi-stream harness retains first tool name"
            first.raw.name "counter_read"
          assertEqual "DeepSeek multi-stream harness retains second tool name"
            second.raw.name "counter_read"
          let _firstCertificate := DeepSeekHarness.executedToolResultJson_decodes first
          let _secondCertificate := DeepSeekHarness.executedToolResultJson_decodes second
          pure ()
      | executions =>
          fail s!"DeepSeek multi-stream harness returned {executions.length} tool executions"

  let streamLoopProcess : Cordis.DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #[
      "-c",
      "body=$(cat); case \"$body\" in " ++
        "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
        "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
      "cordis-stream-loop-fixture",
      DeepSeekStreamHarness.counterMultiToolStreamBody,
      DeepSeekRichStream.exampleTextStreamBody
    ]
  }
  let streamLoopResult :
      Except DeepSeekStreamHarness.StreamConversationError
        (DeepSeekStreamHarness.StreamConversationRunResult
          (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
          Cordis.Harness.counterConfig) ←
    DeepSeekStreamHarness.runConversationMultiStream 2 streamLoopProcess
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner
  match streamLoopResult with
  | .error error => fail s!"DeepSeek streamed conversation loop failed: {reprStr error}"
  | .ok result =>
      assertEqual "DeepSeek streamed conversation loop retains both round witnesses"
        result.rounds.length 2
      assertEqual "DeepSeek streamed conversation loop preserves the final model"
        result.finalModel 0
      assertEqual "DeepSeek streamed conversation loop appends the text terminal round"
        result.runner.session.messages [
          .user "Read the counter.",
          .assistant "" [
            { id := { value := 0 }, name := "counter_read", arguments := "null" },
            { id := { value := 1 }, name := "counter_read", arguments := "null" }
          ],
          .toolResult { value := 0 } "[true,0]" false,
          .toolResult { value := 1 } "[true,0]" false,
          .assistant "Hello world" []
        ]
      assertEqual "DeepSeek streamed conversation loop reports completion"
        (DeepSeekStreamHarness.StreamConversationStop.isCompleted result.stop) true
  let streamLoopExhausted :
      Except DeepSeekStreamHarness.StreamConversationError
        (DeepSeekStreamHarness.StreamConversationRunResult
          (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
          Cordis.Harness.counterConfig) ←
    DeepSeekStreamHarness.runConversationMultiStream 1 streamLoopProcess
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner
  match streamLoopExhausted with
  | .error error => fail s!"DeepSeek streamed loop exhaustion failed: {reprStr error}"
  | .ok result =>
      assertEqual "DeepSeek streamed loop exhaustion retains the completed tool prefix"
        result.runner.session.nextSeq 4
      assertEqual "DeepSeek streamed loop exhaustion is distinct from completion"
        (DeepSeekStreamHarness.StreamConversationStop.isCompleted result.stop) false

private def testDeepSeekStreamHarnessByte : IO Unit := do
  let process := DeepSeekStreamHarness.streamFlagFixtureProcess
    DeepSeekStreamHarness.counterToolStreamBody
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let roundResult ← DeepSeekStreamHarnessByte.executeConversationByteStreamRound
    DeepSeekSessionRunner.finishTool 4096 2 process "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource
    Cordis.Harness.counterConfig 0 initialRunner [] (by simp) (by simp)
  match roundResult with
  | .error _ => fail "byte-backed streamed Harness round failed"
  | .ok ⟨body, result⟩ =>
      assertEqual "byte-backed Harness preserves the decoded SSE body"
        body DeepSeekStreamHarness.counterToolStreamBody
      assertEqual "byte-backed Harness retains multiple stdout chunks"
        (decide (result.observed.chunks.length > 1)) true
      assertEqual "byte-backed Harness retains the exact framed body"
        result.observed.framed.text body
      let _rawChunks := result.observed.raw_chunks_eq
      let _bodyChunks := result.observed.body_chunks_eq
      let _wireExact := DeepSeekCurlByteFraming.ByteChunkResponse.validateSseBytes_exact
        result.observed
      assertEqual "byte-backed Harness executes the streamed dependent call"
        result.round.finalModel 0
      assertEqual "byte-backed Harness appends the certified tool result"
        result.round.runner.session.nextSeq 3

  let loopProcess : Cordis.DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #[
      "-c",
      "body=$(cat); case \"$body\" in " ++
        "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
        "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
      "cordis-byte-stream-loop-fixture",
      DeepSeekStreamHarness.counterMultiToolStreamBody,
      DeepSeekRichStream.exampleTextStreamBody
    ]
  }
  let loopResult :
      Except DeepSeekStreamHarnessByte.ByteStreamConversationError
        (DeepSeekStreamHarnessByte.ByteStreamConversationRunResult
          (Model := Nat) (Capability := Cordis.Examples.Counter.Capability)
          Cordis.Harness.counterConfig) ←
    DeepSeekStreamHarnessByte.runConversationMultiByteStream 2 4096 3 loopProcess
    "https://fixture.invalid" { value := "fixture-key" }
    DeepSeekHarness.counterRequestSource [] (by simp) (by
      intro current source sourceMem
      cases sourceMem) 0 initialRunner
  match loopResult with
  | .error _ => fail "byte-backed streamed Harness loop failed"
  | .ok result =>
      assertEqual "byte-backed Harness loop retains both round witnesses"
        result.rounds.length 2
      assertEqual "byte-backed Harness loop preserves the final model"
        result.finalModel 0
      assertEqual "byte-backed Harness loop reports completion"
        (DeepSeekStreamHarnessByte.ByteStreamConversationStop.isCompleted result.stop) true

private def testDeepSeekStreamHarnessBytePrefix : IO Unit := do
  let process := DeepSeekStreamHarness.streamFlagFixtureProcess
    DeepSeekStreamHarness.counterToolStreamBody
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let roundResult ← DeepSeekStreamHarnessBytePrefix.executeConversationBytePrefixRound
    DeepSeekSessionRunner.finishTool 4096 1 process "https://fixture.invalid"
    { value := "fixture-key" } DeepSeekHarness.counterRequestSource
    Cordis.Harness.counterConfig 0 initialRunner [] (by simp) (by simp)
  match roundResult with
  | .error _ => fail "byte-prefix Harness round failed"
  | .ok ⟨body, result⟩ =>
      assertEqual "byte-prefix Harness preserves the decoded body"
        body DeepSeekStreamHarness.counterToolStreamBody
      assertEqual "byte-prefix Harness retains many process chunks"
        (decide (result.observed.rawChunks.length > 1)) true
      assertEqual "byte-prefix Harness executes the dependent tool"
        result.round.finalModel 0
      assertEqual "byte-prefix Harness appends the certified result"
        result.round.runner.session.nextSeq 3
      match result.observed.stop with
      | .completed stream =>
          assertEqual "byte-prefix Harness completion retains the exact body"
            stream.text body
      | .fuelExhausted => fail "byte-prefix Harness round exhausted"
      | .cancelled _ _ _ => fail "byte-prefix Harness round cancelled"

  let loopProcess : Cordis.DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #[
      "-c",
      "body=$(cat); case \"$body\" in " ++
        "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
        "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
      "cordis-byte-prefix-loop-fixture",
      DeepSeekStreamHarness.counterMultiToolStreamBody,
      DeepSeekRichStream.exampleTextStreamBody
    ]
  }
  let loopResult :
      Except DeepSeekStreamHarnessBytePrefix.BytePrefixConversationError
        (DeepSeekStreamHarnessBytePrefix.BytePrefixConversationRunResult
          Cordis.Harness.counterConfig) ←
    DeepSeekStreamHarnessBytePrefix.runConversationMultiBytePrefix 2 4096 1
    loopProcess "https://fixture.invalid" { value := "fixture-key" }
    DeepSeekHarness.counterRequestSource [] (by simp) (by
      intro current source sourceMem
      cases sourceMem) 0 initialRunner
  match loopResult with
  | .error _ => fail "byte-prefix Harness loop failed"
  | .ok result =>
      assertEqual "byte-prefix Harness loop retains both round witnesses"
        result.rounds.length 2
      assertEqual "byte-prefix Harness loop preserves the final model"
        result.finalModel 0
      assertEqual "byte-prefix Harness loop reports completion"
        (DeepSeekStreamHarnessBytePrefix.BytePrefixConversationStop.isCompleted result.stop) true

private def testDeepSeekStreamHarnessCancellation : IO Unit := do
  let streamLoopProcess : Cordis.DeepSeekCurlTransport.ProcessConfig := {
    command := "sh"
    args := fun _ => #[
      "-c",
      "body=$(cat); case \"$body\" in " ++
        "*tool_calls*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$2\" ;; " ++
        "*) printf '%s\\n__CORDIS_HTTP_STATUS__200\\n' \"$1\" ;; esac",
      "cordis-stream-cancellation-fixture",
      DeepSeekStreamHarness.counterMultiToolStreamBody,
      DeepSeekRichStream.exampleTextStreamBody
    ]
  }
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let beforePolicy := DeepSeekHarnessCancellation.CancellationPolicy.atRound 0 .user
  match ← DeepSeekStreamHarnessCancellation.runConversationMultiStreamCancellable
      (cfg := Cordis.Harness.counterConfig) beforePolicy 2 streamLoopProcess
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error error => fail s!"stream pre-round cancellation failed: {reprStr error}"
  | .ok result =>
      assertEqual "stream pre-round cancellation retains no round history"
        result.rounds.length 0
      assertEqual "stream pre-round cancellation preserves the runner"
        result.runner.session.nextSeq initialRunner.session.nextSeq
      assertEqual "stream pre-round cancellation preserves the model"
        result.finalModel 0
      assertEqual "stream pre-round cancellation reports cancellation"
        (DeepSeekStreamHarnessCancellation.CancellableStop.isCancelled result.stop) true
      assertEqual "stream pre-round cancellation records its round"
        (DeepSeekStreamHarnessCancellation.CancellableStop.cancelledRound result.stop) (some 0)
      assertEqual "stream pre-round cancellation records its reason"
        (DeepSeekStreamHarnessCancellation.CancellableStop.cancelledReason result.stop) (some .user)

  let betweenPolicy := DeepSeekHarnessCancellation.CancellationPolicy.atRound 1 .timeout
  match ← DeepSeekStreamHarnessCancellation.runConversationMultiStreamCancellable
      (cfg := Cordis.Harness.counterConfig) betweenPolicy 2 streamLoopProcess
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error error => fail s!"stream between-round cancellation failed: {reprStr error}"
  | .ok result =>
      assertEqual "stream between-round cancellation retains the completed tool round"
        result.rounds.length 1
      assertEqual "stream between-round cancellation preserves the tool prefix"
        result.runner.session.nextSeq 4
      assertEqual "stream between-round cancellation reports cancellation"
        (DeepSeekStreamHarnessCancellation.CancellableStop.isCancelled result.stop) true
      assertEqual "stream between-round cancellation records its round"
        (DeepSeekStreamHarnessCancellation.CancellableStop.cancelledRound result.stop) (some 1)
      assertEqual "stream between-round cancellation records its reason"
        (DeepSeekStreamHarnessCancellation.CancellableStop.cancelledReason result.stop)
        (some .timeout)

  let neverPolicy := DeepSeekHarnessCancellation.CancellationPolicy.never .user
  match ← DeepSeekStreamHarnessCancellation.runConversationMultiStreamCancellable
      (cfg := Cordis.Harness.counterConfig) neverPolicy 2 streamLoopProcess
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error error => fail s!"stream completion policy failed: {reprStr error}"
  | .ok result =>
      assertEqual "stream cancellation wrapper retains both completed witnesses"
        result.rounds.length 2
      assertEqual "stream cancellation wrapper reports completion"
        (DeepSeekStreamHarnessCancellation.CancellableStop.isCancelled result.stop) false
      assertEqual "stream cancellation wrapper reports no fuel exhaustion"
        (DeepSeekStreamHarnessCancellation.CancellableStop.isFuelExhausted result.stop) false

private def testDeepSeekStreamHarnessPrefix : IO Unit := do
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let linePolicy := Cordis.DeepSeekStreamIncremental.LinePolicy.atLine 1 "line:user"
  let cancelled ← DeepSeekStreamHarnessPrefix.executeConversationMultiStreamPrefixRound
    linePolicy 64 DeepSeekStreamHarnessPrefix.fixtureMultiProcess
    "https://fixture.invalid" { value := "fixture-key" }
    DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 0 initialRunner []
    (by simp) (by intro source sourceMem; cases sourceMem)
  match cancelled with
  | .error error => fail s!"DeepSeek prefix cancellation failed: {reprStr error}"
  | .ok outcome =>
      assertEqual "DeepSeek prefix cancellation reports cancellation"
        (DeepSeekStreamHarnessPrefix.PrefixStreamRoundOutcome.isCancelled outcome) true
      assertEqual "DeepSeek prefix cancellation records line"
        (DeepSeekStreamHarnessPrefix.PrefixStreamRoundOutcome.cancelledLine outcome) (some 1)
      match outcome with
      | .cancelled observed line reason decided =>
          assertEqual "DeepSeek prefix cancellation retains one parsed line"
            observed.state.line 1
          assertEqual "DeepSeek prefix cancellation retains one parsed frame"
            observed.state.frames.length 1
          assertEqual "DeepSeek prefix cancellation preserves line and reason"
            (line, reason) (1, "line:user")
          let _ := decided
      | _ => fail "DeepSeek prefix cancellation returned the wrong stop"

  let completed ← DeepSeekStreamHarnessPrefix.executeConversationMultiStreamPrefixRound
    Cordis.DeepSeekStreamIncremental.LinePolicy.never 64
    DeepSeekStreamHarnessPrefix.fixtureMultiProcess
    "https://fixture.invalid" { value := "fixture-key" }
    DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 0 initialRunner []
    (by simp) (by intro source sourceMem; cases sourceMem)
  match completed with
  | .error error => fail s!"DeepSeek prefix completion failed: {reprStr error}"
  | .ok outcome =>
      assertEqual "DeepSeek prefix completion reports completion"
        (DeepSeekStreamHarnessPrefix.PrefixStreamRoundOutcome.isCompleted outcome) true
      match outcome with
      | .completed observed _ round =>
          assertEqual "DeepSeek prefix completion retains all body lines"
            observed.state.line 7
          assertEqual "DeepSeek prefix completion appends both streamed tools"
            round.executions.length 2
          assertEqual "DeepSeek prefix completion advances the session"
            round.runner.session.nextSeq 4
      | _ => fail "DeepSeek prefix completion returned the wrong stop"

  let exhausted ← DeepSeekStreamHarnessPrefix.executeConversationMultiStreamPrefixRound
    Cordis.DeepSeekStreamIncremental.LinePolicy.never 1
    DeepSeekStreamHarnessPrefix.fixtureMultiProcess
    "https://fixture.invalid" { value := "fixture-key" }
    DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 0 initialRunner []
    (by simp) (by intro source sourceMem; cases sourceMem)
  match exhausted with
  | .error error => fail s!"DeepSeek prefix fuel stop failed: {reprStr error}"
  | .ok outcome =>
      assertEqual "DeepSeek prefix fuel stop is distinct from completion"
        (DeepSeekStreamHarnessPrefix.PrefixStreamRoundOutcome.isFuelExhausted outcome) true
      match outcome with
      | .fuelExhausted observed =>
          assertEqual "DeepSeek prefix fuel stop retains the first line"
            observed.state.line 1
      | _ => fail "DeepSeek prefix fuel stop returned the wrong stop"

private def failingProvider (operation : Operation) :
    Provider catalog.signature operation where
  id := providerId operation
  handle := fun _ => .error "deterministic provider failure"

private def failingRegistry : Registry catalog.signature
  | .read => some (failingProvider .read)
  | .increment => some (failingProvider .increment)

private def failingView : View catalog.signature failingRegistry needs where
  resolve operation _ := by
    cases operation <;> exact { provider := failingProvider _, present := rfl }

private def failingCounterConfig : GenericHarness.Config Nat Capability where
  catalog := catalog
  wire := wire
  needs := needs
  needsDecidable := fun _ => isTrue trivial
  registry := failingRegistry
  view := failingView
  granted := fun _ _ _ => True
  grantedDecidable := fun _ _ _ => isTrue trivial
  PolicyRejected := fun _ => String
  renderPolicyRejected := fun _ reason => reason
  decide := fun _ _ _ => .allow

private def testDeepSeekHarnessErrors : IO Unit := do
  let raw : DeepSeekApi.FunctionCall := {
    id := "failing-counter-read"
    name := "counter_read"
    arguments := "null"
  }
  match DeepSeekHarnessErrors.executeFunctionCallRecoverable failingCounterConfig 0 raw with
  | .error error => fail s!"recoverable provider call rejected: {reprStr error}"
  | .ok (.providerFailed failed) =>
      assertEqual "recoverable provider failure retains the model"
        failed.before 0
      assertEqual "recoverable provider failure retains the typed message"
        failed.message "deterministic provider failure"
      let session := DeepSeekHarnessErrors.appendProviderFailedToolResult
        DeepSeekHarness.counterSession 1 0 { value := 0 } 0 failed (by decide)
      assertEqual "recoverable provider failure appends an error tool result"
        session.messages [
          .user "Read the counter.",
          .toolResult { value := 0 } "deterministic provider failure" true
        ]
      let _messageCertificate :=
        DeepSeekHarnessErrors.appendProviderFailedToolResult_messages
          DeepSeekHarness.counterSession 1 0 { value := 0 } 0 failed (by decide)
      pure ()
  | .ok (.succeeded _) => fail "recoverable provider fixture unexpectedly succeeded"

  let source : DeepSeekHarness.RequestSource := {
    DeepSeekHarness.counterRequestSource with
    errorToolResults := .include
  }
  let transport : DeepSeekApi.Transport := {
    send := fun request => do
      let body := if request.body.contains "deterministic provider failure" then
          DeepSeekHarness.counterFinalResponseBody
        else
          DeepSeekHarness.counterResponseBody
      pure (.ok { status := 200, body })
  }
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  match ← DeepSeekHarnessErrors.executeConversationRoundRecoverable transport
      "https://fixture.invalid" { value := "fixture-key" } source failingCounterConfig 0
      initialRunner [] (by simp) (by simp) with
  | .error error => fail s!"recoverable conversation round failed: {reprStr error}"
  | .ok ⟨firstBody, first⟩ =>
      assertEqual "recoverable round preserves the provider response body"
        firstBody DeepSeekHarness.counterResponseBody
      assertEqual "recoverable round keeps the provider-failed model stable"
        first.finalModel 0
      assertEqual "recoverable round exposes the error tool result"
        first.runner.session.messages [
          .user "Read the counter.",
          .assistant "I will read the counter." [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "deterministic provider failure" true
        ]
      match first.attempts with
      | [.providerFailed failed] =>
          assertEqual "recoverable round retains the provider failure text"
            failed.message "deterministic provider failure"
      | attempts => fail s!"recoverable round returned {attempts.length} attempts"
      match ← DeepSeekHarnessErrors.executeConversationRoundRecoverable transport
          "https://fixture.invalid" { value := "fixture-key" } source failingCounterConfig
          first.finalModel first.runner [] (by simp) (by simp) with
      | .error error => fail s!"recoverable continuation request failed: {reprStr error}"
      | .ok ⟨secondBody, second⟩ =>
          assertEqual "recoverable continuation accepts the opted-in error result"
            secondBody DeepSeekHarness.counterFinalResponseBody
          assertEqual "recoverable continuation appends the final assistant message"
            second.runner.session.messages [
              .user "Read the counter.",
              .assistant "I will read the counter." [{
                id := { value := 0 }, name := "counter_read", arguments := "null"
              }],
              .toolResult { value := 0 } "deterministic provider failure" true,
              .assistant "The counter is 0." []
            ]

      pure ()

private def testDeepSeekStreamHarnessErrors : IO Unit := do
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  match ← DeepSeekStreamHarnessErrors.executeConversationMultiStreamRoundRecoverable
      DeepSeekStreamHarnessErrors.fixtureFailureProcess
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource failingCounterConfig 0 initialRunner []
      (by simp) (by simp) with
  | .error error => fail s!"stream recoverable round failed: {reprStr error}"
  | .ok ⟨body, result⟩ =>
      assertEqual "stream recoverable round preserves the complete body"
        body DeepSeekStreamHarness.counterToolStreamBody
      assertEqual "stream recoverable round preserves the failed model"
        result.finalModel 0
      assertEqual "stream recoverable round appends an error tool result"
        result.runner.session.messages [
          .user "Read the counter.",
          .assistant "" [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "deterministic provider failure" true
        ]
      assertEqual "stream recoverable round advances assistant and tool events"
        result.runner.session.nextSeq 3
      match result.attempts with
      | [.providerFailed failed] =>
          assertEqual "stream recoverable round retains the typed failure"
            failed.message "deterministic provider failure"
          assertEqual "stream recoverable round retains the failed model witness"
            failed.before 0
      | attempts => fail s!"stream recoverable round returned {attempts.length} attempts"
      let _attemptCertificate := result.attempts_eq
      pure ()

private def testDeepSeekStreamHarnessErrorsLoop : IO Unit := do
  let source : DeepSeekHarness.RequestSource := {
    DeepSeekHarness.counterRequestSource with
    errorToolResults := .include
  }
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  match ← DeepSeekStreamHarnessErrors.runConversationMultiStreamRecoverable
      (cfg := failingCounterConfig) 2
      DeepSeekStreamHarnessErrors.fixtureRecoverableProcess
      "https://fixture.invalid" { value := "fixture-key" } source [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error error => fail s!"stream recoverable loop failed: {reprStr error}"
  | .ok result =>
      assertEqual "stream recoverable loop retains both round witnesses"
        result.rounds.length 2
      assertEqual "stream recoverable loop preserves the model after failure"
        result.finalModel 0
      assertEqual "stream recoverable loop appends the error then terminal assistant"
        result.runner.session.messages [
          .user "Read the counter.",
          .assistant "" [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "deterministic provider failure" true,
          .assistant "Hello world" []
        ]
      assertEqual "stream recoverable loop reports terminal completion"
        (DeepSeekStreamHarnessErrors.StreamRecoverableConversationStop.isCompleted result.stop)
        true
      match result.rounds with
      | [⟨_, ⟨firstBody, first⟩⟩, ⟨_, ⟨secondBody, second⟩⟩] =>
          assertEqual "stream recoverable loop retains the failed tool body"
            firstBody DeepSeekStreamHarness.counterToolStreamBody
          assertEqual "stream recoverable loop retains the terminal text body"
            secondBody DeepSeekRichStream.exampleTextStreamBody
          match first.attempts, second.attempts with
          | [.providerFailed failed], [] =>
              assertEqual "stream recoverable loop keeps the provider error text"
                failed.message "deterministic provider failure"
          | firstAttempts, secondAttempts =>
              fail s!"unexpected streamed recoverable attempts: {firstAttempts.length},
                {secondAttempts.length}"
      | rounds => fail s!"stream recoverable loop returned {rounds.length} rounds"
      pure ()

private def testDeepSeekHarnessRetry : IO Unit := do
  let plan ←
    match DeepSeekHarness.counterPlan with
    | .error error => fail s!"retry fixture request plan failed: {reprStr error}"
    | .ok plan => pure plan
  let bodies ← IO.mkRef ([] : List String)
  let retryTransport : DeepSeekApi.Transport := {
    send := fun request => do
      bodies.modify (fun previous => previous ++ [request.body])
      let seen ← bodies.get
      if seen.length = 1 then
        pure (.error "transient transport")
      else
        pure (.ok { status := 200, body := DeepSeekHarness.counterResponseBody })
  }
  let policy : DeepSeekHarnessRetry.RetryPolicy := {
    maxRetries := 1
    retryTransport := true
    retryTransientHttp := true
  }
  assertEqual "retry policy admits transport failures"
    (policy.retryable (.transport "offline")) true
  assertEqual "retry policy admits transient server failures"
    (policy.retryable (.httpStatus 503 "busy")) true
  assertEqual "retry policy rejects ordinary HTTP failures"
    (policy.retryable (.httpStatus 401 "unauthorized")) false
  assertEqual "retry policy rejects decoded provider response errors"
    (policy.retryable (.response (.invalidJson "bad"))) false
  match ← DeepSeekHarnessRetry.executeWithRetry policy retryTransport plan with
  | .failed history error =>
      fail (s!"retry fixture unexpectedly terminated: {reprStr error}; history " ++
        reprStr history.failures)
  | .succeeded history ⟨body, validated⟩ =>
      assertEqual "retry fixture preserves the validated response body"
        body DeepSeekHarness.counterResponseBody
      assertEqual "retry fixture retains the transient failure history"
        history.failures [.transport "transient transport"]
      assertEqual "retry fixture makes the initial attempt plus one retry"
        (DeepSeekHarnessRetry.RetryHistory.attemptCount history) 2
      assertEqual "retry fixture accepts the tool-call response"
        validated.response.choices.head.message.toolCalls.length 1
      let bodySnapshot ← bodies.get
      assertEqual "retry fixture sends the exact same request body on every attempt"
        bodySnapshot [plan.request.body, plan.request.body]
      let _bodyCertificate := DeepSeekHarnessRetry.retryPlan_body_eq plan

  let statusBodies ← IO.mkRef ([] : List String)
  let statusTransport : DeepSeekApi.Transport := {
    send := fun request => do
      statusBodies.modify (fun previous => previous ++ [request.body])
      pure (.ok { status := 401, body := "unauthorized" })
  }
  match ← DeepSeekHarnessRetry.executeWithRetry {
      maxRetries := 3
      retryTransport := true
      retryTransientHttp := true
    } statusTransport plan with
  | .succeeded _ _ => fail "non-retryable HTTP status unexpectedly succeeded"
  | .failed history (.httpStatus 401 body) =>
      assertEqual "non-retryable HTTP status preserves its body" body "unauthorized"
      assertEqual "non-retryable HTTP status does not consume retries" history.failures []
      let statusSnapshot ← statusBodies.get
      assertEqual "non-retryable HTTP status makes one request" statusSnapshot.length 1
  | .failed _ error => fail s!"wrong terminal retry error: {reprStr error}"

  let exhaustedBodies ← IO.mkRef ([] : List String)
  let exhaustedTransport : DeepSeekApi.Transport := {
    send := fun request => do
      exhaustedBodies.modify (fun previous => previous ++ [request.body])
      pure (.error "still offline")
  }
  match ← DeepSeekHarnessRetry.executeWithRetry policy exhaustedTransport plan with
  | .succeeded _ _ => fail "retry budget fixture unexpectedly succeeded"
  | .failed history (.transport message) =>
      assertEqual "retry budget fixture preserves its terminal transport message"
        message "still offline"
      assertEqual "retry budget fixture retains only the earlier retryable failure"
        history.failures [.transport "still offline"]
      assertEqual "retry budget fixture performs exactly the bounded attempts"
        (DeepSeekHarnessRetry.RetryHistory.attemptCount history) 2
      let _boundCertificate :=
        DeepSeekHarnessRetry.RetryHistory.attemptCount_le_maxAttempts history
      let exhaustedSnapshot ← exhaustedBodies.get
      assertEqual "retry budget fixture stops at maxRetries plus one"
        exhaustedSnapshot.length 2
  | .failed _ error => fail s!"wrong retry budget error: {reprStr error}"

  let conversationBodies ← IO.mkRef ([] : List String)
  let conversationTransport : DeepSeekApi.Transport := {
    send := fun request => do
      conversationBodies.modify (fun previous => previous ++ [request.body])
      let seen ← conversationBodies.get
      if seen.length = 1 then
        pure (.error "one transient conversation failure")
      else
        pure (.ok { status := 200, body := DeepSeekHarness.counterResponseBody })
  }
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  match ← DeepSeekHarnessRetry.executeConversationRoundRetry policy conversationTransport
      "https://fixture.invalid" { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      Cordis.Harness.counterConfig 0 initialRunner [] (by simp) (by simp) with
  | .error (.client history error) =>
      fail s!"retrying conversation terminated: {reprStr error}; history {reprStr history.failures}"
  | .error _ => fail "retrying conversation failed outside the client boundary"
  | .ok ⟨body, round⟩ =>
      assertEqual "retrying conversation preserves the accepted body"
        body DeepSeekHarness.counterResponseBody
      assertEqual "retrying conversation exposes its retry history"
        round.retryHistory.failures [.transport "one transient conversation failure"]
      assertEqual "retrying conversation preserves the tool successor"
        round.finalModel 0
      assertEqual "retrying conversation appends the assistant and tool result"
        round.runner.session.messages [
          .user "Read the counter.",
          .assistant "I will read the counter." [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "[true,0]" false
        ]
      let conversationSnapshot ← conversationBodies.get
      assertEqual "retrying conversation sends one repeated plan body"
        conversationSnapshot [plan.request.body, plan.request.body]

private def testDeepSeekStreamHarnessRetry : IO Unit := do
  let policy : DeepSeekStreamHarnessRetry.RetryPolicy := {
    maxRetries := 1
    retryProcess := true
    retryTransientHttp := true
  }
  assertEqual "stream retry policy admits process failures"
    (policy.retryable (.transport (.process (.spawn "offline")))) true
  assertEqual "stream retry policy admits transient HTTP failures"
    (policy.retryable (.transport (.httpStatus 503 "busy"))) true
  assertEqual "stream retry policy rejects stream framing failures"
    (policy.retryable (.transport (.stream .missingDone))) false
  assertEqual "stream retry policy rejects semantic response failures"
    (policy.retryable (.response (.terminal .notTerminal))) false

  let attempts ← IO.mkRef 0
  let attempt : IO (Except Cordis.DeepSeekCurlSession.SessionClientError
      DeepSeekStreamHarnessRetry.ProcessedStreamResponse) := do
    let seen ← attempts.get
    attempts.set (seen + 1)
    if seen = 0 then
      pure (.error (.transport (.httpStatus 503 "temporary")))
    else
      DeepSeekCurlSession.executeWith DeepSeekSessionRunner.finishMulti
        (DeepSeekStreamHarnessRetry.fixtureStreamProcess
          DeepSeekStreamHarness.counterToolStreamBody)
        DeepSeekCurlTransport.fixtureRequest.request
  let initialHistory : DeepSeekStreamHarnessRetry.RetryHistory policy := {
    failures := []
    failures_le := by simp
  }
  match ← DeepSeekStreamHarnessRetry.executeWithRetryAux policy attempt 1 initialHistory
      (by simp [initialHistory, policy]) with
  | .failed history error => fail s!"stream retry unexpectedly failed: {reprStr error}"
  | .succeeded history ⟨body, processed⟩ =>
      assertEqual "stream retry preserves the terminal streamed body"
        body DeepSeekStreamHarness.counterToolStreamBody
      assertEqual "stream retry retains the transient HTTP history"
        history.failures [.transport (.httpStatus 503 "temporary")]
      assertEqual "stream retry performs one initial attempt plus one retry"
        (DeepSeekStreamHarnessRetry.RetryHistory.attemptCount history) 2
      assertEqual "stream retry executes the supplied attempt twice"
        (← attempts.get) 2
      assertEqual "stream retry retains the parsed terminal tool count"
        processed.finished.finished.view.rawToolCalls.length 1
      let _bound := DeepSeekStreamHarnessRetry.RetryHistory.attemptCount_le_maxAttempts history

  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  match ← DeepSeekStreamHarnessRetry.executeConversationMultiStreamRound policy
      (DeepSeekStreamHarness.streamFlagFixtureProcess
        DeepSeekStreamHarness.counterToolStreamBody)
      "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource Cordis.Harness.counterConfig 0 initialRunner []
      (by simp) (by simp) with
  | .error _ => fail "stream retry conversation failed"
  | .ok ⟨body, result⟩ =>
      assertEqual "stream retry conversation preserves its body"
        body DeepSeekStreamHarness.counterToolStreamBody
      assertEqual "stream retry conversation has no failed attempts"
        result.retryHistory.failures []
      assertEqual "stream retry conversation executes the streamed tool"
        result.round.finalModel 0
      assertEqual "stream retry conversation appends the tool result"
        result.round.runner.session.messages [
          .user "Read the counter.",
          .assistant "" [{ id := { value := 0 }, name := "counter_read", arguments := "null" }],
          .toolResult { value := 0 } "[true,0]" false
        ]

private def testDeepSeekStreamHarnessRetryConversation : IO Unit := do
  match ← DeepSeekStreamHarnessRetryConversation.Example.loop with
  | .error _ => fail "stream retry conversation loop failed"
  | .ok ⟨finalRunner, ⟨finalModel, run⟩⟩ =>
      assertEqual "stream retry conversation loop retains both round witnesses"
        run.trace.length 2
      assertEqual "stream retry conversation loop preserves the final model"
        finalModel 0
      assertEqual "stream retry conversation loop appends the text terminal"
        finalRunner.session.messages [
          .user "Read the counter.",
          .assistant "" [
            { id := { value := 0 }, name := "counter_read", arguments := "null" },
            { id := { value := 1 }, name := "counter_read", arguments := "null" }
          ],
          .toolResult { value := 0 } "[true,0]" false,
          .toolResult { value := 1 } "[true,0]" false,
          .assistant "Hello world" []
        ]
      assertEqual "stream retry conversation loop reports completion"
        (DeepSeekStreamHarnessRetryConversation.StreamRetryStop.isCompleted run.stop) true
      match run.trace with
      | .cons first (.cons second _) =>
          assertEqual "stream retry loop first round executes both streamed tools"
            first.round.round.executions.length 2
          assertEqual "stream retry loop first round has no failed attempts"
            first.round.retryHistory.failures.length 0
          assertEqual "stream retry loop final round has no failed attempts"
            second.round.retryHistory.failures.length 0
      | _ => fail "stream retry conversation loop returned the wrong trace shape"

  match ← DeepSeekStreamHarnessRetryConversation.Example.failure with
  | .error (.client history (.transport (.httpStatus 503 _))) =>
      assertEqual "stream retry conversation failure retains both retry failures"
        history.failures.length 2
      assertEqual "stream retry conversation failure reports the retry bound"
        (DeepSeekStreamHarnessRetry.RetryHistory.attemptCount history) 3
  | .error _ => fail "stream retry conversation returned the wrong failure"
  | .ok _ => fail "stream retry conversation accepted an exhausted transient process"

private def testDeepSeekHarnessCancellation : IO Unit := do
  let initialRunner : DeepSeekHarness.ConversationRunner := {
    session := DeepSeekHarness.counterSession
    turn := 1
    step := 0
    nextCall := 0
    toolCallCount_eq_nextCall := by rfl
  }
  let beforeBodies ← IO.mkRef ([] : List String)
  let beforeTransport : DeepSeekApi.Transport := {
    send := fun request => do
      beforeBodies.modify (fun previous => previous ++ [request.body])
      pure (.ok { status := 200, body := DeepSeekHarness.counterResponseBody })
  }
  let beforePolicy :=
    DeepSeekHarnessCancellation.CancellationPolicy.atRound 0 .user
  match ← DeepSeekHarnessCancellation.runConversationCancellable
      (cfg := Cordis.Harness.counterConfig) beforePolicy 2
      beforeTransport "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error _ => fail "cancellation before the first request returned an error"
  | .ok result =>
      assertEqual "pre-request cancellation retains an empty round history"
        result.rounds.length 0
      assertEqual "pre-request cancellation preserves the runner sequence"
        result.runner.session.nextSeq initialRunner.session.nextSeq
      assertEqual "pre-request cancellation preserves the model" result.finalModel 0
      assertEqual "pre-request cancellation reports cancellation"
        (DeepSeekHarnessCancellation.CancellableStop.isCancelled result.stop) true
      assertEqual "pre-request cancellation records round zero"
        (DeepSeekHarnessCancellation.CancellableStop.cancelledRound result.stop) (some 0)
      assertEqual "pre-request cancellation records the user reason"
        (DeepSeekHarnessCancellation.CancellableStop.cancelledReason result.stop) (some .user)
      let beforeSnapshot ← beforeBodies.get
      assertEqual "pre-request cancellation sends no request" beforeSnapshot.length 0

  let afterBodies ← IO.mkRef ([] : List String)
  let afterTransport : DeepSeekApi.Transport := {
    send := fun request => do
      afterBodies.modify (fun previous => previous ++ [request.body])
      let seen ← afterBodies.get
      pure (.ok {
        status := 200
        body := if seen.length = 1 then DeepSeekHarness.counterResponseBody
          else DeepSeekHarness.counterFinalResponseBody
      })
  }
  let afterPolicy :=
    DeepSeekHarnessCancellation.CancellationPolicy.atRound 1 .timeout
  match ← DeepSeekHarnessCancellation.runConversationCancellable
      (cfg := Cordis.Harness.counterConfig) afterPolicy 2
      afterTransport "https://fixture.invalid" { value := "fixture-key" }
      DeepSeekHarness.counterRequestSource [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error _ => fail "between-round cancellation returned an error"
  | .ok result =>
      assertEqual "between-round cancellation retains the completed prefix"
        result.rounds.length 1
      assertEqual "between-round cancellation preserves the post-tool model"
        result.finalModel 0
      assertEqual "between-round cancellation preserves the post-tool sequence"
        result.runner.session.nextSeq 3
      assertEqual "between-round cancellation reports cancellation"
        (DeepSeekHarnessCancellation.CancellableStop.isCancelled result.stop) true
      assertEqual "between-round cancellation records round one"
        (DeepSeekHarnessCancellation.CancellableStop.cancelledRound result.stop) (some 1)
      assertEqual "between-round cancellation records the timeout reason"
        (DeepSeekHarnessCancellation.CancellableStop.cancelledReason result.stop) (some .timeout)
      let afterSnapshot ← afterBodies.get
      assertEqual "between-round cancellation does not issue a second request"
        afterSnapshot.length 1
      assertEqual "between-round cancellation retains the first assistant/tool messages"
        result.runner.session.messages [
          .user "Read the counter.",
          .assistant "I will read the counter." [{
            id := { value := 0 }, name := "counter_read", arguments := "null"
          }],
          .toolResult { value := 0 } "[true,0]" false
        ]

  let fuelBodies ← IO.mkRef ([] : List String)
  let fuelTransport : DeepSeekApi.Transport := {
    send := fun request => do
      fuelBodies.modify (fun previous => previous ++ [request.body])
      pure (.ok { status := 200, body := DeepSeekHarness.counterResponseBody })
  }
  match ← DeepSeekHarnessCancellation.runConversationCancellable
      (cfg := Cordis.Harness.counterConfig)
      (DeepSeekHarnessCancellation.CancellationPolicy.never) 1 fuelTransport
      "https://fixture.invalid" { value := "fixture-key" } DeepSeekHarness.counterRequestSource
      [] (by simp) (by
        intro current source sourceMem
        cases sourceMem) 0 initialRunner with
  | .error _ => fail "non-cancelled cancellable runner returned an error"
  | .ok result =>
      assertEqual "non-cancelled runner retains the fuel-bounded prefix"
        result.rounds.length 1
      assertEqual "non-cancelled runner reports fuel exhaustion"
        (DeepSeekHarnessCancellation.CancellableStop.isFuelExhausted result.stop) true

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
  assertEqual "aborted turn-end reasons retain their structured wire cause"
    (SessionRefinement.turnEndReasonSummary
      (SessionRefinement.decodeEvent SessionRefinement.abortedTurnEndExampleJson))
    (some (.aborted .user))
  assertEqual "blocked turn-end reasons remain source-visible"
    (SessionRefinement.turnEndReasonSummary
      (SessionRefinement.decodeEvent SessionRefinement.blockedTurnEndExampleJson))
    (some .blocked)
  assertEqual "interrupted turn-end reasons remain source-visible"
    (SessionRefinement.turnEndReasonSummary
      (SessionRefinement.decodeEvent SessionRefinement.interruptedTurnEndExampleJson))
    (some .interrupted)
  assertEqual "error turn-end reasons retain structured failure facts"
    (SessionRefinement.turnEndReasonSummary
      (SessionRefinement.decodeEvent SessionRefinement.errorTurnEndExampleJson))
    (some (.error {
      message := "provider failed"
      code := "TIMEOUT"
      status := some { value := 504, safe := by decide }
      providerRetryAfterMs := some { value := 250, safe := by decide }
      requestId := some "req-1"
    }))
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
  match SessionRefinement.surfaceValidationSummary
      (SessionRefinement.validateJsonLog SessionRefinement.messageExampleJson) with
  | none => fail "text-only surface message example failed to validate"
  | some summary =>
      assertRuntimeStateEqual "text-only surface messages reach the closed local turn"
        (eraseState summary.protocol) (.ready 2)
      assertEqual "text-only surface messages project into the local message vocabulary"
        summary.messages [.user "hello", .assistant "hi" []]
      assertEqual "surface metadata retains upstream message identities"
        summary.surfaceIds ["user-1", "assistant-1"]
      assertEqual "surface metadata retains the assistant provider"
        summary.surfaceProviders ["", "deepseek"]
      assertEqual "surface messages remain absent from intrinsic protocol events"
        summary.runtimeEvents [
          .turnStart 1,
          .stepStart 1 0,
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
  assertEqual "assistant reasoning and image surface blocks remain in the wire witness"
    (SessionRefinement.surfaceAssistantBlockTags
      (SessionRefinement.validateJsonLog SessionRefinement.messageExampleJson))
    (some ["reasoning", "image", "text"])
  match SessionRefinement.surfaceValidationSummary
      (SessionRefinement.validateJsonLog SessionRefinement.toolMessageExampleJson) with
  | none => fail "assistant tool-call surface example failed to validate"
  | some summary =>
      assertRuntimeStateEqual "assistant tool-call surface reaches the closed local turn"
        (eraseState summary.protocol) (.ready 2)
      assertEqual "assistant tool-call blocks append a typed local call"
        summary.messages [
          .user "look up lean",
          .assistant "I will look it up." [{
            id := { value := 0 }, name := "lookup", arguments := "{\"q\":\"lean\"}"
          }],
          .toolResult { value := 0 } "result" false
        ]
      assertEqual "assistant tool-call IDs are reused by call and result runtime events"
        summary.runtimeEvents [
          .turnStart 1,
          .stepStart 1 0,
          .toolCall 1 0 { value := 0 },
          .toolResult 1 0 { value := 0 },
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
      assertEqual "assistant tool-call surface metadata retains source identities"
        summary.surfaceIds ["user-1", "assistant-1"]
      assertEqual "assistant tool-call surface metadata retains the model provider"
        summary.surfaceProviders ["", "deepseek"]
  match SessionRefinement.surfaceValidationSummary
      (SessionRefinement.validateJsonLog SessionRefinement.replacementMessageExampleJson) with
  | none => fail "replacement surface example failed to validate"
  | some summary =>
      assertRuntimeStateEqual "replacement surface reaches the closed local turn"
        (eraseState summary.protocol) (.ready 2)
      assertEqual "replacement surface shadows the assistant/tool-result interval"
        summary.messages [.user "look up lean", .assistant "I summarized the lookup." []]
      assertEqual "replacement surface leaves intrinsic protocol events unchanged"
        summary.runtimeEvents [
          .turnStart 1,
          .stepStart 1 0,
          .toolCall 1 0 { value := 0 },
          .toolResult 1 0 { value := 0 },
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
      assertEqual "replacement surface retains the replacement source identity"
        summary.surfaceIds ["user-1", "assistant-1", "assistant-summary"]
      assertEqual "replacement surface retains its model provider"
        summary.surfaceProviders ["", "deepseek", "deepseek"]
  match SessionRefinement.surfaceValidationSummary
      (SessionRefinement.validateJsonLog
        SessionRefinement.malformedReplacementMessageExampleJson) with
  | none => pure ()
  | some _ => fail "replacement surface accepted incomplete source coverage"
  match SessionRefinement.validationSummary
      (SessionRefinement.validateJsonLog SessionRefinement.headerChunkExampleJson) with
  | none => fail "request-header/text-chunk example failed to validate"
  | some summary =>
      assertRuntimeStateEqual "request-header/text-chunk example reaches the closed local turn"
        (eraseState summary.protocol) (.ready 2)
      assertEqual "request-header/text-chunk example preserves physical sequence continuity"
        summary.nextSeq 6
      assertEqual "text chunks remain log-only in the intrinsic protocol projection"
        summary.runtimeEvents [
          .turnStart 1,
          .stepStart 1 0,
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
  match SessionRefinement.latestHeaderSummary
      (SessionRefinement.validateJsonLog SessionRefinement.headerChunkExampleJson) with
  | some (some header) =>
      assertEqual "request/header retains provider/model and selected tool schema"
        header SessionRefinement.headerChunkExpectedHeader
  | _ => fail "request/header was not retained in the certified session log"
  match SessionRefinement.validationSummary
      (SessionRefinement.validateJsonLog SessionRefinement.metadataExampleJson) with
  | none => fail "todo/context/seed example failed to validate"
  | some summary =>
      assertRuntimeStateEqual "todo/context/seed metadata remains log-only"
        (eraseState summary.protocol) (.ready 2)
      assertEqual "todo/context/seed metadata preserves sequence continuity"
        summary.nextSeq 8
      assertEqual "todo/context/seed metadata does not alter model messages"
        summary.messages []
      assertEqual "todo/context/seed metadata preserves only structural runtime events"
        summary.runtimeEvents [
          .turnStart 1,
          .stepStart 1 0,
          .stepEnd 1 0,
          .turnEnd 1 1
        ]
  match SessionRefinement.decodeEvents SessionRefinement.metadataExampleJson with
  | .ok (first :: second :: third :: _) =>
      match first.payload, second.payload, third.payload with
      | .requestContext context, .todoWrite write, .sessionEndSeed =>
          assertEqual "request/context retains its provider route"
            context.provider "deepseek"
          assertEqual "request/context retains its model route"
            context.model "deepseek-reasoner"
          assertEqual "request/context retains its safe context window"
            (context.contextWindow.map (fun value => value.value)) (some 131072)
          assertEqual "todo/write retains the complete whole-list snapshot"
            write.todos [
              { content := "formalize context", status := .completed },
              { content := "audit session seed", status := .inProgress }
            ]
      | _, _, _ => fail "decoded metadata payload tags were not preserved"
  | result => fail s!"todo/write/session-end-seed payloads were not retained: {reprStr result}"
  match SessionRefinement.decodeEvent SessionRefinement.malformedTodoStatusExampleJson with
  | .error (.unsupportedTag _ "blocked") => pure ()
  | result => fail s!"unknown todo status was not rejected: {reprStr result}"
  match SessionRefinement.decodeEvent SessionRefinement.malformedSessionEndSeedExampleJson with
  | .error (.unsupportedField _ "unexpected") => pure ()
  | result => fail s!"nonempty session/end-seed payload was not rejected: {reprStr result}"
  if SessionRefinement.assistantChunkSummary
      (SessionRefinement.decodeEvent SessionRefinement.malformedAssistantChunkExampleJson) ==
      some (1, 1, "hidden") then
    pure ()
  else
    fail "reasoning assistant chunk was not retained as a log-only payload"
  match SessionRefinement.decodeEvent SessionRefinement.malformedAssistantChunkIndexExampleJson with
  | .error (.unsupportedTag _ "1") => pure ()
  | result => fail s!"nonzero-index assistant chunk was not rejected: {reprStr result}"
  match SessionRefinement.decodeEvent SessionRefinement.malformedRequestHeaderExampleJson with
  | .error (.unsupportedField _ "temperature") => pure ()
  | result => fail s!"unsupported request-header field was not rejected: {reprStr result}"

private def testSessionOpaqueMetadata : IO Unit := do
  match SessionOpaqueMetadata.decodeEventRetainingMetadata
      (List.getD SessionOpaqueMetadata.metadataExampleJson 5 .null) with
  | .error error => fail s!"opaque tool-result metadata event failed: {reprStr error}"
  | .ok retained =>
      assertEqual "opaque tool-result metadata event is retained as a tool result"
        retained.metadata.isSome true
      assertEqual "opaque tool-result metadata event still decodes semantically"
        (match retained.wire.payload with
        | .toolResult _ => true
        | _ => false) true
      let _metadataCertificate := retained.metadata_eq
      let _eventCertificate := retained.decode_eq
      pure ()
  match SessionOpaqueMetadata.validateLogRetainingMetadata
      SessionOpaqueMetadata.metadataExampleJson with
  | .error error => fail s!"opaque metadata session failed: {reprStr error}"
  | .ok retained =>
      assertEqual "opaque metadata validation keeps one metadata-bearing result"
        (retained.metadata.filterMap (fun metadata =>
          metadata.map (fun value => (value.error.isSome, value.metaValue.isSome))))
        [(true, true)]
      let _exactMetadataCertificate := SessionOpaqueMetadata.metadata_example_exact
      assertEqual "opaque metadata validation reaches the existing derived endpoint"
        (eraseState retained.validation.final.protocol) (.ready 2)
      assertEqual "opaque metadata validation preserves the sanitized event count"
        retained.sanitized.length SessionOpaqueMetadata.metadataExampleJson.length
      let _projectionCertificate := SessionOpaqueMetadata.metadata_example_projection
      pure ()

private def testSessionArchive : IO Unit := do
  assertEqual "lossless archive classifies supported and extension envelopes"
    (SessionArchive.archiveTags SessionArchive.archiveExampleJson)
    ["supported", "opaque-required", "opaque-ignorable"]
  match SessionArchive.archive SessionArchive.archiveExampleJson with
  | .error error => fail s!"lossless archive example failed: {reprStr error}"
  | .ok log =>
      assertEqual "lossless archive retains every input envelope"
        log.events.length 3
      assertEqual "lossless archive preserves raw event order"
        ((log.events.map SessionArchive.ArchivedEvent.raw) ==
          SessionArchive.archiveExampleJson) true
      assertEqual "required opaque records are never silently reclassified as ignorable"
        (log.events.map SessionArchive.ArchivedEvent.isRequired)
        [false, true, false]
  match SessionArchive.archive
      [SessionArchive.supportedTurnStartJson,
        Lean.Json.mkObj [("type", .str "vendor/malformed"), ("seq", .num 3),
          ("data", Lean.Json.mkObj [])]] with
  | .error (.missingField [.index 1] "time") => pure ()
  | _ => fail "archive did not retain the failing envelope index"

private def testSessionEventArchive : IO Unit := do
  assertEqual "full current event union exposes every pinned core tag"
    SessionEventArchive.allKnownTagWires
    (SessionEventArchive.KnownTag.all.map SessionEventArchive.KnownTag.wire)
  match SessionEventArchive.archive SessionEventArchive.allKnownEventJson with
  | .error error => fail s!"full event-tag archive failed: {reprStr error}"
  | .ok log =>
      assertEqual "full event-tag archive retains all thirteen core envelopes"
        log.events.length 13
      assertEqual "full event-tag archive preserves raw input order"
        (log.events.map SessionEventArchive.ArchivedEvent.raw ==
          SessionEventArchive.allKnownEventJson) true
      assertEqual "full event-tag archive recognizes every record as a known core event"
        (log.events.map SessionEventArchive.ArchivedEvent.isKnown)
        (List.replicate 13 true)
  match SessionEventArchive.archive [SessionEventArchive.reasoningSurfaceJson] with
  | .ok log =>
      match log.events with
      | [event] =>
          assertEqual "reasoning surface payload is semantically recognized and tagged"
            (event.isOpaque, event.tag?) (false, some .assistantMessage)
      | _ => fail "reasoning fixture did not produce one archived event"
  | .error error => fail s!"reasoning payload was not archived: {reprStr error}"
  match SessionEventArchive.archive [SessionEventArchive.unsupportedToolResultMetaJson] with
  | .ok log =>
      match log.events with
      | [event] =>
          assertEqual "tool-result error/meta stays opaque but tagged"
            (event.isOpaque, event.tag?) (true, some .toolResult)
      | _ => fail "tool-result fixture did not produce one archived event"
  | .error error => fail s!"tool-result payload was not archived: {reprStr error}"
  match SessionEventArchive.archive [SessionEventArchive.illegalLogOnlyMetadataJson] with
  | .error (.knownMetadata 0 .turnStart) => pure ()
  | _ => fail "log-only surface metadata was not rejected"
  match SessionEventArchive.archive [SessionEventArchive.knownNonObjectDataJson] with
  | .error (.knownDataNotObject 0 .turnStart) => pure ()
  | _ => fail "known non-object data was not rejected"
  match SessionEventArchive.archive [SessionEventArchive.requiredExtensionJson,
      SessionEventArchive.ignorableExtensionJson] with
  | .ok log =>
      assertEqual "unknown required and ignorable extensions remain opaque"
        (log.events.map fun event => (event.isKnown, event.isRequired))
        [(false, true), (false, false)]
  | .error error => fail s!"extension archive failed: {reprStr error}"

private def testSessionPayloadArchive : IO Unit := do
  assertEqual "payload archive classifies reasoning/image blocks without projecting them"
    SessionPayloadArchive.reasoningImageTyped true
  assertEqual "payload archive retains assistant usage and tool-result opaque fields"
    SessionPayloadArchive.toolResultOpaqueTyped true
  assertEqual "payload archive captures raw assistant usage"
    SessionPayloadArchive.assistantUsageCaptured true
  assertEqual "payload archive captures raw tool-result error/meta"
    SessionPayloadArchive.toolResultErrorMetaCaptured true
  assertEqual "payload archive retains unknown content-block extensions"
    SessionPayloadArchive.unknownBlockRetained true
  assertEqual "payload archive retains malformed known payloads losslessly"
    SessionPayloadArchive.malformedPayloadIsRetained true
  match SessionPayloadArchive.archivePayload
      [SessionPayloadArchive.reasoningImagePayloadJson,
        SessionPayloadArchive.toolResultOpaquePayloadJson] with
  | .error error => fail s!"typed payload archive failed: {reprStr error}"
  | .ok log =>
      assertEqual "typed payload archive preserves event count" log.events.length 2
      assertEqual "typed payload archive preserves raw event order"
        (log.events.map SessionPayloadArchive.EnrichedEvent.raw ==
          [SessionPayloadArchive.reasoningImagePayloadJson,
            SessionPayloadArchive.toolResultOpaquePayloadJson]) true
      assertEqual "typed payload archive exposes both payload tags"
        (log.events.map SessionPayloadArchive.EnrichedEvent.tag?)
        [some .assistantMessage, some .toolResult]

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

private def testObservationalPartialTransformation : IO Unit := do
  let left := ObservationalPartialTransformation.RespectGap.left
  let right := ObservationalPartialTransformation.RespectGap.right
  assertEqual "respect-gap inputs agree on their visible observation"
    (left.visible, right.visible) (false, false)
  assertEqual "the exact bad map leaks hidden representation into visible observation"
    ((ObservationalPartialTransformation.RespectGap.bad left).visible,
      (ObservationalPartialTransformation.RespectGap.bad right).visible)
    (false, true)

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

private def testGlobalIteratorIndependence : IO Unit := do
  let forwardMap := GlobalIteratorIndependence.forward
    GlobalIteratorIndependence.Example.program 10
  let inverseMap := GlobalIteratorIndependence.total
    (GlobalLifecycle.Example.dynamics.applyUndo GlobalLifecycle.Example.firstStep.undo)
  let left := PartialTransformation.comp forwardMap inverseMap
    GlobalIteratorIndependence.Example.zeroState
  let right := PartialTransformation.comp inverseMap forwardMap
    GlobalIteratorIndependence.Example.zeroState
  assertEqual "a real iterator and one yielded inverse need not commute"
    (left.map (fun state ↦ state.ambient), right.map (fun state ↦ state.ambient))
    (some 1, some 0)
  assertEqual "registration continuation retains the oracle-selected child"
    (GlobalIteratorIndependence.RawRegistrationGap.request.next false,
      GlobalIteratorIndependence.RawRegistrationGap.request.next true)
    (some false, some true)

private def testGlobalTransposition : IO Unit := do
  let falseTag : Option Bool :=
    match GlobalTransposition.Counterexample.falseStep.undo with
    | .external code => some code
    | .retire _ => none
  let trueTag : Option Bool :=
    match GlobalTransposition.Counterexample.trueStep.undo with
    | .external code => some code
    | .retire _ => none
  assertEqual "semantic yield agreement retains distinct stored undo codes"
    (falseTag, trueTag) (some false, some true)
  let probe := GlobalTransposition.Counterexample.state true
  let falseRecovered := GlobalTransposition.Counterexample.dynamics.applyUndo
    GlobalTransposition.Counterexample.falseStep.undo probe
  let trueRecovered := GlobalTransposition.Counterexample.dynamics.applyUndo
    GlobalTransposition.Counterexample.trueStep.undo probe
  assertEqual "distinct undo codes have the same concrete interpretation on a probe"
    (falseRecovered.ambient, falseRecovered.nextBirth)
    (trueRecovered.ambient, trueRecovered.nextBirth)

private def testGlobalForeignPhase : IO Unit := do
  assertEqual "full iterator independence does not hide foreign-phase-sensitive undo syntax"
    (GlobalForeignPhase.IndependenceGap.selectedUndo false
        GlobalForeignPhase.IndependenceGap.before,
      GlobalForeignPhase.IndependenceGap.selectedUndo false
      GlobalForeignPhase.IndependenceGap.afterPhaseEdit)
    (false, true)

private def testGlobalLandingTransposition : IO Unit := do
  assertEqual "landing activation diamond preserves the exact Iter/Finish rule pair"
    GlobalLandingTransposition.Example.executableRulePair
    (.iter, .finish)

private def testGlobalActivationTransposition : IO Unit := do
  assertEqual "all-nine activation layer retains the exact Iter/Finish pair"
    GlobalActivationTransposition.Example.LandingPair.executableRulePair
    (.iter, .finish)
  assertEqual "Begin/Begin needs no iterator compatibility law"
    (GlobalActivationTransposition.Example.BeginPairs.beginLeft.rule,
      GlobalActivationTransposition.Example.BeginPairs.beginRight.rule)
    (.begin, .begin)
  assertEqual "Begin/Finish consumes only the landing program frame"
    (GlobalActivationTransposition.Example.BeginPairs.mixedBegin.rule,
      GlobalActivationTransposition.Example.BeginPairs.mixedFinish.rule)
    (.begin, .finish)
  assertEqual "the all-nine constructor includes the Finish/Finish branch"
    (GlobalActivationTransposition.Example.FinishPair.left.rule,
      GlobalActivationTransposition.Example.FinishPair.right.rule)
    (.finish, .finish)

private def testGlobalActivationOrchestrationTransposition : IO Unit := do
  assertEqual "corrected exchange exposes the early Insert actor and moved Begin rule"
    GlobalActivationOrchestrationTransposition.BeginInsert.executableTags
    (.insert, 1, .begin)
  let normalBirth :=
    (GlobalActivationOrchestrationTransposition.LiteralPaperGap.normal.registry 1).map
      (fun fiber => fiber.birth)
  let swappedBirth :=
    (GlobalActivationOrchestrationTransposition.LiteralPaperGap.swapped.registry 1).map
      (fun fiber => fiber.birth)
  assertEqual "opposite fresh insertion orders retain different per-fiber birth ranks"
    (normalBirth, swappedBirth) (some 1, some 2)

private def testGlobalTraceRewrite : IO Unit := do
  assertEqual "an internal exact rewrite retains context and reverses the selected pair"
    GlobalTraceRewrite.Example.ActivationOrchestration.executableProjection
    ([.oInsert, .oInsert, .lBegin], [0, 1, 0])

private def testGlobalDeletion : IO Unit := do
  assertEqual "intrinsic deletion replay records one dropped and one retained occurrence"
    GlobalDeletion.Positive.deletionReplay.decisions
    [.drop, .keep]
  assertEqual "bounded deletion keeps the surviving orchestration rule in order"
    (GlobalDeletion.Positive.deletionSourceTrace.rules,
      GlobalDeletion.Positive.deletionShadowTrace.rules)
    ([.oRemove, .oRetire], [.oRetire])
  assertEqual "safe vestigial suffix exposes the rule copied by the exact trace square"
    GlobalDeletion.Positive.sourceTrace.rules [.oRetire]
  assertEqual "safe vestigial suffix exposes the actor copied by the exact trace square"
    (GlobalDeletion.Positive.sourceTrace.actors.map fun actor => match actor with
      | .fiber name => name)
    [0]

private def testGlobalPaperRelation : IO Unit := do
  let normalControl :=
    (GlobalActivationOrchestrationTransposition.LiteralPaperGap.normal.registry 1).map
      (fun fiber => (fiber.parent, fiber.retired))
  let swappedControl :=
    (GlobalActivationOrchestrationTransposition.LiteralPaperGap.swapped.registry 1).map
      (fun fiber => (fiber.parent, fiber.retired))
  let normalBirth :=
    (GlobalActivationOrchestrationTransposition.LiteralPaperGap.normal.registry 1).map
      (fun fiber => fiber.birth)
  let swappedBirth :=
    (GlobalActivationOrchestrationTransposition.LiteralPaperGap.swapped.registry 1).map
      (fun fiber => fiber.birth)
  assertEqual "paper-visible parent and retirement agree while allocator birth differs"
    (normalControl, swappedControl, normalBirth, swappedBirth)
    (some (some 0, false), some (some 0, false), some 1, some 2)
  assertEqual "birth-erased orchestration replay retains the exact rule and actor"
    GlobalPaperRelation.BirthGap.executableMatchedTags
    (.retire, 1)
  let _directedReplayFinal := GlobalPaperRelation.DirectedReplayExample.final_related
  assertEqual "directed paper-relation replay retains the safe suffix rule"
    GlobalPaperRelation.DirectedReplayExample.executableReplayRules [.oRetire]

private def testGlobalPaperTraceSimulation : IO Unit := do
  let _clockGap := GlobalPaperTraceSimulation.ClockGap.no_forward_step_simulation
  assertEqual "birth-erased trace layer exposes the concrete detailed source tag"
    GlobalPaperTraceSimulation.PositiveOrchestration.executableDetailedRules
    [.orchestration .retire]
  assertEqual "birth-erased trace layer exposes the concrete source actor list"
    GlobalPaperTraceSimulation.PositiveOrchestration.executableActorNames [1]
  assertEqual "birth-erased trace layer retains the projected global rule tag"
    (GlobalPaperTraceSimulation.PositiveOrchestration.executableDetailedRules.map
      GlobalPaperTraceSimulation.DetailedRule.global)
    [.oRetire]
  let _forwardLocal := GlobalPaperTraceSimulation.PositiveLifecycle.forwardReplay_final_related
  let _backwardLocal := GlobalPaperTraceSimulation.PositiveLifecycle.backwardReplay_final_related
  assertEqual "trace-local lifecycle replay exposes the leave/unload tags"
    GlobalPaperTraceSimulation.PositiveLifecycle.executableDetailedRules
    [.lifecycle .leave, .lifecycle .unload]
  assertEqual "trace-local lifecycle replay preserves the two acting names"
    GlobalPaperTraceSimulation.PositiveLifecycle.executableActorNames [0, 0]

private def testGlobalPaperTraceDeletion : IO Unit := do
  assertEqual "assigned deletion replay retains the concrete detailed rule"
    GlobalPaperTraceDeletion.Example.executableDetailedRules
    [.orchestration .retire]
  assertEqual "assigned deletion replay retains the concrete actor"
    GlobalPaperTraceDeletion.Example.executableActorNames
    [0]
  assertEqual "assigned deletion replay exposes an executable keep decision"
    GlobalPaperTraceDeletion.Example.executableDecisions
    [.keep]

private def testGlobalPaperTraceNormalization : IO Unit := do
  let _related := GlobalPaperTraceNormalization.Example.empty_chain_related
  let _rules := GlobalPaperTraceNormalization.Example.empty_chain_rules
  let _actors := GlobalPaperTraceNormalization.Example.empty_chain_actors
  assertEqual "finite rewrite-chain surface has an executable empty-chain witness"
    GlobalPaperTraceNormalization.Example.executableLinkCount 0
  assertEqual "finite rewrite-chain surface executes one activation/orchestration link"
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.executableLinkCount 1
  assertEqual "nonempty rewrite-chain witness exposes the rewritten rule ledger"
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.executableTerminalRules
    [GlobalCalculus.Rule.oInsert, GlobalCalculus.Rule.oInsert, GlobalCalculus.Rule.lBegin]
  assertEqual "nonempty rewrite-chain witness exposes the rewritten actor ledger"
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.executableTerminalActors
    [0, 1, 0]
  assertEqual "rewrite-chain surface also executes a connected reverse link"
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.executableTwoLinkCount 2
  let _twoRelated :=
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.twoChain_terminal_final_related
  assertEqual "two-link rewrite chain returns the original rule ledger"
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.executableTwoLinkTerminalRules
    [GlobalCalculus.Rule.oInsert, GlobalCalculus.Rule.lBegin, GlobalCalculus.Rule.oInsert]
  assertEqual "two-link rewrite chain returns the original actor ledger"
    GlobalPaperTraceNormalization.Example.ActivationOrchestration.executableTwoLinkTerminalActors
    [0, 0, 1]

private def testGlobalProgress : IO Unit := do
  assertEqual "conditional progress constructs the expected concrete Begin rule"
    GlobalProgress.BeginExample.executableRule .begin
  assertEqual "the concrete progress source is inactive rather than already installed"
    GlobalProgress.BeginExample.executableSourcePhase true

private def testGlobalProgressTermination : IO Unit := do
  assertEqual "quantitative progress example has two exact edges"
    GlobalProgressTermination.Example.executableLength 2
  assertEqual "quantitative progress starts with potential two"
    (GlobalProgressTermination.Example.potential.value
      GlobalProgressTermination.Example.State.start) 2
  assertEqual "quantitative progress ends with potential zero"
    (GlobalProgressTermination.Example.potential.value
      GlobalProgressTermination.Example.State.done) 0

private def testGlobalSupport : IO Unit := do
  assertEqual "separate acyclic relations can form one cyclic support dependency"
    GlobalSupport.MixedCycle.cycleProjection (true, true, true)

private def testGlobalRelations : IO Unit := do
  let absentTable : Option Nat :=
    GlobalRelations.tableAt GlobalRelations.Example.emptyState false ()
  let vestigialTable : Option Nat :=
    GlobalRelations.tableAt GlobalRelations.Example.vestigialState false ()
  assertEqual "effect relation normalizes absence and a present empty table"
    (absentTable, vestigialTable) (none, none)
  assertEqual "rule relation still observes the vestigial registry entry"
    ((GlobalRelations.controlAt GlobalRelations.Example.emptyState false).isSome,
      (GlobalRelations.controlAt GlobalRelations.Example.vestigialState false).isSome)
    (false, true)

private def testGlobalSpatial : IO Unit := do
  assertEqual "spatial lifecycle classification retains the acted-on owner"
    (GlobalSpatial.lifecycleOwner GlobalLifecycle.Example.iterTransition,
      GlobalSpatial.lifecycleOwner GlobalLifecycle.Example.finishTransition,
      GlobalSpatial.lifecycleOwner GlobalLifecycle.Example.leaveTransition)
    (0, 0, 0)

private def testGlobalVestigial : IO Unit := do
  assertEqual "vestigial removal erases only the child registry entry"
    ((GlobalVestigial.Counterexample.state.registry
        GlobalVestigial.Counterexample.Name.vestigial).isSome,
      (GlobalVestigial.Counterexample.withoutVestigial.registry
        GlobalVestigial.Counterexample.Name.vestigial).isSome)
    (true, false)
  assertEqual "forward parent-adoption and backward parent-removal exceptions are distinct"
    ((GlobalVestigial.orchestrationKind
        GlobalVestigial.Counterexample.adoptingInsert),
      (GlobalVestigial.orchestrationKind
        GlobalVestigial.Counterexample.removeParentAfterChild))
    (.insert, .remove)
  assertEqual "exception steps retain their exact acted-on names"
    ((GlobalVestigial.orchestrationName
        GlobalVestigial.Counterexample.adoptingInsert),
      (GlobalVestigial.orchestrationName
        GlobalVestigial.Counterexample.removeParentAfterChild))
    (.fresh, .parent)

private def testGlobalRuleInvariance : IO Unit := do
  assertEqual "rule invariance example keeps unequal parity-related counter values"
    (GlobalRegistry.Example.providerTable .counter,
      GlobalRuleInvariance.HeterogeneousExample.rightTable .counter)
    (some 7, some 9)
  assertEqual "rule invariance example keeps unequal length-related labels"
    (GlobalRegistry.Example.providerTable .label,
      GlobalRuleInvariance.HeterogeneousExample.rightTable .label)
    (some "ready", some "other")
  let matched := GlobalRuleInvariance.HeterogeneousExample.insertionMatch
  assertEqual "matched orchestration step retains inserted actor and endpoint presence"
    (GlobalVestigial.orchestrationName matched.matched,
      (matched.rightAfter.registry 1).isSome)
    (1, true)

private def testGlobalRuleObservations : IO Unit := do
  assertEqual "rule observation intentionally ignores ambient state"
    (GlobalRuleObservations.AmbientGap.baseline.ambient,
      GlobalRuleObservations.AmbientGap.shifted.ambient)
    (3, 4)
  assertEqual "matched active fibers retain unequal private table observations"
    (GlobalRegistry.Example.activeProviderFiber.table .counter,
      GlobalRuleInvariance.HeterogeneousExample.rightProviderFiber.table .counter)
    (some 7, some 9)

private def testGlobalLifecycleBisimulation : IO Unit := do
  let pathRules :=
    [GlobalLifecycleBisimulation.ReflexiveExample.beginMatch.matched.rule,
      GlobalLifecycleBisimulation.ReflexiveExample.iterMatch.matched.rule,
      GlobalLifecycleBisimulation.ReflexiveExample.finishMatch.matched.rule,
      GlobalLifecycleBisimulation.ReflexiveExample.leaveMatch.matched.rule,
      GlobalLifecycleBisimulation.ReflexiveExample.unloadMatch.matched.rule]
  assertEqual "conditional lifecycle matching exercises the existing exact path"
    pathRules [.begin, .iter, .finish, .leave, .unload]
  assertEqual "finish seam starts with unrelated private reloading tables"
    ((GlobalLifecycleBisimulation.FinishSeam.fiber 7).table .counter,
      (GlobalLifecycleBisimulation.FinishSeam.fiber 8).table .counter)
    (some 7, some 8)

private def testGlobalNameAction : IO Unit := do
  assertEqual "name action swaps registry names and child parent"
    ((GlobalNameAction.Example.actedState.registry false).isSome,
      (GlobalNameAction.Example.actedState.registry true).isSome,
      (GlobalNameAction.actFiber GlobalNameAction.Example.swapAction
        GlobalNameAction.Example.childFiber).parent)
    (true, true, some true)
  assertEqual "name action maps ambient and dependent provider values"
    (GlobalNameAction.Example.actedState.ambient,
      (GlobalNameAction.actFiber GlobalNameAction.Example.swapAction
        GlobalNameAction.Example.providerFiber).table .flag)
    (false, some false)
  assertEqual "acted orchestration step renames its exact actor"
    (GlobalVestigial.orchestrationName GlobalNameAction.Example.actedRetireChild)
    false

private def testGlobalNameLifecycle : IO Unit := do
  let reflexiveRules :=
    [GlobalNameLifecycle.ReflexiveExample.actedBegin.acted.rule,
      GlobalNameLifecycle.ReflexiveExample.actedIter.acted.rule,
      GlobalNameLifecycle.ReflexiveExample.actedFinish.acted.rule,
      GlobalNameLifecycle.ReflexiveExample.actedLeave.acted.rule,
      GlobalNameLifecycle.ReflexiveExample.actedUnload.acted.rule]
  assertEqual "name lifecycle action covers the existing exact path"
    reflexiveRules [.begin, .iter, .finish, .leave, .unload]
  assertEqual "nonidentity lifecycle action renames owner and exact endpoint presence"
    (GlobalLifecycleBisimulation.lifecycleOwner
        GlobalNameLifecycle.NonidentityRaiseExample.actedRaise.acted,
      ((GlobalNameAction.actState GlobalNameAction.Example.swapAction
        GlobalNameLifecycle.NonidentityRaiseExample.raiseAfter).registry true).isSome)
    (true, true)
  assertEqual "catalog entry counterexample moves a fixed entry code"
    (GlobalNameLifecycle.NonidentityRaiseExample.entryBreakingAction.iterator
        GlobalNameAction.Example.providerDecl.entry,
      GlobalNameAction.Example.providerDecl.entry)
    (true, false)

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
  testParallelHarness
  testParallelSchedule
  testAsyncHarness
  testDurableSettlement
  testDurableCodec
  testDurableBytes
  testDurableIO
  testRichStream
  testStreamSessionBridge
  testContextualEquivalence
  testUnifiedContexts
  testRuntimeRefinement
  testRuntimeFailureRefinement
  testRuntimeOutcomeRefinement
  testRuntimeOutcomeSession
  testTextRefinement
  testHarnessPersistence
  testHarnessPersistenceBytes
  testHarnessPersistenceArchive
  testHarnessPersistenceIO
  testDeepSeekApi
  testDeepSeekCurlTransport
  testDeepSeekCurlStream
  testDeepSeekCurlOutcome
  testDeepSeekOutcomeSession
  testDeepSeekOutcomeConversation
  testDeepSeekOutcomeConversationExecution
  testDeepSeekOutcomeConversationLoop
  testDeepSeekOutcomeTransportLoop
  testDeepSeekCurlSession
  testDeepSeekHarnessProcess
  testDeepSeekHarnessProcessOutcome
  testDeepSeekHarnessProcessSchema
  testDeepSeekHarnessProcessSchemaPrefix
  testDeepSeekHarnessProcessSchemaPrefixConversation
  testDeepSeekCurlIncremental
  testDeepSeekCurlPrefix
  testDeepSeekCurlPrefixSession
  testDeepSeekAsyncHarness
  testDeepSeekAsyncStreamHarness
  testDeepSeekAsyncStreamCancellation
  testDeepSeekStream
  testDeepSeekStreamFailure
  testDeepSeekTerminalOutcome
  testDeepSeekStreamIncremental
  testDeepSeekStreamByteFraming
  testDeepSeekCurlByteFraming
  testDeepSeekCurlBytePrefix
  testDeepSeekRichStream
  testDeepSeekRichToolStream
  testDeepSeekRichMixedStream
  testDeepSeekRichMultiStream
  testDeepSeekSessionBridge
  testDeepSeekSessionRunner
  testDeepSeekApiSession
  testDeepSeekHarness
  testDeepSeekHarnessPersistence
  testDeepSeekHarnessPersistenceIO
  testDeepSeekHarnessOpaqueMetadata
  testDeepSeekHarnessMetadataArchive
  testDeepSeekToolSchema
  testDeepSeekScopedRegistry
  testDeepSeekHarnessExtensions
  testSessionExtensionRefinement
  testDeepSeekHarnessExtensionPersistence
  testDeepSeekHarnessMixedPersistence
  testDeepSeekHarnessSchemaLift
  testDeepSeekHarnessMixedReplay
  testDeepSeekHarnessTransportContract
  testDeepSeekHarnessTransportToolRound
  testDeepSeekHarnessPersistenceTransportRound
  testDeepSeekHarnessTransportConversation
  testDeepSeekHarnessTransportRetry
  testDeepSeekHarnessTransportRetryConversation
  testDeepSeekSchemaStreamConversation
  testDeepSeekSchemaStreamPrefixConversation
  testDeepSeekSchemaStreamErrors
  testDeepSeekHarnessEventArchive
  testDeepSeekHarnessEventText
  testDeepSeekHarnessEventProcessOutcome
  testLoaderHMR
  testDeepSeekHarnessPayloadText
  testDeepSeekHarnessPayloadPersistence
  testDeepSeekStreamHarness
  testDeepSeekStreamHarnessByte
  testDeepSeekStreamHarnessBytePrefix
  testDeepSeekStreamHarnessCancellation
  testDeepSeekStreamHarnessPrefix
  testDeepSeekHarnessErrors
  testDeepSeekStreamHarnessErrors
  testDeepSeekStreamHarnessErrorsLoop
  testDeepSeekHarnessRetry
  testDeepSeekStreamHarnessRetry
  testDeepSeekStreamHarnessRetryConversation
  testDeepSeekHarnessCancellation
  testQuotientEffects
  testCoeffectQuotientLift
  testOperationalEquivalence
  testSessionRefinement
  testSessionOpaqueMetadata
  testSessionArchive
  testSessionEventArchive
  testSessionPayloadArchive
  testTransformationIndependence
  testOperationIndependence
  testArbitraryRemoval
  testGlobalRegistry
  testMediatedIndependenceBoundary
  testMediatedWholeRun
  testPartialTransformation
  testObservationalPartialTransformation
  testGlobalDynamics
  testGlobalLifecycle
  testGlobalCalculus
  testGlobalTraceFacts
  testGlobalTemporal
  testGlobalIteratorIndependence
  testGlobalTransposition
  testGlobalForeignPhase
  testGlobalLandingTransposition
  testGlobalActivationTransposition
  testGlobalActivationOrchestrationTransposition
  testGlobalTraceRewrite
  testGlobalDeletion
  testGlobalPaperRelation
  testGlobalPaperTraceSimulation
  testGlobalPaperTraceDeletion
  testGlobalPaperTraceNormalization
  testGlobalProgress
  testGlobalProgressTermination
  testGlobalSupport
  testGlobalRelations
  testGlobalSpatial
  testGlobalVestigial
  testGlobalRuleInvariance
  testGlobalRuleObservations
  testGlobalLifecycleBisimulation
  testGlobalNameAction
  testGlobalNameLifecycle
  testHarnessPhaseFailures
  testCounterAdmission
  testDependentChoiceSessionHarness
  testHarnessDemo
  IO.println "CORDIS adversarial and integration tests passed"

end Cordis.TestSuite
