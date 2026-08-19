import Cordis.Harness
import Cordis.Coeffect
import Cordis.CoeffectQuotient
import Cordis.ContextualEquivalence
import Cordis.Examples.DependentChoice
import Cordis.GlobalCalculus
import Cordis.GlobalDynamics
import Cordis.GlobalIteratorIndependence
import Cordis.GlobalTransposition
import Cordis.GlobalForeignPhase
import Cordis.GlobalLifecycle
import Cordis.GlobalLifecycleBisimulation
import Cordis.GlobalNameAction
import Cordis.GlobalNameLifecycle
import Cordis.GlobalRelations
import Cordis.GlobalRegistry
import Cordis.GlobalRuleInvariance
import Cordis.GlobalRuleObservations
import Cordis.GlobalSpatial
import Cordis.GlobalTemporal
import Cordis.GlobalTraceFacts
import Cordis.GlobalVestigial
import Cordis.Lifecycle
import Cordis.MediatedIndependence
import Cordis.MediatedTheorem
import Cordis.Policy
import Cordis.Protocol
import Cordis.OperationIndependence
import Cordis.ObservationalPartialTransformation
import Cordis.OperationalEquivalence
import Cordis.PartialTransformation
import Cordis.QuotientEffect
import Cordis.Removal
import Cordis.RichStream
import Cordis.RuntimeRefinement
import Cordis.Schedule
import Cordis.Session
import Cordis.SessionRefinement
import Cordis.StreamSession
import Cordis.Transformation
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

/-! A heterogeneous operational outcome keeps the exact operation-selected value type. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : OperationalEquivalence.OutcomeEvent OperationalEquivalence.Example.coeffect where
  op := .bump
  value := "not a Nat"

/-! An inverse test letter cannot be fabricated at a seed outside the operation domain. -/

/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs (substring := true) in
example : OperationalEquivalence.Letter OperationalEquivalence.Example.coeffect :=
  .inverse .bump () OperationalEquivalence.Example.blocked (by
    letI := OperationalEquivalence.Example.coeffect.enabledDecidable .bump ()
      OperationalEquivalence.Example.blocked
    decide)

/-! Provider-call assignment state cannot contain duplicate provider identifiers. -/

/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs (substring := true) in
example : SessionRefinement.BindingState where
  nextLocalId := 2
  bindings := [
    { providerId := "same", localId := { value := 0 } },
    { providerId := "same", localId := { value := 1 } }
  ]
  providerNodup := by decide
  localNodup := by decide
  localBelowNext := by decide

/-! Definition 41 continuations retain the exact heterogeneous prior outcome type. -/

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
example : OperationIndependence.Computation Coeffect.Quotient.Example.coeffects :=
  .step .counter Coeffect.Quotient.Example.counterOp
    Coeffect.Quotient.Example.counterAmount (fun previous ↦
      .step .label OperationIndependence.Example.DistinctKeys.labelOp previous
        (fun _ ↦ .pure))

/-! Commuting forward maps cannot fabricate Definition 19 inverse stability. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : Transformation.InverseStable
    OperationIndependence.Example.ForwardOnlyGap.sensitiveX
    (fun state ↦ (OperationIndependence.Example.ForwardOnlyGap.bumpY state).after) := by
  intro state
  rfl

/-! An occupied global fiber name cannot satisfy the insertion freshness witness. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : Coeffect.Absent GlobalRegistry.Example.withProvider.registry 0 := by
  constructor
  rfl

/-! A list that drops a retained inverse cannot witness Corollary 21's permutation. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : (Removal.yieldedInverses Removal.Example.effects Removal.Example.initial).Perm
    [Removal.Example.inverseX, Removal.Example.inverseY] := by
  simp [Removal.Example.effects]

/-! Observationally related contexts do not provide exact representative equality for free. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : MediatedIndependence.ExactRepresentativeCoherence
    (Coeffect.Observational.equivalencesOf
      MediatedIndependence.Counterexample.coeffects) := by
  intro left right related
  rfl

/-! An inertia policy that denies abortion cannot fabricate an abort-before-landing witness. -/

/-- error: Tactic `assumption` failed -/
#guard_msgs (substring := true) in
example : GlobalLifecycle.Example.inertia.canAbort 0 10
    GlobalLifecycle.Example.beginState := by
  trivial

/-! A state containing a registered fiber cannot witness Definition 53's empty origin. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalCalculus.EmptyRegistry GlobalLifecycle.Example.start := by
  intro name
  rfl

/-! The heterogeneous mediated continuation still requires its exact `Nat` root outcome. -/

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
example : OperationIndependence.Computation
    MediatedTheorem.Example.IndependentBranching.demoCoeffects :=
  MediatedTheorem.Example.IndependentBranching.leftNext true

/-! Bare unload admission cannot fabricate the missing foreign-recovery confinement law. -/

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example : GlobalTraceFacts.RecoveryConfinement
    GlobalTraceFacts.Counterexample.dynamics
    (GlobalTraceFacts.Counterexample.state 7) false [.external ()] := by
  constructor

/-! An exact iterator landing does not make its map executable at every off-source state. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalTemporal.Step.partialMap GlobalCalculus.Example.iterStep
    GlobalCalculus.Example.emptyStart =
      some GlobalLifecycle.Example.firstStep.after := by
  rfl

/-! Whole-run equality cannot fabricate commutation of differently seeded inverse generators. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : PartialTransformation.Commutes
    (PartialTransformation.total PartialTransformation.WholeRunGap.falseResult.undo)
    (PartialTransformation.total PartialTransformation.WholeRunGap.trueResult.undo) := by
  intro state
  rfl

/-! Exact commutation does not fabricate quotient respect. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : ObservationalPartialTransformation.Respects
    ObservationalPartialTransformation.RespectGap.modelRelation
    ObservationalPartialTransformation.RespectGap.badPartial := by
  intro _ _ _
  rfl

/-! Effect observation does not fabricate rule-level registry-domain equality. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalRelations.RuleRelated GlobalRelations.Example.universalValues
    GlobalRelations.Example.emptyState GlobalRelations.Example.vestigialState := by
  rfl

/-! Same-owner lifecycle traces cannot use the foreign-table confinement shortcut. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalSpatial.TraceForeignTo GlobalCalculus.Example.unifiedTrace 0 := by
  intro _ _
  rfl

/-! Literal Lemma 57 cannot omit either newly exposed parent-pointer exception. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalVestigial.AvoidsVestigialParent
    GlobalVestigial.Counterexample.Name.vestigial
    GlobalVestigial.Counterexample.adoptingInsert := by
  rfl

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : ¬GlobalVestigial.RemovesVestigialParent
    GlobalVestigial.Counterexample.vestigial
    GlobalVestigial.Counterexample.removeParentAfterChild := by
  rfl

/-! Rule observation alone cannot transport an ambient-sensitive abort policy. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalRuleInvariance.InertiaRespectsRuleRelated
    GlobalRuleInvariance.HeterogeneousExample.values
    GlobalDynamics.Example.dynamics
    GlobalRuleInvariance.InertiaGap.ambientSensitiveInertia := by
  rfl

/-! Rule observation does not fabricate exact active-context or ambient equality. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalRegistry.activeContext GlobalRuleObservations.HeterogeneousExample.leftState =
    GlobalRegistry.activeContext GlobalRuleObservations.HeterogeneousExample.rightState := by
  rfl

/-! Finish cannot expose unrelated tables hidden during reloading. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalRuleObservations.FiberTableRelated
    GlobalLifecycleBisimulation.FinishSeam.values
    (GlobalLifecycleBisimulation.FinishSeam.fiber 7)
    (GlobalLifecycleBisimulation.FinishSeam.fiber 8) := by
  rfl

/-! The old opaque name-equivariance record does not imply a bijective name action. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : Function.Injective
    (GlobalNameAction.ConstantNameGap.badAssumption.actName ()) := by
  rfl

/-! Carrier actions do not fabricate fixed catalog-entry semantics. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalNameAction.NameAction.CatalogEntryInvariant
    GlobalNameLifecycle.NonidentityRaiseExample.entryBreakingAction
    GlobalNameAction.Example.exampleCatalog := by
  rfl

/-! One family occurrence does not make a real iterator program self-independent. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalIteratorIndependence.Independent
    GlobalIteratorIndependence.Example.program
    GlobalIteratorIndependence.Example.program := by
  rfl

/-! A registration component alone does not determine its child-indexed continuation. -/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalIteratorIndependence.RawRegistrationGap.request.next false =
    GlobalIteratorIndependence.RawRegistrationGap.request.next true := by
  rfl

/-!
Semantic yield agreement cannot fabricate the syntactic undo equality stored by lifecycle phases.
-/

/-- error: Tactic `rfl` failed -/
#guard_msgs (substring := true) in
example : GlobalTransposition.LifecycleYieldAgrees
    GlobalTransposition.Counterexample.falseStep
    GlobalTransposition.Counterexample.trueStep := by
  refine {
    undo_eq := ?_
    continuation := GlobalTransposition.Counterexample.semantic_yields_agree.continuation
    kind := GlobalTransposition.Counterexample.semantic_yields_agree.kind
  }
  rfl

/-! Full iterator independence cannot fabricate readability across a foreign phase edit. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example : GlobalTransposition.ForeignPhaseCompatibility
    GlobalForeignPhase.IndependenceGap.observedProgram :=
  GlobalForeignPhase.IndependenceGap.programs_independent

end Cordis.NegativeTests
