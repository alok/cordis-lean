import Cordis.GlobalSpatial
import Cordis.GlobalTraceRewrite

/-!
# Corrected finite global deletion replay

This module isolates the strongest exact deletion substrate justified by the current finite global
calculus. It constructs dependent trace filters one constructor at a time and proves an exact
finite replay theorem for safe foreign orchestration suffixes after a finite family of entries has
already been proved vestigial.

It is deliberately not CORDIS paper Lemma 72 or Theorem 73. Definition 53 puts a closing episode's
opening L-Begin at `b - 1`, while printed Lemma 72 deletes owner steps only in `[b,u]`; the future
corrected selection is `BoundedEpisode.core`, corresponding to `[b - 1,u]`. Full episode deletion
still needs temporal recovery, lifecycle/read/oracle/inertia/recovery simulation, registration and
retirement provenance, no-redraw or lifetime indexing, and a birth-erased outside relation.

The negative models come first. They kernel-check the parent-enablement, well-formedness,
allocator-clock, surviving-birth-order, and name-redraw obstructions that prevent the exact suffix
theorem below from being overstated as the paper result.
-/

set_option autoImplicit false

namespace Cordis.GlobalDeletion

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalCalculus Cordis.GlobalTraceFacts Cordis.GlobalTraceRewrite
open Cordis.GlobalVestigial Cordis.GlobalSpatial
open Cordis.GlobalActivationOrchestrationTransposition

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Parent-closure surfaces -/

/-- No retained registry entry points to a name selected for deletion. -/
def NoSurvivingParentRefs
    (deleted : sig.Name → Prop) (state : State catalog Ambient) : Prop :=
  ∀ child fiber, state.registry child = some fiber → ¬deleted child →
    ∀ parent, fiber.parent = some parent → ¬deleted parent

/-- Deleting a parent forces deletion of every currently present child. -/
def DescendantClosed
    (deleted : sig.Name → Prop) (state : State catalog Ambient) : Prop :=
  ∀ child fiber parent, state.registry child = some fiber →
    fiber.parent = some parent → deleted parent → deleted child

theorem descendantClosed_iff_noSurvivingParentRefs
    (deleted : sig.Name → Prop) (state : State catalog Ambient) :
    DescendantClosed deleted state ↔ NoSurvivingParentRefs deleted state := by
  constructor
  · intro closed child fiber present survives parent parentEq erasedParent
    exact survives (closed child fiber parent present parentEq erasedParent)
  · intro safe child fiber parent present parentEq erasedParent
    by_cases erasedChild : deleted child
    · exact erasedChild
    · exact False.elim (safe child fiber present erasedChild parent parentEq erasedParent)

/-- A retained O-Insert does not adopt any selected name as its parent. -/
def AvoidsDeletedParents
    (deleted : sig.Name → Prop)
    {before after : State catalog Ambient}
    (step : OrchestrationStep before after) : Prop :=
  ∀ name, deleted name → AvoidsVestigialParent name step

/-! ## Full-trace parent and allocator counterexample -/

namespace ParentGap

abbrev dynamics := Cordis.GlobalLifecycle.Example.dynamics
abbrev inertia := Cordis.GlobalLifecycle.Example.inertia

open Cordis.GlobalRegistry.Example

abbrev exampleCatalog := Cordis.GlobalRegistry.Example.catalog
abbrev ExampleState := GlobalState exampleCatalog Nat

def source : ExampleState := Cordis.GlobalLifecycle.Example.start

def providerFiber : Fiber exampleCatalog where
  component := .provider
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

theorem source_provider : source.registry 0 = some providerFiber := rfl

def registered : ExampleState := insertFiber source 1 (some 0) .consumer

def registeredChildFiber : Fiber exampleCatalog where
  component := .consumer
  parent := some 0
  birth := source.nextBirth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

theorem registered_child_present :
    registered.registry 1 = some registeredChildFiber := by
  simp [registered, registeredChildFiber]

def registerChild : OrchestrationStep source registered :=
  .insert source 1 (by constructor; rfl) (some 0) (by
    intro parent equal
    have parentEq : parent = 0 := Option.some.inj equal.symm
    subst parent
    exact ⟨_, rfl⟩) .consumer (by simp [consumerDecl])

def adoptionAfter : ExampleState := insertFiber registered 2 (some 1) .consumer

def adoptingInsert : OrchestrationStep registered adoptionAfter :=
  .insert registered 2 (by constructor; rfl) (some 1) (by
    intro parent equal
    have parentEq : parent = 1 := Option.some.inj equal.symm
    subst parent
    exact ⟨registeredChildFiber, registered_child_present⟩) .consumer
      (by simp [consumerDecl])

def trace : GlobalCalculus.Trace dynamics inertia source adoptionAfter :=
  .cons (.orchestration registerChild) (.cons (.orchestration adoptingInsert) (.nil _))

theorem source_wellFormed : WellFormed source := Cordis.GlobalLifecycle.Example.start_wellFormed

theorem registered_wellFormed : WellFormed registered :=
  registerChild.preservesWellFormed source_wellFormed

theorem adoptionAfter_wellFormed : WellFormed adoptionAfter :=
  adoptingInsert.preservesWellFormed registered_wellFormed

theorem trace_rules : trace.rules = [GlobalCalculus.Rule.oInsert, .oInsert] := rfl

theorem trace_actors : trace.actors = [Actor.fiber 1, Actor.fiber 2] := rfl

theorem removing_child_does_not_restore_clock :
    removeFiber registered 1 ≠ source := by
  intro equal
  have clockEq := congrArg GlobalState.nextBirth equal
  change source.nextBirth + 1 = source.nextBirth at clockEq
  omega

/-- The retained second record has no same-template replay before child `1` exists. -/
theorem no_surviving_same_template_insert :
    ¬∃ earlyAfter, ∃ early : OrchestrationStep source earlyAfter,
      Cordis.GlobalActivationOrchestrationTransposition.SameOrchestrationTemplate
        early adoptingInsert := by
  rintro ⟨earlyAfter, early, template⟩
  cases early with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      have actorEq := template.same_actor
      change inserted = 2 at actorEq
      subst inserted
      have replayEq := template.replay_eq
      change (fun state : ExampleState => insertFiber state 2 parent component) =
        (fun state : ExampleState => insertFiber state 2 (some 1)
          Component.consumer) at replayEq
      have endpointEq := congrFun replayEq source
      have lookupEq := congrArg (fun state => state.registry 2) endpointEq
      rw [insertFiber_lookup_same, insertFiber_lookup_same] at lookupEq
      have fiberEq := Option.some.inj lookupEq
      have parentIsDeleted : parent = some 1 := congrArg Fiber.parent fiberEq
      obtain ⟨parentFiber, present⟩ := parentPresent 1 parentIsDeleted
      rw [show source.registry 1 = none by rfl] at present
      cases present
  | retire name fiber present =>
      have impossible := template.same_kind
      change OrchestrationKind.retire = .insert at impossible
      cases impossible
  | remove name fiber present retired inactive childless =>
      have impossible := template.same_kind
      change OrchestrationKind.remove = .insert at impossible
      cases impossible

theorem final_parent_closure_fails :
    ¬NoSurvivingParentRefs (fun name : Nat => name = 1) adoptionAfter := by
  intro safe
  have childPresent : adoptionAfter.registry 2 = some {
      component := .consumer
      parent := some 1
      birth := registered.nextBirth
      table := Coeffect.empty
      table_within_provision := by simp
      retired := false
      phase := .inactive none
    } := by simp [adoptionAfter]
  exact safe 2 _ childPresent (by decide) 1 rfl rfl

theorem removed_final_not_wellFormed :
    ¬WellFormed (removeFiber adoptionAfter 1) := by
  intro wf
  let child : Fiber exampleCatalog := {
    component := .consumer
    parent := some 1
    birth := registered.nextBirth
    table := Coeffect.empty
    table_within_provision := by simp
    retired := false
    phase := .inactive none
  }
  have beforeLookup : adoptionAfter.registry 2 = some child := by
    simp [adoptionAfter, child]
  have afterLookup : (removeFiber adoptionAfter 1).registry 2 = some child := by
    simpa [removeFiber_lookup_other, show (2 : Nat) ≠ 1 by decide] using beforeLookup
  obtain ⟨parentFiber, parentLookup⟩ :=
    wf.parent_present 2 child 1 afterLookup rfl
  rw [removeFiber_lookup_same] at parentLookup
  cases parentLookup

end ParentGap

/-! ## Exact landing and episode provenance -/

/-- Actual registered child for every landing lifecycle rule, including landing L-Divert. -/
def transitionRegisteredChild
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Transition dynamics inertia before after) : Option sig.Name := by
  cases step with
  | iter owner fiber present code undos committed phase target landing next continues =>
      exact Cordis.GlobalActivationOrchestrationTransposition.stepRegisteredChild landing.step
  | finish owner fiber present code undos committed phase target landing done =>
      exact Cordis.GlobalActivationOrchestrationTransposition.stepRegisteredChild landing.step
  | divertLand owner fiber present code undos committed phase targetChanged landing =>
      exact Cordis.GlobalActivationOrchestrationTransposition.stepRegisteredChild landing.step
  | begin | divertAbort | raise | leave | unload => exact none

/-- Unified-step projection of every actual landing registration child. -/
def landedRegisteredChild
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Option sig.Name :=
  match step with
  | .orchestration _ => none
  | .lifecycle transition => transitionRegisteredChild transition

/-- Exact fixed-program provenance for Iter, Finish, and landing Divert occurrences. -/
inductive LandingOccurrence
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics} :
    {before after : State catalog Ambient} →
      Step dynamics inertia before after → Type (u + 1) where
  | iter
      {before : State catalog Ambient}
      (program : Cordis.GlobalIteratorIndependence.Program dynamics)
      (fiber : Fiber catalog) (present : before.registry program.owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (target : targetView before program.owner fiber = some committed)
      (landing : Landing dynamics program.owner code before fiber)
      (program_witness :
        Cordis.GlobalLandingTransposition.LandingProgramWitness program landing)
      (next : sig.IteratorCode) (continues : landing.step.next = some next) :
      LandingOccurrence (.lifecycle (.iter before program.owner fiber present code undos
        committed phase target landing next continues))
  | finish
      {before : State catalog Ambient}
      (program : Cordis.GlobalIteratorIndependence.Program dynamics)
      (fiber : Fiber catalog) (present : before.registry program.owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (target : targetView before program.owner fiber = some committed)
      (landing : Landing dynamics program.owner code before fiber)
      (program_witness :
        Cordis.GlobalLandingTransposition.LandingProgramWitness program landing)
      (done : landing.step.next = none) :
      LandingOccurrence (.lifecycle (.finish before program.owner fiber present code undos
        committed phase target landing done))
  | divertLand
      {before : State catalog Ambient}
      (program : Cordis.GlobalIteratorIndependence.Program dynamics)
      (fiber : Fiber catalog) (present : before.registry program.owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (targetChanged : targetView before program.owner fiber ≠ some committed)
      (landing : Landing dynamics program.owner code before fiber)
      (program_witness :
        Cordis.GlobalLandingTransposition.LandingProgramWitness program landing) :
      LandingOccurrence (.lifecycle (.divertLand before program.owner fiber present code
        undos committed phase targetChanged landing))

/-- Assign all five intrinsic pieces of one located episode. -/
structure AssignedLocatedEpisode
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) where
  beforeAssignment :
    TraceProgramAssignment dynamics inertia located.episode.beforeTrace
  openAssignment : StepProgramAssignment located.episode.openStep
  interiorAssignment :
    TraceProgramAssignment dynamics inertia located.episode.interior
  closeAssignment : StepProgramAssignment located.episode.closeStep
  afterAssignment : TraceProgramAssignment dynamics inertia located.episode.afterTrace

noncomputable def AssignedLocatedEpisode.masterAssignment
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    {located : LocatedEpisode dynamics inertia master}
    (assigned : AssignedLocatedEpisode located) :
    TraceProgramAssignment dynamics inertia master := by
  let closeAndAfter : TraceProgramAssignment dynamics inertia
      (.cons located.episode.closeStep located.episode.afterTrace) :=
    .cons assigned.closeAssignment assigned.afterAssignment
  let interiorAndAfter := TraceProgramAssignment.append
    assigned.interiorAssignment closeAndAfter
  let openAndAfter : TraceProgramAssignment dynamics inertia
      (.cons located.episode.openStep
        (GlobalTraceFacts.Trace.append located.episode.interior
          (.cons located.episode.closeStep located.episode.afterTrace))) :=
    .cons assigned.openAssignment interiorAndAfter
  let complete := TraceProgramAssignment.append assigned.beforeAssignment openAndAfter
  rw [← located.trace_eq]
  exact complete

/-- One exact registered child witnessed inside the selected episode core. -/
structure RegisteredChildInEpisode
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) (child : sig.Name) where
  record : StepRecord dynamics inertia
  member : record ∈
    GlobalTraceFacts.Trace.records (GlobalSpatial.BoundedEpisode.core located.episode)
  owner : record.step.actedName = located.episode.name
  landing : LandingOccurrence record.step
  registered : landedRegisteredChild record.step = some child

/-- Name-level finite ledger of all and only registered children in the selected core. -/
structure RegistrationLedger
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) where
  names : List sig.Name
  nodup : names.Nodup
  complete : ∀ child, child ∈ names ↔ Nonempty (RegisteredChildInEpisode located child)

/-- Explicit corrected boundary: every registered child is actually vestigial after closing. -/
structure VestigialRegistrationBoundary
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    {located : LocatedEpisode dynamics inertia master}
    (ledger : RegistrationLedger located) where
  witness : ∀ child, child ∈ ledger.names →
    Vestigial located.episode.closeAfter child

/-- Owner-only core policy; child drops need positional or lifetime evidence. -/
def MayDropInCore
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    (owner : sig.Name) (record : StepRecord dynamics inertia) : Prop :=
  record.step.actedName = owner

/-- Bare-name suffix policy, sound only with the explicit no-redraw boundary below. -/
def MayDropInSuffix
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    (deleted : List sig.Name) (record : StepRecord dynamics inertia) : Prop :=
  record.step.actedName ∈ deleted

/-! ## Intrinsic keep/drop replay -/

/-- One retained occurrence replayed from the current shadow state. -/
structure RetainedStep
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  replay : Step dynamics inertia shadowBefore shadowAfter
  same_rule : replay.rule = source.rule
  same_actor : replay.actor = source.actor
  transportAssignment : StepProgramAssignment source → StepProgramAssignment replay

/-- Constructor-by-constructor source filtering with an intrinsically adjacent replay trace. -/
inductive DeletionReplay
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    (Related : State catalog Ambient → State catalog Ambient → Prop)
    (MayDrop : StepRecord dynamics inertia → Prop) :
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient} →
      GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter →
      GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter → Type (u + 1) where
  | nil {source shadow : State catalog Ambient}
      (related : Related source shadow) :
      DeletionReplay Related MayDrop (.nil source) (.nil shadow)
  | keep
      {sourceBefore sourceMiddle sourceAfter shadowBefore shadowAfter :
        State catalog Ambient}
      {sourceHead : Step dynamics inertia sourceBefore sourceMiddle}
      {sourceTail : GlobalCalculus.Trace dynamics inertia sourceMiddle sourceAfter}
      (related : Related sourceBefore shadowBefore)
      (retained : RetainedStep (shadowBefore := shadowBefore) sourceHead)
      {shadowTail : GlobalCalculus.Trace dynamics inertia retained.shadowAfter shadowAfter}
      (tail : DeletionReplay Related MayDrop sourceTail shadowTail) :
      DeletionReplay Related MayDrop (.cons sourceHead sourceTail)
        (.cons retained.replay shadowTail)
  | drop
      {sourceBefore sourceMiddle sourceAfter shadowBefore shadowAfter : State catalog Ambient}
      {sourceHead : Step dynamics inertia sourceBefore sourceMiddle}
      {sourceTail : GlobalCalculus.Trace dynamics inertia sourceMiddle sourceAfter}
      {shadowTrace : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
      (related : Related sourceBefore shadowBefore)
      (mayDrop : MayDrop ⟨sourceBefore, sourceMiddle, sourceHead⟩)
      (tail : DeletionReplay Related MayDrop sourceTail shadowTrace) :
      DeletionReplay Related MayDrop (.cons sourceHead sourceTail) shadowTrace

/-- Existential replay endpoint packaged without weakening the intrinsic trace indices. -/
structure DeletionResult
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    (Related : State catalog Ambient → State catalog Ambient → Prop)
    (MayDrop : StepRecord dynamics inertia → Prop)
    {sourceBefore sourceAfter : State catalog Ambient}
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (shadowBefore : State catalog Ambient) where
  shadowAfter : State catalog Ambient
  shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter
  certificate : DeletionReplay Related MayDrop source shadow

inductive ReplayDecision where
  | keep
  | drop
deriving DecidableEq, Repr

namespace DeletionReplay

def decisions
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter} :
    DeletionReplay Related MayDrop source shadow → List ReplayDecision
  | .nil _ => []
  | .keep _ _ tail => .keep :: decisions tail
  | .drop _ _ tail => .drop :: decisions tail

theorem decisions_length
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    replay.decisions.length = (GlobalTraceFacts.Trace.records source).length := by
  induction replay with
  | nil => rfl
  | keep related retained tail ih =>
      simp [decisions, GlobalTraceFacts.Trace.records, ih]
  | drop related mayDrop tail ih =>
      simp [decisions, GlobalTraceFacts.Trace.records, ih]

noncomputable def transportAssignment
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceProgramAssignment dynamics inertia shadow := by
  induction replay with
  | nil => exact .nil _
  | keep related retained tail ih =>
      cases assignment with
      | cons headAssignment tailAssignment =>
          exact .cons (retained.transportAssignment headAssignment) (ih tailAssignment)
  | drop related mayDrop tail ih =>
      cases assignment with
      | cons headAssignment tailAssignment => exact ih tailAssignment

theorem final_related
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    Related sourceAfter shadowAfter := by
  induction replay with
  | nil related => exact related
  | keep related retained tail ih => exact ih
  | drop related mayDrop tail ih => exact ih

theorem rules_sublist
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    shadow.rules.Sublist source.rules := by
  induction replay with
  | nil => exact .slnil
  | keep related retained tail ih =>
      simp only [GlobalCalculus.Trace.rules]
      rw [retained.same_rule]
      exact .cons_cons _ ih
  | drop related mayDrop tail ih =>
      simp only [GlobalCalculus.Trace.rules]
      exact .cons _ ih

theorem actors_sublist
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    shadow.actors.Sublist source.actors := by
  induction replay with
  | nil => exact .slnil
  | keep related retained tail ih =>
      simp only [GlobalCalculus.Trace.actors]
      rw [retained.same_actor]
      exact .cons_cons _ ih
  | drop related mayDrop tail ih =>
      simp only [GlobalCalculus.Trace.actors]
      exact .cons _ ih

theorem shadow_aligned
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (_replay : DeletionReplay Related MayDrop source shadow) :
    GlobalTraceFacts.Trace.Aligned dynamics inertia
      (GlobalTraceFacts.Trace.states shadow) (GlobalTraceFacts.Trace.records shadow) :=
  GlobalTraceFacts.Trace.aligned shadow

theorem records_length_le
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    (GlobalTraceFacts.Trace.records shadow).length ≤
      (GlobalTraceFacts.Trace.records source).length := by
  induction replay with
  | nil => simp [GlobalTraceFacts.Trace.records]
  | keep related retained tail ih =>
      simpa [GlobalTraceFacts.Trace.records] using Nat.succ_le_succ ih
  | drop related mayDrop tail ih =>
      simp only [GlobalTraceFacts.Trace.records, List.length_cons]
      omega

theorem rules_length_le
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    shadow.rules.length ≤ source.rules.length :=
  replay.rules_sublist.length_le

theorem actors_length_le
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {Related : State catalog Ambient → State catalog Ambient → Prop}
    {MayDrop : StepRecord dynamics inertia → Prop}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter}
    (replay : DeletionReplay Related MayDrop source shadow) :
    shadow.actors.length ≤ source.actors.length :=
  replay.actors_sublist.length_le

end DeletionReplay

/-! ## Exact multi-vestigial orchestration replay -/

theorem forwardOrchestration_sameTemplate
    {state after : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    (step : OrchestrationStep state after)
    (foreign : orchestrationName step ≠ name)
    (parentSafe : AvoidsVestigialParent name step) :
    Cordis.GlobalActivationOrchestrationTransposition.SameOrchestrationTemplate
      (vestigial.forward_orchestration step foreign parentSafe).matched step := by
  cases step <;> exact ⟨rfl, rfl, rfl⟩

theorem forwardOrchestration_avoidsParent
    {state after : State catalog Ambient} {name other : sig.Name}
    (vestigial : Vestigial state name)
    (step : OrchestrationStep state after)
    (foreign : orchestrationName step ≠ name)
    (parentSafe : AvoidsVestigialParent name step)
    (otherSafe : AvoidsVestigialParent other step) :
    AvoidsVestigialParent other
      (vestigial.forward_orchestration step foreign parentSafe).matched := by
  cases step <;> exact otherSafe

def Vestigial.remove_other
    {state : State catalog Ambient} {kept removed : sig.Name}
    (vestigial : Vestigial state kept) (different : kept ≠ removed) :
    Vestigial (removeFiber state removed) kept where
  fiber := vestigial.fiber
  present := by
    simpa [removeFiber_lookup_other, different] using vestigial.present
  retired := vestigial.retired
  inactive := vestigial.inactive
  table_empty := vestigial.table_empty
  childless := by
    intro child fiber lookup
    by_cases childRemoved : child = removed
    · subst child
      rw [removeFiber_lookup_same] at lookup
      cases lookup
    · have original : state.registry child = some fiber := by
        simpa [removeFiber_lookup_other, childRemoved] using lookup
      exact vestigial.childless child fiber original

/-- A finite family simultaneously vestigial at one source state. -/
structure VestigialNames (state : State catalog Ambient) (names : List sig.Name) where
  nodup : names.Nodup
  witness : ∀ name, name ∈ names → Vestigial state name

/-- Ordered erasure; no permutation-independence claim is made here. -/
def removeNames (state : State catalog Ambient) : List sig.Name → State catalog Ambient
  | [] => state
  | name :: names => removeNames (removeFiber state name) names

def SafeForVestigialNames
    (names : List sig.Name) {before after : State catalog Ambient}
    (step : OrchestrationStep before after) : Prop :=
  orchestrationName step ∉ names ∧
    AvoidsDeletedParents (fun name ↦ name ∈ names) step

theorem safeForVestigialNames_iff_pointwise
    {names : List sig.Name} {before after : State catalog Ambient}
    {step : OrchestrationStep before after} :
    SafeForVestigialNames names step ↔
      ∀ name, name ∈ names →
        orchestrationName step ≠ name ∧ AvoidsVestigialParent name step := by
  constructor
  · intro safe name member
    constructor
    · intro actorEq
      apply safe.1
      simpa [actorEq] using member
    · exact safe.2 name member
  · intro pointwise
    constructor
    · intro actorMember
      exact (pointwise (orchestrationName step) actorMember).1 rfl
    · intro name member
      exact (pointwise name member).2

structure ForwardNamesStepSquare
    {before after : State catalog Ambient} {names : List sig.Name}
    (family : VestigialNames before names)
    (step : OrchestrationStep before after) where
  removedAfter : State catalog Ambient
  matched : OrchestrationStep (removeNames before names) removedAfter
  same_template :
    Cordis.GlobalActivationOrchestrationTransposition.SameOrchestrationTemplate matched step
  remove_after : removeNames after names = removedAfter
  remains : VestigialNames after names

noncomputable def forwardNamesStep
    {before after : State catalog Ambient} {names : List sig.Name}
    (family : VestigialNames before names)
    (step : OrchestrationStep before after)
    (safe : SafeForVestigialNames names step) :
    ForwardNamesStepSquare family step := by
  induction names generalizing before after with
  | nil =>
      exact {
        removedAfter := after
        matched := step
        same_template := ⟨rfl, rfl, rfl⟩
        remove_after := rfl
        remains := {
          nodup := by simp
          witness := by intro name member; simp at member
        }
      }
  | cons head tail ih =>
      have pointwise := safeForVestigialNames_iff_pointwise.mp safe
      have headMem : head ∈ head :: tail := by simp
      let headVestigial := family.witness head headMem
      have headSafe := pointwise head headMem
      let headSquare :=
        headVestigial.forward_orchestration step headSafe.1 headSafe.2
      have nodupParts := List.nodup_cons.mp family.nodup
      let tailFamily : VestigialNames (removeFiber before head) tail := {
        nodup := nodupParts.2
        witness := by
          intro name member
          have original := family.witness name (by simp [member])
          apply Vestigial.remove_other original
          intro equal
          subst name
          exact nodupParts.1 member
      }
      have tailSafe : SafeForVestigialNames tail headSquare.matched := by
        apply safeForVestigialNames_iff_pointwise.mpr
        intro name member
        have original := pointwise name (by simp [member])
        have same := forwardOrchestration_sameTemplate headVestigial step
          headSafe.1 headSafe.2
        constructor
        · intro matchedActor
          exact original.1 (same.same_actor.symm.trans matchedActor)
        · exact forwardOrchestration_avoidsParent headVestigial step
            headSafe.1 headSafe.2 original.2
      let tailSquare := ih tailFamily headSquare.matched tailSafe
      let afterFamily : VestigialNames after (head :: tail) := {
        nodup := family.nodup
        witness := by
          intro name member
          have original := family.witness name member
          have occurrenceSafe := pointwise name member
          exact (original.forward_orchestration step occurrenceSafe.1
            occurrenceSafe.2).remains_vestigial
      }
      exact {
        removedAfter := tailSquare.removedAfter
        matched := by
          simpa [removeNames, headSquare] using tailSquare.matched
        same_template := {
          same_kind := tailSquare.same_template.same_kind.trans
            (forwardOrchestration_sameTemplate headVestigial step
              headSafe.1 headSafe.2).same_kind
          same_actor := tailSquare.same_template.same_actor.trans
            (forwardOrchestration_sameTemplate headVestigial step
              headSafe.1 headSafe.2).same_actor
          replay_eq := tailSquare.same_template.replay_eq.trans
            (forwardOrchestration_sameTemplate headVestigial step
              headSafe.1 headSafe.2).replay_eq
        }
        remove_after := by
          simpa [removeNames, headSquare.remove_after] using tailSquare.remove_after
        remains := afterFamily
      }

inductive SafeNamesOrchestrationTrace
    (names : List sig.Name)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    {before after : State catalog Ambient} →
      GlobalCalculus.Trace dynamics inertia before after → Type (u + 1) where
  | nil (state : State catalog Ambient) :
      SafeNamesOrchestrationTrace names dynamics inertia (.nil state)
  | cons
      {before middle after : State catalog Ambient}
      (step : OrchestrationStep before middle)
      (tail : GlobalCalculus.Trace dynamics inertia middle after)
      (stepSafe : SafeForVestigialNames names step)
      (tailSafe : SafeNamesOrchestrationTrace names dynamics inertia tail) :
      SafeNamesOrchestrationTrace names dynamics inertia
        (.cons (.orchestration step) tail)

/-- Positional equality of orchestration edit templates for two intrinsic traces. -/
inductive SameOrchestrationTraceTemplate
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) :
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient} →
      GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter →
      GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter → Type (u + 1) where
  | nil (source shadow : State catalog Ambient) :
      SameOrchestrationTraceTemplate dynamics inertia (.nil source) (.nil shadow)
  | cons
      {sourceBefore sourceMiddle sourceAfter shadowBefore shadowMiddle shadowAfter :
        State catalog Ambient}
      (source : OrchestrationStep sourceBefore sourceMiddle)
      (shadow : OrchestrationStep shadowBefore shadowMiddle)
      (sourceTail : GlobalCalculus.Trace dynamics inertia sourceMiddle sourceAfter)
      (shadowTail : GlobalCalculus.Trace dynamics inertia shadowMiddle shadowAfter)
      (same : Cordis.GlobalActivationOrchestrationTransposition.SameOrchestrationTemplate
        shadow source)
      (tail : SameOrchestrationTraceTemplate dynamics inertia sourceTail shadowTail) :
      SameOrchestrationTraceTemplate dynamics inertia
        (.cons (.orchestration source) sourceTail)
        (.cons (.orchestration shadow) shadowTail)

def SameOrchestrationTraceTemplate.shadowAssignment
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {sourceBefore sourceAfter shadowBefore shadowAfter : State catalog Ambient}
    {source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter}
    {shadow : GlobalCalculus.Trace dynamics inertia shadowBefore shadowAfter} :
    SameOrchestrationTraceTemplate dynamics inertia source shadow →
      TraceProgramAssignment dynamics inertia shadow
  | .nil _ _ => .nil _
  | .cons source shadow sourceTail shadowTail same tail =>
      .cons (StepProgramAssignment.ofOrchestration shadow) tail.shadowAssignment

structure ForwardNamesTraceSquare
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    (family : VestigialNames before names)
    (trace : GlobalCalculus.Trace dynamics inertia before after) where
  removedAfter : State catalog Ambient
  matched : GlobalCalculus.Trace dynamics inertia (removeNames before names) removedAfter
  rules_eq : matched.rules = trace.rules
  actors_eq : matched.actors = trace.actors
  templates : SameOrchestrationTraceTemplate dynamics inertia trace matched
  remove_after : removeNames after names = removedAfter
  remains : VestigialNames after names
  matchedAssignment : TraceProgramAssignment dynamics inertia matched

noncomputable def forwardNamesOrchestrationTrace
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (family : VestigialNames before names)
    (safe : SafeNamesOrchestrationTrace names dynamics inertia trace) :
    ForwardNamesTraceSquare family trace := by
  induction safe with
  | nil state =>
      exact {
        removedAfter := removeNames state names
        matched := .nil _
        rules_eq := rfl
        actors_eq := rfl
        templates := .nil _ _
        remove_after := rfl
        remains := family
        matchedAssignment := .nil _
      }
  | @cons before middle after step tail stepSafe tailSafe ih =>
      obtain ⟨headAfter, headMatched, headTemplate, headEndpoint, headFamily⟩ :=
        forwardNamesStep family step stepSafe
      cases headEndpoint
      let tailSquare := ih headFamily
      have tags := Cordis.GlobalTraceRewrite.sameOrchestrationTemplate_global_tags
        (dynamics := dynamics) (inertia := inertia) headTemplate
      exact {
        removedAfter := tailSquare.removedAfter
        matched := .cons (.orchestration headMatched) tailSquare.matched
        rules_eq := by
          simp only [GlobalCalculus.Trace.rules]
          rw [tailSquare.rules_eq]
          exact congrArg (fun rule ↦ rule :: tail.rules) tags.1
        actors_eq := by
          simp only [GlobalCalculus.Trace.actors]
          rw [tailSquare.actors_eq]
          exact congrArg (fun actor ↦ actor :: tail.actors) tags.2
        templates := .cons step headMatched tail tailSquare.matched
          headTemplate tailSquare.templates
        remove_after := tailSquare.remove_after
        remains := tailSquare.remains
        matchedAssignment := .cons (StepProgramAssignment.ofOrchestration headMatched)
          tailSquare.matchedAssignment
      }

/-! ## Name-reuse boundary -/

structure FiberLifetime (Name : Type u) where
  name : Name
  birth : Nat

def FiberLifetime.PresentAt
    (lifetime : FiberLifetime sig.Name) (state : State catalog Ambient) : Prop :=
  ∃ fiber, state.registry lifetime.name = some fiber ∧ fiber.birth = lifetime.birth

/-- A step draws `name` exactly when that registry slot changes from absent to present. -/
def DrawsName
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (_step : Step dynamics inertia before after) (name : sig.Name) : Prop :=
  before.registry name = none ∧ ∃ fiber, after.registry name = some fiber

def NoRedraw
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    (names : List sig.Name) {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) : Prop :=
  ∀ record, record ∈ GlobalTraceFacts.Trace.records trace →
    ∀ name, DrawsName record.step name → name ∉ names

namespace RedrawGap

open Cordis.GlobalVestigial.Counterexample

variable (dynamics : Dynamics signature exampleCatalog Unit)
  (inertia : InertiaPolicy dynamics)

def redrawTrace : GlobalCalculus.Trace dynamics inertia withoutVestigial
    (insertFiber withoutVestigial .vestigial none .empty) :=
  .cons (.orchestration redrawVestigial) (.nil _)

theorem redraw_trace_not_noRedraw :
    ¬NoRedraw [Name.vestigial] (redrawTrace dynamics inertia) := by
  intro noRedraw
  have draws : DrawsName
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) redrawVestigial)
      Name.vestigial := by
    constructor
    · exact without_vestigial_absent
    · exact ⟨_, insertFiber_lookup_same _ _ _ _⟩
  have forbidden := noRedraw
    ⟨withoutVestigial, insertFiber withoutVestigial .vestigial none .empty,
      Step.orchestration (dynamics := dynamics) (inertia := inertia) redrawVestigial⟩
    (by simp [redrawTrace, GlobalTraceFacts.Trace.records]) Name.vestigial draws
  exact forbidden (by simp)

end RedrawGap

/-! ## Positive exact suffix and actual keep/drop replay -/

namespace Positive

abbrev dynamics := Cordis.GlobalLifecycle.Example.dynamics
abbrev inertia := Cordis.GlobalLifecycle.Example.inertia

open Cordis.GlobalRegistry.Example

abbrev exampleCatalog := Cordis.GlobalRegistry.Example.catalog
abbrev ExampleState := GlobalState exampleCatalog Nat

def source : ExampleState := Cordis.GlobalLifecycle.Example.start

def providerFiber : Fiber exampleCatalog where
  component := .provider
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

theorem source_provider : source.registry 0 = some providerFiber := rfl

def registered : ExampleState := insertFiber source 1 (some 0) .consumer

def childFiber : Fiber exampleCatalog := {
  component := .consumer
  parent := some 0
  birth := source.nextBirth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none
}

theorem registered_child : registered.registry 1 = some childFiber := by
  simp [registered, childFiber]

def retired : ExampleState := retireFiber registered 1 childFiber

def retiredChild : Fiber exampleCatalog := { childFiber with retired := true }

theorem retired_child : retired.registry 1 = some retiredChild := by
  simp [retired, retiredChild, childFiber]

def vestigial : Vestigial retired 1 where
  fiber := retiredChild
  present := retired_child
  retired := rfl
  inactive := rfl
  table_empty := rfl
  childless := by
    intro child fiber present
    by_cases childOne : child = 1
    · subst child
      rw [retired_child] at present
      have fiberEq := Option.some.inj present
      subst fiber
      decide
    · unfold retired at present
      rw [retireFiber_lookup_other registered 1 child childFiber childOne] at present
      unfold registered at present
      by_cases childZero : child = 0
      · subst child
        rw [insertFiber_lookup_other source 1 0 (some 0) .consumer (by decide)] at present
        rw [source_provider] at present
        have fiberEq := Option.some.inj present
        subst fiber
        decide
      · rw [insertFiber_lookup_other source 1 child (some 0) .consumer childOne] at present
        have sourceAbsent : source.registry child = none := by
          change Cordis.GlobalRegistry.Example.withProvider.registry child = none
          unfold Cordis.GlobalRegistry.Example.withProvider
          rw [insertFiber_lookup_other Cordis.GlobalRegistry.Example.initial 0 child none
            Component.provider childZero]
          rfl
        rw [sourceAbsent] at present
        cases present

def retireProvider : OrchestrationStep retired
    (retireFiber retired 0 providerFiber) :=
  .retire retired 0 providerFiber (by
    unfold retired registered
    change (insertFiber source 1 (some 0) Component.consumer).registry 0 =
      some providerFiber
    rw [insertFiber_lookup_other source 1 0 (some 0) .consumer (by decide)]
    rfl)

def sourceTrace : GlobalCalculus.Trace dynamics inertia retired
    (retireFiber retired 0 providerFiber) :=
  .cons (.orchestration retireProvider) (.nil _)

def family : VestigialNames retired [(1 : Nat)] where
  nodup := by simp
  witness := by
    intro name member
    simp at member
    subst name
    exact vestigial

def namesSafe : SafeNamesOrchestrationTrace [(1 : Nat)] dynamics inertia sourceTrace :=
  .cons retireProvider (.nil _) (by
    constructor
    · change (0 : Nat) ∉ [1]
      decide
    · intro name member
      simp at member
      subst name
      trivial) (.nil _)

noncomputable def namesSquare : ForwardNamesTraceSquare family sourceTrace :=
  forwardNamesOrchestrationTrace family namesSafe

theorem names_endpoint_exact :
    removeNames (retireFiber retired 0 providerFiber) [(1 : Nat)] =
      namesSquare.removedAfter := namesSquare.remove_after

theorem names_rules_exact : namesSquare.matched.rules = sourceTrace.rules :=
  namesSquare.rules_eq

theorem names_actors_exact : namesSquare.matched.actors = sourceTrace.actors :=
  namesSquare.actors_eq

noncomputable def names_family_preserved : VestigialNames
    (retireFiber retired 0 providerFiber) [(1 : Nat)] :=
  namesSquare.remains

noncomputable def namesMatchedAssignment :
    TraceProgramAssignment dynamics inertia namesSquare.matched :=
  namesSquare.matchedAssignment

/-! The generic replay actually drops O-Remove(1) and retains O-Retire(0). -/

def removeChild : OrchestrationStep retired (removeFiber retired 1) :=
  .remove retired 1 retiredChild retired_child rfl vestigial.notInstalled vestigial.childless

def removed : ExampleState := removeFiber retired 1

theorem removed_provider : removed.registry 0 = some providerFiber := by
  have registeredProvider : registered.registry 0 = some providerFiber := by
    unfold registered
    rw [insertFiber_lookup_other source 1 0 (some 0) Component.consumer (by decide)]
    exact source_provider
  have retiredProvider : retired.registry 0 = some providerFiber := by
    unfold retired
    rw [retireFiber_lookup_other registered 1 0 childFiber (by decide)]
    exact registeredProvider
  simpa [removed, removeFiber_lookup_other, show (0 : Nat) ≠ 1 by decide] using
    retiredProvider

def retireProviderRemoved : OrchestrationStep removed
    (retireFiber removed 0 providerFiber) :=
  .retire removed 0 providerFiber removed_provider

def deletionSourceTrace : GlobalCalculus.Trace dynamics inertia retired
    (retireFiber removed 0 providerFiber) :=
  .cons (.orchestration removeChild)
    (.cons (.orchestration retireProviderRemoved) (.nil _))

def deletionShadowTrace : GlobalCalculus.Trace dynamics inertia removed
    (retireFiber removed 0 providerFiber) :=
  .cons (.orchestration retireProviderRemoved) (.nil _)

def retainedProvider : RetainedStep
    (shadowBefore := removed)
    (Step.orchestration (dynamics := dynamics) (inertia := inertia)
      retireProviderRemoved) where
  shadowAfter := retireFiber removed 0 providerFiber
  replay := .orchestration retireProviderRemoved
  same_rule := rfl
  same_actor := rfl
  transportAssignment := fun _ ↦ StepProgramAssignment.ofOrchestration retireProviderRemoved

def mayDropChild (record : StepRecord dynamics inertia) : Prop :=
  record.step.actedName = 1

def deletionReplay :
    DeletionReplay Cordis.GlobalRelations.EffectRelated mayDropChild
      deletionSourceTrace deletionShadowTrace :=
  .drop vestigial.effectRelated_remove rfl <|
    .keep (Cordis.GlobalRelations.effectRelated_refl removed) retainedProvider <|
      .nil (Cordis.GlobalRelations.effectRelated_refl _)

def deletionResult :
    DeletionResult Cordis.GlobalRelations.EffectRelated mayDropChild
      deletionSourceTrace removed where
  shadowAfter := retireFiber removed 0 providerFiber
  shadow := deletionShadowTrace
  certificate := deletionReplay

theorem deletion_result_shadow_eq : deletionResult.shadow = deletionShadowTrace := rfl

theorem deletion_source_rules :
    deletionSourceTrace.rules = [GlobalCalculus.Rule.oRemove, .oRetire] := rfl

theorem deletion_source_actors :
    deletionSourceTrace.actors = [Actor.fiber 1, Actor.fiber 0] := rfl

theorem filtered_rules : deletionShadowTrace.rules = [GlobalCalculus.Rule.oRetire] := rfl

theorem filtered_rule_sublist :
    deletionShadowTrace.rules.Sublist deletionSourceTrace.rules :=
  deletionReplay.rules_sublist

theorem filtered_actors : deletionShadowTrace.actors = [Actor.fiber 0] := rfl

theorem filtered_actor_sublist :
    deletionShadowTrace.actors.Sublist deletionSourceTrace.actors :=
  deletionReplay.actors_sublist

theorem deletion_final_related :
    Cordis.GlobalRelations.EffectRelated
      (retireFiber removed 0 providerFiber) deletionResult.shadowAfter :=
  deletionResult.certificate.final_related

theorem deletion_shadow_aligned :
    GlobalTraceFacts.Trace.Aligned dynamics inertia
      (GlobalTraceFacts.Trace.states deletionResult.shadow)
      (GlobalTraceFacts.Trace.records deletionResult.shadow) :=
  deletionResult.certificate.shadow_aligned

theorem deletion_decisions :
    deletionResult.certificate.decisions = [.drop, .keep] := rfl

theorem deletion_decisions_length :
    deletionResult.certificate.decisions.length =
      (GlobalTraceFacts.Trace.records deletionSourceTrace).length :=
  deletionResult.certificate.decisions_length

def deletionSourceAssignment :
    TraceProgramAssignment dynamics inertia deletionSourceTrace :=
  .cons (StepProgramAssignment.ofOrchestration removeChild) <|
    .cons (StepProgramAssignment.ofOrchestration retireProviderRemoved) (.nil _)

noncomputable def deletionShadowAssignment :
    TraceProgramAssignment dynamics inertia deletionResult.shadow :=
  deletionResult.certificate.transportAssignment deletionSourceAssignment

noncomputable def filtered_assignment
    (assignment : TraceProgramAssignment dynamics inertia deletionSourceTrace) :
    TraceProgramAssignment dynamics inertia deletionShadowTrace :=
  deletionReplay.transportAssignment assignment

end Positive

/-! ## Explicit remaining boundaries -/

/-- Future suffix deletion must allow a selected slot to be vestigial or already absent. -/
def VestigialOrAbsent (state : State catalog Ambient) (name : sig.Name) : Prop :=
  state.registry name = none ∨ Nonempty (Vestigial state name)

theorem vestigialOrAbsent_of_vestigial
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name) : VestigialOrAbsent state name :=
  Or.inr ⟨vestigial⟩

theorem vestigialOrAbsent_after_remove
    (state : State catalog Ambient) (name : sig.Name) :
    VestigialOrAbsent (removeFiber state name) name := by
  left
  exact removeFiber_lookup_same state name

/-- Independent allocator obstruction: swapping two legal insertions exchanges fixed births. -/
theorem registration_insert_birth_order_gap :
    LiteralPaperGap.normal ≠ LiteralPaperGap.swapped :=
  LiteralPaperGap.registration_insert_birth_order_differs

/-- Current rule observation also rejects those opposite allocator orders. -/
theorem registration_insert_rule_relation_gap :
    ¬Cordis.GlobalRelations.RuleRelated
      LiteralPaperGap.exactValues LiteralPaperGap.normal LiteralPaperGap.swapped :=
  LiteralPaperGap.birth_order_not_ruleRelated

/-!
No theorem here deletes a general closing lifecycle episode, derives registration retirement,
simulates lifecycle/read/oracle/inertia/recovery behavior, proves a birth-erased relation, orders a
normalization plan, proves paper Lemma 72, or proves Theorem 73/confluence/termination.
-/

end Cordis.GlobalDeletion
