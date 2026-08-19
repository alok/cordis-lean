import Cordis.GlobalDeletion
import Cordis.GlobalProgress
import Cordis.GlobalRuleInvariance

/-!
# Birth-erased finite paper-visible global relations

This module erases the proof-only allocator clock `GlobalState.nextBirth` and each fiber's `birth`
from rule observation while retaining registry domain, component, parent, retirement, lifecycle
phase, and the active coeffect context. It supplies full-domain and outside-deleted Setoids, their
conjunction with exact effect observation, and a genuine well-formed bidirectional simulation for
the three orchestration constructors.

The outside-deleted relation is intentionally only an observation. Domain differences make a
symmetric operational theorem false; safe finite vestigial replay is therefore directional and is
built from `GlobalDeletion` certificates. Lifecycle behavior is also not determined by this
relation: explicit frontier records retain the missing assignment transport, and ambient- and
clock-sensitive inertia countermodels prevent an accidental full-rule claim.

This is a bounded finite candidate for the paper's visible relations. It does not prove lifecycle
simulation, name quotienting, Lemmas 55--57 or 72, normalization, confluence, termination, or
Theorem 73.
-/

set_option autoImplicit false

namespace Cordis.GlobalPaperRelation

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus
open Cordis.GlobalRelations Cordis.GlobalVestigial Cordis.GlobalRuleInvariance
open Cordis.GlobalDeletion
open Cordis.GlobalTraceRewrite

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-- Rule-visible fiber control after erasing the local allocator birth rank. -/
structure PaperFiberControl (catalog : Catalog sig) where
  component : sig.ComponentId
  parent : Option sig.Name
  retired : Bool
  phase : Phase (catalog.declaration component)

def paperFiberControl (fiber : Fiber catalog) : PaperFiberControl catalog where
  component := fiber.component
  parent := fiber.parent
  retired := fiber.retired
  phase := fiber.phase

def paperControlAt (state : State catalog Ambient) (name : sig.Name) :
    Option (PaperFiberControl catalog) :=
  match state.registry name with
  | none => none
  | some fiber => some (paperFiberControl fiber)

def eraseFiberControl (control : FiberControl catalog) : PaperFiberControl catalog where
  component := control.component
  parent := control.parent
  retired := control.retired
  phase := control.phase

theorem paperControlAt_eq_map_controlAt
    (state : State catalog Ambient) (name : sig.Name) :
    paperControlAt state name =
      (GlobalRelations.controlAt state name).map eraseFiberControl := by
  cases lookup : state.registry name <;> simp [paperControlAt,
    GlobalRelations.controlAt, lookup,
    eraseFiberControl, paperFiberControl, fiberControl]

/-- Paper rule observation: active coeffects and control, but no allocator ranks. -/
def BirthErasedRuleRelated
    (values : ValueSetoids sig) (left right : State catalog Ambient) : Prop :=
  ContextRelated values (activeContext left) (activeContext right) ∧
    ∀ name, paperControlAt left name = paperControlAt right name

theorem birthErasedRuleRelated_refl
    (values : ValueSetoids sig) (state : State catalog Ambient) :
    BirthErasedRuleRelated values state state :=
  ⟨contextRelated_refl values _, fun _ ↦ rfl⟩

theorem birthErasedRuleRelated_symm
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right) :
    BirthErasedRuleRelated values right left :=
  ⟨contextRelated_symm related.1, fun name ↦ (related.2 name).symm⟩

theorem birthErasedRuleRelated_trans
    {values : ValueSetoids sig} {first second third : State catalog Ambient}
    (left : BirthErasedRuleRelated values first second)
    (right : BirthErasedRuleRelated values second third) :
    BirthErasedRuleRelated values first third :=
  ⟨contextRelated_trans left.1 right.1, fun name ↦ (left.2 name).trans (right.2 name)⟩

def birthErasedRuleSetoid
    (values : ValueSetoids sig) : Setoid (State catalog Ambient) where
  r := BirthErasedRuleRelated values
  iseqv := {
    refl := birthErasedRuleRelated_refl values
    symm := birthErasedRuleRelated_symm
    trans := birthErasedRuleRelated_trans
  }

/-- Paper rule observation restricted to names outside the selected deletion set. -/
def BirthErasedRuleRelatedOutside
    (values : ValueSetoids sig) (deleted : sig.Name → Prop)
    (left right : State catalog Ambient) : Prop :=
  ContextRelated values (activeContext left) (activeContext right) ∧
    ∀ name, ¬deleted name → paperControlAt left name = paperControlAt right name

theorem birthErasedRuleRelatedOutside_refl
    (values : ValueSetoids sig) (deleted : sig.Name → Prop)
    (state : State catalog Ambient) :
    BirthErasedRuleRelatedOutside values deleted state state :=
  ⟨contextRelated_refl values _, fun _ _ ↦ rfl⟩

theorem birthErasedRuleRelatedOutside_symm
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : BirthErasedRuleRelatedOutside values deleted left right) :
    BirthErasedRuleRelatedOutside values deleted right left :=
  ⟨contextRelated_symm related.1, fun name outside ↦ (related.2 name outside).symm⟩

theorem birthErasedRuleRelatedOutside_trans
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {first second third : State catalog Ambient}
    (left : BirthErasedRuleRelatedOutside values deleted first second)
    (right : BirthErasedRuleRelatedOutside values deleted second third) :
    BirthErasedRuleRelatedOutside values deleted first third :=
  ⟨contextRelated_trans left.1 right.1,
    fun name outside ↦ (left.2 name outside).trans (right.2 name outside)⟩

def birthErasedRuleOutsideSetoid
    (values : ValueSetoids sig) (deleted : sig.Name → Prop) :
    Setoid (State catalog Ambient) where
  r := BirthErasedRuleRelatedOutside values deleted
  iseqv := {
    refl := birthErasedRuleRelatedOutside_refl values deleted
    symm := birthErasedRuleRelatedOutside_symm
    trans := birthErasedRuleRelatedOutside_trans
  }

/-- Lemma-72-shaped final observation: effects globally, rule control outside deletion. -/
def DeletionRelated
    (values : ValueSetoids sig) (deleted : sig.Name → Prop)
    (left right : State catalog Ambient) : Prop :=
  EffectRelated left right ∧ BirthErasedRuleRelatedOutside values deleted left right

theorem deletionRelated_refl
    (values : ValueSetoids sig) (deleted : sig.Name → Prop)
    (state : State catalog Ambient) : DeletionRelated values deleted state state :=
  ⟨effectRelated_refl state, birthErasedRuleRelatedOutside_refl values deleted state⟩

theorem deletionRelated_symm
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : DeletionRelated values deleted left right) :
    DeletionRelated values deleted right left :=
  ⟨effectRelated_symm related.1, birthErasedRuleRelatedOutside_symm related.2⟩

theorem deletionRelated_trans
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {first second third : State catalog Ambient}
    (left : DeletionRelated values deleted first second)
    (right : DeletionRelated values deleted second third) :
    DeletionRelated values deleted first third :=
  ⟨effectRelated_trans left.1 right.1,
    birthErasedRuleRelatedOutside_trans left.2 right.2⟩

def deletionSetoid
    (values : ValueSetoids sig) (deleted : sig.Name → Prop) :
    Setoid (State catalog Ambient) where
  r := DeletionRelated values deleted
  iseqv := {
    refl := deletionRelated_refl values deleted
    symm := deletionRelated_symm
    trans := deletionRelated_trans
  }

theorem DeletionRelated.effect
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : DeletionRelated values deleted left right) : EffectRelated left right :=
  related.1

theorem DeletionRelated.outside
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : DeletionRelated values deleted left right) :
    BirthErasedRuleRelatedOutside values deleted left right :=
  related.2

theorem paperControlAt_isSome
    (state : State catalog Ambient) (name : sig.Name) :
    (paperControlAt state name).isSome = (state.registry name).isSome := by
  cases lookup : state.registry name <;> simp [paperControlAt, lookup]

theorem birthErased_registry_domain
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right) (name : sig.Name) :
    (left.registry name).isSome = (right.registry name).isSome := by
  rw [← paperControlAt_isSome, ← paperControlAt_isSome, related.2 name]

theorem outside_registry_domain
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : BirthErasedRuleRelatedOutside values deleted left right)
    (name : sig.Name) (kept : ¬deleted name) :
    (left.registry name).isSome = (right.registry name).isSome := by
  rw [← paperControlAt_isSome, ← paperControlAt_isSome, related.2 name kept]

theorem outside_registry_none_iff
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : BirthErasedRuleRelatedOutside values deleted left right)
    (name : sig.Name) (kept : ¬deleted name) :
    left.registry name = none ↔ right.registry name = none := by
  constructor
  · intro leftNone
    have domain := outside_registry_domain related name kept
    rw [leftNone] at domain
    cases rightLookup : right.registry name <;> simp [rightLookup] at domain ⊢
  · intro rightNone
    have domain := outside_registry_domain related name kept
    rw [rightNone] at domain
    cases leftLookup : left.registry name <;> simp [leftLookup] at domain ⊢

theorem birthErased_of_outsideEmpty
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelatedOutside values (fun _ ↦ False) left right) :
    BirthErasedRuleRelated values left right :=
  ⟨related.1, fun name ↦ related.2 name (by simp)⟩

theorem birthErased_of_deletionEmpty
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : DeletionRelated values (fun _ ↦ False) left right) :
    BirthErasedRuleRelated values left right :=
  birthErased_of_outsideEmpty related.2

theorem outside_mono
    {values : ValueSetoids sig} {smaller larger : sig.Name → Prop}
    {left right : State catalog Ambient}
    (included : ∀ name, smaller name → larger name)
    (related : BirthErasedRuleRelatedOutside values smaller left right) :
    BirthErasedRuleRelatedOutside values larger left right := by
  constructor
  · exact related.1
  · intro name outside
    exact related.2 name (fun deleted ↦ outside (included name deleted))

theorem deletion_mono
    {values : ValueSetoids sig} {smaller larger : sig.Name → Prop}
    {left right : State catalog Ambient}
    (included : ∀ name, smaller name → larger name)
    (related : DeletionRelated values smaller left right) :
    DeletionRelated values larger left right :=
  ⟨related.1, outside_mono included related.2⟩

/-! ## Bridges from the current stricter relation -/

theorem birthErased_of_ruleRelated
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) :
    BirthErasedRuleRelated values left right := by
  constructor
  · exact related.1
  · intro name
    rw [paperControlAt_eq_map_controlAt, paperControlAt_eq_map_controlAt]
    exact congrArg (Option.map eraseFiberControl) (related.2.2 name)

theorem outside_of_birthErased
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right) :
    BirthErasedRuleRelatedOutside values deleted left right :=
  ⟨related.1, fun name _ ↦ related.2 name⟩

theorem outside_of_ruleRelated
    {values : ValueSetoids sig} {deleted : sig.Name → Prop}
    {left right : State catalog Ambient}
    (related : RuleRelated values left right) :
    BirthErasedRuleRelatedOutside values deleted left right :=
  outside_of_birthErased (birthErased_of_ruleRelated related)

/-! ## Exact control transport and orchestration matching -/

theorem paperFiberControl_component_eq
    {left right : Fiber catalog}
    (equal : paperFiberControl left = paperFiberControl right) :
    left.component = right.component :=
  congrArg PaperFiberControl.component equal

theorem paperFiberControl_parent_eq
    {left right : Fiber catalog}
    (equal : paperFiberControl left = paperFiberControl right) :
    left.parent = right.parent :=
  congrArg PaperFiberControl.parent equal

theorem paperFiberControl_retired_eq
    {left right : Fiber catalog}
    (equal : paperFiberControl left = paperFiberControl right) :
    left.retired = right.retired :=
  congrArg PaperFiberControl.retired equal

theorem paperFiberControl_installed_iff
    {left right : Fiber catalog}
    (equal : paperFiberControl left = paperFiberControl right) :
    left.Installed ↔ right.Installed := by
  change (paperFiberControl left).phase.Installed ↔
    (paperFiberControl right).phase.Installed
  rw [equal]

theorem paperFiberControl_active_iff
    {left right : Fiber catalog}
    (equal : paperFiberControl left = paperFiberControl right) :
    left.Active ↔ right.Active := by
  change (paperFiberControl left).phase.Active ↔
    (paperFiberControl right).phase.Active
  rw [equal]

structure PaperFiberMatch
    (values : ValueSetoids sig) (source peer : State catalog Ambient)
    (name : sig.Name) (sourceFiber : Fiber catalog) where
  peerFiber : Fiber catalog
  peer_present : peer.registry name = some peerFiber
  control_eq : paperFiberControl sourceFiber = paperFiberControl peerFiber

def matchPaperFiber
    {values : ValueSetoids sig} {source peer : State catalog Ambient}
    {name : sig.Name} {sourceFiber : Fiber catalog}
    (related : BirthErasedRuleRelated values source peer)
    (sourcePresent : source.registry name = some sourceFiber) :
    PaperFiberMatch values source peer name sourceFiber := by
  have controls := related.2 name
  cases peerPresent : peer.registry name with
  | none => simp [paperControlAt, sourcePresent, peerPresent] at controls
  | some peerFiber =>
      refine {
        peerFiber := peerFiber
        peer_present := peerPresent
        control_eq := ?_
      }
      have optionEq : some (paperFiberControl sourceFiber) =
          some (paperFiberControl peerFiber) := by
        simpa [paperControlAt, sourcePresent, peerPresent] using controls
      exact Option.some.inj optionEq

theorem birthErased_registry_none_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right) (name : sig.Name) :
    left.registry name = none ↔ right.registry name = none := by
  constructor
  · intro leftNone
    have controls := related.2 name
    cases rightLookup : right.registry name with
    | none => rfl
    | some rightFiber => simp [paperControlAt, leftNone, rightLookup] at controls
  · intro rightNone
    have controls := related.2 name
    cases leftLookup : left.registry name with
    | none => rfl
    | some leftFiber => simp [paperControlAt, leftLookup, rightNone] at controls

theorem paperControlAt_insert_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right)
    (name : sig.Name) (parent : Option sig.Name) (component : sig.ComponentId) :
    ∀ observed,
      paperControlAt (insertFiber left name parent component) observed =
        paperControlAt (insertFiber right name parent component) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    simp [paperControlAt, paperFiberControl]
  · simpa [paperControlAt, insertFiber_lookup_other, same] using related.2 observed

theorem paperControlAt_retire_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (controls : paperFiberControl leftFiber = paperFiberControl rightFiber) :
    ∀ observed,
      paperControlAt (retireFiber left name leftFiber) observed =
        paperControlAt (retireFiber right name rightFiber) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    have updated := congrArg
      (fun control : PaperFiberControl catalog ↦ { control with retired := true }) controls
    simpa [paperControlAt, paperFiberControl] using congrArg some updated
  · simpa [paperControlAt, retireFiber_lookup_other, same] using related.2 observed

theorem paperControlAt_remove_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : BirthErasedRuleRelated values left right) (name : sig.Name) :
    ∀ observed,
      paperControlAt (removeFiber left name) observed =
        paperControlAt (removeFiber right name) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    simp [paperControlAt]
  · simpa [paperControlAt, removeFiber_lookup_other, same] using related.2 observed

theorem contextRelated_after_orchestration
    {values : ValueSetoids sig}
    {left right leftAfter rightAfter : State catalog Ambient}
    (leftStep : OrchestrationStep left leftAfter)
    (rightStep : OrchestrationStep right rightAfter)
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : BirthErasedRuleRelated values left right) :
    ContextRelated values (activeContext leftAfter) (activeContext rightAfter) := by
  rw [orchestration_activeContext_eq leftStep leftWf,
    orchestration_activeContext_eq rightStep rightWf]
  exact related.1

structure ForwardPaperOrchestrationMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    (step : OrchestrationStep left leftAfter) where
  rightAfter : State catalog Ambient
  matched : OrchestrationStep right rightAfter
  same_kind : orchestrationKind matched = orchestrationKind step
  same_actor : orchestrationName matched = orchestrationName step
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : BirthErasedRuleRelated values leftAfter rightAfter

def matchOrchestrationForward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : BirthErasedRuleRelated values left right)
    (step : OrchestrationStep left leftAfter) :
    ForwardPaperOrchestrationMatch values (dynamics := dynamics)
      (inertia := inertia) (right := right) step := by
  cases step with
  | insert name fresh parent parentPresent component provisionFresh =>
      have rightFresh : Coeffect.Absent right.registry name := {
        lookup_eq := (birthErased_registry_none_iff related name).1 fresh.lookup_eq
      }
      have rightParentPresent : ∀ parentName, parent = some parentName →
          ∃ parentFiber, right.registry parentName = some parentFiber := by
        intro parentName parentEq
        obtain ⟨leftParent, leftPresent⟩ := parentPresent parentName parentEq
        let aligned := matchPaperFiber related leftPresent
        exact ⟨aligned.peerFiber, aligned.peer_present⟩
      have rightProvisionFresh : ∀ existing existingFiber key,
          right.registry existing = some existingFiber →
          key ∈ (catalog.declaration component).provision →
          key ∈ (catalog.declaration existingFiber.component).provision → False := by
        intro existing existingFiber key existingPresent insertedKey existingKey
        let aligned := matchPaperFiber (birthErasedRuleRelated_symm related) existingPresent
        have componentEq := paperFiberControl_component_eq aligned.control_eq
        have leftExistingKey :
            key ∈ (catalog.declaration aligned.peerFiber.component).provision := by
          simpa [componentEq] using existingKey
        exact provisionFresh existing aligned.peerFiber key aligned.peer_present insertedKey
          leftExistingKey
      let matched : OrchestrationStep right (insertFiber right name parent component) :=
        .insert right name rightFresh parent rightParentPresent component rightProvisionFresh
      have leftAfterWf :=
        (OrchestrationStep.insert left name fresh parent parentPresent component
          provisionFresh).preservesWellFormed leftWf
      have rightAfterWf := matched.preservesWellFormed rightWf
      exact {
        rightAfter := insertFiber right name parent component
        matched := matched
        same_kind := rfl
        same_actor := rfl
        leftAfter_wellFormed := leftAfterWf
        rightAfter_wellFormed := rightAfterWf
        successors_related := ⟨
          contextRelated_after_orchestration
            (.insert left name fresh parent parentPresent component provisionFresh)
            matched leftWf rightWf related,
          paperControlAt_insert_related related name parent component⟩
      }
  | retire name leftFiber leftPresent =>
      let aligned := matchPaperFiber related leftPresent
      let matched : OrchestrationStep right
          (retireFiber right name aligned.peerFiber) :=
        .retire right name aligned.peerFiber aligned.peer_present
      have leftAfterWf :=
        (OrchestrationStep.retire left name leftFiber leftPresent).preservesWellFormed leftWf
      have rightAfterWf := matched.preservesWellFormed rightWf
      exact {
        rightAfter := retireFiber right name aligned.peerFiber
        matched := matched
        same_kind := rfl
        same_actor := rfl
        leftAfter_wellFormed := leftAfterWf
        rightAfter_wellFormed := rightAfterWf
        successors_related := ⟨
          contextRelated_after_orchestration
            (.retire left name leftFiber leftPresent) matched leftWf rightWf related,
          paperControlAt_retire_related related name leftFiber aligned.peerFiber
            aligned.control_eq⟩
      }
  | remove name leftFiber leftPresent retired inactive childless =>
      let aligned := matchPaperFiber related leftPresent
      have rightRetired : aligned.peerFiber.retired = true :=
        (paperFiberControl_retired_eq aligned.control_eq).symm.trans retired
      have rightInactive : ¬aligned.peerFiber.Installed := by
        intro rightInstalled
        exact inactive ((paperFiberControl_installed_iff aligned.control_eq).2 rightInstalled)
      have rightChildless : ∀ child childFiber,
          right.registry child = some childFiber → childFiber.parent ≠ some name := by
        intro child childFiber childPresent childParent
        let childAligned := matchPaperFiber
          (birthErasedRuleRelated_symm related) childPresent
        have parentEq := paperFiberControl_parent_eq childAligned.control_eq
        have leftParent : childAligned.peerFiber.parent = some name :=
          parentEq.symm.trans childParent
        exact childless child childAligned.peerFiber childAligned.peer_present leftParent
      let matched : OrchestrationStep right (removeFiber right name) :=
        .remove right name aligned.peerFiber aligned.peer_present rightRetired rightInactive
          rightChildless
      have leftAfterWf :=
        (OrchestrationStep.remove left name leftFiber leftPresent retired inactive
          childless).preservesWellFormed leftWf
      have rightAfterWf := matched.preservesWellFormed rightWf
      exact {
        rightAfter := removeFiber right name
        matched := matched
        same_kind := rfl
        same_actor := rfl
        leftAfter_wellFormed := leftAfterWf
        rightAfter_wellFormed := rightAfterWf
        successors_related := ⟨
          contextRelated_after_orchestration
            (.remove left name leftFiber leftPresent retired inactive childless)
            matched leftWf rightWf related,
          paperControlAt_remove_related related name⟩
      }

structure BackwardPaperOrchestrationMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    (step : OrchestrationStep right rightAfter) where
  leftAfter : State catalog Ambient
  matched : OrchestrationStep left leftAfter
  same_kind : orchestrationKind matched = orchestrationKind step
  same_actor : orchestrationName matched = orchestrationName step
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : BirthErasedRuleRelated values leftAfter rightAfter

def matchOrchestrationBackward
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : BirthErasedRuleRelated values left right)
    (step : OrchestrationStep right rightAfter) :
    BackwardPaperOrchestrationMatch values (dynamics := dynamics)
      (inertia := inertia) (left := left) step := by
  let swapped := matchOrchestrationForward (dynamics := dynamics) (inertia := inertia)
    (left := right) (right := left)
    rightWf leftWf (birthErasedRuleRelated_symm related) step
  exact {
    leftAfter := swapped.rightAfter
    matched := swapped.matched
    same_kind := swapped.same_kind
    same_actor := swapped.same_actor
    leftAfter_wellFormed := swapped.rightAfter_wellFormed
    rightAfter_wellFormed := swapped.leftAfter_wellFormed
    successors_related := birthErasedRuleRelated_symm swapped.successors_related
  }

def ForwardPaperOrchestrationMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient} {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    {step : OrchestrationStep left leftAfter}
    (matched : ForwardPaperOrchestrationMatch values (dynamics := dynamics)
      (inertia := inertia) (right := right) step) :
    RetainedStep (shadowBefore := right)
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) step) where
  shadowAfter := matched.rightAfter
  replay := .orchestration matched.matched
  same_rule := by
    rw [Cordis.GlobalNameLifecycle.orchestrationStep_global_rule,
      Cordis.GlobalNameLifecycle.orchestrationStep_global_rule, matched.same_kind]
  same_actor := by
    change Actor.fiber (orchestrationName matched.matched) =
      Actor.fiber (orchestrationName step)
    exact congrArg Actor.fiber matched.same_actor
  transportAssignment _ := StepProgramAssignment.ofOrchestration matched.matched

def BackwardPaperOrchestrationMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient} {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    {step : OrchestrationStep right rightAfter}
    (matched : BackwardPaperOrchestrationMatch values (dynamics := dynamics)
      (inertia := inertia) (left := left) step) :
    RetainedStep (shadowBefore := left)
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) step) where
  shadowAfter := matched.leftAfter
  replay := .orchestration matched.matched
  same_rule := by
    rw [Cordis.GlobalNameLifecycle.orchestrationStep_global_rule,
      Cordis.GlobalNameLifecycle.orchestrationStep_global_rule, matched.same_kind]
  same_actor := by
    change Actor.fiber (orchestrationName matched.matched) =
      Actor.fiber (orchestrationName step)
    exact congrArg Actor.fiber matched.same_actor
  transportAssignment _ := StepProgramAssignment.ofOrchestration matched.matched

structure BirthErasedOrchestrationSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) where
  forward : ∀ {left right leftAfter : State catalog Ambient},
    WellFormed left → WellFormed right → BirthErasedRuleRelated values left right →
    (step : OrchestrationStep left leftAfter) →
      ForwardPaperOrchestrationMatch values (dynamics := dynamics)
        (inertia := inertia) (right := right) step
  backward : ∀ {left right rightAfter : State catalog Ambient},
    WellFormed left → WellFormed right → BirthErasedRuleRelated values left right →
    (step : OrchestrationStep right rightAfter) →
      BackwardPaperOrchestrationMatch values (dynamics := dynamics)
        (inertia := inertia) (left := left) step

def birthErasedOrchestrationSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    BirthErasedOrchestrationSimulation values dynamics inertia where
  forward := matchOrchestrationForward
  backward := matchOrchestrationBackward

/-! ## Exact lifecycle assigned-simulation frontier -/

structure ForwardAssignedLifecycleMatch
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    {left right leftAfter : State catalog Ambient}
    (transition : GlobalLifecycle.Transition dynamics inertia left leftAfter) where
  rightAfter : State catalog Ambient
  matched : GlobalLifecycle.Transition dynamics inertia right rightAfter
  same_lifecycle_rule : matched.rule = transition.rule
  same_actor :
    (Step.lifecycle matched : Step dynamics inertia right rightAfter).actor =
      (Step.lifecycle transition : Step dynamics inertia left leftAfter).actor
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : BirthErasedRuleRelated values leftAfter rightAfter
  transportAssignment :
    StepProgramAssignment (Step.lifecycle transition) →
      StepProgramAssignment (Step.lifecycle matched)

def ForwardAssignedLifecycleMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    {transition : GlobalLifecycle.Transition dynamics inertia left leftAfter}
    (matched : ForwardAssignedLifecycleMatch values dynamics inertia
      (right := right) transition) :
    RetainedStep (shadowBefore := right) (Step.lifecycle transition) where
  shadowAfter := matched.rightAfter
  replay := .lifecycle matched.matched
  same_rule := by
    rw [Cordis.GlobalNameLifecycle.lifecycleStep_global_rule,
      Cordis.GlobalNameLifecycle.lifecycleStep_global_rule, matched.same_lifecycle_rule]
  same_actor := matched.same_actor
  transportAssignment := matched.transportAssignment

structure BackwardAssignedLifecycleMatch
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    {left right rightAfter : State catalog Ambient}
    (transition : GlobalLifecycle.Transition dynamics inertia right rightAfter) where
  leftAfter : State catalog Ambient
  matched : GlobalLifecycle.Transition dynamics inertia left leftAfter
  same_lifecycle_rule : matched.rule = transition.rule
  same_actor :
    (Step.lifecycle matched : Step dynamics inertia left leftAfter).actor =
      (Step.lifecycle transition : Step dynamics inertia right rightAfter).actor
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : BirthErasedRuleRelated values leftAfter rightAfter
  transportAssignment :
    StepProgramAssignment (Step.lifecycle transition) →
      StepProgramAssignment (Step.lifecycle matched)

def BackwardAssignedLifecycleMatch.toRetainedStep
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    {transition : GlobalLifecycle.Transition dynamics inertia right rightAfter}
    (matched : BackwardAssignedLifecycleMatch values dynamics inertia
      (left := left) transition) :
    RetainedStep (shadowBefore := left) (Step.lifecycle transition) where
  shadowAfter := matched.leftAfter
  replay := .lifecycle matched.matched
  same_rule := by
    rw [Cordis.GlobalNameLifecycle.lifecycleStep_global_rule,
      Cordis.GlobalNameLifecycle.lifecycleStep_global_rule, matched.same_lifecycle_rule]
  same_actor := matched.same_actor
  transportAssignment := matched.transportAssignment

/-- Explicit frontier contract; it is not derived merely from the relation. -/
structure BirthErasedLifecycleAssignedSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) where
  forward : ∀ {left right leftAfter : State catalog Ambient},
    WellFormed left → WellFormed right → BirthErasedRuleRelated values left right →
    (transition : GlobalLifecycle.Transition dynamics inertia left leftAfter) →
      ForwardAssignedLifecycleMatch values dynamics inertia (right := right) transition
  backward : ∀ {left right rightAfter : State catalog Ambient},
    WellFormed left → WellFormed right → BirthErasedRuleRelated values left right →
    (transition : GlobalLifecycle.Transition dynamics inertia right rightAfter) →
      BackwardAssignedLifecycleMatch values dynamics inertia (left := left) transition

def InertiaRespectsBirthErased
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) : Prop :=
  ∀ owner code {left right : State catalog Ambient},
    BirthErasedRuleRelated values left right →
      (inertia.canAbort owner code left ↔ inertia.canAbort owner code right)

namespace LifecycleGap

open Cordis.GlobalRuleInvariance.InertiaGap

theorem sources_birth_erased :
    BirthErasedRuleRelated HeterogeneousExample.values baseline shifted :=
  birthErased_of_ruleRelated baseline_ruleRelated_shifted

theorem inertia_not_respected :
    ¬InertiaRespectsBirthErased HeterogeneousExample.values
      Cordis.GlobalDynamics.Example.dynamics ambientSensitiveInertia := by
  intro respects
  have decisions := respects 0 0 sources_birth_erased
  exact does_not_abort_at_shifted (decisions.1 aborts_at_baseline)

end LifecycleGap

namespace ClockLifecycleGap

open Cordis.GlobalProgress.RegistrationRejectionGap

abbrev Signature := Cordis.GlobalForeignPhase.OracleGap.Signature
abbrev exampleCatalog := Cordis.GlobalForeignPhase.OracleGap.exampleCatalog
abbrev ExampleState := Cordis.GlobalForeignPhase.OracleGap.ExampleState
abbrev dynamics := Cordis.GlobalForeignPhase.OracleGap.dynamics
abbrev view := Cordis.GlobalForeignPhase.OracleGap.view

def values : ValueSetoids Signature where
  relation _ := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

def shifted : ExampleState := { changed with nextBirth := changed.nextBirth + 1 }

theorem shifted_wellFormed : WellFormed shifted := by
  exact {
    birth_bounded := by
      intro name fiber lookup
      exact Nat.lt_trans (changed_wellFormed.birth_bounded name fiber lookup)
        (Nat.lt_succ_self _)
    parent_present := by simpa [shifted] using changed_wellFormed.parent_present
    parent_older := by simpa [shifted] using changed_wellFormed.parent_older
    provisions_unique := by simpa [shifted] using changed_wellFormed.provisions_unique
    committed_provider_present := by
      simpa [shifted] using changed_wellFormed.committed_provider_present
    committed_provider_installed := by
      simpa [shifted] using changed_wellFormed.committed_provider_installed
  }

theorem sources_related : BirthErasedRuleRelated values changed shifted := by
  constructor
  · exact contextRelated_refl values _
  · intro name
    rfl

def clockInertia : GlobalLifecycle.InertiaPolicy dynamics where
  canAbort _ _ state := state.nextBirth = changed.nextBirth

theorem aborts_original : clockInertia.canAbort 0 () changed := rfl

theorem not_abort_shifted : ¬clockInertia.canAbort 0 () shifted := by
  change ¬(changed.nextBirth + 1 = changed.nextBirth)
  omega

def originalAbortAfter : ExampleState :=
  GlobalLifecycle.setPhase changed 0 changedFiber (.unloading [] view none)

def originalAbort : GlobalLifecycle.Transition dynamics clockInertia
    changed originalAbortAfter :=
  .divertAbort changed 0 changedFiber changed_owner_present () [] view rfl
    changed_target_differs aborts_original

theorem no_shifted_divertAbort :
    ¬∃ after, ∃ transition : GlobalLifecycle.Transition dynamics clockInertia
      shifted after, transition.rule = .divertAbort := by
  rintro ⟨after, transition, ruleEq⟩
  cases transition with
  | begin => cases ruleEq
  | iter => cases ruleEq
  | finish => cases ruleEq
  | divertAbort owner fiber present code undos committed phase targetChanged abortable =>
      exact not_abort_shifted abortable
  | divertLand => cases ruleEq
  | raise => cases ruleEq
  | leave => cases ruleEq
  | unload => cases ruleEq

theorem no_assigned_simulation :
    ¬Nonempty (BirthErasedLifecycleAssignedSimulation values dynamics clockInertia) := by
  rintro ⟨simulation⟩
  let matched := simulation.forward changed_wellFormed shifted_wellFormed
    sources_related originalAbort
  exact no_shifted_divertAbort
    ⟨matched.rightAfter, matched.matched, matched.same_lifecycle_rule⟩

end ClockLifecycleGap

/-! ## Literal allocator gap becomes related after erasing births -/

namespace BirthGap

open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap

theorem activeContext_eq : activeContext normal = activeContext swapped := by
  calc
    activeContext normal = activeContext registered :=
      orchestration_activeContext_eq normalInsert registered_wellFormed
    _ = activeContext Source := orchestration_activeContext_eq registerChild source_wellFormed
    _ = activeContext swappedFirst :=
      (orchestration_activeContext_eq swappedFirstInsert source_wellFormed).symm
    _ = activeContext swapped :=
      (orchestration_activeContext_eq swappedSecondInsert
        (swappedFirstInsert.preservesWellFormed source_wellFormed)).symm

theorem paperControlAt_eq (name : Nat) :
    paperControlAt normal name = paperControlAt swapped name := by
  by_cases zero : name = 0
  · subst name
    rfl
  · by_cases one : name = 1
    · subst name
      rfl
    · by_cases two : name = 2
      · subst name
        rfl
      · simp [paperControlAt, normal, swapped, swappedFirst,
          registered, Source, Cordis.GlobalRegistry.Example.withProvider,
          Cordis.GlobalRegistry.Example.initial, insertFiber_lookup_other, zero, one, two]

theorem birth_erased_related :
    BirthErasedRuleRelated exactValues normal swapped := by
  constructor
  · rw [activeContext_eq]
    exact contextRelated_refl exactValues _
  · exact paperControlAt_eq

theorem strict_rule_relation_fails : ¬RuleRelated exactValues normal swapped :=
  birth_order_not_ruleRelated

theorem exact_states_differ : normal ≠ swapped :=
  registration_insert_birth_order_differs

def normalOneFiber : Fiber exampleCatalog where
  component := .consumer
  parent := some 0
  birth := Source.nextBirth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

theorem normal_one_present : normal.registry 1 = some normalOneFiber := by
  simp [normal, registered, normalOneFiber]

def retireOne : OrchestrationStep normal (retireFiber normal 1 normalOneFiber) :=
  .retire normal 1 normalOneFiber normal_one_present

def matchedRetire
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    ForwardPaperOrchestrationMatch exactValues (dynamics := dynamics)
      (inertia := inertia) (right := swapped) retireOne :=
  matchOrchestrationForward normal_wellFormed swapped_wellFormed birth_erased_related retireOne

def executableMatchedTags : OrchestrationKind × Nat :=
  (.retire, 1)

theorem matchedRetire_tags
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    (orchestrationKind (matchedRetire dynamics inertia).matched,
      orchestrationName (matchedRetire dynamics inertia).matched) = executableMatchedTags := by
  rfl

theorem matched_retire_successors
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    BirthErasedRuleRelated exactValues
      (retireFiber normal 1 normalOneFiber) (matchedRetire dynamics inertia).rightAfter :=
  (matchedRetire dynamics inertia).successors_related

def retainedRetire
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    RetainedStep (shadowBefore := swapped)
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) retireOne) :=
  (matchedRetire dynamics inertia).toRetainedStep

def swappedOneFiber : Fiber exampleCatalog where
  component := .consumer
  parent := some 0
  birth := swappedFirst.nextBirth
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

theorem swapped_one_present : swapped.registry 1 = some swappedOneFiber := by
  simp [swapped, swappedFirst, swappedOneFiber]

def retireOneSwapped : OrchestrationStep swapped
    (retireFiber swapped 1 swappedOneFiber) :=
  .retire swapped 1 swappedOneFiber swapped_one_present

def matchedRetireBackward
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    BackwardPaperOrchestrationMatch exactValues (dynamics := dynamics)
      (inertia := inertia) (left := normal) retireOneSwapped :=
  matchOrchestrationBackward normal_wellFormed swapped_wellFormed
    birth_erased_related retireOneSwapped

def retainedRetireBackward
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    RetainedStep (shadowBefore := normal)
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) retireOneSwapped) :=
  (matchedRetireBackward dynamics inertia).toRetainedStep

def forwardSourceAssignment
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    StepProgramAssignment
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) retireOne) :=
  StepProgramAssignment.ofOrchestration retireOne

noncomputable def forwardMatchedAssignment
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    StepProgramAssignment (retainedRetire dynamics inertia).replay :=
  (retainedRetire dynamics inertia).transportAssignment
    (forwardSourceAssignment dynamics inertia)

def backwardSourceAssignment
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    StepProgramAssignment
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) retireOneSwapped) :=
  StepProgramAssignment.ofOrchestration retireOneSwapped

noncomputable def backwardMatchedAssignment
    (dynamics : Dynamics Cordis.GlobalRegistry.Example.signature exampleCatalog Unit)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    StepProgramAssignment (retainedRetireBackward dynamics inertia).replay :=
  (retainedRetireBackward dynamics inertia).transportAssignment
    (backwardSourceAssignment dynamics inertia)

end BirthGap

namespace OneSidedWellFormedGap

open Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap

def malformed : ExampleState := { normal with nextBirth := 0 }

theorem related : BirthErasedRuleRelated exactValues normal malformed := by
  exact ⟨contextRelated_refl exactValues _, fun _ ↦ rfl⟩

theorem malformed_not_wellFormed : ¬WellFormed malformed := by
  intro wf
  have present : malformed.registry 0 = some GlobalDeletion.ParentGap.providerFiber := rfl
  have bounded := wf.birth_bounded 0 GlobalDeletion.ParentGap.providerFiber present
  change 0 < 0 at bounded
  omega

theorem source_wellFormed : WellFormed normal := normal_wellFormed

end OneSidedWellFormedGap

/-! ## Literal vestigial removal is deletion-related, not globally rule-related -/

namespace VestigialGap

open Cordis.GlobalVestigial.Counterexample

def exactValues : ValueSetoids signature where
  relation _ := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

def deleted (name : Name) : Prop := name = .vestigial

theorem outside_rule_related :
    BirthErasedRuleRelatedOutside exactValues deleted state withoutVestigial := by
  constructor
  · have activeEq := orchestration_activeContext_eq removeVestigial state_wellFormed
    rw [activeEq]
    exact contextRelated_refl exactValues _
  · intro name outside
    cases name with
    | parent => rfl
    | vestigial => exact False.elim (outside rfl)
    | fresh => rfl

theorem effect_related : EffectRelated state withoutVestigial :=
  vestigial.effectRelated_remove

theorem deletion_related : DeletionRelated exactValues deleted state withoutVestigial :=
  ⟨effect_related, outside_rule_related⟩

theorem global_rule_relation_fails :
    ¬BirthErasedRuleRelated exactValues state withoutVestigial := by
  intro related
  have atDeleted := related.2 Name.vestigial
  change some (paperFiberControl vestigialFiber) = none at atDeleted
  cases atDeleted

end VestigialGap

namespace OutsideGap

open Cordis.GlobalVestigial.Counterexample

theorem unsafe_parent_step_rejected :
    ¬SafeForVestigialNames [Name.vestigial] adoptingInsert := by
  intro safe
  have parentSafe := safe.2 Name.vestigial (by simp)
  change (some Name.vestigial : Option Name) ≠ some Name.vestigial at parentSafe
  exact parentSafe rfl

theorem no_backward_same_tag_redraw :
    ¬∃ after, ∃ step : OrchestrationStep state after,
      orchestrationKind step = orchestrationKind redrawVestigial ∧
        orchestrationName step = orchestrationName redrawVestigial := by
  rintro ⟨after, step, sameKind, sameName⟩
  cases step with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      change inserted = Name.vestigial at sameName
      subst inserted
      have absent := fresh.lookup_eq
      rw [vestigial_present] at absent
      cases absent
  | retire name fiber present =>
      change OrchestrationKind.retire = .insert at sameKind
      cases sameKind
  | remove name fiber present retired inactive childless =>
      change OrchestrationKind.remove = .insert at sameKind
      cases sameKind

theorem provision_conflict_is_real :
    ClaimsVestigialProvision vestigial claimingInsert :=
  claimingInsert_claims_vestigial_provision

theorem parent_removal_conflict_is_real :
    RemovesVestigialParent vestigial removeParentAfterChild :=
  removesVestigialParent

end OutsideGap

/-! ## Generic singleton and finite vestigial removal -/

def vestigialRemoveStep
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name) :
    OrchestrationStep state (removeFiber state name) :=
  .remove state name vestigial.fiber vestigial.present vestigial.retired
    vestigial.notInstalled vestigial.childless

theorem vestigial_remove_outside
    (values : ValueSetoids sig)
    {state : State catalog Ambient} {name : sig.Name}
    (stateWf : WellFormed state) (vestigial : Vestigial state name) :
    BirthErasedRuleRelatedOutside values (fun candidate ↦ candidate = name)
      state (removeFiber state name) := by
  constructor
  · have removedWf := GlobalRegistry.preserve_remove state name vestigial.fiber
      vestigial.present vestigial.retired vestigial.notInstalled vestigial.childless stateWf
    have activeEq := activeContext_remove_eq state name vestigial.fiber vestigial.present
      vestigial.notInstalled stateWf removedWf
    rw [activeEq]
    exact contextRelated_refl values _
  · intro candidate different
    simp [paperControlAt, removeFiber_lookup_other, different]

theorem vestigial_remove_deletion_related
    (values : ValueSetoids sig)
    {state : State catalog Ambient} {name : sig.Name}
    (stateWf : WellFormed state) (vestigial : Vestigial state name) :
    DeletionRelated values (fun candidate ↦ candidate = name)
      state (removeFiber state name) :=
  ⟨vestigial.effectRelated_remove,
    vestigial_remove_outside values stateWf vestigial⟩

theorem vestigial_remove_wellFormed
    {state : State catalog Ambient} {name : sig.Name}
    (stateWf : WellFormed state) (vestigial : Vestigial state name) :
    WellFormed (removeFiber state name) :=
  GlobalRegistry.preserve_remove state name vestigial.fiber vestigial.present
    vestigial.retired vestigial.notInstalled vestigial.childless stateWf

theorem vestigial_remove_not_birthErased
    (values : ValueSetoids sig)
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name) :
    ¬BirthErasedRuleRelated values state (removeFiber state name) := by
  intro related
  have atRemoved := related.2 name
  simp [paperControlAt, vestigial.present] at atRemoved

private def tailVestigialNames
    {state : State catalog Ambient} {head : sig.Name} {tail : List sig.Name}
    (family : VestigialNames state (head :: tail)) :
    VestigialNames (removeFiber state head) tail := by
  have nodup := List.nodup_cons.mp family.nodup
  exact {
    nodup := nodup.2
    witness := by
      intro name member
      have original := family.witness name (by simp [member])
      apply Vestigial.remove_other original
      intro equal
      subst name
      exact nodup.1 member
  }

theorem removeNames_wellFormed
    {state : State catalog Ambient} {names : List sig.Name}
    (stateWf : WellFormed state) (family : VestigialNames state names) :
    WellFormed (removeNames state names) := by
  induction names generalizing state with
  | nil => exact stateWf
  | cons head tail ih =>
      let headVestigial := family.witness head (by simp)
      have removedWf := GlobalRegistry.preserve_remove state head headVestigial.fiber
        headVestigial.present headVestigial.retired headVestigial.notInstalled
        headVestigial.childless stateWf
      exact ih removedWf (tailVestigialNames family)

theorem vestigialNames_deletionRelated
    (values : ValueSetoids sig)
    {state : State catalog Ambient} {names : List sig.Name}
    (stateWf : WellFormed state) (family : VestigialNames state names) :
    DeletionRelated values (fun name ↦ name ∈ names) state (removeNames state names) := by
  induction names generalizing state with
  | nil => exact deletionRelated_refl values (fun name ↦ name ∈ []) state
  | cons head tail ih =>
      let headVestigial := family.witness head (by simp)
      have first := vestigial_remove_deletion_related values stateWf headVestigial
      have firstFull : DeletionRelated values (fun name ↦ name ∈ head :: tail)
          state (removeFiber state head) :=
        deletion_mono (fun name equal ↦ by simp [equal]) first
      have removedWf := GlobalRegistry.preserve_remove state head headVestigial.fiber
        headVestigial.present headVestigial.retired headVestigial.notInstalled
        headVestigial.childless stateWf
      have rest := ih removedWf (tailVestigialNames family)
      have restFull : DeletionRelated values (fun name ↦ name ∈ head :: tail)
          (removeFiber state head) (removeNames (removeFiber state head) tail) :=
        deletion_mono (fun name member ↦ by simp [member]) rest
      exact deletionRelated_trans firstFull restFull

/-! ## Directed safe replay under the combined deletion observation -/

def ForwardNamesStepSquare.retained
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : OrchestrationStep before after}
    (square : ForwardNamesStepSquare family source) :
    RetainedStep (shadowBefore := removeNames before names)
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) source) where
  shadowAfter := square.removedAfter
  replay := .orchestration square.matched
  same_rule := (Cordis.GlobalTraceRewrite.sameOrchestrationTemplate_global_tags
    (dynamics := dynamics) (inertia := inertia) square.same_template).1
  same_actor := (Cordis.GlobalTraceRewrite.sameOrchestrationTemplate_global_tags
    (dynamics := dynamics) (inertia := inertia) square.same_template).2
  transportAssignment _ := StepProgramAssignment.ofOrchestration square.matched

structure ForwardDeletedOrchestrationReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    (family : VestigialNames before names)
    (source : OrchestrationStep before after) where
  retained : RetainedStep (shadowBefore := removeNames before names)
    (Step.orchestration (dynamics := dynamics) (inertia := inertia) source)
  remove_after : removeNames after names = retained.shadowAfter
  before_related : DeletionRelated values (fun name ↦ name ∈ names)
    before (removeNames before names)
  after_wellFormed : WellFormed after
  shadowAfter_wellFormed : WellFormed retained.shadowAfter
  after_related : DeletionRelated values (fun name ↦ name ∈ names)
    after retained.shadowAfter
  remains : VestigialNames after names

noncomputable def replaySafeVestigialOrchestration
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    (beforeWf : WellFormed before) (family : VestigialNames before names)
    (source : OrchestrationStep before after)
    (safe : SafeForVestigialNames names source) :
    ForwardDeletedOrchestrationReplay values (dynamics := dynamics)
      (inertia := inertia) family source := by
  let square := forwardNamesStep family source safe
  let retained : RetainedStep (shadowBefore := removeNames before names)
      (Step.orchestration (dynamics := dynamics) (inertia := inertia) source) :=
    Cordis.GlobalPaperRelation.ForwardNamesStepSquare.retained
      (dynamics := dynamics) (inertia := inertia) square
  have afterWf := source.preservesWellFormed beforeWf
  have removedBeforeWf := removeNames_wellFormed beforeWf family
  have shadowWf := square.matched.preservesWellFormed removedBeforeWf
  have afterRelated := vestigialNames_deletionRelated values afterWf square.remains
  exact {
    retained := retained
    remove_after := square.remove_after
    before_related := vestigialNames_deletionRelated values beforeWf family
    after_wellFormed := afterWf
    shadowAfter_wellFormed := shadowWf
    after_related := by
      change DeletionRelated values (fun name ↦ name ∈ names) after square.removedAfter
      rw [square.remove_after] at afterRelated
      exact afterRelated
    remains := square.remains
  }

structure ForwardDeletedTraceReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    (family : VestigialNames before names)
    (source : GlobalCalculus.Trace dynamics inertia before after) where
  shadow : GlobalCalculus.Trace dynamics inertia
    (removeNames before names) (removeNames after names)
  certificate : DeletionReplay
    (DeletionRelated values (fun name ↦ name ∈ names))
    (fun _ ↦ False) source shadow
  sourceAfter_wellFormed : WellFormed after
  shadowAfter_wellFormed : WellFormed (removeNames after names)
  remains : VestigialNames after names

def transportStepAssignmentAfter
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before leftAfter rightAfter : State catalog Ambient}
    {step : Step dynamics inertia before leftAfter}
    (equal : leftAfter = rightAfter)
    (assignment : StepProgramAssignment step) :
    StepProgramAssignment (transportStepAfter equal step) := by
  cases equal
  exact assignment

noncomputable def replaySafeVestigialTrace
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (beforeWf : WellFormed before) (family : VestigialNames before names)
    (safe : SafeNamesOrchestrationTrace names dynamics inertia source) :
    ForwardDeletedTraceReplay values family source := by
  induction safe with
  | nil state =>
      exact {
        shadow := .nil _
        certificate := .nil (vestigialNames_deletionRelated values beforeWf family)
        sourceAfter_wellFormed := beforeWf
        shadowAfter_wellFormed := removeNames_wellFormed beforeWf family
        remains := family
      }
  | @cons before middle after step tail stepSafe tailSafe ih =>
      let head := replaySafeVestigialOrchestration values
        (dynamics := dynamics) (inertia := inertia) beforeWf family step stepSafe
      let moved : RetainedStep (shadowBefore := removeNames before names)
          (Step.orchestration (dynamics := dynamics) (inertia := inertia) step) := {
        shadowAfter := removeNames middle names
        replay := transportStepAfter head.remove_after.symm head.retained.replay
        same_rule := by
          rw [transportStepAfter_rule]
          exact head.retained.same_rule
        same_actor := by
          rw [transportStepAfter_actor]
          exact head.retained.same_actor
        transportAssignment := by
          intro assignment
          exact transportStepAssignmentAfter head.remove_after.symm
            (head.retained.transportAssignment assignment)
      }
      let rest := ih head.after_wellFormed head.remains
      exact {
        shadow := .cons moved.replay rest.shadow
        certificate := .keep head.before_related moved rest.certificate
        sourceAfter_wellFormed := rest.sourceAfter_wellFormed
        shadowAfter_wellFormed := rest.shadowAfter_wellFormed
        remains := rest.remains
      }

theorem ForwardDeletedTraceReplay.final_related
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (replay : ForwardDeletedTraceReplay values family source) :
    DeletionRelated values (fun name ↦ name ∈ names)
      after (removeNames after names) :=
  replay.certificate.final_related

noncomputable def ForwardDeletedTraceReplay.transportAssignment
    {values : ValueSetoids sig}
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {names : List sig.Name}
    {family : VestigialNames before names}
    {source : GlobalCalculus.Trace dynamics inertia before after}
    (replay : ForwardDeletedTraceReplay values family source)
    (assignment : TraceProgramAssignment dynamics inertia source) :
    TraceProgramAssignment dynamics inertia replay.shadow :=
  replay.certificate.transportAssignment assignment

namespace DirectedReplayExample

open Cordis.GlobalDeletion.Positive

abbrev values :=
  Cordis.GlobalActivationOrchestrationTransposition.LiteralPaperGap.exactValues

theorem registered_wellFormed : WellFormed registered := by
  simpa [registered, source, GlobalDeletion.ParentGap.registered,
    GlobalDeletion.ParentGap.source] using GlobalDeletion.ParentGap.registered_wellFormed

theorem retired_wellFormed : WellFormed retired :=
  GlobalRegistry.preserve_retire registered 1 childFiber registered_child registered_wellFormed

noncomputable def replay : ForwardDeletedTraceReplay values family sourceTrace :=
  replaySafeVestigialTrace values retired_wellFormed family namesSafe

def executableReplayRules : List GlobalCalculus.Rule :=
  [.oRetire]

theorem replay_shadow_rules : replay.shadow.rules = executableReplayRules := by
  have sameAsSource : replay.shadow.rules = sourceTrace.rules := by
    apply List.Sublist.eq_of_length replay.certificate.rules_sublist
    simp [replay, replaySafeVestigialTrace, GlobalDeletion.Positive.namesSafe,
      GlobalDeletion.Positive.sourceTrace, GlobalCalculus.Trace.rules]
  exact sameAsSource.trans (by rfl)

theorem final_related : DeletionRelated values (fun name ↦ name ∈ [(1 : Nat)])
    (retireFiber retired 0 providerFiber)
    (removeNames (retireFiber retired 0 providerFiber) [1]) :=
  replay.final_related

def sourceAssignment : TraceProgramAssignment dynamics inertia sourceTrace :=
  .cons (StepProgramAssignment.ofOrchestration retireProvider) (.nil _)

noncomputable def shadowAssignment :
    TraceProgramAssignment dynamics inertia replay.shadow :=
  replay.transportAssignment sourceAssignment

end DirectedReplayExample

end Cordis.GlobalPaperRelation
