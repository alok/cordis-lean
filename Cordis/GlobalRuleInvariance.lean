import Cordis.GlobalVestigial

/-!
# Rule invariance for the three orchestration constructors

This module proves the orchestration-only fragment of CORDIS paper Lemma 55 at revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`. For well-formed states related by the finite
`GlobalRelations.RuleRelated` candidate, O-Insert, O-Retire, and O-Remove can be matched in
both directions with the same constructor kind and acted-on name. The exact endpoints are
retained, are well formed, and are again rule-related.

The active-context argument does not assume private fiber tables equal. It proves that each
orchestration edit preserves the active values of its own state, using freshness for insertion,
the fact that retirement does not change phase or table, and O-Remove's non-installed premise.
Initial active contexts are then related by the supplied value setoids.

This is not the paper's full ten-rule bisimulation. Lifecycle rules additionally need iterator
and read relation transport, registration-oracle transport, recovery-admission transport, and an
inertia policy that respects rule observation. A finite counterexample below shows that
`RuleRelated` alone does not imply the last law.
-/

set_option autoImplicit false

namespace Cordis.GlobalRuleInvariance

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus
  Cordis.GlobalRelations Cordis.GlobalVestigial

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-!
## Exact control and registry transport
-/

theorem fiberControl_component_eq
    {left right : Fiber catalog}
    (equal : fiberControl left = fiberControl right) : left.component = right.component :=
  congrArg FiberControl.component equal

theorem fiberControl_parent_eq
    {left right : Fiber catalog}
    (equal : fiberControl left = fiberControl right) : left.parent = right.parent :=
  congrArg FiberControl.parent equal

theorem fiberControl_birth_eq
    {left right : Fiber catalog}
    (equal : fiberControl left = fiberControl right) : left.birth = right.birth :=
  congrArg FiberControl.birth equal

theorem fiberControl_retired_eq
    {left right : Fiber catalog}
    (equal : fiberControl left = fiberControl right) : left.retired = right.retired :=
  congrArg FiberControl.retired equal

theorem fiberControl_installed_iff
    {left right : Fiber catalog}
    (equal : fiberControl left = fiberControl right) : left.Installed ↔ right.Installed := by
  change (fiberControl left).phase.Installed ↔ (fiberControl right).phase.Installed
  rw [equal]

theorem fiberControl_active_iff
    {left right : Fiber catalog}
    (equal : fiberControl left = fiberControl right) : left.Active ↔ right.Active := by
  change (fiberControl left).phase.Active ↔ (fiberControl right).phase.Active
  rw [equal]

/-- A lookup transported across exact rule-control observation. -/
structure FiberMatch
    (values : ValueSetoids sig)
    (source peer : State catalog Ambient)
    (name : sig.Name) (sourceFiber : Fiber catalog) where
  peerFiber : Fiber catalog
  peer_present : peer.registry name = some peerFiber
  control_eq : fiberControl sourceFiber = fiberControl peerFiber

def matchFiber
    {values : ValueSetoids sig} {source peer : State catalog Ambient}
    {name : sig.Name} {sourceFiber : Fiber catalog}
    (related : RuleRelated values source peer)
    (sourcePresent : source.registry name = some sourceFiber) :
    FiberMatch values source peer name sourceFiber := by
  have controls := related.2.2 name
  cases peerPresent : peer.registry name with
  | none =>
      simp [GlobalRelations.controlAt, sourcePresent, peerPresent] at controls
  | some peerFiber =>
      refine {
        peerFiber := peerFiber
        peer_present := peerPresent
        control_eq := ?_
      }
      have optionEq : some (fiberControl sourceFiber) = some (fiberControl peerFiber) := by
        simpa [GlobalRelations.controlAt, sourcePresent, peerPresent] using controls
      exact Option.some.inj optionEq

theorem registry_none_iff
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) (name : sig.Name) :
    left.registry name = none ↔ right.registry name = none := by
  constructor
  · intro leftNone
    have controls := related.2.2 name
    cases rightLookup : right.registry name with
    | none => rfl
    | some rightFiber =>
        simp [GlobalRelations.controlAt, leftNone, rightLookup] at controls
  · intro rightNone
    have controls := related.2.2 name
    cases leftLookup : left.registry name with
    | none => rfl
    | some leftFiber =>
        simp [GlobalRelations.controlAt, leftLookup, rightNone] at controls

/-!
## Active values are invariant under orchestration edits
-/

theorem notActive_of_notInstalled
    {fiber : Fiber catalog} (notInstalled : ¬fiber.Installed) : ¬fiber.Active := by
  cases phase : fiber.phase <;>
    simp [Fiber.Active, Fiber.Installed, Phase.Active, Phase.Installed, phase]
      at notInstalled ⊢

theorem activeValue_insert_iff
    (state : State catalog Ambient) (name : sig.Name) (parent : Option sig.Name)
    (component : sig.ComponentId) (fresh : Coeffect.Absent state.registry name)
    {key : sig.Key} {value : sig.Value key} :
    ActiveValue (insertFiber state name parent component) key value ↔
      ActiveValue state key value := by
  constructor
  · rintro ⟨provider, fiber, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [insertFiber_lookup_same] at lookup
      have equal := Option.some.inj lookup
      subst fiber
      simp [Fiber.Active, Phase.Active] at active
    · exact ⟨provider, fiber,
        by simpa [insertFiber_lookup_other, same] using lookup, active, valueEq⟩
  · rintro ⟨provider, fiber, lookup, active, valueEq⟩
    have different : provider ≠ name := by
      intro same
      subst provider
      rw [fresh.lookup_eq] at lookup
      cases lookup
    exact ⟨provider, fiber,
      by simpa [insertFiber_lookup_other, different] using lookup, active, valueEq⟩

theorem activeValue_retire_iff
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber)
    {key : sig.Key} {value : sig.Value key} :
    ActiveValue (retireFiber state name fiber) key value ↔ ActiveValue state key value := by
  constructor
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [retireFiber_lookup_same] at lookup
      have equal := Option.some.inj lookup
      subst current
      exact ⟨name, fiber, present, by simpa [Fiber.Active] using active, valueEq⟩
    · exact ⟨provider, current,
        by simpa [retireFiber_lookup_other, same] using lookup, active, valueEq⟩
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    by_cases same : provider = name
    · subst provider
      rw [present] at lookup
      have equal := Option.some.inj lookup
      subst current
      exact ⟨name, { fiber with retired := true }, retireFiber_lookup_same state name fiber,
        by simpa [Fiber.Active] using active, valueEq⟩
    · exact ⟨provider, current,
        by simpa [retireFiber_lookup_other, same] using lookup, active, valueEq⟩

theorem activeValue_remove_iff
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber) (notInstalled : ¬fiber.Installed)
    {key : sig.Key} {value : sig.Value key} :
    ActiveValue (removeFiber state name) key value ↔ ActiveValue state key value := by
  have notActive := notActive_of_notInstalled notInstalled
  constructor
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    have different : provider ≠ name := by
      intro same
      subst provider
      rw [removeFiber_lookup_same] at lookup
      cases lookup
    exact ⟨provider, current,
      by simpa [removeFiber_lookup_other, different] using lookup, active, valueEq⟩
  · rintro ⟨provider, current, lookup, active, valueEq⟩
    have different : provider ≠ name := by
      intro same
      subst provider
      rw [present] at lookup
      have equal := Option.some.inj lookup
      subst current
      exact notActive active
    exact ⟨provider, current,
      by simpa [removeFiber_lookup_other, different] using lookup, active, valueEq⟩

theorem activeContext_eq_of_activeValue_iff
    {left right : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (activeValues : ∀ key value, ActiveValue left key value ↔ ActiveValue right key value) :
    activeContext left = activeContext right := by
  apply Coeffect.Context.ext
  intro key
  cases leftLookup : activeContext left key with
  | none =>
      cases rightLookup : activeContext right key with
      | none => rfl
      | some rightValue =>
          have rightActive := (activeContext_value_iff rightWf).1 rightLookup
          have leftActive := (activeValues key rightValue).2 rightActive
          have impossible := (activeContext_value_iff leftWf).2 leftActive
          rw [leftLookup] at impossible
          cases impossible
  | some leftValue =>
      have leftActive := (activeContext_value_iff leftWf).1 leftLookup
      have rightActive := (activeValues key leftValue).1 leftActive
      exact ((activeContext_value_iff rightWf).2 rightActive).symm

theorem activeContext_insert_eq
    (state : State catalog Ambient) (name : sig.Name) (parent : Option sig.Name)
    (component : sig.ComponentId) (fresh : Coeffect.Absent state.registry name)
    (beforeWf : WellFormed state)
    (afterWf : WellFormed (insertFiber state name parent component)) :
    activeContext (insertFiber state name parent component) = activeContext state := by
  apply activeContext_eq_of_activeValue_iff afterWf beforeWf
  intro key value
  exact activeValue_insert_iff state name parent component fresh

theorem activeContext_retire_eq
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber) (beforeWf : WellFormed state)
    (afterWf : WellFormed (retireFiber state name fiber)) :
    activeContext (retireFiber state name fiber) = activeContext state := by
  apply activeContext_eq_of_activeValue_iff afterWf beforeWf
  intro key value
  exact activeValue_retire_iff state name fiber present

theorem activeContext_remove_eq
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : state.registry name = some fiber) (notInstalled : ¬fiber.Installed)
    (beforeWf : WellFormed state) (afterWf : WellFormed (removeFiber state name)) :
    activeContext (removeFiber state name) = activeContext state := by
  apply activeContext_eq_of_activeValue_iff afterWf beforeWf
  intro key value
  exact activeValue_remove_iff state name fiber present notInstalled

theorem orchestration_activeContext_eq
    {before after : State catalog Ambient}
    (step : OrchestrationStep before after) (wf : WellFormed before) :
    activeContext after = activeContext before := by
  have afterWf := step.preservesWellFormed wf
  cases step with
  | insert name fresh parent parentPresent component provisionFresh =>
      exact activeContext_insert_eq before name parent component fresh wf afterWf
  | retire name fiber present =>
      exact activeContext_retire_eq before name fiber present wf afterWf
  | remove name fiber present retired inactive childless =>
      exact activeContext_remove_eq before name fiber present inactive wf afterWf

/-!
## Paired control edits and related successors
-/

theorem controlAt_insert_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right)
    (name : sig.Name) (parent : Option sig.Name) (component : sig.ComponentId) :
    ∀ observed,
      GlobalRelations.controlAt (insertFiber left name parent component) observed =
        GlobalRelations.controlAt (insertFiber right name parent component) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    simp [GlobalRelations.controlAt, fiberControl, related.2.1]
  · simpa [GlobalRelations.controlAt, insertFiber_lookup_other, same] using
      related.2.2 observed

theorem controlAt_retire_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right)
    (name : sig.Name) (leftFiber rightFiber : Fiber catalog)
    (controls : fiberControl leftFiber = fiberControl rightFiber) :
    ∀ observed,
      GlobalRelations.controlAt (retireFiber left name leftFiber) observed =
        GlobalRelations.controlAt (retireFiber right name rightFiber) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    have updated := congrArg
      (fun control : FiberControl catalog ↦ { control with retired := true }) controls
    simpa [GlobalRelations.controlAt, fiberControl] using congrArg some updated
  · simpa [GlobalRelations.controlAt, retireFiber_lookup_other, same] using
      related.2.2 observed

theorem controlAt_remove_related
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) (name : sig.Name) :
    ∀ observed,
      GlobalRelations.controlAt (removeFiber left name) observed =
        GlobalRelations.controlAt (removeFiber right name) observed := by
  intro observed
  by_cases same : observed = name
  · subst observed
    simp [GlobalRelations.controlAt]
  · simpa [GlobalRelations.controlAt, removeFiber_lookup_other, same] using
      related.2.2 observed

theorem contextRelated_after_orchestration
    {values : ValueSetoids sig}
    {left right leftAfter rightAfter : State catalog Ambient}
    (leftStep : OrchestrationStep left leftAfter)
    (rightStep : OrchestrationStep right rightAfter)
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right) :
    ContextRelated values (activeContext leftAfter) (activeContext rightAfter) := by
  rw [orchestration_activeContext_eq leftStep leftWf,
    orchestration_activeContext_eq rightStep rightWf]
  exact related.1

/-!
## Exact matched-step squares
-/

structure ForwardOrchestrationMatch
    (values : ValueSetoids sig)
    {left right leftAfter : State catalog Ambient}
    (step : OrchestrationStep left leftAfter) where
  rightAfter : State catalog Ambient
  matched : OrchestrationStep right rightAfter
  same_kind : orchestrationKind matched = orchestrationKind step
  same_actor : orchestrationName matched = orchestrationName step
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : RuleRelated values leftAfter rightAfter

structure BackwardOrchestrationMatch
    (values : ValueSetoids sig)
    {left right rightAfter : State catalog Ambient}
    (step : OrchestrationStep right rightAfter) where
  leftAfter : State catalog Ambient
  matched : OrchestrationStep left leftAfter
  same_kind : orchestrationKind matched = orchestrationKind step
  same_actor : orchestrationName matched = orchestrationName step
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related : RuleRelated values leftAfter rightAfter

def matchOrchestrationForward
    {values : ValueSetoids sig}
    {left right leftAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (step : OrchestrationStep left leftAfter) :
    ForwardOrchestrationMatch values (right := right) step := by
  cases step with
  | insert name fresh parent parentPresent component provisionFresh =>
      have rightFresh : Coeffect.Absent right.registry name := {
        lookup_eq := (registry_none_iff related name).1 fresh.lookup_eq
      }
      have rightParentPresent : ∀ parentName, parent = some parentName →
          ∃ parentFiber, right.registry parentName = some parentFiber := by
        intro parentName parentEq
        obtain ⟨leftParent, leftPresent⟩ := parentPresent parentName parentEq
        let aligned := matchFiber related leftPresent
        exact ⟨aligned.peerFiber, aligned.peer_present⟩
      have rightProvisionFresh : ∀ existing existingFiber key,
          right.registry existing = some existingFiber →
          key ∈ (catalog.declaration component).provision →
          key ∈ (catalog.declaration existingFiber.component).provision → False := by
        intro existing existingFiber key existingPresent insertedKey existingKey
        let aligned := matchFiber (ruleRelated_symm related) existingPresent
        have componentEq := fiberControl_component_eq aligned.control_eq
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
        successors_related := by
          constructor
          · exact contextRelated_after_orchestration
              (.insert left name fresh parent parentPresent component provisionFresh)
              matched leftWf rightWf related
          · constructor
            · change left.nextBirth + 1 = right.nextBirth + 1
              exact congrArg (fun birth ↦ birth + 1) related.2.1
            · exact controlAt_insert_related related name parent component
      }
  | retire name leftFiber leftPresent =>
      let aligned := matchFiber related leftPresent
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
        successors_related := by
          constructor
          · exact contextRelated_after_orchestration
              (.retire left name leftFiber leftPresent) matched leftWf rightWf related
          · exact ⟨related.2.1,
              controlAt_retire_related related name leftFiber aligned.peerFiber
                aligned.control_eq⟩
      }
  | remove name leftFiber leftPresent retired inactive childless =>
      let aligned := matchFiber related leftPresent
      have rightRetired : aligned.peerFiber.retired = true :=
        (fiberControl_retired_eq aligned.control_eq).symm.trans retired
      have rightInactive : ¬aligned.peerFiber.Installed := by
        intro rightInstalled
        exact inactive ((fiberControl_installed_iff aligned.control_eq).2 rightInstalled)
      have rightChildless : ∀ child childFiber,
          right.registry child = some childFiber → childFiber.parent ≠ some name := by
        intro child childFiber childPresent childParent
        let childAligned := matchFiber (ruleRelated_symm related) childPresent
        have parentEq := fiberControl_parent_eq childAligned.control_eq
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
        successors_related := by
          constructor
          · exact contextRelated_after_orchestration
              (.remove left name leftFiber leftPresent retired inactive childless)
              matched leftWf rightWf related
          · exact ⟨related.2.1, controlAt_remove_related related name⟩
      }

def matchOrchestrationBackward
    {values : ValueSetoids sig}
    {left right rightAfter : State catalog Ambient}
    (leftWf : WellFormed left) (rightWf : WellFormed right)
    (related : RuleRelated values left right)
    (step : OrchestrationStep right rightAfter) :
    BackwardOrchestrationMatch values (left := left) step := by
  let swapped := matchOrchestrationForward (left := right) (right := left)
    rightWf leftWf (ruleRelated_symm related) step
  exact {
    leftAfter := swapped.rightAfter
    matched := swapped.matched
    same_kind := swapped.same_kind
    same_actor := swapped.same_actor
    leftAfter_wellFormed := swapped.rightAfter_wellFormed
    rightAfter_wellFormed := swapped.leftAfter_wellFormed
    successors_related := ruleRelated_symm swapped.successors_related
  }

/-- Exact well-formed bisimulation for the three orchestration constructors. -/
structure OrchestrationRuleBisimulation
    (values : ValueSetoids sig) where
  forward : ∀ {left right leftAfter : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    (step : OrchestrationStep left leftAfter) →
      ForwardOrchestrationMatch values (right := right) step
  backward : ∀ {left right rightAfter : State catalog Ambient},
    WellFormed left → WellFormed right → RuleRelated values left right →
    (step : OrchestrationStep right rightAfter) →
      BackwardOrchestrationMatch values (left := left) step

def orchestrationRuleBisimulation
    (values : ValueSetoids sig) : OrchestrationRuleBisimulation
      (catalog := catalog) (Ambient := Ambient) values where
  forward := matchOrchestrationForward
  backward := matchOrchestrationBackward

/-!
## Explicit lifecycle boundary
-/

/-- One missing lifecycle law: abortability may inspect data forgotten by `RuleRelated`. -/
def InertiaRespectsRuleRelated
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) : Prop :=
  ∀ owner code {left right : State catalog Ambient},
    RuleRelated values left right →
      (inertia.canAbort owner code left ↔ inertia.canAbort owner code right)

/-!
## Heterogeneous example with nontrivial value relations
-/

namespace HeterogeneousExample

abbrev Signature := Cordis.GlobalRegistry.Example.signature
abbrev Catalog := Cordis.GlobalRegistry.Example.catalog
abbrev Key := Cordis.GlobalRegistry.Example.Key
abbrev Value := Cordis.GlobalRegistry.Example.Value
abbrev ExampleState := GlobalState Catalog Unit

def natParity : Setoid Nat where
  r left right := left % 2 = right % 2
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

def stringLength : Setoid String where
  r left right := left.length = right.length
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

def values : ValueSetoids Signature where
  relation
    | .counter => natParity
    | .label => stringLength

def rightTable : Coeffect.Context Key Value :=
  Coeffect.setAt
    (Coeffect.setAt Coeffect.empty .counter (show Value .counter from 9))
    .label (show Value .label from "other")

def rightProviderFiber : Fiber Catalog where
  component := .provider
  parent := none
  birth := 0
  table := rightTable
  table_within_provision := by
    intro key present
    cases key <;> simp [Cordis.GlobalRegistry.Example.providerDecl]
  retired := false
  phase := .active [] Cordis.GlobalRegistry.Example.emptyProviderView

abbrev leftState : ExampleState := Cordis.GlobalRegistry.Example.activeState

def rightState : ExampleState where
  ambient := ()
  nextBirth := 1
  registry := Coeffect.setAt Coeffect.empty 0 rightProviderFiber

theorem leftState_wellFormed : WellFormed leftState :=
  Cordis.GlobalRegistry.Example.activeState_wellFormed

theorem rightState_wellFormed : WellFormed rightState := by
  constructor
  · intro name fiber lookup
    by_cases same : name = 0
    · subst name
      simp [rightState] at lookup
      subst fiber
      decide
    · simp [rightState, Coeffect.setAt_other, same] at lookup
  · intro name fiber parent lookup parentEq
    by_cases same : name = 0
    · subst name
      simp [rightState] at lookup
      subst fiber
      simp [rightProviderFiber] at parentEq
    · simp [rightState, Coeffect.setAt_other, same] at lookup
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    by_cases same : name = 0
    · subst name
      simp [rightState] at lookup
      subst fiber
      simp [rightProviderFiber] at parentEq
    · simp [rightState, Coeffect.setAt_other, same] at lookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    have leftEq : left = 0 := by
      by_cases same : left = 0
      · exact same
      · simp [rightState, Coeffect.setAt_other, same] at leftLookup
    have rightEq : right = 0 := by
      by_cases same : right = 0
      · exact same
      · simp [rightState, Coeffect.setAt_other, same] at rightLookup
    exact leftEq.trans rightEq.symm
  · intro name fiber lookup committed committedEq declared
    by_cases same : name = 0
    · subst name
      simp [rightState] at lookup
      subst fiber
      rcases declared with ⟨key, declared⟩
      change key ∈ Cordis.GlobalRegistry.Example.providerDecl.dependencies.keys at declared
      simp [Cordis.GlobalRegistry.Example.providerDecl] at declared
    · simp [rightState, Coeffect.setAt_other, same] at lookup
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    by_cases same : name = 0
    · subst name
      simp [rightState] at lookup
      subst fiber
      rcases declared with ⟨key, declared⟩
      change key ∈ Cordis.GlobalRegistry.Example.providerDecl.dependencies.keys at declared
      simp [Cordis.GlobalRegistry.Example.providerDecl] at declared
    · simp [rightState, Coeffect.setAt_other, same] at lookup

theorem right_counter_exact : activeContext rightState .counter = some 9 := by
  apply (activeContext_value_iff rightState_wellFormed).2
  exact ⟨0, rightProviderFiber, rfl,
    by simp [rightProviderFiber, Fiber.Active, Phase.Active], rfl⟩

theorem right_label_exact : activeContext rightState .label = some "other" := by
  apply (activeContext_value_iff rightState_wellFormed).2
  exact ⟨0, rightProviderFiber, rfl,
    by simp [rightProviderFiber, Fiber.Active, Phase.Active], rfl⟩

theorem source_values_are_not_equal :
    Cordis.GlobalRegistry.Example.providerTable .counter ≠ rightTable .counter ∧
      Cordis.GlobalRegistry.Example.providerTable .label ≠ rightTable .label := by
  constructor
  · change (some 7 : Option Nat) ≠ some 9
    decide
  · change (some "ready" : Option String) ≠ some "other"
    decide

theorem source_values_are_related :
    (values.relation .counter).r 7 9 ∧
      (values.relation .label).r "ready" "other" := by
  constructor
  · change 7 % 2 = 9 % 2
    decide
  · change "ready".length = "other".length
    decide

theorem states_ruleRelated : RuleRelated values leftState rightState := by
  constructor
  · intro key
    cases key with
    | counter =>
        rw [Cordis.GlobalRegistry.Example.active_counter_exact, right_counter_exact]
        change 7 % 2 = 9 % 2
        decide
    | label =>
        rw [Cordis.GlobalRegistry.Example.active_label_exact, right_label_exact]
        change "ready".length = "other".length
        decide
  · constructor
    · rfl
    · intro name
      by_cases same : name = 0
      · subst name
        rfl
      · simp [leftState, rightState, Cordis.GlobalRegistry.Example.activeState,
          GlobalRelations.controlAt, Coeffect.setAt_other, same]

def leftInsert : OrchestrationStep leftState
    (insertFiber leftState 1 (some 0) .consumer) :=
  .insert leftState 1 (by constructor; rfl) (some 0) (by
      intro parent parentEq
      have equal : parent = 0 := Option.some.inj parentEq.symm
      subst parent
      exact ⟨Cordis.GlobalRegistry.Example.activeProviderFiber, rfl⟩)
    .consumer (by simp [Cordis.GlobalRegistry.Example.consumerDecl])

def insertionMatch : ForwardOrchestrationMatch values (right := rightState) leftInsert :=
  matchOrchestrationForward leftState_wellFormed rightState_wellFormed states_ruleRelated
    leftInsert

theorem insertionMatch_endpoint :
    insertionMatch.rightAfter = insertFiber rightState 1 (some 0) .consumer := rfl

theorem insertionMatch_successors :
    RuleRelated values
      (insertFiber leftState 1 (some 0) .consumer)
      (insertFiber rightState 1 (some 0) .consumer) := by
  simpa [insertionMatch_endpoint] using insertionMatch.successors_related

end HeterogeneousExample

/-!
## Ambient-sensitive inertia counterexample
-/

namespace InertiaGap

abbrev Signature := Cordis.GlobalDynamics.Example.ExampleSig
abbrev Catalog := Cordis.GlobalDynamics.Example.exampleCatalog
abbrev ExampleState := Cordis.GlobalDynamics.Example.ExampleState

abbrev baseline : ExampleState := Cordis.GlobalDynamics.Example.start

def shifted : ExampleState := { baseline with ambient := baseline.ambient + 1 }

theorem baseline_wellFormed : WellFormed baseline :=
  Cordis.GlobalDynamics.Example.start_wellFormed

theorem shifted_wellFormed : WellFormed shifted := by
  exact {
    birth_bounded := by
      simpa [shifted, baseline] using baseline_wellFormed.birth_bounded
    parent_present := by
      simpa [shifted, baseline] using baseline_wellFormed.parent_present
    parent_older := by
      simpa [shifted, baseline] using baseline_wellFormed.parent_older
    provisions_unique := by
      simpa [shifted, baseline] using baseline_wellFormed.provisions_unique
    committed_provider_present := by
      simpa [shifted, baseline] using baseline_wellFormed.committed_provider_present
    committed_provider_installed := by
      simpa [shifted, baseline] using baseline_wellFormed.committed_provider_installed
  }

theorem shifted_activeContext_eq : activeContext shifted = activeContext baseline := by
  apply Coeffect.Context.ext
  intro key
  rfl

theorem baseline_ruleRelated_shifted :
    RuleRelated HeterogeneousExample.values baseline shifted := by
  exact ⟨by
      rw [shifted_activeContext_eq]
      exact contextRelated_refl HeterogeneousExample.values (activeContext baseline),
    rfl, fun _ ↦ rfl⟩

def ambientSensitiveInertia :
    GlobalLifecycle.InertiaPolicy Cordis.GlobalDynamics.Example.dynamics where
  canAbort _ _ state := state.ambient = baseline.ambient

theorem aborts_at_baseline : ambientSensitiveInertia.canAbort 0 0 baseline := rfl

theorem does_not_abort_at_shifted :
    ¬ambientSensitiveInertia.canAbort 0 0 shifted := by
  simp [ambientSensitiveInertia, shifted, baseline, Cordis.GlobalDynamics.Example.start]

/-- `RuleRelated` alone cannot transport the L-DivertAbort inertia premise. -/
theorem ambientSensitiveInertia_not_respecting :
    ¬InertiaRespectsRuleRelated HeterogeneousExample.values
      Cordis.GlobalDynamics.Example.dynamics ambientSensitiveInertia := by
  intro respects
  have decisions := respects 0 0 baseline_ruleRelated_shifted
  exact does_not_abort_at_shifted (decisions.1 aborts_at_baseline)

end InertiaGap

end Cordis.GlobalRuleInvariance
