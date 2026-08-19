import Cordis.GlobalRelations

/-!
# Vestigial global entries: corrected orchestration slice

This module proves the source-faithful part of CORDIS paper Lemma 57 supported by the current
raw global calculus at revision `948a07b369c62adb3b12e102458be5c18dfb69b9`.

The effect-equivalence sentence is exact: a retired, successful-inactive, empty-table, childless
entry is `EffectRelated` to its removal. The rule-simulation result is deliberately restricted to
the three orchestration constructors and states every premise the literal raw relation needs.

Two parent-pointer cases are absent from the paper statement. Forward simulation fails when an
O-Insert at a foreign name adopts the vestigial entry as its parent: removing that entry destroys
the parent-presence premise. Backward simulation fails when O-Remove deletes the vestigial
entry's parent: after the child is removed the parent is childless, while restoring the vestigial
child blocks the removal. The paper's vestigial condition says no fiber has the vestigial entry as
parent; it does not say that the vestigial entry itself has no parent. Accordingly, the corrected
backward simulation has three exclusions: drawing the removed name, claiming its provision, and
removing its parent.

This is not full Lemma 57. Iterator, lifecycle, oracle, inertia, and accumulated-recovery
insensitivity require additional dynamics laws and remain out of scope.
-/

set_option autoImplicit false

namespace Cordis.GlobalVestigial

open Cordis.GlobalRegistry Cordis.GlobalCalculus Cordis.GlobalRelations

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-!
## Generic vestigial entries and effect observation
-/

/-- The exact proof-carrying vestigial-entry witness from paper Lemma 57. -/
structure Vestigial (state : State catalog Ambient) (name : sig.Name) where
  fiber : Fiber catalog
  present : state.registry name = some fiber
  retired : fiber.retired = true
  inactive : fiber.phase = .inactive none
  table_empty : fiber.table = Coeffect.empty
  childless : ∀ child childFiber,
    state.registry child = some childFiber → childFiber.parent ≠ some name

namespace Vestigial

theorem notInstalled
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name) : ¬vestigial.fiber.Installed := by
  rw [Fiber.Installed, vestigial.inactive]
  simp [Phase.Installed]

theorem notActive
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name) : ¬vestigial.fiber.Active := by
  rw [Fiber.Active, vestigial.inactive]
  simp [Phase.Active]

/-- The paper's effect-observation sentence: empty-table presence is equivalent to absence. -/
theorem effectRelated_remove
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name) :
    EffectRelated state (removeFiber state name) := by
  constructor
  · rfl
  · intro observed key
    by_cases same : observed = name
    · subst observed
      simp [tableAt, vestigial.present, vestigial.table_empty]
    · simp [tableAt, removeFiber_lookup_other, same]

end Vestigial

/-!
## Public orchestration projections
-/

inductive OrchestrationKind where
  | insert
  | retire
  | remove
deriving DecidableEq, Repr

def orchestrationKind
    {before after : State catalog Ambient} :
    OrchestrationStep before after → OrchestrationKind
  | .insert .. => .insert
  | .retire .. => .retire
  | .remove .. => .remove

def orchestrationName
    {before after : State catalog Ambient} : OrchestrationStep before after → sig.Name
  | .insert _ name .. => name
  | .retire _ name .. => name
  | .remove _ name .. => name

/-- Forward insertion must not use the soon-to-be-absent vestigial entry as parent. -/
def AvoidsVestigialParent
    {before after : State catalog Ambient}
    (name : sig.Name) (step : OrchestrationStep before after) : Prop :=
  match step with
  | .insert _ _ _ parent _ _ _ => parent ≠ some name
  | .retire .. => True
  | .remove .. => True

/-- First backward exception from the paper: the smaller state can reissue the removed name. -/
def DrawsVestigialName
    {before after : State catalog Ambient}
    (name : sig.Name) (step : OrchestrationStep before after) : Prop :=
  match step with
  | .insert _ inserted .. => inserted = name
  | .retire .. => False
  | .remove .. => False

/-- Second backward exception from the paper: restoring the fiber can create a provision clash. -/
def ClaimsVestigialProvision
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    {after : State catalog Ambient}
    (step : OrchestrationStep (removeFiber state name) after) : Prop :=
  match step with
  | .insert _ _ _ _ _ component _ =>
      ∃ key,
        key ∈ (catalog.declaration component).provision ∧
        key ∈ (catalog.declaration vestigial.fiber.component).provision
  | .retire .. => False
  | .remove .. => False

/-- Corrected third backward exception: restoring the vestigial child can block parent removal. -/
def RemovesVestigialParent
    {state : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    {after : State catalog Ambient}
    (step : OrchestrationStep (removeFiber state name) after) : Prop :=
  match step with
  | .remove _ removed .. => vestigial.fiber.parent = some removed
  | .insert .. => False
  | .retire .. => False

/-!
## Exact removal squares
-/

structure ForwardRemovalSquare
    {state after : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    (step : OrchestrationStep state after) where
  removedAfter : State catalog Ambient
  matched : OrchestrationStep (removeFiber state name) removedAfter
  same_kind : orchestrationKind matched = orchestrationKind step
  same_actor : orchestrationName matched = orchestrationName step
  remove_after : removeFiber after name = removedAfter
  remains_vestigial : Vestigial after name

structure BackwardRemovalSquare
    {state removedAfter : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    (step : OrchestrationStep (removeFiber state name) removedAfter) where
  after : State catalog Ambient
  matched : OrchestrationStep state after
  same_kind : orchestrationKind matched = orchestrationKind step
  same_actor : orchestrationName matched = orchestrationName step
  remove_after : removeFiber after name = removedAfter
  remains_vestigial : Vestigial after name

/-!
## Pure edit commutation
-/

theorem remove_insert_commute
    (state : State catalog Ambient) (inserted removed : sig.Name)
    (parent : Option sig.Name) (component : sig.ComponentId)
    (different : inserted ≠ removed) :
    removeFiber (insertFiber state inserted parent component) removed =
      insertFiber (removeFiber state removed) inserted parent component := by
  cases state
  simp [removeFiber, insertFiber,
    Coeffect.setAt_removeAt_commute, different]

theorem remove_retire_commute
    (state : State catalog Ambient) (retired removed : sig.Name)
    (fiber : Fiber catalog) (different : retired ≠ removed) :
    removeFiber (retireFiber state retired fiber) removed =
      retireFiber (removeFiber state removed) retired fiber := by
  cases state
  simp [removeFiber, retireFiber,
    Coeffect.setAt_removeAt_commute, different]

theorem remove_remove_commute
    (state : State catalog Ambient) (first second : sig.Name) :
    removeFiber (removeFiber state first) second =
      removeFiber (removeFiber state second) first := by
  cases state
  simp [removeFiber, Coeffect.removeAt_commute]

/-!
## Corrected forward orchestration simulation
-/

def Vestigial.forward_orchestration
    {state after : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    (step : OrchestrationStep state after)
    (foreign : orchestrationName step ≠ name)
    (parentSafe : AvoidsVestigialParent name step) :
    ForwardRemovalSquare vestigial step := by
  cases step with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      change inserted ≠ name at foreign
      change parent ≠ some name at parentSafe
      have removedFresh : Coeffect.Absent (removeFiber state name).registry inserted := by
        constructor
        simpa [removeFiber_lookup_other, foreign] using fresh.lookup_eq
      have removedParent : ∀ parentName, parent = some parentName →
          ∃ parentFiber, (removeFiber state name).registry parentName = some parentFiber := by
        intro parentName parentEq
        obtain ⟨parentFiber, parentLookup⟩ := parentPresent parentName parentEq
        have different : parentName ≠ name := by
          intro equal
          subst parentName
          exact parentSafe parentEq
        exact ⟨parentFiber, by
          simpa [removeFiber_lookup_other, different] using parentLookup⟩
      have removedProvision : ∀ existing existingFiber key,
          (removeFiber state name).registry existing = some existingFiber →
          key ∈ (catalog.declaration component).provision →
          key ∈ (catalog.declaration existingFiber.component).provision → False := by
        intro existing existingFiber key lookup insertedKey existingKey
        have different : existing ≠ name := by
          intro equal
          subst existing
          rw [removeFiber_lookup_same] at lookup
          cases lookup
        have prior : state.registry existing = some existingFiber := by
          simpa [removeFiber_lookup_other, different] using lookup
        exact provisionFresh existing existingFiber key prior insertedKey existingKey
      let matched : OrchestrationStep (removeFiber state name)
          (insertFiber (removeFiber state name) inserted parent component) :=
        .insert (removeFiber state name) inserted removedFresh parent removedParent component
          removedProvision
      let remains : Vestigial (insertFiber state inserted parent component) name := {
        fiber := vestigial.fiber
        present := by
          simpa [insertFiber_lookup_other, Ne.symm foreign] using vestigial.present
        retired := vestigial.retired
        inactive := vestigial.inactive
        table_empty := vestigial.table_empty
        childless := by
          intro child childFiber lookup
          by_cases childIsInserted : child = inserted
          · subst child
            rw [insertFiber_lookup_same] at lookup
            have equal := Option.some.inj lookup
            subst childFiber
            exact parentSafe
          · rw [insertFiber_lookup_other state inserted child parent component childIsInserted]
              at lookup
            exact vestigial.childless child childFiber lookup
      }
      exact {
        removedAfter := insertFiber (removeFiber state name) inserted parent component
        matched := matched
        same_kind := rfl
        same_actor := rfl
        remove_after := remove_insert_commute state inserted name parent component foreign
        remains_vestigial := remains
      }
  | retire retired fiber present =>
      change retired ≠ name at foreign
      let matched : OrchestrationStep (removeFiber state name)
          (retireFiber (removeFiber state name) retired fiber) :=
        .retire (removeFiber state name) retired fiber (by
          simpa [removeFiber_lookup_other, foreign] using present)
      let remains : Vestigial (retireFiber state retired fiber) name := {
        fiber := vestigial.fiber
        present := by
          simpa [retireFiber_lookup_other, Ne.symm foreign] using vestigial.present
        retired := vestigial.retired
        inactive := vestigial.inactive
        table_empty := vestigial.table_empty
        childless := by
          intro child childFiber lookup
          by_cases childIsRetired : child = retired
          · subst child
            rw [retireFiber_lookup_same] at lookup
            have equal := Option.some.inj lookup
            subst childFiber
            simpa using vestigial.childless retired fiber present
          · rw [retireFiber_lookup_other state retired child fiber childIsRetired] at lookup
            exact vestigial.childless child childFiber lookup
      }
      exact {
        removedAfter := retireFiber (removeFiber state name) retired fiber
        matched := matched
        same_kind := rfl
        same_actor := rfl
        remove_after := remove_retire_commute state retired name fiber foreign
        remains_vestigial := remains
      }
  | remove removed fiber present retired inactive childless =>
      change removed ≠ name at foreign
      have removedPresent : (removeFiber state name).registry removed = some fiber := by
        simpa [removeFiber_lookup_other, foreign] using present
      have removedChildless : ∀ child childFiber,
          (removeFiber state name).registry child = some childFiber →
          childFiber.parent ≠ some removed := by
        intro child childFiber lookup
        have childDifferent : child ≠ name := by
          intro equal
          subst child
          rw [removeFiber_lookup_same] at lookup
          cases lookup
        have prior : state.registry child = some childFiber := by
          simpa [removeFiber_lookup_other, childDifferent] using lookup
        exact childless child childFiber prior
      let matched : OrchestrationStep (removeFiber state name)
          (removeFiber (removeFiber state name) removed) :=
        .remove (removeFiber state name) removed fiber removedPresent retired inactive
          removedChildless
      let remains : Vestigial (removeFiber state removed) name := {
        fiber := vestigial.fiber
        present := by
          simpa [removeFiber_lookup_other, Ne.symm foreign] using vestigial.present
        retired := vestigial.retired
        inactive := vestigial.inactive
        table_empty := vestigial.table_empty
        childless := by
          intro child childFiber lookup
          have childDifferent : child ≠ removed := by
            intro equal
            subst child
            rw [removeFiber_lookup_same] at lookup
            cases lookup
          have prior : state.registry child = some childFiber := by
            simpa [removeFiber_lookup_other, childDifferent] using lookup
          exact vestigial.childless child childFiber prior
      }
      exact {
        removedAfter := removeFiber (removeFiber state name) removed
        matched := matched
        same_kind := rfl
        same_actor := rfl
        remove_after := remove_remove_commute state removed name
        remains_vestigial := remains
      }

/-!
## Corrected backward orchestration simulation
-/

def Vestigial.backward_orchestration
    {state removedAfter : State catalog Ambient} {name : sig.Name}
    (vestigial : Vestigial state name)
    (step : OrchestrationStep (removeFiber state name) removedAfter)
    (notDraws : ¬DrawsVestigialName name step)
    (noProvisionConflict : ¬ClaimsVestigialProvision vestigial step)
    (notRemovesParent : ¬RemovesVestigialParent vestigial step) :
    BackwardRemovalSquare vestigial step := by
  cases step with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      change inserted ≠ name at notDraws
      change ¬∃ key,
        key ∈ (catalog.declaration component).provision ∧
        key ∈ (catalog.declaration vestigial.fiber.component).provision
        at noProvisionConflict
      have originalFresh : Coeffect.Absent state.registry inserted := by
        constructor
        simpa [removeFiber_lookup_other, notDraws] using fresh.lookup_eq
      have originalParent : ∀ parentName, parent = some parentName →
          ∃ parentFiber, state.registry parentName = some parentFiber := by
        intro parentName parentEq
        obtain ⟨parentFiber, parentLookup⟩ := parentPresent parentName parentEq
        have different : parentName ≠ name := by
          intro equal
          subst parentName
          rw [removeFiber_lookup_same] at parentLookup
          cases parentLookup
        exact ⟨parentFiber, by
          simpa [removeFiber_lookup_other, different] using parentLookup⟩
      have originalProvision : ∀ existing existingFiber key,
          state.registry existing = some existingFiber →
          key ∈ (catalog.declaration component).provision →
          key ∈ (catalog.declaration existingFiber.component).provision → False := by
        intro existing existingFiber key lookup insertedKey existingKey
        by_cases same : existing = name
        · subst existing
          rw [vestigial.present] at lookup
          have equal := Option.some.inj lookup
          subst existingFiber
          exact noProvisionConflict ⟨key, insertedKey, existingKey⟩
        · have removedLookup :
              (removeFiber state name).registry existing = some existingFiber := by
            simpa [removeFiber_lookup_other, same] using lookup
          exact provisionFresh existing existingFiber key removedLookup insertedKey existingKey
      have parentSafe : parent ≠ some name := by
        intro parentEq
        obtain ⟨parentFiber, parentLookup⟩ := parentPresent name parentEq
        rw [removeFiber_lookup_same] at parentLookup
        cases parentLookup
      let matched : OrchestrationStep state
          (insertFiber state inserted parent component) :=
        .insert state inserted originalFresh parent originalParent component originalProvision
      let forward := vestigial.forward_orchestration matched notDraws parentSafe
      exact {
        after := insertFiber state inserted parent component
        matched := matched
        same_kind := rfl
        same_actor := rfl
        remove_after := forward.remove_after
        remains_vestigial := forward.remains_vestigial
      }
  | retire retired fiber present =>
      have foreign : retired ≠ name := by
        intro equal
        subst retired
        rw [removeFiber_lookup_same] at present
        cases present
      have originalPresent : state.registry retired = some fiber := by
        simpa [removeFiber_lookup_other, foreign] using present
      let matched : OrchestrationStep state (retireFiber state retired fiber) :=
        .retire state retired fiber originalPresent
      let forward := vestigial.forward_orchestration matched foreign trivial
      exact {
        after := retireFiber state retired fiber
        matched := matched
        same_kind := rfl
        same_actor := rfl
        remove_after := forward.remove_after
        remains_vestigial := forward.remains_vestigial
      }
  | remove removed fiber present retired inactive childless =>
      change vestigial.fiber.parent ≠ some removed at notRemovesParent
      have foreign : removed ≠ name := by
        intro equal
        subst removed
        rw [removeFiber_lookup_same] at present
        cases present
      have originalPresent : state.registry removed = some fiber := by
        simpa [removeFiber_lookup_other, foreign] using present
      have originalChildless : ∀ child childFiber,
          state.registry child = some childFiber → childFiber.parent ≠ some removed := by
        intro child childFiber lookup
        by_cases childIsVestigial : child = name
        · subst child
          rw [vestigial.present] at lookup
          have equal := Option.some.inj lookup
          subst childFiber
          exact notRemovesParent
        · have removedLookup :
              (removeFiber state name).registry child = some childFiber := by
            simpa [removeFiber_lookup_other, childIsVestigial] using lookup
          exact childless child childFiber removedLookup
      let matched : OrchestrationStep state (removeFiber state removed) :=
        .remove state removed fiber originalPresent retired inactive originalChildless
      let forward := vestigial.forward_orchestration matched foreign trivial
      exact {
        after := removeFiber state removed
        matched := matched
        same_kind := rfl
        same_actor := rfl
        remove_after := forward.remove_after
        remains_vestigial := forward.remains_vestigial
      }

/-!
## Kernel counterexamples for the omitted parent cases
-/

namespace Counterexample

inductive Name where
  | parent
  | vestigial
  | fresh
deriving DecidableEq, Repr

inductive Key where
  | slot
deriving DecidableEq, Repr

inductive Component where
  | empty
  | claiming
deriving DecidableEq, Repr

abbrev Value : Key → Type
  | .slot => Unit

abbrev signature : StaticSignature where
  Name := Name
  Key := Key
  ComponentId := Component
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Unit
  Value := Value
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def emptyDecl : ComponentDecl signature where
  dependencies := { keys := [], nodup := by simp }
  provision := []
  provision_nodup := by simp
  entry := ()

def claimingDecl : ComponentDecl signature where
  dependencies := { keys := [], nodup := by simp }
  provision := [.slot]
  provision_nodup := by simp
  entry := ()

abbrev exampleCatalog : Catalog signature where
  declaration
    | .empty => emptyDecl
    | .claiming => claimingDecl

abbrev ExampleState := GlobalState exampleCatalog Unit

def parentFiber : Fiber exampleCatalog where
  component := .empty
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := true
  phase := .inactive none

def vestigialFiber : Fiber exampleCatalog where
  component := .claiming
  parent := some .parent
  birth := 1
  table := Coeffect.empty
  table_within_provision := by simp
  retired := true
  phase := .inactive none

def state : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty .parent parentFiber) .vestigial vestigialFiber

theorem parent_present : state.registry .parent = some parentFiber := by rfl
theorem vestigial_present : state.registry .vestigial = some vestigialFiber := by rfl
theorem fresh_absent : state.registry .fresh = none := by rfl

def vestigial : Vestigial state .vestigial where
  fiber := vestigialFiber
  present := vestigial_present
  retired := rfl
  inactive := rfl
  table_empty := rfl
  childless := by
    intro child childFiber lookup
    cases child with
    | parent =>
        rw [parent_present] at lookup
        have equal := Option.some.inj lookup
        subst childFiber
        simp [parentFiber]
    | vestigial =>
        rw [vestigial_present] at lookup
        have equal := Option.some.inj lookup
        subst childFiber
        simp [vestigialFiber]
    | fresh =>
        rw [fresh_absent] at lookup
        cases lookup

theorem state_wellFormed : WellFormed state := by
  constructor
  · intro name fiber lookup
    cases name with
    | parent =>
        rw [parent_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        change 0 < 2
        decide
    | vestigial =>
        rw [vestigial_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        change 1 < 2
        decide
    | fresh =>
        rw [fresh_absent] at lookup
        cases lookup
  · intro name fiber parentName lookup parentEq
    cases name with
    | parent =>
        rw [parent_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        simp [parentFiber] at parentEq
    | vestigial =>
        rw [vestigial_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        have parentNameEq : parentName = .parent := Option.some.inj parentEq.symm
        subst parentName
        exact ⟨parentFiber, parent_present⟩
    | fresh =>
        rw [fresh_absent] at lookup
        cases lookup
  · intro name fiber parentName parentValue lookup parentEq parentLookup
    cases name with
    | parent =>
        rw [parent_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        simp [parentFiber] at parentEq
    | vestigial =>
        rw [vestigial_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        have parentNameEq : parentName = .parent := Option.some.inj parentEq.symm
        subst parentName
        rw [parent_present] at parentLookup
        have parentEqual := Option.some.inj parentLookup
        subst parentValue
        simp [parentFiber, vestigialFiber]
    | fresh =>
        rw [fresh_absent] at lookup
        cases lookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases left <;> cases right <;> simp [state] at leftLookup rightLookup <;>
      subst leftFiber <;> subst rightFiber <;>
      simp [vestigialFiber, parentFiber, exampleCatalog, emptyDecl, claimingDecl]
        at leftKey rightKey ⊢
  · intro name fiber lookup committed committedEq declared
    cases name with
    | parent =>
        rw [parent_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        simp [parentFiber, Phase.committed?] at committedEq
    | vestigial =>
        rw [vestigial_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        simp [vestigialFiber, Phase.committed?] at committedEq
    | fresh =>
        rw [fresh_absent] at lookup
        cases lookup
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    cases name with
    | parent =>
        rw [parent_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        simp [parentFiber, Phase.committed?] at committedEq
    | vestigial =>
        rw [vestigial_present] at lookup
        have equal := Option.some.inj lookup
        subst fiber
        simp [vestigialFiber, Phase.committed?] at committedEq
    | fresh =>
        rw [fresh_absent] at lookup
        cases lookup

def withoutVestigial : ExampleState := removeFiber state .vestigial

theorem without_parent_present : withoutVestigial.registry .parent = some parentFiber := by rfl
theorem without_vestigial_absent : withoutVestigial.registry .vestigial = none := by rfl
theorem without_fresh_absent : withoutVestigial.registry .fresh = none := by rfl

def removeVestigial : OrchestrationStep state withoutVestigial :=
  .remove state .vestigial vestigialFiber vestigial_present rfl
    (by simp [Fiber.Installed, vestigialFiber, Phase.Installed]) vestigial.childless

theorem withoutVestigial_wellFormed : WellFormed withoutVestigial :=
  removeVestigial.preservesWellFormed state_wellFormed

/-- The generic effect-equivalence theorem applies to the well-formed counterexample state. -/
theorem effectRelated_withoutVestigial : EffectRelated state withoutVestigial :=
  vestigial.effectRelated_remove

/-- Literal forward Lemma 57(1) fails: this valid insertion adopts the vestigial entry. -/
def adoptingInsert : OrchestrationStep state
    (insertFiber state .fresh (some .vestigial) .empty) :=
  .insert state .fresh (by constructor; exact fresh_absent) (some .vestigial)
    (by
      intro candidateParent parentEq
      have equal : candidateParent = .vestigial := Option.some.inj parentEq.symm
      subst candidateParent
      exact ⟨vestigialFiber, vestigial_present⟩)
    .empty (by simp [exampleCatalog, emptyDecl])

theorem adoptingInsert_is_foreign : orchestrationName adoptingInsert ≠ .vestigial := by decide

theorem adoptingInsert_uses_vestigial_parent :
    ¬AvoidsVestigialParent Name.vestigial adoptingInsert := by
  change ¬((some Name.vestigial : Option Name) ≠ some Name.vestigial)
  simp

theorem no_parent_witness_after_removal :
    ¬(∀ candidate, (some .vestigial : Option Name) = some candidate →
      ∃ parentFiber, withoutVestigial.registry candidate = some parentFiber) := by
  intro parentWitness
  obtain ⟨fiber, lookup⟩ := parentWitness .vestigial rfl
  rw [without_vestigial_absent] at lookup
  cases lookup

theorem adoptedState_wellFormed :
    WellFormed (insertFiber state .fresh (some .vestigial) .empty) :=
  adoptingInsert.preservesWellFormed state_wellFormed

/-!
The paper's two stated backward exceptions are genuine as well. The first step redraws the
removed name; the second inserts a component whose provision overlaps the restored fiber.
-/

def redrawVestigial : OrchestrationStep withoutVestigial
    (insertFiber withoutVestigial .vestigial none .empty) :=
  .insert withoutVestigial .vestigial
    (by constructor; exact without_vestigial_absent) none (by simp) .empty
    (by simp [exampleCatalog, emptyDecl])

theorem redrawVestigial_draws_name :
    DrawsVestigialName Name.vestigial redrawVestigial := rfl

theorem redrawVestigial_not_fresh_before : ¬Coeffect.Absent state.registry .vestigial := by
  intro absent
  have lookup := absent.lookup_eq
  rw [vestigial_present] at lookup
  cases lookup

theorem redrawnState_wellFormed :
    WellFormed (insertFiber withoutVestigial .vestigial none .empty) :=
  redrawVestigial.preservesWellFormed withoutVestigial_wellFormed

def claimingInsert : OrchestrationStep withoutVestigial
    (insertFiber withoutVestigial .fresh none .claiming) :=
  .insert withoutVestigial .fresh (by
      constructor
      rfl) none (by simp) .claiming (by
        intro existing existingFiber key lookup _ existingKey
        cases key
        cases existing with
        | parent =>
            rw [without_parent_present] at lookup
            have equal := Option.some.inj lookup
            subst existingFiber
            simp [parentFiber, exampleCatalog, emptyDecl] at existingKey
        | vestigial =>
            rw [without_vestigial_absent] at lookup
            cases lookup
        | fresh =>
            rw [without_fresh_absent] at lookup
            cases lookup)

theorem claimingInsert_claims_vestigial_provision :
    ClaimsVestigialProvision vestigial claimingInsert := by
  change ∃ key : Key, key ∈ [Key.slot] ∧ key ∈ [Key.slot]
  exact ⟨.slot, by simp, by simp⟩

theorem claimingInsert_does_not_draw_name :
    ¬DrawsVestigialName Name.vestigial claimingInsert := by
  change Name.fresh ≠ Name.vestigial
  decide

theorem claimingInsert_not_fresh_before :
    ¬(∀ existing existingFiber key,
      state.registry existing = some existingFiber →
      key ∈ (exampleCatalog.declaration Component.claiming).provision →
      key ∈ (exampleCatalog.declaration existingFiber.component).provision → False) := by
  intro provisionFresh
  exact provisionFresh .vestigial vestigialFiber .slot vestigial_present
    (by simp [claimingDecl])
    (by simp [vestigialFiber, exampleCatalog, claimingDecl])

theorem claimingState_wellFormed :
    WellFormed (insertFiber withoutVestigial .fresh none .claiming) :=
  claimingInsert.preservesWellFormed withoutVestigial_wellFormed

/-- After removing the vestigial child, its parent becomes removable. -/
def removeParentAfterChild : OrchestrationStep withoutVestigial
    (removeFiber withoutVestigial .parent) :=
  .remove withoutVestigial .parent parentFiber without_parent_present rfl
    (by simp [Fiber.Installed, parentFiber, Phase.Installed]) (by
      intro child childFiber lookup
      cases child with
      | parent =>
          rw [without_parent_present] at lookup
          have equal := Option.some.inj lookup
          subst childFiber
          simp [parentFiber]
      | vestigial =>
          rw [without_vestigial_absent] at lookup
          cases lookup
      | fresh =>
          change (removeFiber state .vestigial).registry .fresh = some childFiber at lookup
          rw [removeFiber_lookup_other state .vestigial .fresh (by decide), fresh_absent] at lookup
          cases lookup)

theorem removesVestigialParent :
    RemovesVestigialParent vestigial removeParentAfterChild := rfl

/-- Restoring the vestigial child blocks the same O-Remove of its parent. -/
theorem parent_not_childless_before :
    ¬(∀ child childFiber, state.registry child = some childFiber →
      childFiber.parent ≠ some .parent) := by
  intro childless
  exact childless .vestigial vestigialFiber vestigial_present rfl

theorem withoutParent_wellFormed :
    WellFormed (removeFiber withoutVestigial .parent) :=
  removeParentAfterChild.preservesWellFormed withoutVestigial_wellFormed

end Counterexample

end Cordis.GlobalVestigial
