import Cordis.GlobalProgress

/-!
# Corrected global support

This module implements the counterexample-first support layer specified in
`docs/GLOBAL_SUPPORT_SPEC.md`, against CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

A finite `FromEmpty` execution proves that well-founded provider precedence and birth-ranked
parent acyclicity do not make their union well founded. The same state gives two distinct
solutions of the printed Definition 67 equations. Positive support therefore consumes an explicit
`SupportOrder` for the combined relation and defines the unique solution by well-founded recursion.

At quiescence, active names form that solution only under state-local provision totality, failure
exclusion, and explicit active-parent closure. A second finite model proves the parent premise
independent even when the combined support order is well founded.

This module does not derive combined well-foundedness or parent provenance from `FromEmpty`, lift
state-local totality to components or episodes, or prove deletion, confluence, progress, or
termination.
-/

set_option autoImplicit false

namespace Cordis.GlobalSupport

open Cordis.GlobalRegistry Cordis.GlobalProgress

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Static support equations and explicit recursion authority -/

/-- A direct parent pointer, oriented from the parent prerequisite to its child. -/
def ParentEdge
    (state : State catalog Ambient) (parent child : sig.Name) : Prop :=
  ∃ childFiber,
    state.registry child = some childFiber ∧ childFiber.parent = some parent

/-- The union of provider precedence and parent prerequisites, with one common orientation. -/
def SupportEdge
    (state : State catalog Ambient) (lower upper : sig.Name) : Prop :=
  PrecedesAt state lower upper ∨ ParentEdge state lower upper

/-- The root-parent clause, interpreted against a candidate support predicate. -/
def ParentSupported (candidate : sig.Name → Prop) (fiber : Fiber catalog) : Prop :=
  match fiber.parent with
  | none => True
  | some parent => candidate parent

/-- Every declared dependency has a present candidate-supported possible provider. -/
def DependenciesSupported
    (state : State catalog Ambient) (candidate : sig.Name → Prop)
    (fiber : Fiber catalog) : Prop :=
  ∀ key, key ∈ (catalog.declaration fiber.component).dependencies.keys →
    ∃ provider providerFiber,
      state.registry provider = some providerFiber ∧
        candidate provider ∧
        key ∈ (catalog.declaration providerFiber.component).provision

/-- One unfolding of paper Definition 67 at a single registry name. -/
def SupportClause
    (state : State catalog Ambient) (candidate : sig.Name → Prop)
    (name : sig.Name) : Prop :=
  ∃ fiber,
    state.registry name = some fiber ∧
      fiber.retired = false ∧
      ParentSupported candidate fiber ∧
      DependenciesSupported state candidate fiber

/-- A predicate solves the support equations exactly at every name. -/
def SupportSolution
    (state : State catalog Ambient) (candidate : sig.Name → Prop) : Prop :=
  ∀ name, candidate name ↔ SupportClause state candidate name

/-- Explicit registry-domain predicate, used instead of a carrier-wide literal `True`. -/
def PresentNames (state : State catalog Ambient) (name : sig.Name) : Prop :=
  ∃ fiber, state.registry name = some fiber

/-- Existence and extensional uniqueness of a solution to the support equations. -/
def HasUniqueSupport (state : State catalog Ambient) : Prop :=
  ∃ candidate : sig.Name → Prop,
    SupportSolution state candidate ∧
      ∀ other, SupportSolution state other → other = candidate

/-! ## Reachable mixed parent/provider cycle -/

namespace MixedCycle

inductive Component where
  | consumer
  | provider
deriving DecidableEq

abbrev Signature : StaticSignature where
  Name := Bool
  Key := Unit
  ComponentId := Component
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Unit
  Value _ := Unit
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def consumerDecl : ComponentDecl Signature where
  dependencies := { keys := [()], nodup := by simp }
  provision := []
  provision_nodup := by simp
  entry := ()

def providerDecl : ComponentDecl Signature where
  dependencies := { keys := [], nodup := by simp }
  provision := [()]
  provision_nodup := by simp
  entry := ()

abbrev mixedCatalog : Catalog Signature where
  declaration
    | .consumer => consumerDecl
    | .provider => providerDecl

abbrev ExampleState := GlobalState mixedCatalog Unit

def stateSetoid : Setoid ExampleState where
  r := Eq
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }

def dynamics : GlobalDynamics.Dynamics Signature mixedCatalog Unit where
  equivalence := stateSetoid
  runIterator _ _ _ := .error ()
  applyExternalUndo _ state := state
  ordinary_recovers := by intros; contradiction
  externalUndo_respects := by
    intro undo left right related
    exact related
  ordinary_confined := by intros; contradiction
  ordinary_preserves_wellFormed := by intros; contradiction
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact .errors rfl
  ReadEquivalent _ _ _ := True
  read_refl := by intros; trivial
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact .errors rfl
  retire_respects := by
    intro name left right related
    subst right
    rfl

def inertia : GlobalLifecycle.InertiaPolicy dynamics where
  canAbort _ _ _ := False

def initial : ExampleState where
  ambient := ()
  nextBirth := 0
  registry := Cordis.Coeffect.empty

theorem initial_empty : GlobalCalculus.EmptyRegistry initial := by
  intro name
  rfl

theorem initial_wellFormed : WellFormed initial := by
  constructor <;> intros <;> simp [initial, Cordis.Coeffect.empty] at *

def withConsumer : ExampleState := insertFiber initial false none .consumer

def insertConsumer : OrchestrationStep initial withConsumer :=
  .insert initial false (by constructor; rfl) none (by simp) .consumer (by
    intro existing existingFiber key lookup
    simp [initial, Cordis.Coeffect.empty] at lookup)

def final : ExampleState := insertFiber withConsumer true (some false) .provider

def insertProvider : OrchestrationStep withConsumer final :=
  .insert withConsumer true (by constructor; rfl) (some false) (by
    intro parent parentEq
    have parent_eq : parent = false := Option.some.inj parentEq.symm
    subst parent
    exact ⟨_, rfl⟩) .provider (by
      intro existing existingFiber key lookup newProvision existingProvision
      cases existing
      · simp [withConsumer, initial, insertFiber] at lookup
        subst existingFiber
        simp [consumerDecl] at existingProvision
      · simp [withConsumer, initial, insertFiber] at lookup)

def trace : GlobalCalculus.Trace dynamics inertia initial final :=
  .cons (.orchestration insertConsumer)
    (.cons (.orchestration insertProvider) (.nil final))

def fromEmpty : GlobalCalculus.FromEmpty dynamics inertia final where
  initial := initial
  empty := initial_empty
  initial_wellFormed := initial_wellFormed
  trace := trace

theorem final_wellFormed : WellFormed final := fromEmpty.final_wellFormed

theorem precedence_iff (provider consumer : Bool) :
    PrecedesAt final provider consumer ↔ provider = true ∧ consumer = false := by
  cases provider <;> cases consumer <;>
    simp [PrecedesAt, final, withConsumer, initial, insertFiber, consumerDecl, providerDecl]

theorem precedence_wellFounded : WellFounded (PrecedesAt final) := by
  refine Subrelation.wf ?_
    (InvImage.wf (fun name : Bool ↦ if name then 0 else 1) Nat.lt_wfRel.wf)
  intro provider consumer precedes
  obtain ⟨rfl, rfl⟩ := (precedence_iff provider consumer).1 precedes
  change 0 < 1
  decide

theorem parent_edge : ParentEdge final false true := by
  refine ⟨_, rfl, rfl⟩

theorem provider_edge : PrecedesAt final true false :=
  (precedence_iff true false).2 ⟨rfl, rfl⟩

theorem support_cycle : Relation.TransGen (SupportEdge final) false false :=
  .tail (.single (.inr parent_edge)) (.inl provider_edge)

theorem acc_irrefl {Name : Type} {relation : Name → Name → Prop} {name : Name}
    (accessible : Acc relation name) : ¬relation name name := by
  intro self
  induction accessible with
  | intro current predecessors inductionHypothesis =>
      exact inductionHypothesis current self self

/-- Even well-founded precedence and birth-ranked parents have a cyclic union. -/
theorem supportEdge_not_wellFounded : ¬WellFounded (SupportEdge final) := by
  intro wellFounded
  exact acc_irrefl (wellFounded.transGen.apply false) support_cycle

theorem empty_support_solution : SupportSolution final (fun _ ↦ False) := by
  intro name
  cases name <;>
    simp [SupportClause, ParentSupported, DependenciesSupported, final, withConsumer, initial,
      insertFiber, consumerDecl, providerDecl]

theorem present_support_solution : SupportSolution final (PresentNames final) := by
  intro name
  cases name <;>
    simp [PresentNames, SupportClause, ParentSupported, DependenciesSupported, final,
      withConsumer, initial, insertFiber, consumerDecl, providerDecl]

theorem presentNames_eq_full : PresentNames final = fun _ ↦ True := by
  funext name
  cases name <;> simp [PresentNames, final, withConsumer, initial, insertFiber]

theorem support_solutions_differ : (fun _ : Bool ↦ False) ≠ PresentNames final := by
  intro equal
  have atFalse := congrFun equal false
  simp [PresentNames, final, withConsumer, initial, insertFiber] at atFalse

/-- The cyclic Definition 67 equations have distinct empty and present-name solutions. -/
theorem no_unique_support : ¬HasUniqueSupport final := by
  rintro ⟨candidate, solution, unique⟩
  have emptyEq := unique _ empty_support_solution
  have presentEq := unique _ present_support_solution
  exact support_solutions_differ (emptyEq.trans presentEq.symm)

def precedesFlag (provider consumer : Bool) : Bool := provider && !consumer

def parentFlag (parent child : Bool) : Bool := !parent && child

def cycleProjection : Bool × Bool × Bool :=
  (precedesFlag true false, parentFlag false true,
    parentFlag false true && precedesFlag true false)

theorem cycleProjection_eq : cycleProjection = (true, true, true) := rfl

theorem cycleProjection_sound :
    PrecedesAt final true false ∧ ParentEdge final false true ∧
      Relation.TransGen (SupportEdge final) false false :=
  ⟨provider_edge, parent_edge, support_cycle⟩

end MixedCycle

/-- Direct authority for recursion over the combined support relation. -/
structure SupportOrder (state : State catalog Ambient) : Prop where
  wellFounded : WellFounded (SupportEdge state)

private noncomputable def supportBody
    (state : State catalog Ambient) (name : sig.Name)
    (lower : ∀ candidate, SupportEdge state candidate name → Prop) : Prop :=
  letI := Classical.propDecidable
  SupportClause state
    (fun candidate ↦
      if edge : SupportEdge state candidate name then lower candidate edge else False)
    name

/-- The unique recursive support predicate selected by a combined well-founded order. -/
noncomputable def supported
    {state : State catalog Ambient} (order : SupportOrder state) : sig.Name → Prop :=
  order.wellFounded.fix (supportBody state)

private theorem supportClause_congr
    {state : State catalog Ambient} {left right : sig.Name → Prop} {name : sig.Name}
    (lower : ∀ candidate, SupportEdge state candidate name →
      (left candidate ↔ right candidate)) :
    SupportClause state left name ↔ SupportClause state right name := by
  constructor
  · rintro ⟨fiber, present, retired, parent, dependencies⟩
    refine ⟨fiber, present, retired, ?_, ?_⟩
    · cases parentEq : fiber.parent with
      | none => simp [ParentSupported, parentEq]
      | some parentName =>
          have leftParent : left parentName := by
            simpa [ParentSupported, parentEq] using parent
          have rightParent :=
            (lower parentName (.inr ⟨fiber, present, parentEq⟩)).1 leftParent
          simpa [ParentSupported, parentEq] using rightParent
    · intro key required
      obtain ⟨provider, providerFiber, providerPresent, providerSupported, provision⟩ :=
        dependencies key required
      exact ⟨provider, providerFiber, providerPresent,
        (lower provider (.inl ⟨providerFiber, fiber, key, providerPresent, present,
          provision, required⟩)).1 providerSupported, provision⟩
  · rintro ⟨fiber, present, retired, parent, dependencies⟩
    refine ⟨fiber, present, retired, ?_, ?_⟩
    · cases parentEq : fiber.parent with
      | none => simp [ParentSupported, parentEq]
      | some parentName =>
          have rightParent : right parentName := by
            simpa [ParentSupported, parentEq] using parent
          have leftParent :=
            (lower parentName (.inr ⟨fiber, present, parentEq⟩)).2 rightParent
          simpa [ParentSupported, parentEq] using leftParent
    · intro key required
      obtain ⟨provider, providerFiber, providerPresent, providerSupported, provision⟩ :=
        dependencies key required
      exact ⟨provider, providerFiber, providerPresent,
        (lower provider (.inl ⟨providerFiber, fiber, key, providerPresent, present,
          provision, required⟩)).2 providerSupported, provision⟩

/-- The well-founded definition unfolds to the public Definition 67 clause. -/
theorem supported_iff
    {state : State catalog Ambient} (order : SupportOrder state) (name : sig.Name) :
    supported order name ↔ SupportClause state (supported order) name := by
  rw [supported, WellFounded.fix_eq]
  apply supportClause_congr
  intro candidate edge
  simp [edge]

/-- Recursive support is a solution of every displayed support equation. -/
theorem supported_solution
    {state : State catalog Ambient} (order : SupportOrder state) :
    SupportSolution state (supported order) :=
  supported_iff order

/-- Every solution agrees extensionally with well-founded recursive support. -/
theorem support_solution_unique
    {state : State catalog Ambient} (order : SupportOrder state)
    (candidate : sig.Name → Prop) (solution : SupportSolution state candidate) :
    candidate = supported order := by
  funext name
  apply propext
  induction name using order.wellFounded.induction with
  | h current inductionHypothesis =>
      calc
        candidate current ↔ SupportClause state candidate current := solution current
        _ ↔ SupportClause state (supported order) current :=
          supportClause_congr fun lower edge ↦ inductionHypothesis lower edge
        _ ↔ supported order current := (supported_iff order current).symm

/-- Combined well-foundedness supplies existence and uniqueness of support. -/
theorem hasUniqueSupport
    {state : State catalog Ambient} (order : SupportOrder state) :
    HasUniqueSupport state :=
  ⟨supported order, supported_solution order,
    fun candidate solution ↦ support_solution_unique order candidate solution⟩

/-! ## State-local provision totality and active-name observations -/

/-- Every active fiber has installed every key its component may provide. -/
def TotalOnProvisionAt (state : State catalog Ambient) : Prop :=
  ∀ name fiber,
    state.registry name = some fiber → fiber.Active →
      ∀ key, key ∈ (catalog.declaration fiber.component).provision →
        (fiber.table key).isSome = true

/-- At an active total fiber, table domain is exactly the declared provision. -/
theorem active_table_present_iff_provision
    {state : State catalog Ambient} (total : TotalOnProvisionAt state)
    {name : sig.Name} {fiber : Fiber catalog}
    (present : state.registry name = some fiber) (active : fiber.Active) (key : sig.Key) :
    (fiber.table key).isSome = true ↔
      key ∈ (catalog.declaration fiber.component).provision := by
  exact ⟨fiber.table_within_provision key, total name fiber present active key⟩

/-- No registered fiber carries a failed inactive error outcome. -/
def NoFailedFiber (state : State catalog Ambient) : Prop :=
  ∀ name fiber error,
    state.registry name = some fiber → fiber.phase ≠ .inactive (some error)

/-- A registry name whose current fiber is in the Active lifecycle phase. -/
def ActiveNames (state : State catalog Ambient) (name : sig.Name) : Prop :=
  ∃ fiber, state.registry name = some fiber ∧ fiber.Active

/-- Every active name is in the exact registry domain. -/
theorem activeNames_present
    {state : State catalog Ambient} {name : sig.Name}
    (active : ActiveNames state name) : PresentNames state name := by
  obtain ⟨fiber, present, fiberActive⟩ := active
  exact ⟨fiber, present⟩

/-- Failure exclusion forces every inactive outcome to be successful. -/
theorem inactive_outcome_eq_none
    {state : State catalog Ambient} (noFailed : NoFailedFiber state)
    {name : sig.Name} {fiber : Fiber catalog} {outcome : Option sig.Error}
    (present : state.registry name = some fiber)
    (phase : fiber.phase = .inactive outcome) : outcome = none := by
  cases outcome with
  | none => rfl
  | some error => exact False.elim ((noFailed name fiber error present) phase)

/-- Every active non-root child has an active parent. -/
def ActiveParentClosed (state : State catalog Ambient) : Prop :=
  ∀ child childFiber parent,
    state.registry child = some childFiber →
    childFiber.parent = some parent → childFiber.Active →
      ∃ parentFiber, state.registry parent = some parentFiber ∧ parentFiber.Active

private theorem positive_target_of_support_clause
    {state : State catalog Ambient} (wf : WellFormed state)
    (total : TotalOnProvisionAt state) {name : sig.Name} {fiber : Fiber catalog}
    (present : state.registry name = some fiber) (retired : fiber.retired = false)
    (dependencies : DependenciesSupported state (ActiveNames state) fiber) :
    ∃ committed, targetView state name fiber = some committed := by
  classical
  have providerExists : ∀ declared : DeclaredKey (catalog.declaration fiber.component),
      ∃ provider, ActiveProvider state declared.key provider := by
    intro declared
    obtain ⟨provider, providerFiber, providerPresent, providerActive, provision⟩ :=
      dependencies declared.key declared.declared
    obtain ⟨activeFiber, activePresent, active⟩ := providerActive
    rw [providerPresent] at activePresent
    have fiberEq : providerFiber = activeFiber := Option.some.inj activePresent
    subst activeFiber
    have tablePresent := total provider providerFiber providerPresent active declared.key provision
    exact ⟨provider, providerFiber, providerPresent, active, tablePresent⟩
  let committed : CommittedView (catalog.declaration fiber.component) := {
    provider := fun declared ↦ Classical.choose (providerExists declared)
  }
  refine ⟨committed, targetView_eq_of_isTarget wf ?_⟩
  exact {
    present := present
    not_retired := retired
    resolves_active := fun declared ↦ Classical.choose_spec (providerExists declared)
  }

/-- Under the explicit local laws, active names solve the support equations. -/
theorem activeNames_solution
    {state : State catalog Ambient} (wf : WellFormed state) (quiet : Quiescent state)
    (noFailed : NoFailedFiber state) (total : TotalOnProvisionAt state)
    (parents : ActiveParentClosed state) : SupportSolution state (ActiveNames state) := by
  intro name
  constructor
  · rintro ⟨fiber, present, active⟩
    cases phaseEq : fiber.phase with
    | inactive outcome => simp [Fiber.Active, Phase.Active, phaseEq] at active
    | reloading code undos committed => simp [Fiber.Active, Phase.Active, phaseEq] at active
    | unloading undos committed outcome => simp [Fiber.Active, Phase.Active, phaseEq] at active
    | active undos committed =>
        have quietAt := quiet name fiber present
        have target : targetView state name fiber = some committed := by
          simpa [phaseEq] using quietAt
        let targetWitness := targetView_sound wf target
        refine ⟨fiber, present, targetWitness.not_retired, ?_, ?_⟩
        · cases parentEq : fiber.parent with
          | none => simp [ParentSupported, parentEq]
          | some parent =>
              simpa [ParentSupported, parentEq, ActiveNames] using
                parents name fiber parent present parentEq active
        · intro key required
          let declared : DeclaredKey (catalog.declaration fiber.component) := ⟨key, required⟩
          obtain ⟨providerFiber, providerPresent, providerActive, tablePresent⟩ :=
            targetWitness.resolves_active declared
          exact ⟨committed.provider declared, providerFiber, providerPresent,
            ⟨providerFiber, providerPresent, providerActive⟩,
            providerFiber.table_within_provision key tablePresent⟩
  · rintro ⟨fiber, present, retired, parent, dependencies⟩
    obtain ⟨committed, target⟩ :=
      positive_target_of_support_clause wf total present retired dependencies
    cases phaseEq : fiber.phase with
    | inactive outcome =>
        cases outcome with
        | none =>
            have quietAt := quiet name fiber present
            have targetNone : targetView state name fiber = none := by
              simpa [phaseEq] using quietAt
            rw [target] at targetNone
            cases targetNone
        | some error => exact False.elim ((noFailed name fiber error present) phaseEq)
    | reloading code undos sourceCommitted =>
        have quietAt := quiet name fiber present
        simp [phaseEq] at quietAt
    | active undos sourceCommitted =>
        exact ⟨fiber, present, by simp [Fiber.Active, phaseEq, Phase.Active]⟩
    | unloading undos sourceCommitted outcome =>
        have quietAt := quiet name fiber present
        simp [phaseEq] at quietAt

/-- Corrected local Lemma 70: unique recursive support is exactly activity. -/
theorem support_eq_active
    {state : State catalog Ambient} (order : SupportOrder state)
    (wf : WellFormed state) (quiet : Quiescent state)
    (noFailed : NoFailedFiber state) (total : TotalOnProvisionAt state)
    (parents : ActiveParentClosed state) : supported order = ActiveNames state := by
  exact (support_solution_unique order _
    (activeNames_solution wf quiet noFailed total parents)).symm

/-! ## Printed-hypothesis active mixed cycle -/

namespace MixedCycle

def consumerView : CommittedView consumerDecl where
  provider _ := true

def providerView : CommittedView providerDecl where
  provider declared := False.elim (by simpa [providerDecl] using declared.declared)

def providerTable : Cordis.Coeffect.Context Unit (fun _ ↦ Unit) :=
  Cordis.Coeffect.setAt Cordis.Coeffect.empty () ()

def activeConsumerFiber : Fiber mixedCatalog where
  component := .consumer
  parent := none
  birth := 0
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .active [] consumerView

def activeProviderFiber : Fiber mixedCatalog where
  component := .provider
  parent := some false
  birth := 1
  table := providerTable
  table_within_provision := by simp [providerTable, providerDecl]
  retired := false
  phase := .active [] providerView

def activeState : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Cordis.Coeffect.setAt
    (Cordis.Coeffect.setAt Cordis.Coeffect.empty false activeConsumerFiber)
      true activeProviderFiber

@[simp] theorem active_consumer_present :
    activeState.registry false = some activeConsumerFiber := by simp [activeState]

@[simp] theorem active_provider_present :
    activeState.registry true = some activeProviderFiber := by simp [activeState]

theorem activeState_wellFormed : WellFormed activeState := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [activeState] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [activeState] at lookup <;> subst fiber
    · simp [activeConsumerFiber] at parentEq
    · simp [activeProviderFiber] at parentEq
      subst parent
      exact ⟨activeConsumerFiber, active_consumer_present⟩
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [activeState] at lookup <;> subst fiber
    · simp [activeConsumerFiber] at parentEq
    · simp [activeProviderFiber] at parentEq
      subst parent
      rw [active_consumer_present] at parentLookup
      have parent_eq : activeConsumerFiber = parentFiber := Option.some.inj parentLookup
      subst parentFiber
      decide
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases left <;> cases right <;>
      simp [activeState] at leftLookup rightLookup <;>
      subst leftFiber <;> subst rightFiber
    · rfl
    · change key ∈ consumerDecl.provision at leftKey
      simp [consumerDecl] at leftKey
    · change key ∈ consumerDecl.provision at rightKey
      simp [consumerDecl] at rightKey
    · rfl
  · intro name fiber lookup committed committedEq declared
    cases name <;> simp [activeState] at lookup <;> subst fiber
    · have viewEq : consumerView = committed := by
        simpa [activeConsumerFiber, Phase.committed?] using Option.some.inj committedEq
      subst committed
      exact ⟨activeProviderFiber, active_provider_present⟩
    · rcases declared with ⟨key, required⟩
      change key ∈ providerDecl.dependencies.keys at required
      simp [providerDecl] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    cases name <;> simp [activeState] at lookup <;> subst fiber
    · have viewEq : consumerView = committed := by
        simpa [activeConsumerFiber, Phase.committed?] using Option.some.inj committedEq
      subst committed
      rcases declared with ⟨key, required⟩
      have normalized : activeState.registry true = some providerFiber := by
        simpa [consumerView] using providerLookup
      rw [active_provider_present] at normalized
      have providerEq : activeProviderFiber = providerFiber := Option.some.inj normalized
      subst providerFiber
      simp [Fiber.Installed, activeProviderFiber, Phase.Installed]
    · rcases declared with ⟨key, required⟩
      change key ∈ providerDecl.dependencies.keys at required
      simp [providerDecl] at required

theorem active_consumer_target :
    targetView activeState false activeConsumerFiber = some consumerView := by
  apply targetView_eq_of_isTarget activeState_wellFormed
  exact {
    present := active_consumer_present
    not_retired := rfl
    resolves_active := by
      intro declared
      exact ⟨activeProviderFiber, active_provider_present, trivial, by
        simp [activeProviderFiber, providerTable]⟩
  }

theorem active_provider_target :
    targetView activeState true activeProviderFiber = some providerView := by
  apply targetView_eq_of_isTarget activeState_wellFormed
  exact {
    present := active_provider_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      change key ∈ providerDecl.dependencies.keys at required
      simp [providerDecl] at required
  }

theorem activeState_quiescent : Quiescent activeState := by
  intro name fiber lookup
  cases name <;> simp [activeState] at lookup <;> subst fiber
  · simpa [activeConsumerFiber] using active_consumer_target
  · simpa [activeProviderFiber] using active_provider_target

theorem activeState_noFailed : NoFailedFiber activeState := by
  intro name fiber error lookup
  cases name <;> simp [activeState] at lookup <;> subst fiber
  · simp [activeConsumerFiber]
  · simp [activeProviderFiber]

theorem activeState_total : TotalOnProvisionAt activeState := by
  intro name fiber lookup active key provision
  cases name <;> simp [activeState] at lookup <;> subst fiber
  · simp [activeConsumerFiber, consumerDecl] at provision
  · simp [activeProviderFiber, providerTable]

theorem active_precedence_iff (provider consumer : Bool) :
    PrecedesAt activeState provider consumer ↔
      provider = true ∧ consumer = false := by
  cases provider <;> cases consumer <;>
    simp [PrecedesAt, activeState, activeConsumerFiber, activeProviderFiber, consumerDecl,
      providerDecl]

theorem active_precedence_wellFounded : WellFounded (PrecedesAt activeState) := by
  refine Subrelation.wf ?_
    (InvImage.wf (fun name : Bool ↦ if name then 0 else 1) Nat.lt_wfRel.wf)
  intro provider consumer precedes
  obtain ⟨rfl, rfl⟩ := (active_precedence_iff provider consumer).1 precedes
  change 0 < 1
  decide

theorem active_empty_support_solution :
    SupportSolution activeState (fun _ ↦ False) := by
  intro name
  cases name <;>
    simp [SupportClause, ParentSupported, DependenciesSupported, activeState,
      activeConsumerFiber, activeProviderFiber, consumerDecl, providerDecl]

theorem active_present_support_solution :
    SupportSolution activeState (PresentNames activeState) := by
  intro name
  cases name <;>
    simp [PresentNames, SupportClause, ParentSupported, DependenciesSupported, activeState,
      activeConsumerFiber, activeProviderFiber, consumerDecl, providerDecl]

theorem activeNames_eq_present : ActiveNames activeState = PresentNames activeState := by
  funext name
  cases name <;>
    simp [ActiveNames, PresentNames, activeState, activeConsumerFiber, activeProviderFiber,
      Fiber.Active, Phase.Active]

theorem active_parent_closed : ActiveParentClosed activeState := by
  intro child childWitness parent childPresent parentEq active
  cases child <;> simp [activeState] at childPresent <;> subst childWitness
  · simp [activeConsumerFiber] at parentEq
  · simp [activeProviderFiber] at parentEq
    subst parent
    exact ⟨activeConsumerFiber, active_consumer_present, by trivial⟩

theorem activeState_no_unique_support : ¬HasUniqueSupport activeState := by
  rintro ⟨candidate, solution, unique⟩
  have emptyEq := unique _ active_empty_support_solution
  have presentEq := unique _ active_present_support_solution
  have differ : (fun _ : Bool ↦ False) ≠ PresentNames activeState := by
    intro equal
    have atFalse := congrFun equal false
    simp [PresentNames, activeState] at atFalse
  exact differ (emptyEq.trans presentEq.symm)

theorem printed_hypotheses_hold :
    WellFormed activeState ∧ WellFounded (PrecedesAt activeState) ∧
      Quiescent activeState ∧ NoFailedFiber activeState ∧
      TotalOnProvisionAt activeState ∧ ActiveParentClosed activeState :=
  ⟨activeState_wellFormed, active_precedence_wellFounded, activeState_quiescent,
    activeState_noFailed, activeState_total, active_parent_closed⟩

end MixedCycle

/-! ## Active-parent closure is independent -/

namespace ActiveParentGap

abbrev Signature : StaticSignature where
  Name := Bool
  Key := Unit
  ComponentId := Unit
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Unit
  Value _ := Unit
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def declaration : ComponentDecl Signature where
  dependencies := { keys := [], nodup := by simp }
  provision := []
  provision_nodup := by simp
  entry := ()

abbrev gapCatalog : Catalog Signature where
  declaration _ := declaration

abbrev ExampleState := GlobalState gapCatalog Unit

def view : CommittedView declaration where
  provider declared := False.elim (by simpa [declaration] using declared.declared)

def parentFiber : Fiber gapCatalog where
  component := ()
  parent := none
  birth := 0
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := true
  phase := .inactive none

def childFiber : Fiber gapCatalog where
  component := ()
  parent := some false
  birth := 1
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .active [] view

def state : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Cordis.Coeffect.setAt
    (Cordis.Coeffect.setAt Cordis.Coeffect.empty false parentFiber) true childFiber

@[simp] theorem parent_present : state.registry false = some parentFiber := by simp [state]

@[simp] theorem child_present : state.registry true = some childFiber := by simp [state]

theorem wellFormed : WellFormed state := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [state] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [state] at lookup <;> subst fiber
    · simp [parentFiber] at parentEq
    · simp [childFiber] at parentEq
      subst parent
      exact ⟨parentFiber, parent_present⟩
  · intro name fiber parent parentWitness lookup parentEq parentLookup
    cases name <;> simp [state] at lookup <;> subst fiber
    · simp [parentFiber] at parentEq
    · simp [childFiber] at parentEq
      subst parent
      rw [parent_present] at parentLookup
      have witnessEq : parentFiber = parentWitness := Option.some.inj parentLookup
      subst parentWitness
      decide
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases left <;> cases right <;>
      simp [state] at leftLookup rightLookup <;>
      subst leftFiber <;> subst rightFiber <;>
      simp [declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    cases name <;> simp [state] at lookup <;> subst fiber
    · simp [parentFiber, Phase.committed?] at committedEq
    · rcases declared with ⟨key, required⟩
      change key ∈ declaration.dependencies.keys at required
      simp [declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    cases name <;> simp [state] at lookup <;> subst fiber
    · simp [parentFiber, Phase.committed?] at committedEq
    · rcases declared with ⟨key, required⟩
      change key ∈ declaration.dependencies.keys at required
      simp [declaration] at required

theorem child_target : targetView state true childFiber = some view := by
  apply targetView_eq_of_isTarget wellFormed
  exact {
    present := child_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      change key ∈ declaration.dependencies.keys at required
      simp [declaration] at required
  }

theorem quiescent : Quiescent state := by
  intro name fiber lookup
  cases name <;> simp [state] at lookup <;> subst fiber
  · simp [parentFiber, targetView_none_of_retired]
  · simpa [childFiber] using child_target

theorem noFailed : NoFailedFiber state := by
  intro name fiber error lookup
  cases name <;> simp [state] at lookup <;> subst fiber
  · simp [parentFiber]
  · simp [childFiber]

theorem total : TotalOnProvisionAt state := by
  intro name fiber lookup active key provision
  cases name <;> simp [state] at lookup <;> subst fiber <;>
    simp [declaration] at provision

theorem supportEdge_iff (lower upper : Bool) :
    SupportEdge state lower upper ↔ lower = false ∧ upper = true := by
  cases lower <;> cases upper <;>
    simp [SupportEdge, ParentEdge, PrecedesAt, state, parentFiber, childFiber, declaration]

theorem order : SupportOrder state where
  wellFounded := by
    refine Subrelation.wf ?_
      (InvImage.wf (fun name : Bool ↦ if name then 1 else 0) Nat.lt_wfRel.wf)
    intro lower upper edge
    obtain ⟨rfl, rfl⟩ := (supportEdge_iff lower upper).1 edge
    change 0 < 1
    decide

theorem not_parent_closed : ¬ActiveParentClosed state := by
  intro closed
  obtain ⟨found, foundPresent, foundActive⟩ :=
    closed true childFiber false child_present rfl (by trivial)
  rw [parent_present] at foundPresent
  have foundEq : parentFiber = found := Option.some.inj foundPresent
  subst found
  simp [parentFiber, Fiber.Active, Phase.Active] at foundActive

theorem parent_not_supported : ¬supported order false := by
  intro supportedParent
  obtain ⟨fiber, present, retired, parent, dependencies⟩ :=
    (supported_iff order false).1 supportedParent
  rw [parent_present] at present
  have fiberEq : parentFiber = fiber := Option.some.inj present
  subst fiber
  simp [parentFiber] at retired

theorem child_not_supported : ¬supported order true := by
  intro supportedChild
  obtain ⟨fiber, present, retired, parent, dependencies⟩ :=
    (supported_iff order true).1 supportedChild
  rw [child_present] at present
  have fiberEq : childFiber = fiber := Option.some.inj present
  subst fiber
  exact parent_not_supported (by simpa [ParentSupported, childFiber] using parent)

theorem active_child : ActiveNames state true :=
  ⟨childFiber, child_present, by trivial⟩

/-- With an inactive parent, well-founded recursive support omits the active child. -/
theorem support_ne_active : supported order ≠ ActiveNames state := by
  intro equal
  apply child_not_supported
  rw [equal]
  exact active_child

theorem activeNames_not_solution : ¬SupportSolution state (ActiveNames state) := by
  intro solution
  have clause := (solution true).1 active_child
  obtain ⟨fiber, present, retired, parent, dependencies⟩ := clause
  rw [child_present] at present
  have fiberEq : childFiber = fiber := Option.some.inj present
  subst fiber
  obtain ⟨parentWitness, parentPresent, parentActive⟩ : ActiveNames state false := by
    simpa [ParentSupported, childFiber] using parent
  rw [parent_present] at parentPresent
  have parentEq : parentFiber = parentWitness := Option.some.inj parentPresent
  subst parentWitness
  simp [parentFiber, Fiber.Active, Phase.Active] at parentActive

end ActiveParentGap

/-! ## Positive acyclic root-only example -/

namespace PositiveRoot

open ActiveParentGap

def rootFiber : Fiber gapCatalog where
  component := ()
  parent := none
  birth := 0
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .active [] view

def state : ExampleState where
  ambient := ()
  nextBirth := 1
  registry := Cordis.Coeffect.setAt Cordis.Coeffect.empty false rootFiber

@[simp] theorem root_present : state.registry false = some rootFiber := by simp [state]

theorem true_absent : state.registry true = none := by simp [state]

theorem wellFormed : WellFormed state := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [state] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [state] at lookup <;> subst fiber <;> simp [rootFiber] at parentEq
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [state] at lookup <;> subst fiber <;> simp [rootFiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases left <;> cases right <;> simp [state] at leftLookup rightLookup <;>
      subst leftFiber <;> subst rightFiber <;> simp [declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    cases name <;> simp [state] at lookup <;> subst fiber
    · rcases declared with ⟨key, required⟩
      change key ∈ declaration.dependencies.keys at required
      simp [declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    cases name <;> simp [state] at lookup <;> subst fiber
    · rcases declared with ⟨key, required⟩
      change key ∈ declaration.dependencies.keys at required
      simp [declaration] at required

theorem root_target : targetView state false rootFiber = some view := by
  apply targetView_eq_of_isTarget wellFormed
  exact {
    present := root_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      change key ∈ declaration.dependencies.keys at required
      simp [declaration] at required
  }

theorem quiescent : Quiescent state := by
  intro name fiber lookup
  cases name <;> simp [state] at lookup <;> subst fiber
  simpa [rootFiber] using root_target

theorem noFailed : NoFailedFiber state := by
  intro name fiber error lookup
  cases name <;> simp [state] at lookup <;> subst fiber
  simp [rootFiber]

theorem total : TotalOnProvisionAt state := by
  intro name fiber lookup active key provision
  cases name <;> simp [state] at lookup <;> subst fiber
  simp [declaration] at provision

theorem parentClosed : ActiveParentClosed state := by
  intro child childFiber parent childPresent parentEq active
  cases child <;> simp [state] at childPresent <;> subst childFiber
  simp [rootFiber] at parentEq

theorem no_support_edge (lower upper : Bool) : ¬SupportEdge state lower upper := by
  cases lower <;> cases upper <;>
    simp [SupportEdge, ParentEdge, PrecedesAt, state, rootFiber, declaration]

theorem order : SupportOrder state where
  wellFounded := by
    apply WellFounded.intro
    intro upper
    apply Acc.intro
    intro lower edge
    exact False.elim (no_support_edge lower upper edge)

/-- The corrected theorem applies to an explicit empty support order. -/
theorem support_eq_active_positive : supported order = ActiveNames state :=
  support_eq_active order wellFormed quiescent noFailed total parentClosed

end PositiveRoot

end Cordis.GlobalSupport
