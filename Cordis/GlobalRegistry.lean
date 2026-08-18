import Cordis.Coeffect
import Std

/-!
# Birth-ranked global fiber registry

This module is the first global slice after the local effect/coeffect development. It models the
data portions of paper Definitions 43--46 and 49 plus the three orchestration rules. It does not
interpret Definition 47 registration callbacks, Definition 51 iterators, or the lifecycle rules of
Definitions 50--53.

A literal global state containing fibers that contain functions on that same global state would
repeat Definition 32's negative recursive occurrence. `StaticSignature` therefore contains only
types and codes. Fibers store component, iterator, and undo codes; a later, separate dynamics
record may interpret them after `GlobalState` has been defined.

Fresh insertion consumes an explicit absence witness. `FreshSupply` is an optional executable
allocator interface and is not an assumption of the relational preservation theorems. Parent
birth ranks strengthen paper Definition 58(1): parent presence alone does not imply the acyclic
tree required by Definition 45. The strengthening is named in `WellFormed.parent_older`.

The component declaration gives a finite dependency list, finite provision list, and entry code.
`Fiber.table_within_provision` intrinsically exposes Definition 43's write-confinement obligation
at every retained state. `WritesWithinProvision` is the transition-level surface that a later
dynamics interpreter must establish; read confinement remains out of scope until that interpreter
and the paper's global state equivalence are represented.
-/

set_option autoImplicit false

namespace Cordis.GlobalRegistry

universe u

/-- Static universes and opaque execution codes; no field mentions `GlobalState`. -/
structure StaticSignature where
  Name : Type u
  Key : Type u
  ComponentId : Type u
  Error : Type u
  IteratorCode : Type u
  ExternalUndoCode : Type u
  Value : Key → Type u
  nameDecEq : DecidableEq Name
  keyDecEq : DecidableEq Key
  componentDecEq : DecidableEq ComponentId

attribute [instance] StaticSignature.nameDecEq StaticSignature.keyDecEq
  StaticSignature.componentDecEq

/-- Definition 43's static declaration, with execution represented by an opaque entry code. -/
structure ComponentDecl (sig : StaticSignature) where
  dependencies : Coeffect.Spec sig.Key
  provision : List sig.Key
  provision_nodup : provision.Nodup
  entry : sig.IteratorCode

/-- External component catalog. `GlobalState` stores catalog identities, not effect functions. -/
structure Catalog (sig : StaticSignature) where
  declaration : sig.ComponentId → ComponentDecl sig

/-- A table transition writes no key outside the component's declared provision. -/
def WritesWithinProvision {sig : StaticSignature} (decl : ComponentDecl sig)
    (before after : Coeffect.Context sig.Key sig.Value) : Prop :=
  ∀ key, key ∉ decl.provision → after key = before key

/-- A dependency key paired with proof that the component declared it. -/
structure DeclaredKey {sig : StaticSignature} (decl : ComponentDecl sig) where
  key : sig.Key
  declared : key ∈ decl.dependencies.keys

/-- Definition 44's committed provider-valued view, total exactly on declared dependencies. -/
structure CommittedView {sig : StaticSignature} (decl : ComponentDecl sig) where
  provider : DeclaredKey decl → sig.Name

namespace CommittedView

@[ext]
theorem ext {sig : StaticSignature} {decl : ComponentDecl sig}
    {left right : CommittedView decl}
    (provider_eq : ∀ declared, left.provider declared = right.provider declared) :
    left = right := by
  cases left
  cases right
  simp only [mk.injEq]
  funext declared
  exact provider_eq declared

end CommittedView

/-- Stored undo codes distinguish external inverses from Definition 47 child retirement. -/
inductive UndoCode (sig : StaticSignature) where
  | external (code : sig.ExternalUndoCode)
  | retire (name : sig.Name)

/-- Definition 49's lifecycle data, represented entirely by static codes. -/
inductive Phase {sig : StaticSignature} (decl : ComponentDecl sig) where
  | inactive (outcome : Option sig.Error)
  | reloading (iterator : sig.IteratorCode) (undo : List (UndoCode sig))
      (committed : CommittedView decl)
  | active (undo : List (UndoCode sig)) (committed : CommittedView decl)
  | unloading (undo : List (UndoCode sig)) (committed : CommittedView decl)
      (outcome : Option sig.Error)

namespace Phase

/-- Installed phases are exactly the three phases carrying an accumulator and committed view. -/
def Installed {sig : StaticSignature} {decl : ComponentDecl sig} : Phase decl → Prop
  | .inactive _ => False
  | .reloading _ _ _ => True
  | .active _ _ => True
  | .unloading _ _ _ => True

/-- Only active fibers contribute their table to Definition 45's derived context. -/
def Active {sig : StaticSignature} {decl : ComponentDecl sig} : Phase decl → Prop
  | .active _ _ => True
  | _ => False

/-- Extract the committed view exactly from installed phases. -/
def committed? {sig : StaticSignature} {decl : ComponentDecl sig} :
    Phase decl → Option (CommittedView decl)
  | .inactive _ => none
  | .reloading _ _ committed => some committed
  | .active _ committed => some committed
  | .unloading _ committed _ => some committed

@[simp] theorem installed_iff_committed_isSome
    {sig : StaticSignature} {decl : ComponentDecl sig} (phase : Phase decl) :
    phase.Installed ↔ phase.committed?.isSome = true := by
  cases phase <;> simp [Installed, committed?]

theorem installed_of_committed_some
    {sig : StaticSignature} {decl : ComponentDecl sig}
    {phase : Phase decl} {committed : CommittedView decl}
    (committed_eq : phase.committed? = some committed) : phase.Installed := by
  cases phase <;> simp [committed?, Installed] at committed_eq ⊢

theorem committed_none_of_not_installed
    {sig : StaticSignature} {decl : ComponentDecl sig}
    {phase : Phase decl} (notInstalled : ¬phase.Installed) : phase.committed? = none := by
  cases phase <;> simp [committed?, Installed] at notInstalled ⊢

end Phase

/-- Definition 44 fiber data, indexed by the external catalog it references. -/
structure Fiber {sig : StaticSignature} (catalog : Catalog sig) where
  component : sig.ComponentId
  parent : Option sig.Name
  birth : Nat
  table : Coeffect.Context sig.Key sig.Value
  table_within_provision : ∀ key, (table key).isSome = true →
    key ∈ (catalog.declaration component).provision
  retired : Bool
  phase : Phase (catalog.declaration component)

namespace Fiber

def Installed {sig : StaticSignature} {catalog : Catalog sig}
    (fiber : Fiber catalog) : Prop :=
  fiber.phase.Installed

def Active {sig : StaticSignature} {catalog : Catalog sig}
    (fiber : Fiber catalog) : Prop :=
  fiber.phase.Active

end Fiber

/-- Definition 45's finite registry, reusing the dependent finite context. -/
abbrev Registry {sig : StaticSignature} (catalog : Catalog sig) :=
  Coeffect.Context sig.Name (fun _ ↦ Fiber catalog)

/-- Global state carries ambient data, a proof-only birth clock, and the finite registry. -/
structure GlobalState {sig : StaticSignature} (catalog : Catalog sig) (Ambient : Type u) where
  ambient : Ambient
  nextBirth : Nat
  registry : Registry catalog

/-- Optional executable allocator interface. Preservation itself only consumes `Absent` evidence. -/
class FreshSupply (Name : Type u) where
  fresh : (used : List Name) → { name // name ∉ used }

/-- A current fiber/name lookup witness. -/
structure PresentFiber {sig : StaticSignature} {catalog : Catalog sig}
    {Ambient : Type u} (state : GlobalState catalog Ambient) (name : sig.Name) where
  fiber : Fiber catalog
  lookup_eq : state.registry name = some fiber

/-- One active fiber actually supplies a present value at `key`. -/
def ActiveProvider {sig : StaticSignature} {catalog : Catalog sig}
    {Ambient : Type u} (state : GlobalState catalog Ambient)
    (key : sig.Key) (name : sig.Name) : Prop :=
  ∃ fiber, state.registry name = some fiber ∧ fiber.Active ∧
    (fiber.table key).isSome = true

/-- One retained active value in Definition 45's derived coeffect context. -/
def ActiveValue {sig : StaticSignature} {catalog : Catalog sig}
    {Ambient : Type u} (state : GlobalState catalog Ambient)
    (key : sig.Key) (value : sig.Value key) : Prop :=
  ∃ name fiber, state.registry name = some fiber ∧ fiber.Active ∧
    fiber.table key = some value

/-- A provider/name resolution claimed by one committed view. -/
def ResolvesTo {sig : StaticSignature} {catalog : Catalog sig}
    (consumer : Fiber catalog) (provider : sig.Name) : Prop :=
  ∃ committed : CommittedView (catalog.declaration consumer.component),
    consumer.phase.committed? = some committed ∧
    ∃ declared, committed.provider declared = provider

/-- Definition 50's global reliance predicate, derived from installed fibers and their views. -/
def Relied {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (provider : sig.Name) : Prop :=
  ∃ consumerName consumer,
    state.registry consumerName = some consumer ∧
    consumerName ≠ provider ∧ consumer.Installed ∧ ResolvesTo consumer provider

/-- Definition 58 plus an explicit birth-order strengthening that proves parent acyclicity. -/
structure WellFormed {sig : StaticSignature} {catalog : Catalog sig}
    {Ambient : Type u} (state : GlobalState catalog Ambient) : Prop where
  birth_bounded : ∀ name fiber, state.registry name = some fiber →
    fiber.birth < state.nextBirth
  parent_present : ∀ name fiber parent,
    state.registry name = some fiber → fiber.parent = some parent →
      ∃ parentFiber, state.registry parent = some parentFiber
  parent_older : ∀ name fiber parent parentFiber,
    state.registry name = some fiber → fiber.parent = some parent →
    state.registry parent = some parentFiber → parentFiber.birth < fiber.birth
  provisions_unique : ∀ left leftFiber right rightFiber key,
    state.registry left = some leftFiber → state.registry right = some rightFiber →
    key ∈ (catalog.declaration leftFiber.component).provision →
    key ∈ (catalog.declaration rightFiber.component).provision → left = right
  committed_provider_present : ∀ name fiber
      (_present : state.registry name = some fiber)
      (committed : CommittedView (catalog.declaration fiber.component)),
    fiber.phase.committed? = some committed →
    ∀ declared, ∃ providerFiber,
      state.registry (committed.provider declared) = some providerFiber
  committed_provider_installed : ∀ name fiber
      (_present : state.registry name = some fiber)
      (committed : CommittedView (catalog.declaration fiber.component)),
    fiber.phase.committed? = some committed →
    ∀ declared providerFiber,
      state.registry (committed.provider declared) = some providerFiber →
        providerFiber.Installed

namespace WellFormed

/-- Pairwise-disjoint provisions and table confinement make an active provider unique. -/
theorem activeProvider_unique
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} (wf : WellFormed state)
    {key : sig.Key} {left right : sig.Name}
    (leftProvider : ActiveProvider state key left)
    (rightProvider : ActiveProvider state key right) : left = right := by
  obtain ⟨leftFiber, leftLookup, leftActive, leftPresent⟩ := leftProvider
  obtain ⟨rightFiber, rightLookup, rightActive, rightPresent⟩ := rightProvider
  exact wf.provisions_unique left leftFiber right rightFiber key leftLookup rightLookup
    (leftFiber.table_within_provision key leftPresent)
    (rightFiber.table_within_provision key rightPresent)

/-- The derived active context has at most one value at each dependent key. -/
theorem activeValue_unique
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} (wf : WellFormed state)
    {key : sig.Key} {left right : sig.Value key}
    (leftValue : ActiveValue state key left)
    (rightValue : ActiveValue state key right) : left = right := by
  obtain ⟨leftName, leftFiber, leftLookup, leftActive, leftValueEq⟩ := leftValue
  obtain ⟨rightName, rightFiber, rightLookup, rightActive, rightValueEq⟩ := rightValue
  have provider_eq : leftName = rightName := by
    have leftPresent : (leftFiber.table key).isSome = true := by
      rw [leftValueEq]
      rfl
    have rightPresent : (rightFiber.table key).isSome = true := by
      rw [rightValueEq]
      rfl
    exact wf.activeProvider_unique
      ⟨leftFiber, leftLookup, leftActive, leftPresent⟩
      ⟨rightFiber, rightLookup, rightActive, rightPresent⟩
  subst rightName
  rw [leftLookup] at rightLookup
  have fiber_eq := Option.some.inj rightLookup
  subst rightFiber
  rw [leftValueEq] at rightValueEq
  exact Option.some.inj rightValueEq

end WellFormed

/-! ## Derived active context and Definition 46 target -/

noncomputable def activeLookup
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (key : sig.Key) : Option (sig.Value key) :=
  letI := Classical.propDecidable (∃ value, ActiveValue state key value)
  if present : ∃ value, ActiveValue state key value then some (Classical.choose present) else none

/-- The derived active context. Finiteness follows from finite fibers and finite provisions. -/
noncomputable def activeContext
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) : Coeffect.Context sig.Key sig.Value where
  lookup := activeLookup state
  finite := by
    obtain ⟨names, names_cover⟩ := state.registry.finite
    let support := names.flatMap fun name ↦
      match state.registry name with
      | none => []
      | some fiber => (catalog.declaration fiber.component).provision
    refine ⟨support, ?_⟩
    intro key present
    simp only [activeLookup] at present
    split at present
    next hasValue =>
      obtain ⟨value, activeValue⟩ := hasValue
      obtain ⟨providerName, fiber, lookup, active, valueEq⟩ := activeValue
      have name_mem : providerName ∈ names :=
        names_cover providerName (by simp [lookup])
      apply List.mem_flatMap.mpr
      refine ⟨providerName, name_mem, ?_⟩
      rw [lookup]
      exact fiber.table_within_provision key (by simp [valueEq])
    next noValue => simp at present

theorem activeContext_value_iff
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} (wf : WellFormed state)
    {key : sig.Key} {value : sig.Value key} :
    activeContext state key = some value ↔ ActiveValue state key value := by
  classical
  simp only [activeContext, activeLookup]
  split
  next hasValue =>
    constructor
    · intro equal
      have chosen : ActiveValue state key (Classical.choose hasValue) :=
        Classical.choose_spec hasValue
      have value_eq : Classical.choose hasValue = value := Option.some.inj equal
      exact value_eq ▸ chosen
    · intro active
      exact congrArg some (wf.activeValue_unique (Classical.choose_spec hasValue) active)
  next noValue =>
    constructor
    · simp
    · intro active
      exact False.elim (noValue ⟨value, active⟩)

/-- A candidate committed view is exactly the current active provider resolution. -/
structure IsTargetView
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (view : CommittedView (catalog.declaration fiber.component)) : Prop where
  present : state.registry name = some fiber
  not_retired : fiber.retired = false
  resolves_active : ∀ declared, ActiveProvider state declared.key (view.provider declared)

theorem IsTargetView.unique
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} (wf : WellFormed state)
    {name : sig.Name} {fiber : Fiber catalog}
    {left right : CommittedView (catalog.declaration fiber.component)}
    (leftTarget : IsTargetView state name fiber left)
    (rightTarget : IsTargetView state name fiber right) : left = right := by
  ext declared
  exact wf.activeProvider_unique (leftTarget.resolves_active declared)
    (rightTarget.resolves_active declared)

/-- Definition 46 target, defined by unique choice from the finite current registry. -/
noncomputable def targetView
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) :
    Option (CommittedView (catalog.declaration fiber.component)) :=
  letI := Classical.propDecidable (∃ view, IsTargetView state name fiber view)
  if target : ∃ view, IsTargetView state name fiber view then some (Classical.choose target)
  else none

theorem targetView_sound
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    {view : CommittedView (catalog.declaration fiber.component)}
    (_wf : WellFormed state) (target_eq : targetView state name fiber = some view) :
    IsTargetView state name fiber view := by
  classical
  simp only [targetView] at target_eq
  split at target_eq
  next target =>
    have chosen := Classical.choose_spec target
    have view_eq := Option.some.inj target_eq
    exact (view_eq ▸ chosen)
  next noTarget => simp at target_eq

theorem targetView_eq_of_isTarget
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    {view : CommittedView (catalog.declaration fiber.component)}
    (wf : WellFormed state) (target : IsTargetView state name fiber view) :
    targetView state name fiber = some view := by
  classical
  simp only [targetView]
  split
  next existsTarget =>
    exact congrArg some (IsTargetView.unique wf (Classical.choose_spec existsTarget) target)
  next noTarget => exact False.elim (noTarget ⟨view, target⟩)

theorem targetView_none_of_retired
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    (retired : fiber.retired = true) : targetView state name fiber = none := by
  classical
  simp only [targetView]
  split
  next target =>
    obtain ⟨view, targetWitness⟩ := target
    have notRetired := targetWitness.not_retired
    rw [retired] at notRetired
    cases notRetired
  next => rfl

/-- Definition 46/49 quiescence over every currently registered fiber. -/
def Quiescent
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) : Prop :=
  ∀ name fiber, state.registry name = some fiber →
    match fiber.phase with
    | .inactive outcome => outcome.isSome = true ∨ targetView state name fiber = none
    | .active _ committed => targetView state name fiber = some committed
    | .reloading _ _ _ => False
    | .unloading _ _ _ => False

/-! ## Pure registry edits and orchestration relation -/

def insertFiber
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (parent : Option sig.Name)
    (component : sig.ComponentId) : GlobalState catalog Ambient :=
  let fiber : Fiber catalog := {
    component
    parent
    birth := state.nextBirth
    table := Coeffect.empty
    table_within_provision := by simp
    retired := false
    phase := .inactive none
  }
  {
    ambient := state.ambient
    nextBirth := state.nextBirth + 1
    registry := Coeffect.setAt state.registry name fiber
  }

@[simp] theorem insertFiber_nextBirth
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (parent : Option sig.Name)
    (component : sig.ComponentId) :
    (insertFiber state name parent component).nextBirth = state.nextBirth + 1 := rfl

@[simp] theorem insertFiber_lookup_same
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (parent : Option sig.Name)
    (component : sig.ComponentId) :
    (insertFiber state name parent component).registry name = some {
      component := component
      parent := parent
      birth := state.nextBirth
      table := Coeffect.empty
      table_within_provision := by simp
      retired := false
      phase := .inactive none
    } := by
  simp [insertFiber]

@[simp] theorem insertFiber_lookup_other
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name candidate : sig.Name)
    (parent : Option sig.Name) (component : sig.ComponentId)
    (different : candidate ≠ name) :
    (insertFiber state name parent component).registry candidate = state.registry candidate := by
  simp [insertFiber, Coeffect.setAt_other, different]

def retireFiber
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) :
    GlobalState catalog Ambient := {
  state with registry := Coeffect.setAt state.registry name { fiber with retired := true }
}

@[simp] theorem retireFiber_nextBirth
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) :
    (retireFiber state name fiber).nextBirth = state.nextBirth := rfl

@[simp] theorem retireFiber_lookup_same
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog) :
    (retireFiber state name fiber).registry name = some { fiber with retired := true } := by
  simp [retireFiber]

@[simp] theorem retireFiber_lookup_other
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name candidate : sig.Name) (fiber : Fiber catalog)
    (different : candidate ≠ name) :
    (retireFiber state name fiber).registry candidate = state.registry candidate := by
  simp [retireFiber, Coeffect.setAt_other, different]

def removeFiber
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) : GlobalState catalog Ambient := {
  state with registry := Coeffect.removeAt state.registry name
}

@[simp] theorem removeFiber_nextBirth
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) :
    (removeFiber state name).nextBirth = state.nextBirth := rfl

@[simp] theorem removeFiber_lookup_same
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name : sig.Name) :
    (removeFiber state name).registry name = none := by
  simp [removeFiber]

@[simp] theorem removeFiber_lookup_other
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) (name candidate : sig.Name)
    (different : candidate ≠ name) :
    (removeFiber state name).registry candidate = state.registry candidate := by
  simp [removeFiber, Coeffect.removeAt_other, different]

/-- The three orchestration rules, with every premise needed for preservation explicit. -/
inductive OrchestrationStep
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u} :
    GlobalState catalog Ambient → GlobalState catalog Ambient → Type u where
  | insert
      (before : GlobalState catalog Ambient)
      (name : sig.Name)
      (fresh : Coeffect.Absent before.registry name)
      (parent : Option sig.Name)
      (parent_present : ∀ parentName, parent = some parentName →
        ∃ parentFiber, before.registry parentName = some parentFiber)
      (component : sig.ComponentId)
      (provision_fresh : ∀ existing existingFiber key,
        before.registry existing = some existingFiber →
        key ∈ (catalog.declaration component).provision →
        key ∈ (catalog.declaration existingFiber.component).provision → False) :
      OrchestrationStep before (insertFiber before name parent component)
  | retire
      (before : GlobalState catalog Ambient)
      (name : sig.Name)
      (fiber : Fiber catalog)
      (present : before.registry name = some fiber) :
      OrchestrationStep before (retireFiber before name fiber)
  | remove
      (before : GlobalState catalog Ambient)
      (name : sig.Name)
      (fiber : Fiber catalog)
      (present : before.registry name = some fiber)
      (retired : fiber.retired = true)
      (inactive : ¬fiber.Installed)
      (childless : ∀ child childFiber,
        before.registry child = some childFiber → childFiber.parent ≠ some name) :
      OrchestrationStep before (removeFiber before name)

/-! ## Preservation -/

theorem preserve_insert
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (before : GlobalState catalog Ambient)
    (name : sig.Name)
    (fresh : Coeffect.Absent before.registry name)
    (parent : Option sig.Name)
    (parentPresent : ∀ parentName, parent = some parentName →
      ∃ parentFiber, before.registry parentName = some parentFiber)
    (component : sig.ComponentId)
    (provisionFresh : ∀ existing existingFiber key,
      before.registry existing = some existingFiber →
      key ∈ (catalog.declaration component).provision →
      key ∈ (catalog.declaration existingFiber.component).provision → False)
    (wf : WellFormed before) :
    WellFormed (insertFiber before name parent component) := by
  classical
  constructor
  · intro candidate fiber lookup
    by_cases same : candidate = name
    · subst candidate
      rw [insertFiber_lookup_same] at lookup
      have fiber_eq := Option.some.inj lookup
      subst fiber
      exact Nat.lt_succ_self before.nextBirth
    · rw [insertFiber_lookup_other before name candidate parent component same] at lookup
      exact Nat.lt_succ_of_lt (wf.birth_bounded candidate fiber lookup)
  · intro candidate fiber parentName lookup parent_eq
    by_cases same : candidate = name
    · subst candidate
      rw [insertFiber_lookup_same] at lookup
      have fiber_eq := Option.some.inj lookup
      subst fiber
      obtain ⟨parentFiber, parentLookup⟩ := parentPresent parentName parent_eq
      exact ⟨parentFiber, by
        by_cases parentSame : parentName = name
        · subst parentName
          rw [fresh.lookup_eq] at parentLookup
          cases parentLookup
        · simpa [insertFiber_lookup_other, parentSame] using parentLookup⟩
    · rw [insertFiber_lookup_other before name candidate parent component same] at lookup
      obtain ⟨parentFiber, parentLookup⟩ := wf.parent_present candidate fiber parentName
        lookup parent_eq
      refine ⟨parentFiber, ?_⟩
      by_cases parentSame : parentName = name
      · subst parentName
        rw [fresh.lookup_eq] at parentLookup
        cases parentLookup
      · simpa [insertFiber_lookup_other, parentSame] using parentLookup
  · intro candidate fiber parentName parentFiber lookup parent_eq parent_lookup
    by_cases same : candidate = name
    · subst candidate
      rw [insertFiber_lookup_same] at lookup
      have fiber_eq := Option.some.inj lookup
      subst fiber
      have parent_ne : parentName ≠ name := by
        intro equal
        subst parentName
        obtain ⟨priorParent, priorLookup⟩ := parentPresent name parent_eq
        rw [fresh.lookup_eq] at priorLookup
        cases priorLookup
      rw [insertFiber_lookup_other before name parentName parent component parent_ne]
        at parent_lookup
      exact wf.birth_bounded parentName parentFiber parent_lookup
    · rw [insertFiber_lookup_other before name candidate parent component same] at lookup
      have parent_ne : parentName ≠ name := by
        intro equal
        subst parentName
        obtain ⟨priorParent, priorLookup⟩ :=
          wf.parent_present candidate fiber name lookup parent_eq
        rw [fresh.lookup_eq] at priorLookup
        cases priorLookup
      rw [insertFiber_lookup_other before name parentName parent component parent_ne]
        at parent_lookup
      exact wf.parent_older candidate fiber parentName parentFiber lookup parent_eq parent_lookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    by_cases leftSame : left = name
    · subst left
      rw [insertFiber_lookup_same] at leftLookup
      have leftFiber_eq := Option.some.inj leftLookup
      subst leftFiber
      by_cases rightSame : right = name
      · exact rightSame.symm
      · rw [insertFiber_lookup_other before name right parent component rightSame] at rightLookup
        exact False.elim (provisionFresh right rightFiber key rightLookup leftKey rightKey)
    · rw [insertFiber_lookup_other before name left parent component leftSame] at leftLookup
      by_cases rightSame : right = name
      · subst right
        rw [insertFiber_lookup_same] at rightLookup
        have rightFiber_eq := Option.some.inj rightLookup
        subst rightFiber
        exact False.elim (provisionFresh left leftFiber key leftLookup rightKey leftKey)
      · rw [insertFiber_lookup_other before name right parent component rightSame] at rightLookup
        exact wf.provisions_unique left leftFiber right rightFiber key
          leftLookup rightLookup leftKey rightKey
  · intro candidate fiber lookup committed committed_eq declared
    by_cases same : candidate = name
    · subst candidate
      rw [insertFiber_lookup_same] at lookup
      have fiber_eq := Option.some.inj lookup
      subst fiber
      simp [Phase.committed?] at committed_eq
    · rw [insertFiber_lookup_other before name candidate parent component same] at lookup
      obtain ⟨providerFiber, providerLookup⟩ :=
        wf.committed_provider_present candidate fiber lookup committed committed_eq declared
      refine ⟨providerFiber, ?_⟩
      by_cases providerSame : committed.provider declared = name
      · rw [providerSame, fresh.lookup_eq] at providerLookup
        cases providerLookup
      · simpa [insertFiber_lookup_other, providerSame] using providerLookup
  · intro candidate fiber lookup committed committed_eq declared providerFiber providerLookup
    by_cases same : candidate = name
    · subst candidate
      rw [insertFiber_lookup_same] at lookup
      have fiber_eq := Option.some.inj lookup
      subst fiber
      simp [Phase.committed?] at committed_eq
    · rw [insertFiber_lookup_other before name candidate parent component same] at lookup
      have provider_ne : committed.provider declared ≠ name := by
        intro providerSame
        rw [providerSame, insertFiber_lookup_same] at providerLookup
        have providerFiber_eq := Option.some.inj providerLookup
        subst providerFiber
        have prior := wf.committed_provider_present candidate fiber lookup committed
          committed_eq declared
        obtain ⟨priorFiber, priorLookup⟩ := prior
        rw [providerSame, fresh.lookup_eq] at priorLookup
        cases priorLookup
      rw [insertFiber_lookup_other before name (committed.provider declared) parent component
        provider_ne] at providerLookup
      exact wf.committed_provider_installed candidate fiber lookup committed committed_eq
        declared providerFiber providerLookup

theorem preserve_retire
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (before : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : before.registry name = some fiber) (wf : WellFormed before) :
    WellFormed (retireFiber before name fiber) := by
  classical
  let updated : Fiber catalog := { fiber with retired := true }
  constructor
  · intro candidate current lookup
    by_cases same : candidate = name
    · subst candidate
      rw [retireFiber_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      exact wf.birth_bounded name fiber present
    · rw [retireFiber_lookup_other before name candidate fiber same] at lookup
      exact wf.birth_bounded candidate current lookup
  · intro candidate current parentName lookup parent_eq
    by_cases same : candidate = name
    · subst candidate
      rw [retireFiber_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      obtain ⟨parentFiber, parentLookup⟩ :=
        wf.parent_present name fiber parentName present parent_eq
      refine ⟨parentFiber, ?_⟩
      have parent_ne : parentName ≠ name := by
        intro equal
        subst parentName
        rw [present] at parentLookup
        have sameFiber := Option.some.inj parentLookup
        have impossible := wf.parent_older name fiber name fiber present parent_eq present
        exact (Nat.lt_irrefl fiber.birth) (sameFiber ▸ impossible)
      simpa [retireFiber_lookup_other, parent_ne] using parentLookup
    · rw [retireFiber_lookup_other before name candidate fiber same] at lookup
      obtain ⟨parentFiber, parentLookup⟩ :=
        wf.parent_present candidate current parentName lookup parent_eq
      by_cases parentSame : parentName = name
      · subst parentName
        exact ⟨updated, by simp [updated]⟩
      · exact ⟨parentFiber, by
          simpa [retireFiber_lookup_other, parentSame] using parentLookup⟩
  · intro candidate current parentName parentFiber lookup parent_eq parentLookup
    by_cases same : candidate = name
    · subst candidate
      rw [retireFiber_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      by_cases parentSame : parentName = name
      · subst parentName
        rw [retireFiber_lookup_same] at parentLookup
        have parentFiber_eq : updated = parentFiber := Option.some.inj parentLookup
        subst parentFiber
        have prior := wf.parent_older name fiber name fiber present parent_eq present
        exact False.elim ((Nat.lt_irrefl fiber.birth) prior)
      · rw [retireFiber_lookup_other before name parentName fiber parentSame] at parentLookup
        exact wf.parent_older name fiber parentName parentFiber present parent_eq parentLookup
    · rw [retireFiber_lookup_other before name candidate fiber same] at lookup
      by_cases parentSame : parentName = name
      · subst parentName
        rw [retireFiber_lookup_same] at parentLookup
        have parentFiber_eq : updated = parentFiber := Option.some.inj parentLookup
        subst parentFiber
        simpa [updated] using wf.parent_older candidate current name fiber lookup parent_eq present
      · rw [retireFiber_lookup_other before name parentName fiber parentSame] at parentLookup
        exact wf.parent_older candidate current parentName parentFiber lookup parent_eq parentLookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    by_cases leftSame : left = name
    · subst left
      rw [retireFiber_lookup_same] at leftLookup
      have leftFiber_eq : updated = leftFiber := Option.some.inj leftLookup
      subst leftFiber
      by_cases rightSame : right = name
      · exact rightSame.symm
      · rw [retireFiber_lookup_other before name right fiber rightSame] at rightLookup
        simpa [updated] using wf.provisions_unique name fiber right rightFiber key
          present rightLookup leftKey rightKey
    · rw [retireFiber_lookup_other before name left fiber leftSame] at leftLookup
      by_cases rightSame : right = name
      · subst right
        rw [retireFiber_lookup_same] at rightLookup
        have rightFiber_eq : updated = rightFiber := Option.some.inj rightLookup
        subst rightFiber
        simpa [updated] using wf.provisions_unique left leftFiber name fiber key
          leftLookup present leftKey rightKey
      · rw [retireFiber_lookup_other before name right fiber rightSame] at rightLookup
        exact wf.provisions_unique left leftFiber right rightFiber key
          leftLookup rightLookup leftKey rightKey
  · intro candidate current lookup committed committed_eq declared
    by_cases same : candidate = name
    · subst candidate
      rw [retireFiber_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      obtain ⟨priorProvider, priorLookup⟩ :=
        wf.committed_provider_present name fiber present committed committed_eq declared
      by_cases providerSame : committed.provider declared = name
      · exact ⟨updated, by
          rw [providerSame]
          simp [updated]⟩
      · exact ⟨priorProvider, by
          simpa [retireFiber_lookup_other, providerSame] using priorLookup⟩
    · rw [retireFiber_lookup_other before name candidate fiber same] at lookup
      obtain ⟨priorProvider, priorLookup⟩ :=
        wf.committed_provider_present candidate current lookup committed committed_eq declared
      by_cases providerSame : committed.provider declared = name
      · exact ⟨updated, by
          rw [providerSame]
          simp [updated]⟩
      · exact ⟨priorProvider, by
          simpa [retireFiber_lookup_other, providerSame] using priorLookup⟩
  · intro candidate current lookup committed committed_eq declared providerFiber providerLookup
    by_cases same : candidate = name
    · subst candidate
      rw [retireFiber_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      by_cases providerSame : committed.provider declared = name
      · rw [providerSame, retireFiber_lookup_same] at providerLookup
        have providerFiber_eq : updated = providerFiber := Option.some.inj providerLookup
        subst providerFiber
        have priorInstalled := wf.committed_provider_installed name fiber present committed
          committed_eq declared fiber (by simpa [providerSame] using present)
        simpa [updated, Fiber.Installed] using priorInstalled
      · rw [retireFiber_lookup_other before name (committed.provider declared) fiber
          providerSame] at providerLookup
        exact wf.committed_provider_installed name fiber present committed committed_eq
          declared providerFiber providerLookup
    · rw [retireFiber_lookup_other before name candidate fiber same] at lookup
      by_cases providerSame : committed.provider declared = name
      · rw [providerSame, retireFiber_lookup_same] at providerLookup
        have providerFiber_eq : updated = providerFiber := Option.some.inj providerLookup
        subst providerFiber
        have priorInstalled := wf.committed_provider_installed candidate current lookup committed
          committed_eq declared fiber (by simpa [providerSame] using present)
        simpa [updated, Fiber.Installed] using priorInstalled
      · rw [retireFiber_lookup_other before name (committed.provider declared) fiber
          providerSame] at providerLookup
        exact wf.committed_provider_installed candidate current lookup committed committed_eq
          declared providerFiber providerLookup

theorem preserve_remove
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (before : GlobalState catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (present : before.registry name = some fiber)
    (_retired : fiber.retired = true) (inactive : ¬fiber.Installed)
    (childless : ∀ child childFiber,
      before.registry child = some childFiber → childFiber.parent ≠ some name)
    (wf : WellFormed before) : WellFormed (removeFiber before name) := by
  classical
  have priorLookup {candidate : sig.Name} {current : Fiber catalog}
      (lookup : (removeFiber before name).registry candidate = some current) :
      candidate ≠ name ∧ before.registry candidate = some current := by
    have different : candidate ≠ name := by
      intro equal
      subst candidate
      rw [removeFiber_lookup_same] at lookup
      cases lookup
    exact ⟨different, by
      simpa [removeFiber_lookup_other, different] using lookup⟩
  constructor
  · intro candidate current lookup
    exact wf.birth_bounded candidate current (priorLookup lookup).2
  · intro candidate current parentName lookup parent_eq
    let prior := priorLookup lookup
    obtain ⟨parentFiber, parentLookup⟩ :=
      wf.parent_present candidate current parentName prior.2 parent_eq
    have parent_ne : parentName ≠ name := by
      intro equal
      subst parentName
      exact (childless candidate current prior.2) parent_eq
    exact ⟨parentFiber, by
      simpa [removeFiber_lookup_other, parent_ne] using parentLookup⟩
  · intro candidate current parentName parentFiber lookup parent_eq parentLookup
    let prior := priorLookup lookup
    have parent_ne : parentName ≠ name := by
      intro equal
      subst parentName
      exact (childless candidate current prior.2) parent_eq
    rw [removeFiber_lookup_other before name parentName parent_ne] at parentLookup
    exact wf.parent_older candidate current parentName parentFiber prior.2 parent_eq parentLookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    exact wf.provisions_unique left leftFiber right rightFiber key
      (priorLookup leftLookup).2 (priorLookup rightLookup).2 leftKey rightKey
  · intro candidate current lookup committed committed_eq declared
    let prior := priorLookup lookup
    obtain ⟨providerFiber, providerLookup⟩ :=
      wf.committed_provider_present candidate current prior.2 committed committed_eq declared
    have provider_ne : committed.provider declared ≠ name := by
      intro equal
      subst name
      rw [present] at providerLookup
      have providerFiber_eq : fiber = providerFiber := Option.some.inj providerLookup
      subst providerFiber
      have providerInstalled := wf.committed_provider_installed candidate current prior.2
        committed committed_eq declared fiber present
      exact inactive providerInstalled
    exact ⟨providerFiber, by
      simpa [removeFiber_lookup_other, provider_ne] using providerLookup⟩
  · intro candidate current lookup committed committed_eq declared providerFiber providerLookup
    let prior := priorLookup lookup
    have provider_ne : committed.provider declared ≠ name := by
      intro equal
      subst name
      rw [removeFiber_lookup_same] at providerLookup
      cases providerLookup
    rw [removeFiber_lookup_other before name (committed.provider declared) provider_ne]
      at providerLookup
    exact wf.committed_provider_installed candidate current prior.2 committed committed_eq
      declared providerFiber providerLookup

namespace OrchestrationStep

/-- Every orchestration rule preserves the strengthened Definition 58 invariant. -/
theorem preservesWellFormed
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {before after : GlobalState catalog Ambient}
    (step : OrchestrationStep before after) : WellFormed before → WellFormed after := by
  intro wf
  cases step with
  | insert name fresh parent parentPresent component provisionFresh =>
      exact preserve_insert _ name fresh parent parentPresent component provisionFresh wf
  | retire name fiber present =>
      exact preserve_retire _ name fiber present wf
  | remove name fiber present retired inactive childless =>
      exact preserve_remove _ name fiber present retired inactive childless wf

end OrchestrationStep

/-- A positive-length parent path, oriented from older ancestor to younger descendant. -/
inductive Ancestor
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    (state : GlobalState catalog Ambient) : sig.Name → sig.Name → Prop where
  | direct {parent child parentFiber childFiber} :
      state.registry parent = some parentFiber →
      state.registry child = some childFiber →
      childFiber.parent = some parent → Ancestor state parent child
  | cons {ancestor middle child middleFiber childFiber} :
      Ancestor state ancestor middle →
      state.registry middle = some middleFiber →
      state.registry child = some childFiber →
      childFiber.parent = some middle → Ancestor state ancestor child

theorem Ancestor.birth_lt
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} (wf : WellFormed state)
    {ancestor child : sig.Name} (path : Ancestor state ancestor child) :
    ∃ ancestorFiber childFiber,
      state.registry ancestor = some ancestorFiber ∧
      state.registry child = some childFiber ∧ ancestorFiber.birth < childFiber.birth := by
  induction path with
  | direct parentLookup childLookup parent_eq =>
      exact ⟨_, _, parentLookup, childLookup,
        wf.parent_older _ _ _ _ childLookup parent_eq parentLookup⟩
  | cons prior middleLookup childLookup parent_eq inductionHypothesis =>
      obtain ⟨ancestorFiber, priorMiddle, ancestorLookup, priorMiddleLookup, priorLt⟩ :=
        inductionHypothesis
      rw [middleLookup] at priorMiddleLookup
      have middleFiber_eq := Option.some.inj priorMiddleLookup
      subst priorMiddle
      exact ⟨ancestorFiber, _, ancestorLookup, childLookup,
        Nat.lt_trans priorLt
          (wf.parent_older _ _ _ _ childLookup parent_eq middleLookup)⟩

/-- Birth ranking makes the registered parent relation acyclic. -/
theorem parent_acyclic
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {state : GlobalState catalog Ambient} (wf : WellFormed state) (name : sig.Name) :
    ¬Ancestor state name name := by
  intro cycle
  obtain ⟨ancestorFiber, childFiber, ancestorLookup, childLookup, birthLt⟩ := cycle.birth_lt wf
  rw [ancestorLookup] at childLookup
  have fiber_eq := Option.some.inj childLookup
  subst childFiber
  exact (Nat.lt_irrefl ancestorFiber.birth) birthLt

/-- A composable trace of orchestration-only global steps. -/
inductive Trace
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u} :
    GlobalState catalog Ambient → GlobalState catalog Ambient → Type u where
  | nil (state) : Trace state state
  | cons {start middle finish} :
      OrchestrationStep start middle → Trace middle finish → Trace start finish

namespace Trace

theorem preservesWellFormed
    {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}
    {start finish : GlobalState catalog Ambient}
    (trace : Trace start finish) : WellFormed start → WellFormed finish := by
  intro wf
  induction trace with
  | nil => exact wf
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.preservesWellFormed wf)

end Trace

/-! ## Heterogeneous executable example -/

namespace Example

inductive Key where
  | counter
  | label
  deriving DecidableEq, Repr

inductive Component where
  | provider
  | consumer
  deriving DecidableEq, Repr

abbrev Value : Key → Type
  | .counter => Nat
  | .label => String

abbrev signature : StaticSignature where
  Name := Nat
  Key := Key
  ComponentId := Component
  Error := String
  IteratorCode := Nat
  ExternalUndoCode := Nat
  Value := Value
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def providerDecl : ComponentDecl signature where
  dependencies := { keys := [], nodup := by simp }
  provision := [.counter, .label]
  provision_nodup := by decide
  entry := 10

def consumerDecl : ComponentDecl signature where
  dependencies := { keys := [.counter, .label], nodup := by decide }
  provision := []
  provision_nodup := by simp
  entry := 20

abbrev catalog : Catalog signature where
  declaration
    | .provider => providerDecl
    | .consumer => consumerDecl

abbrev State := GlobalState catalog Unit

def initial : State where
  ambient := ()
  nextBirth := 0
  registry := Coeffect.empty

theorem initial_wellFormed : WellFormed initial := by
  constructor <;> intros <;> simp [initial, Coeffect.empty] at *

def withProvider : State := insertFiber initial 0 none .provider

def insertProvider : OrchestrationStep initial withProvider :=
  .insert initial 0 (by constructor; rfl) none (by simp) .provider (by
    intro existing existingFiber key lookup
    simp [initial, Coeffect.empty] at lookup)

theorem withProvider_wellFormed : WellFormed withProvider :=
  insertProvider.preservesWellFormed initial_wellFormed

def withConsumer : State := insertFiber withProvider 1 (some 0) .consumer

def insertConsumer : OrchestrationStep withProvider withConsumer :=
  .insert withProvider 1 (by
    constructor
    rfl) (some 0) (by
      intro parentName equal
      have : parentName = 0 := Option.some.inj equal.symm
      subst parentName
      exact ⟨_, rfl⟩) .consumer (by simp [catalog, consumerDecl])

theorem withConsumer_wellFormed : WellFormed withConsumer :=
  insertConsumer.preservesWellFormed withProvider_wellFormed

def retiredConsumer : State :=
  retireFiber withConsumer 1 {
    component := .consumer
    parent := some 0
    birth := 1
    table := Coeffect.empty
    table_within_provision := by simp
    retired := false
    phase := .inactive none
  }

def retireConsumer : OrchestrationStep withConsumer retiredConsumer :=
  .retire withConsumer 1 _ rfl

theorem retiredConsumer_wellFormed : WellFormed retiredConsumer :=
  retireConsumer.preservesWellFormed withConsumer_wellFormed

def withoutConsumer : State := removeFiber retiredConsumer 1

def removeConsumer : OrchestrationStep retiredConsumer withoutConsumer :=
  .remove retiredConsumer 1 _ rfl rfl (by simp [Fiber.Installed, Phase.Installed]) (by
    intro child childFiber lookup
    by_cases childOne : child = 1
    · subst child
      intro parentEq
      simp [retiredConsumer, withConsumer, withProvider, initial, insertFiber, retireFiber]
        at lookup
      subst childFiber
      simp at parentEq
    · by_cases childZero : child = 0
      · subst child
        intro parentEq
        simp [retiredConsumer, withConsumer, withProvider, initial, insertFiber, retireFiber]
          at lookup
        subst childFiber
        simp at parentEq
      · simp [retiredConsumer, withConsumer, withProvider, initial, insertFiber, retireFiber,
          childOne, childZero] at lookup)

def orchestrationTrace : Trace initial withoutConsumer :=
  .cons insertProvider (.cons insertConsumer (.cons retireConsumer (.cons removeConsumer (.nil _))))

theorem orchestrationTrace_preserves : WellFormed withoutConsumer :=
  orchestrationTrace.preservesWellFormed initial_wellFormed

theorem removed_consumer_absent : withoutConsumer.registry 1 = none := rfl

/-- Name `0` is no longer fresh after the first insertion. -/
theorem used_name_rejected : ¬Coeffect.Absent withProvider.registry 0 := by
  intro fresh
  have impossible :
      (some {
        component := Component.provider
        parent := none
        birth := 0
        table := Coeffect.empty
        table_within_provision := by simp
        retired := false
        phase := Phase.inactive none
      } : Option (Fiber catalog)) = none := by
    simpa [withProvider, initial, insertFiber] using fresh.lookup_eq
  cases impossible

/-- A second provider cannot pass the disjoint-provision premise at the `counter` key. -/
theorem duplicate_provision_rejected :
    ¬(∀ existing existingFiber key,
      withProvider.registry existing = some existingFiber →
      key ∈ (catalog.declaration Component.provider).provision →
      key ∈ (catalog.declaration existingFiber.component).provision → False) := by
  intro provisionFresh
  exact provisionFresh 0 _ .counter rfl (by simp [providerDecl])
    (by simp [providerDecl])

def emptyProviderView : CommittedView providerDecl where
  provider declared := by
    rcases declared with ⟨key, declared⟩
    simp [providerDecl] at declared

def providerTable : Coeffect.Context Key Value :=
  Coeffect.setAt
    (Coeffect.setAt Coeffect.empty .counter (show Value .counter from 7))
    .label (show Value .label from "ready")

def activeProviderFiber : Fiber catalog where
  component := .provider
  parent := none
  birth := 0
  table := providerTable
  table_within_provision := by
    intro key present
    cases key <;> simp [providerDecl]
  retired := false
  phase := .active [] emptyProviderView

def activeState : State where
  ambient := ()
  nextBirth := 1
  registry := Coeffect.setAt Coeffect.empty 0 activeProviderFiber

theorem activeState_wellFormed : WellFormed activeState := by
  constructor
  · intro name fiber lookup
    by_cases same : name = 0
    · subst name
      simp [activeState] at lookup
      subst fiber
      decide
    · simp [activeState, Coeffect.setAt_other, same] at lookup
  · intro name fiber parent lookup parent_eq
    by_cases same : name = 0
    · subst name
      simp [activeState] at lookup
      subst fiber
      simp [activeProviderFiber] at parent_eq
    · simp [activeState, Coeffect.setAt_other, same] at lookup
  · intro name fiber parent parentFiber lookup parent_eq parentLookup
    by_cases same : name = 0
    · subst name
      simp [activeState] at lookup
      subst fiber
      simp [activeProviderFiber] at parent_eq
    · simp [activeState, Coeffect.setAt_other, same] at lookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    have leftEq : left = 0 := by
      by_cases same : left = 0
      · exact same
      · simp [activeState, Coeffect.setAt_other, same] at leftLookup
    have rightEq : right = 0 := by
      by_cases same : right = 0
      · exact same
      · simp [activeState, Coeffect.setAt_other, same] at rightLookup
    exact leftEq.trans rightEq.symm
  · intro name fiber lookup committed committed_eq declared
    by_cases same : name = 0
    · subst name
      simp [activeState] at lookup
      subst fiber
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
    · simp [activeState, Coeffect.setAt_other, same] at lookup
  · intro name fiber lookup committed committed_eq declared providerFiber providerLookup
    by_cases same : name = 0
    · subst name
      simp [activeState] at lookup
      subst fiber
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
    · simp [activeState, Coeffect.setAt_other, same] at lookup

theorem active_counter_exact : activeContext activeState .counter = some 7 := by
  apply (activeContext_value_iff activeState_wellFormed).2
  exact ⟨0, activeProviderFiber, rfl,
    by simp [activeProviderFiber, Fiber.Active, Phase.Active], rfl⟩

theorem active_label_exact : activeContext activeState .label = some "ready" := by
  apply (activeContext_value_iff activeState_wellFormed).2
  exact ⟨0, activeProviderFiber, rfl,
    by simp [activeProviderFiber, Fiber.Active, Phase.Active], rfl⟩

theorem active_provider_unique (name : Nat)
    (provider : ActiveProvider activeState .counter name) : name = 0 := by
  apply activeState_wellFormed.activeProvider_unique provider
  exact ⟨activeProviderFiber, rfl,
    by simp [activeProviderFiber, Fiber.Active, Phase.Active], by rfl⟩

theorem activeState_target :
    targetView activeState 0 activeProviderFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget activeState_wellFormed
  exact {
    present := rfl
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

theorem activeState_quiescent : Quiescent activeState := by
  intro name fiber lookup
  by_cases same : name = 0
  · subst name
    simp [activeState] at lookup
    subst fiber
    simpa [activeProviderFiber] using activeState_target
  · simp [activeState, Coeffect.setAt_other, same] at lookup

end Example

end Cordis.GlobalRegistry
