import Cordis.GlobalRuleInvariance

/-!
# Executable name actions on finite global states

This module implements the structural, orchestration-only base of CORDIS paper Lemma 56 at
revision `948a07b369c62adb3b12e102458be5c18dfb69b9`. A name action contains an actual
`Equiv.Perm` and equivalences for every opaque payload carrier that may contain names. Keys,
component identifiers, declarations, and the catalog remain fixed.

The action is lifted canonically through finite dependent tables, name-indexed registries,
committed provider views, undo codes, phases, fibers, and global states. Identity, composition,
inverse, well-formedness, and the three orchestration rules are proved exactly.

Catalog-entry invariance is recorded separately for a future lifecycle theorem. No dynamics,
iterator, oracle, recovery, inertia, or full Lemma 56 equivariance is claimed here.
-/

set_option autoImplicit false

namespace Cordis.GlobalNameAction

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalRelations
  Cordis.GlobalVestigial

universe u v w

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Minimal executable equivalences for the Std-only project -/

structure Equiv (Alpha : Type u) (Beta : Type v) where
  toFun : Alpha → Beta
  invFun : Beta → Alpha
  left_inv : ∀ value, invFun (toFun value) = value
  right_inv : ∀ value, toFun (invFun value) = value

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

instance : CoeFun (Equiv Alpha Beta) (fun _ ↦ Alpha → Beta) where
  coe := Equiv.toFun

namespace Equiv

abbrev Perm (Alpha : Type u) := Equiv Alpha Alpha

def refl (Alpha : Type u) : Equiv Alpha Alpha where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

def symm (equiv : Equiv Alpha Beta) : Equiv Beta Alpha where
  toFun := equiv.invFun
  invFun := equiv.toFun
  left_inv := equiv.right_inv
  right_inv := equiv.left_inv

def trans (first : Equiv Alpha Beta) (second : Equiv Beta Gamma) : Equiv Alpha Gamma where
  toFun value := second (first value)
  invFun value := first.invFun (second.invFun value)
  left_inv value := by simp [first.left_inv, second.left_inv]
  right_inv value := by simp [first.right_inv, second.right_inv]

@[simp]
theorem symm_apply_apply (equiv : Equiv Alpha Beta) (value : Alpha) :
    equiv.symm (equiv value) = value := equiv.left_inv value

@[simp]
theorem apply_symm_apply (equiv : Equiv Alpha Beta) (value : Beta) :
    equiv (equiv.symm value) = value := equiv.right_inv value

@[simp]
theorem invFun_apply (equiv : Equiv Alpha Beta) (value : Alpha) :
    equiv.invFun (equiv value) = value := equiv.left_inv value

@[simp]
theorem apply_invFun (equiv : Equiv Alpha Beta) (value : Beta) :
    equiv (equiv.invFun value) = value := equiv.right_inv value

theorem injective (equiv : Equiv Alpha Beta) : Function.Injective equiv := by
  intro left right equal
  have := congrArg equiv.invFun equal
  exact (equiv.left_inv left).symm.trans (this.trans (equiv.left_inv right))

theorem surjective (equiv : Equiv Alpha Beta) : Function.Surjective equiv := by
  intro value
  exact ⟨equiv.symm value, equiv.apply_symm_apply value⟩

@[simp] theorem refl_apply (value : Alpha) : (refl Alpha) value = value := rfl

@[simp] theorem refl_symm_apply (value : Alpha) : (refl Alpha).symm value = value := rfl

@[simp] theorem trans_apply
    (first : Equiv Alpha Beta) (second : Equiv Beta Gamma) (value : Alpha) :
    (first.trans second) value = second (first value) := rfl

@[simp] theorem trans_symm_apply
    (first : Equiv Alpha Beta) (second : Equiv Beta Gamma) (value : Gamma) :
    (first.trans second).symm value = first.symm (second.symm value) := rfl

@[simp] theorem symm_symm_apply (equiv : Equiv Alpha Beta) (value : Alpha) :
    equiv.symm.symm value = equiv value := rfl

end Equiv

/-!
## One lawful executable action
-/

structure NameAction (sig : StaticSignature) (Ambient : Type u) where
  name : Equiv.Perm sig.Name
  ambient : Equiv Ambient Ambient
  value : (key : sig.Key) → Equiv (sig.Value key) (sig.Value key)
  error : Equiv sig.Error sig.Error
  iterator : Equiv sig.IteratorCode sig.IteratorCode
  externalUndo : Equiv sig.ExternalUndoCode sig.ExternalUndoCode

namespace NameAction

def refl (sig : StaticSignature) (Ambient : Type u) : NameAction sig Ambient where
  name := Equiv.refl _
  ambient := Equiv.refl _
  value _ := Equiv.refl _
  error := Equiv.refl _
  iterator := Equiv.refl _
  externalUndo := Equiv.refl _

def symm (action : NameAction sig Ambient) : NameAction sig Ambient where
  name := action.name.symm
  ambient := action.ambient.symm
  value key := (action.value key).symm
  error := action.error.symm
  iterator := action.iterator.symm
  externalUndo := action.externalUndo.symm

/-- `first.trans second` means apply `first`, then apply `second`. -/
def trans (first second : NameAction sig Ambient) : NameAction sig Ambient where
  name := first.name.trans second.name
  ambient := first.ambient.trans second.ambient
  value key := (first.value key).trans (second.value key)
  error := first.error.trans second.error
  iterator := first.iterator.trans second.iterator
  externalUndo := first.externalUndo.trans second.externalUndo

/-- Fixed catalogs require every stored entry code to be a fixed point of the iterator action. -/
def CatalogEntryInvariant (action : NameAction sig Ambient) (catalog : Catalog sig) : Prop :=
  ∀ component,
    action.iterator (catalog.declaration component).entry =
      (catalog.declaration component).entry

@[simp] theorem refl_name_apply (name : sig.Name) :
    (refl sig Ambient).name name = name := rfl

@[simp] theorem refl_ambient_apply (value : Ambient) :
    (refl sig Ambient).ambient value = value := rfl

@[simp] theorem refl_value_apply (key : sig.Key) (value : sig.Value key) :
    (refl sig Ambient).value key value = value := rfl

@[simp] theorem refl_error_apply (error : sig.Error) :
    (refl sig Ambient).error error = error := rfl

@[simp] theorem refl_iterator_apply (code : sig.IteratorCode) :
    (refl sig Ambient).iterator code = code := rfl

@[simp] theorem refl_externalUndo_apply (code : sig.ExternalUndoCode) :
    (refl sig Ambient).externalUndo code = code := rfl

@[simp] theorem symm_name_apply (action : NameAction sig Ambient) (name : sig.Name) :
    action.symm.name name = action.name.invFun name := rfl

@[simp] theorem symm_ambient_apply (action : NameAction sig Ambient) (value : Ambient) :
    action.symm.ambient value = action.ambient.invFun value := rfl

@[simp] theorem symm_value_apply
    (action : NameAction sig Ambient) (key : sig.Key) (value : sig.Value key) :
    action.symm.value key value = (action.value key).invFun value := rfl

@[simp] theorem symm_error_apply (action : NameAction sig Ambient) (error : sig.Error) :
    action.symm.error error = action.error.invFun error := rfl

@[simp] theorem symm_iterator_apply
    (action : NameAction sig Ambient) (code : sig.IteratorCode) :
    action.symm.iterator code = action.iterator.invFun code := rfl

@[simp] theorem symm_externalUndo_apply
    (action : NameAction sig Ambient) (code : sig.ExternalUndoCode) :
    action.symm.externalUndo code = action.externalUndo.invFun code := rfl

@[simp] theorem trans_name_apply
    (first second : NameAction sig Ambient) (name : sig.Name) :
    (first.trans second).name name = second.name (first.name name) := rfl

@[simp] theorem trans_ambient_apply
    (first second : NameAction sig Ambient) (value : Ambient) :
    (first.trans second).ambient value = second.ambient (first.ambient value) := rfl

@[simp] theorem trans_value_apply
    (first second : NameAction sig Ambient) (key : sig.Key) (value : sig.Value key) :
    (first.trans second).value key value = second.value key (first.value key value) := rfl

@[simp] theorem trans_error_apply
    (first second : NameAction sig Ambient) (error : sig.Error) :
    (first.trans second).error error = second.error (first.error error) := rfl

@[simp] theorem trans_iterator_apply
    (first second : NameAction sig Ambient) (code : sig.IteratorCode) :
    (first.trans second).iterator code = second.iterator (first.iterator code) := rfl

@[simp] theorem trans_externalUndo_apply
    (first second : NameAction sig Ambient) (code : sig.ExternalUndoCode) :
    (first.trans second).externalUndo code =
      second.externalUndo (first.externalUndo code) := rfl

@[simp] theorem refl_name_symm_apply (name : sig.Name) :
    (refl sig Ambient).name.symm name = name := rfl

@[simp] theorem trans_name_symm_apply
    (first second : NameAction sig Ambient) (name : sig.Name) :
    (first.trans second).name.symm name = first.name.symm (second.name.symm name) := rfl

@[simp] theorem symm_name_symm_apply
    (action : NameAction sig Ambient) (name : sig.Name) :
    action.symm.name.symm name = action.name name := rfl

end NameAction

/-!
## Finite context primitives
-/

def mapValues
    {Key : Type u} [DecidableEq Key] {Value : Key → Type v}
    (map : (key : Key) → Value key → Value key) (context : Coeffect.Context Key Value) :
    Coeffect.Context Key Value where
  lookup key := (context key).map (map key)
  finite := by
    obtain ⟨support, covers⟩ := context.finite
    refine ⟨support, ?_⟩
    intro key present
    apply covers key
    simpa using present

@[simp]
theorem mapValues_lookup
    {Key : Type u} [DecidableEq Key] {Value : Key → Type v}
    (map : (key : Key) → Value key → Value key) (context : Coeffect.Context Key Value)
    (key : Key) : mapValues map context key = (context key).map (map key) := rfl

def reindexConst
    {Key : Type u} [DecidableEq Key] {Value : Type v}
    (perm : Equiv.Perm Key) (map : Value → Value)
    (context : Coeffect.Context Key (fun _ ↦ Value)) :
    Coeffect.Context Key (fun _ ↦ Value) where
  lookup key := (context (perm.symm key)).map map
  finite := by
    obtain ⟨support, covers⟩ := context.finite
    refine ⟨support.map perm, ?_⟩
    intro key present
    have originalPresent : (context (perm.symm key)).isSome = true := by
      simpa using present
    apply List.mem_map.mpr
    exact ⟨perm.symm key, covers (perm.symm key) originalPresent, perm.apply_symm_apply key⟩

@[simp]
theorem reindexConst_lookup
    {Key : Type u} [DecidableEq Key] {Value : Type v}
    (perm : Equiv.Perm Key) (map : Value → Value)
    (context : Coeffect.Context Key (fun _ ↦ Value)) (key : Key) :
    reindexConst perm map context key = (context (perm.symm key)).map map := rfl

@[simp]
theorem reindexConst_lookup_apply
    {Key : Type u} [DecidableEq Key] {Value : Type v}
    (perm : Equiv.Perm Key) (map : Value → Value)
    (context : Coeffect.Context Key (fun _ ↦ Value)) (key : Key) :
    reindexConst perm map context (perm key) = (context key).map map := by
  simp [reindexConst]

theorem mapValues_id
    {Key : Type u} [DecidableEq Key] {Value : Key → Type v}
    (context : Coeffect.Context Key Value) :
    mapValues (fun _ value ↦ value) context = context := by
  apply Coeffect.Context.ext
  intro key
  cases lookup : context key <;> simp [mapValues, lookup]

theorem mapValues_comp
    {Key : Type u} [DecidableEq Key] {Value : Key → Type v}
    (first second : (key : Key) → Value key → Value key)
    (context : Coeffect.Context Key Value) :
    mapValues (fun key value ↦ second key (first key value)) context =
      mapValues second (mapValues first context) := by
  apply Coeffect.Context.ext
  intro key
  cases lookup : context key <;> simp [mapValues, lookup]

theorem reindexConst_refl
    {Key : Type u} [DecidableEq Key] {Value : Type v}
    (context : Coeffect.Context Key (fun _ ↦ Value)) :
    reindexConst (Equiv.refl Key) id context = context := by
  apply Coeffect.Context.ext
  intro key
  simp [reindexConst]

theorem reindexConst_trans
    {Key : Type u} [DecidableEq Key] {Value : Type v}
    (first second : Equiv.Perm Key) (firstMap secondMap : Value → Value)
    (context : Coeffect.Context Key (fun _ ↦ Value)) :
    reindexConst (first.trans second) (fun value ↦ secondMap (firstMap value)) context =
      reindexConst second secondMap (reindexConst first firstMap context) := by
  apply Coeffect.Context.ext
  intro key
  simp [reindexConst, Function.comp_def]

/-!
## Canonical action on global data
-/

def actTable
    (action : NameAction sig Ambient) (table : Coeffect.Context sig.Key sig.Value) :
    Coeffect.Context sig.Key sig.Value :=
  mapValues (fun key ↦ action.value key) table

@[simp]
theorem actTable_lookup
    (action : NameAction sig Ambient) (table : Coeffect.Context sig.Key sig.Value)
    (key : sig.Key) : actTable action table key = (table key).map (action.value key) := rfl

def actCommittedView
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (view : CommittedView decl) : CommittedView decl where
  provider declared := action.name (view.provider declared)

@[simp]
theorem actCommittedView_provider
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (view : CommittedView decl) (declared : DeclaredKey decl) :
    (actCommittedView action view).provider declared = action.name (view.provider declared) := rfl

def actUndoCode (action : NameAction sig Ambient) : UndoCode sig → UndoCode sig
  | .external code => .external (action.externalUndo code)
  | .retire name => .retire (action.name name)

def actPhase
    (action : NameAction sig Ambient) {decl : ComponentDecl sig} : Phase decl → Phase decl
  | .inactive outcome => .inactive (outcome.map action.error)
  | .reloading iterator undos committed =>
      .reloading (action.iterator iterator) (undos.map (actUndoCode action))
        (actCommittedView action committed)
  | .active undos committed =>
      .active (undos.map (actUndoCode action)) (actCommittedView action committed)
  | .unloading undos committed outcome =>
      .unloading (undos.map (actUndoCode action)) (actCommittedView action committed)
        (outcome.map action.error)

def actFiber (action : NameAction sig Ambient) (fiber : Fiber catalog) : Fiber catalog where
  component := fiber.component
  parent := fiber.parent.map action.name
  birth := fiber.birth
  table := actTable action fiber.table
  table_within_provision := by
    intro key present
    apply fiber.table_within_provision key
    simpa [actTable] using present
  retired := fiber.retired
  phase := actPhase action fiber.phase

@[simp]
theorem actFiber_component
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).component = fiber.component := rfl

@[simp]
theorem actFiber_parent
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).parent = fiber.parent.map action.name := rfl

@[simp]
theorem actFiber_birth
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).birth = fiber.birth := rfl

@[simp]
theorem actFiber_table
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).table = actTable action fiber.table := rfl

@[simp]
theorem actFiber_retired
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).retired = fiber.retired := rfl

@[simp]
theorem actFiber_phase
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).phase = actPhase action fiber.phase := rfl

def actRegistry
    (action : NameAction sig Ambient) (registry : Registry catalog) : Registry catalog :=
  reindexConst action.name (actFiber action) registry

@[simp]
theorem actRegistry_lookup
    (action : NameAction sig Ambient) (registry : Registry catalog) (name : sig.Name) :
    actRegistry action registry name =
      (registry (action.name.symm name)).map (actFiber action) := rfl

@[simp]
theorem actRegistry_lookup_apply
    (action : NameAction sig Ambient) (registry : Registry catalog) (name : sig.Name) :
    actRegistry action registry (action.name name) =
      (registry name).map (actFiber action) := by
  simp [actRegistry]

def actState
    (action : NameAction sig Ambient) (state : State catalog Ambient) : State catalog Ambient where
  ambient := action.ambient state.ambient
  nextBirth := state.nextBirth
  registry := actRegistry action state.registry

@[simp]
theorem actState_ambient
    (action : NameAction sig Ambient) (state : State catalog Ambient) :
    (actState action state).ambient = action.ambient state.ambient := rfl

@[simp]
theorem actState_nextBirth
    (action : NameAction sig Ambient) (state : State catalog Ambient) :
    (actState action state).nextBirth = state.nextBirth := rfl

@[simp]
theorem actState_registry
    (action : NameAction sig Ambient) (state : State catalog Ambient) :
    (actState action state).registry = actRegistry action state.registry := rfl

/-!
## Identity, composition, and inverse laws
-/

@[simp]
theorem actTable_refl (table : Coeffect.Context sig.Key sig.Value) :
    actTable (NameAction.refl sig Ambient) table = table := by
  apply Coeffect.Context.ext
  intro key
  cases lookup : table key <;>
    simp [actTable, mapValues, NameAction.refl, Equiv.refl, lookup]

theorem actTable_trans
    (first second : NameAction sig Ambient) (table : Coeffect.Context sig.Key sig.Value) :
    actTable (first.trans second) table = actTable second (actTable first table) := by
  apply Coeffect.Context.ext
  intro key
  cases lookup : table key <;>
    simp [actTable, mapValues, NameAction.trans, Equiv.trans, lookup]

@[simp]
theorem actTable_symm_apply
    (action : NameAction sig Ambient) (table : Coeffect.Context sig.Key sig.Value) :
    actTable action.symm (actTable action table) = table := by
  apply Coeffect.Context.ext
  intro key
  cases lookup : table key with
  | none => simp [actTable, mapValues, NameAction.symm, Equiv.symm, lookup]
  | some value =>
      simp [actTable, mapValues, NameAction.symm, Equiv.symm, lookup]

@[simp]
theorem actTable_apply_symm
    (action : NameAction sig Ambient) (table : Coeffect.Context sig.Key sig.Value) :
    actTable action (actTable action.symm table) = table := by
  apply Coeffect.Context.ext
  intro key
  cases lookup : table key <;>
    simp [actTable, mapValues, NameAction.symm, Equiv.symm, lookup]

@[simp]
theorem actCommittedView_refl
    {decl : ComponentDecl sig} (view : CommittedView decl) :
    actCommittedView (NameAction.refl sig Ambient) view = view := by
  apply CommittedView.ext
  intro declared
  simp [actCommittedView, NameAction.refl, Equiv.refl]

theorem actCommittedView_trans
    (first second : NameAction sig Ambient) {decl : ComponentDecl sig}
    (view : CommittedView decl) :
    actCommittedView (first.trans second) view =
      actCommittedView second (actCommittedView first view) := by
  apply CommittedView.ext
  intro declared
  rfl

@[simp]
theorem actCommittedView_symm_apply
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (view : CommittedView decl) :
    actCommittedView action.symm (actCommittedView action view) = view := by
  apply CommittedView.ext
  intro declared
  simp [actCommittedView, NameAction.symm, Equiv.symm]

@[simp]
theorem actCommittedView_apply_symm
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (view : CommittedView decl) :
    actCommittedView action (actCommittedView action.symm view) = view := by
  apply CommittedView.ext
  intro declared
  simp [actCommittedView, NameAction.symm, Equiv.symm]

@[simp]
theorem actUndoCode_refl (undo : UndoCode sig) :
    actUndoCode (NameAction.refl sig Ambient) undo = undo := by
  cases undo <;> rfl

theorem actUndoCode_trans
    (first second : NameAction sig Ambient) (undo : UndoCode sig) :
    actUndoCode (first.trans second) undo = actUndoCode second (actUndoCode first undo) := by
  cases undo <;> rfl

@[simp]
theorem actUndoCode_symm_apply
    (action : NameAction sig Ambient) (undo : UndoCode sig) :
    actUndoCode action.symm (actUndoCode action undo) = undo := by
  cases undo <;> simp [actUndoCode, NameAction.symm, Equiv.symm]

@[simp]
theorem actUndoCode_apply_symm
    (action : NameAction sig Ambient) (undo : UndoCode sig) :
    actUndoCode action (actUndoCode action.symm undo) = undo := by
  cases undo <;> simp [actUndoCode, NameAction.symm, Equiv.symm]

@[simp]
theorem map_actUndoCode_refl (undos : List (UndoCode sig)) :
    undos.map (actUndoCode (NameAction.refl sig Ambient)) = undos := by
  induction undos with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem map_actUndoCode_trans
    (first second : NameAction sig Ambient) (undos : List (UndoCode sig)) :
    undos.map (actUndoCode (first.trans second)) =
      (undos.map (actUndoCode first)).map (actUndoCode second) := by
  induction undos with
  | nil => rfl
  | cons head tail ih => simp [actUndoCode_trans, ih]

@[simp]
theorem map_actUndoCode_symm_apply
    (action : NameAction sig Ambient) (undos : List (UndoCode sig)) :
    (undos.map (actUndoCode action)).map (actUndoCode action.symm) = undos := by
  induction undos with
  | nil => rfl
  | cons head tail ih => simp [ih]

@[simp]
theorem map_actUndoCode_apply_symm
    (action : NameAction sig Ambient) (undos : List (UndoCode sig)) :
    (undos.map (actUndoCode action.symm)).map (actUndoCode action) = undos := by
  induction undos with
  | nil => rfl
  | cons head tail ih => simp [ih]

@[simp]
theorem actPhase_refl
    {decl : ComponentDecl sig} (phase : Phase decl) :
    actPhase (NameAction.refl sig Ambient) phase = phase := by
  cases phase with
  | inactive outcome => cases outcome <;> rfl
  | reloading iterator undos committed =>
      simp [actPhase, map_actUndoCode_refl, actCommittedView_refl]
  | active undos committed =>
      simp [actPhase, map_actUndoCode_refl, actCommittedView_refl]
  | unloading undos committed outcome =>
      cases outcome <;> simp [actPhase, map_actUndoCode_refl, actCommittedView_refl]

theorem actPhase_trans
    (first second : NameAction sig Ambient) {decl : ComponentDecl sig}
    (phase : Phase decl) :
    actPhase (first.trans second) phase = actPhase second (actPhase first phase) := by
  cases phase with
  | inactive outcome => cases outcome <;> rfl
  | reloading iterator undos committed =>
      simp [actPhase, map_actUndoCode_trans, actCommittedView_trans]
  | active undos committed =>
      simp [actPhase, map_actUndoCode_trans, actCommittedView_trans]
  | unloading undos committed outcome =>
      cases outcome <;> simp [actPhase, map_actUndoCode_trans, actCommittedView_trans]

@[simp]
theorem actPhase_symm_apply
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (phase : Phase decl) : actPhase action.symm (actPhase action phase) = phase := by
  cases phase with
  | inactive outcome => cases outcome <;> simp [actPhase]
  | reloading iterator undos committed =>
      simp only [actPhase]
      rw [map_actUndoCode_symm_apply, actCommittedView_symm_apply]
      simp
  | active undos committed =>
      simp only [actPhase]
      rw [map_actUndoCode_symm_apply, actCommittedView_symm_apply]
  | unloading undos committed outcome =>
      simp only [actPhase]
      rw [map_actUndoCode_symm_apply, actCommittedView_symm_apply]
      cases outcome <;> simp

@[simp]
theorem actPhase_apply_symm
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (phase : Phase decl) : actPhase action (actPhase action.symm phase) = phase := by
  cases phase with
  | inactive outcome => cases outcome <;> simp [actPhase]
  | reloading iterator undos committed =>
      simp only [actPhase]
      rw [map_actUndoCode_apply_symm, actCommittedView_apply_symm]
      simp
  | active undos committed =>
      simp only [actPhase]
      rw [map_actUndoCode_apply_symm, actCommittedView_apply_symm]
  | unloading undos committed outcome =>
      simp only [actPhase]
      rw [map_actUndoCode_apply_symm, actCommittedView_apply_symm]
      cases outcome <;> simp

theorem actPhase_installed_iff
    (action : NameAction sig Ambient) {decl : ComponentDecl sig} (phase : Phase decl) :
    (actPhase action phase).Installed ↔ phase.Installed := by
  cases phase <;> simp [actPhase, Phase.Installed]

theorem actPhase_active_iff
    (action : NameAction sig Ambient) {decl : ComponentDecl sig} (phase : Phase decl) :
    (actPhase action phase).Active ↔ phase.Active := by
  cases phase <;> simp [actPhase, Phase.Active]

theorem actPhase_committed
    (action : NameAction sig Ambient) {decl : ComponentDecl sig} (phase : Phase decl) :
    (actPhase action phase).committed? =
      phase.committed?.map (actCommittedView action) := by
  cases phase <;> rfl

@[simp]
theorem actFiber_refl (fiber : Fiber catalog) :
    actFiber (NameAction.refl sig Ambient) fiber = fiber := by
  cases fiber with
  | mk component parent birth table within retired phase =>
      simp only [actFiber, Fiber.mk.injEq]
      exact ⟨trivial, by cases parent <;> rfl, trivial, actTable_refl table, trivial,
        heq_of_eq (actPhase_refl phase)⟩

theorem actFiber_trans
    (first second : NameAction sig Ambient) (fiber : Fiber catalog) :
    actFiber (first.trans second) fiber = actFiber second (actFiber first fiber) := by
  cases fiber with
  | mk component parent birth table within retired phase =>
      simp only [actFiber, Fiber.mk.injEq]
      exact ⟨trivial, by cases parent <;> rfl, trivial,
        actTable_trans first second table, trivial,
        heq_of_eq (actPhase_trans first second phase)⟩

@[simp]
theorem actFiber_symm_apply
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    actFiber action.symm (actFiber action fiber) = fiber := by
  cases fiber with
  | mk component parent birth table within retired phase =>
      simp only [actFiber, Fiber.mk.injEq]
      exact ⟨trivial, by cases parent <;> simp, trivial,
        actTable_symm_apply action table, trivial,
        heq_of_eq (actPhase_symm_apply action phase)⟩

@[simp]
theorem actFiber_apply_symm
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    actFiber action (actFiber action.symm fiber) = fiber := by
  cases fiber with
  | mk component parent birth table within retired phase =>
      simp only [actFiber, Fiber.mk.injEq]
      exact ⟨trivial, by cases parent <;> simp, trivial,
        actTable_apply_symm action table, trivial,
        heq_of_eq (actPhase_apply_symm action phase)⟩

@[simp]
theorem actRegistry_refl (registry : Registry catalog) :
    actRegistry (NameAction.refl sig Ambient) registry = registry := by
  apply Coeffect.Context.ext
  intro name
  rw [actRegistry_lookup]
  simp only [NameAction.refl_name_symm_apply]
  cases lookup : registry name with
  | none => rfl
  | some fiber => simp

theorem actRegistry_trans
    (first second : NameAction sig Ambient) (registry : Registry catalog) :
    actRegistry (first.trans second) registry =
      actRegistry second (actRegistry first registry) := by
  apply Coeffect.Context.ext
  intro name
  rw [actRegistry_lookup, actRegistry_lookup]
  rw [actRegistry_lookup]
  simp only [NameAction.trans_name_symm_apply]
  cases lookup : registry (first.name.symm (second.name.symm name)) with
  | none => simp
  | some fiber => simp [actFiber_trans]

@[simp]
theorem actRegistry_symm_apply
    (action : NameAction sig Ambient) (registry : Registry catalog) :
    actRegistry action.symm (actRegistry action registry) = registry := by
  apply Coeffect.Context.ext
  intro name
  rw [actRegistry_lookup]
  simp only [NameAction.symm_name_symm_apply]
  rw [actRegistry_lookup_apply]
  cases lookup : registry name with
  | none => simp
  | some fiber => simp

@[simp]
theorem actRegistry_apply_symm
    (action : NameAction sig Ambient) (registry : Registry catalog) :
    actRegistry action (actRegistry action.symm registry) = registry := by
  apply Coeffect.Context.ext
  intro name
  rw [actRegistry_lookup]
  rw [actRegistry_lookup]
  simp only [NameAction.symm_name_symm_apply, Equiv.apply_symm_apply]
  cases lookup : registry name with
  | none => simp
  | some fiber => simp

@[simp]
theorem actState_refl (state : State catalog Ambient) :
    actState (NameAction.refl sig Ambient) state = state := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, GlobalState.mk.injEq]
      exact ⟨rfl, trivial, actRegistry_refl registry⟩

theorem actState_trans
    (first second : NameAction sig Ambient) (state : State catalog Ambient) :
    actState (first.trans second) state = actState second (actState first state) := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, GlobalState.mk.injEq]
      exact ⟨rfl, trivial, actRegistry_trans first second registry⟩

@[simp]
theorem actState_symm_apply
    (action : NameAction sig Ambient) (state : State catalog Ambient) :
    actState action.symm (actState action state) = state := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, GlobalState.mk.injEq]
      exact ⟨action.ambient.left_inv ambient, trivial,
        actRegistry_symm_apply action registry⟩

@[simp]
theorem actState_apply_symm
    (action : NameAction sig Ambient) (state : State catalog Ambient) :
    actState action (actState action.symm state) = state := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, GlobalState.mk.injEq]
      exact ⟨action.ambient.right_inv ambient, trivial,
        actRegistry_apply_symm action registry⟩

theorem actFiber_injective
    (action : NameAction sig Ambient) :
    Function.Injective (actFiber (catalog := catalog) action) := by
  intro left right equal
  have acted := congrArg (actFiber (catalog := catalog) action.symm) equal
  simpa using acted

theorem actRegistry_lookup_some_iff
    (action : NameAction sig Ambient) (registry : Registry catalog)
    (name : sig.Name) (fiber : Fiber catalog) :
    actRegistry action registry (action.name name) = some (actFiber action fiber) ↔
      registry name = some fiber := by
  rw [actRegistry_lookup_apply]
  constructor
  · intro equal
    cases lookup : registry name with
    | none => simp [lookup] at equal
    | some current =>
        rw [lookup] at equal
        have fiberEq : actFiber action current = actFiber action fiber := Option.some.inj equal
        have currentEq := actFiber_injective action fiberEq
        subst current
        rfl
  · intro equal
    simp [equal]

theorem actRegistry_lookup_none_iff
    (action : NameAction sig Ambient) (registry : Registry catalog) (name : sig.Name) :
    actRegistry action registry (action.name name) = none ↔ registry name = none := by
  rw [actRegistry_lookup_apply]
  cases registry name <;> simp

theorem originalFiber_of_actRegistry_lookup
    (action : NameAction sig Ambient) (registry : Registry catalog)
    {actedName : sig.Name} {actedFiber : Fiber catalog}
    (lookup : actRegistry action registry actedName = some actedFiber) :
    ∃ originalFiber,
      registry (action.name.symm actedName) = some originalFiber ∧
        actedFiber = actFiber action originalFiber := by
  rw [actRegistry_lookup] at lookup
  cases originalLookup : registry (action.name.symm actedName) with
  | none => simp [originalLookup] at lookup
  | some originalFiber =>
      rw [originalLookup] at lookup
      have equal : actFiber action originalFiber = actedFiber := Option.some.inj lookup
      exact ⟨originalFiber, rfl, equal.symm⟩

theorem actFiber_installed_iff
    (action : NameAction sig Ambient) (fiber : Fiber catalog) :
    (actFiber action fiber).Installed ↔ fiber.Installed :=
  actPhase_installed_iff action fiber.phase

theorem actCommittedView_injective
    (action : NameAction sig Ambient) {decl : ComponentDecl sig} :
    Function.Injective (actCommittedView action : CommittedView decl → CommittedView decl) := by
  intro left right equal
  have acted := congrArg (actCommittedView action.symm) equal
  simpa using acted

theorem actPhase_committed_some_iff
    (action : NameAction sig Ambient) {decl : ComponentDecl sig}
    (phase : Phase decl) (acted : CommittedView decl) :
    (actPhase action phase).committed? = some acted ↔
      ∃ original, phase.committed? = some original ∧
        acted = actCommittedView action original := by
  cases phase with
  | inactive outcome => simp [actPhase, Phase.committed?]
  | reloading iterator undos committed =>
      constructor
      · intro equal
        exact ⟨committed, rfl, (Option.some.inj equal).symm⟩
      · rintro ⟨original, originalEq, actedEq⟩
        have originalEq' : committed = original := Option.some.inj originalEq
        subst original
        rw [actedEq]
        rfl
  | active undos committed =>
      constructor
      · intro equal
        exact ⟨committed, rfl, (Option.some.inj equal).symm⟩
      · rintro ⟨original, originalEq, actedEq⟩
        have originalEq' : committed = original := Option.some.inj originalEq
        subst original
        rw [actedEq]
        rfl
  | unloading undos committed outcome =>
      constructor
      · intro equal
        exact ⟨committed, rfl, (Option.some.inj equal).symm⟩
      · rintro ⟨original, originalEq, actedEq⟩
        have originalEq' : committed = original := Option.some.inj originalEq
        subst original
        rw [actedEq]
        rfl

theorem wellFormed_act
    (action : NameAction sig Ambient) {state : State catalog Ambient}
    (wf : WellFormed state) : WellFormed (actState action state) := by
  constructor
  · intro actedName actedFiber lookup
    change actRegistry action state.registry actedName = some actedFiber at lookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry lookup
    subst actedFiber
    exact wf.birth_bounded (action.name.symm actedName) originalFiber originalLookup
  · intro actedName actedFiber actedParent lookup parentEq
    change actRegistry action state.registry actedName = some actedFiber at lookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry lookup
    subst actedFiber
    cases originalParentEq : originalFiber.parent with
    | none => simp [actFiber, originalParentEq] at parentEq
    | some originalParent =>
        have actedParentEq : action.name originalParent = actedParent :=
          Option.some.inj (by simpa [actFiber, originalParentEq] using parentEq)
        obtain ⟨parentFiber, parentLookup⟩ :=
          wf.parent_present (action.name.symm actedName) originalFiber originalParent
            originalLookup originalParentEq
        refine ⟨actFiber action parentFiber, ?_⟩
        have actedLookup :=
          (actRegistry_lookup_some_iff action state.registry originalParent parentFiber).2
            parentLookup
        simpa [actedParentEq] using actedLookup
  · intro actedName actedFiber actedParent actedParentFiber lookup parentEq parentLookup
    change actRegistry action state.registry actedName = some actedFiber at lookup
    change actRegistry action state.registry actedParent = some actedParentFiber at parentLookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry lookup
    obtain ⟨originalParentFiber, originalParentLookup, parentFiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry parentLookup
    subst actedFiber
    subst actedParentFiber
    have originalParentEq : originalFiber.parent = some (action.name.symm actedParent) := by
      cases parentLookupEq : originalFiber.parent with
      | none => simp [actFiber, parentLookupEq] at parentEq
      | some originalParent =>
          have nameEq : action.name originalParent = actedParent :=
            Option.some.inj (by simpa [actFiber, parentLookupEq] using parentEq)
          have originalEq : originalParent = action.name.symm actedParent := by
            rw [← nameEq]
            simp
          simp [originalEq]
    exact wf.parent_older (action.name.symm actedName) originalFiber
      (action.name.symm actedParent) originalParentFiber originalLookup originalParentEq
      originalParentLookup
  · intro actedLeft leftFiber actedRight rightFiber key leftLookup rightLookup leftKey
      rightKey
    change actRegistry action state.registry actedLeft = some leftFiber at leftLookup
    change actRegistry action state.registry actedRight = some rightFiber at rightLookup
    obtain ⟨originalLeft, originalLeftLookup, leftFiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry leftLookup
    obtain ⟨originalRight, originalRightLookup, rightFiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry rightLookup
    subst leftFiber
    subst rightFiber
    have originalNames := wf.provisions_unique (action.name.symm actedLeft) originalLeft
      (action.name.symm actedRight) originalRight key originalLeftLookup originalRightLookup
      leftKey rightKey
    have actedNames := congrArg action.name originalNames
    simpa using actedNames
  · intro actedName actedFiber lookup actedCommitted committedEq declared
    change actRegistry action state.registry actedName = some actedFiber at lookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry lookup
    subst actedFiber
    obtain ⟨originalCommitted, originalCommittedEq, actedCommittedEq⟩ :=
      (actPhase_committed_some_iff action originalFiber.phase actedCommitted).1 committedEq
    subst actedCommitted
    obtain ⟨providerFiber, providerLookup⟩ :=
      wf.committed_provider_present (action.name.symm actedName) originalFiber originalLookup
        originalCommitted originalCommittedEq declared
    exact ⟨actFiber action providerFiber,
      (actRegistry_lookup_some_iff action state.registry
        (originalCommitted.provider declared) providerFiber).2 providerLookup⟩
  · intro actedName actedFiber lookup actedCommitted committedEq declared providerFiber
      providerLookup
    change actRegistry action state.registry actedName = some actedFiber at lookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry lookup
    subst actedFiber
    obtain ⟨originalCommitted, originalCommittedEq, actedCommittedEq⟩ :=
      (actPhase_committed_some_iff action originalFiber.phase actedCommitted).1 committedEq
    subst actedCommitted
    change actRegistry action state.registry
      (action.name (originalCommitted.provider declared)) = some providerFiber at providerLookup
    obtain ⟨originalProviderFiber, originalProviderLookup, providerFiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action state.registry providerLookup
    subst providerFiber
    have providerLookup' :
        state.registry (originalCommitted.provider declared) = some originalProviderFiber := by
      simpa using originalProviderLookup
    have installed := wf.committed_provider_installed (action.name.symm actedName)
      originalFiber originalLookup originalCommitted originalCommittedEq declared
      originalProviderFiber providerLookup'
    exact (actFiber_installed_iff action originalProviderFiber).2 installed

theorem wellFormed_act_iff
    (action : NameAction sig Ambient) (state : State catalog Ambient) :
    WellFormed (actState action state) ↔ WellFormed state := by
  constructor
  · intro actedWf
    have restored := wellFormed_act action.symm actedWf
    simpa using restored
  · exact wellFormed_act action

/-!
## Exact structural edit commutation
-/

theorem actRegistry_setAt
    (action : NameAction sig Ambient) (registry : Registry catalog)
    (name : sig.Name) (fiber : Fiber catalog) :
    actRegistry action (Coeffect.setAt registry name fiber) =
      Coeffect.setAt (actRegistry action registry) (action.name name) (actFiber action fiber) := by
  apply Coeffect.Context.ext
  intro observed
  by_cases same : observed = action.name name
  · subst observed
    simp
  · have originalDifferent : action.name.symm observed ≠ name := by
      intro equal
      apply same
      rw [← equal]
      simp
    simp [actRegistry, reindexConst, Coeffect.setAt_other, same, originalDifferent]

theorem actRegistry_removeAt
    (action : NameAction sig Ambient) (registry : Registry catalog) (name : sig.Name) :
    actRegistry action (Coeffect.removeAt registry name) =
      Coeffect.removeAt (actRegistry action registry) (action.name name) := by
  apply Coeffect.Context.ext
  intro observed
  by_cases same : observed = action.name name
  · subst observed
    simp
  · have originalDifferent : action.name.symm observed ≠ name := by
      intro equal
      apply same
      rw [← equal]
      simp
    simp [actRegistry, reindexConst, Coeffect.removeAt_other, same, originalDifferent]

theorem actState_insertFiber
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (name : sig.Name) (parent : Option sig.Name) (component : sig.ComponentId) :
    actState action (insertFiber state name parent component) =
      insertFiber (actState action state) (action.name name) (parent.map action.name)
        component := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, insertFiber, GlobalState.mk.injEq]
      constructor
      · trivial
      · constructor
        · trivial
        · rw [actRegistry_setAt]
          congr 2

theorem actState_retireFiber
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (name : sig.Name) (fiber : Fiber catalog) :
    actState action (retireFiber state name fiber) =
      retireFiber (actState action state) (action.name name) (actFiber action fiber) := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, retireFiber, GlobalState.mk.injEq]
      constructor
      · trivial
      · constructor
        · trivial
        · rw [actRegistry_setAt]
          congr 2

theorem actState_removeFiber
    (action : NameAction sig Ambient) (state : State catalog Ambient) (name : sig.Name) :
    actState action (removeFiber state name) =
      removeFiber (actState action state) (action.name name) := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, removeFiber, GlobalState.mk.injEq]
      exact ⟨trivial, trivial, actRegistry_removeAt action registry name⟩

/-!
## Orchestration equivariance
-/

@[simp]
theorem orchestrationKind_cast_after
    {before after next : State catalog Ambient} (equal : after = next)
    (step : OrchestrationStep before after) :
    orchestrationKind (equal ▸ step) = orchestrationKind step := by
  cases equal
  rfl

@[simp]
theorem orchestrationName_cast_after
    {before after next : State catalog Ambient} (equal : after = next)
    (step : OrchestrationStep before after) :
    orchestrationName (equal ▸ step) = orchestrationName step := by
  cases equal
  rfl

@[simp]
theorem orchestrationKind_cast_before
    {before next after : State catalog Ambient} (equal : before = next)
    (step : OrchestrationStep before after) :
    orchestrationKind (equal ▸ step) = orchestrationKind step := by
  cases equal
  rfl

@[simp]
theorem orchestrationName_cast_before
    {before next after : State catalog Ambient} (equal : before = next)
    (step : OrchestrationStep before after) :
    orchestrationName (equal ▸ step) = orchestrationName step := by
  cases equal
  rfl

structure ForwardOrchestrationAction
    (action : NameAction sig Ambient)
    {before after : State catalog Ambient}
    (step : OrchestrationStep before after) where
  acted : OrchestrationStep (actState action before) (actState action after)
  same_kind : orchestrationKind acted = orchestrationKind step
  acted_name : orchestrationName acted = action.name (orchestrationName step)

def actOrchestrationAction
    (action : NameAction sig Ambient) {before after : State catalog Ambient}
    (step : OrchestrationStep before after) :
    ForwardOrchestrationAction action step := by
  cases step with
  | insert name fresh parent parentPresent component provisionFresh =>
      have actedFresh : Coeffect.Absent (actState action before).registry
          (action.name name) := by
        constructor
        change actRegistry action before.registry (action.name name) = none
        exact (actRegistry_lookup_none_iff action before.registry name).2 fresh.lookup_eq
      have actedParentPresent : ∀ actedParent,
          parent.map action.name = some actedParent →
          ∃ parentFiber,
            (actState action before).registry actedParent = some parentFiber := by
        intro actedParent parentEq
        cases originalParentEq : parent with
        | none => simp [originalParentEq] at parentEq
        | some originalParent =>
            have nameEq : action.name originalParent = actedParent :=
              Option.some.inj (by simpa [originalParentEq] using parentEq)
            obtain ⟨parentFiber, parentLookup⟩ :=
              parentPresent originalParent originalParentEq
            refine ⟨actFiber action parentFiber, ?_⟩
            have actedLookup :=
              (actRegistry_lookup_some_iff action before.registry originalParent parentFiber).2
                parentLookup
            simpa [nameEq] using actedLookup
      have actedProvisionFresh : ∀ existing existingFiber key,
          (actState action before).registry existing = some existingFiber →
          key ∈ (catalog.declaration component).provision →
          key ∈ (catalog.declaration existingFiber.component).provision → False := by
        intro existing existingFiber key existingLookup insertedKey existingKey
        change actRegistry action before.registry existing = some existingFiber at existingLookup
        obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
          originalFiber_of_actRegistry_lookup action before.registry existingLookup
        subst existingFiber
        exact provisionFresh (action.name.symm existing) originalFiber key originalLookup
          insertedKey existingKey
      let acted : OrchestrationStep (actState action before)
          (insertFiber (actState action before) (action.name name)
            (parent.map action.name) component) :=
        .insert (actState action before) (action.name name) actedFresh
          (parent.map action.name) actedParentPresent component actedProvisionFresh
      let exactActed :=
        (actState_insertFiber action before name parent component).symm ▸ acted
      exact {
        acted := exactActed
        same_kind := by
          dsimp [exactActed]
          rw [orchestrationKind_cast_after]
          rfl
        acted_name := by
          dsimp [exactActed]
          rw [orchestrationName_cast_after]
          rfl
      }
  | retire name fiber present =>
      have actedPresent : (actState action before).registry (action.name name) =
          some (actFiber action fiber) := by
        exact (actRegistry_lookup_some_iff action before.registry name fiber).2 present
      let acted : OrchestrationStep (actState action before)
          (retireFiber (actState action before) (action.name name) (actFiber action fiber)) :=
        .retire (actState action before) (action.name name) (actFiber action fiber)
          actedPresent
      let exactActed := (actState_retireFiber action before name fiber).symm ▸ acted
      exact {
        acted := exactActed
        same_kind := by
          dsimp [exactActed]
          rw [orchestrationKind_cast_after]
          rfl
        acted_name := by
          dsimp [exactActed]
          rw [orchestrationName_cast_after]
          rfl
      }
  | remove name fiber present retired inactive childless =>
      have actedPresent : (actState action before).registry (action.name name) =
          some (actFiber action fiber) :=
        (actRegistry_lookup_some_iff action before.registry name fiber).2 present
      have actedInactive : ¬(actFiber action fiber).Installed := by
        intro installed
        exact inactive ((actFiber_installed_iff action fiber).1 installed)
      have actedChildless : ∀ child childFiber,
          (actState action before).registry child = some childFiber →
          childFiber.parent ≠ some (action.name name) := by
        intro child childFiber childLookup parentEq
        change actRegistry action before.registry child = some childFiber at childLookup
        obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
          originalFiber_of_actRegistry_lookup action before.registry childLookup
        subst childFiber
        cases originalParentEq : originalFiber.parent with
        | none => simp [actFiber, originalParentEq] at parentEq
        | some originalParent =>
            have namesEqual : action.name originalParent = action.name name :=
              Option.some.inj (by simpa [actFiber, originalParentEq] using parentEq)
            have originalEqual := action.name.injective namesEqual
            exact childless (action.name.symm child) originalFiber originalLookup
              (by rw [originalParentEq, originalEqual])
      let acted : OrchestrationStep (actState action before)
          (removeFiber (actState action before) (action.name name)) :=
        .remove (actState action before) (action.name name) (actFiber action fiber)
          actedPresent retired actedInactive actedChildless
      let exactActed := (actState_removeFiber action before name).symm ▸ acted
      exact {
        acted := exactActed
        same_kind := by
          dsimp [exactActed]
          rw [orchestrationKind_cast_after]
          rfl
        acted_name := by
          dsimp [exactActed]
          rw [orchestrationName_cast_after]
          rfl
      }

def actOrchestrationStep
    (action : NameAction sig Ambient) {before after : State catalog Ambient}
    (step : OrchestrationStep before after) :
    OrchestrationStep (actState action before) (actState action after) :=
  (actOrchestrationAction action step).acted

theorem actOrchestrationStep_kind
    (action : NameAction sig Ambient) {before after : State catalog Ambient}
    (step : OrchestrationStep before after) :
    orchestrationKind (actOrchestrationStep action step) = orchestrationKind step := by
  exact (actOrchestrationAction action step).same_kind

theorem actOrchestrationStep_name
    (action : NameAction sig Ambient) {before after : State catalog Ambient}
    (step : OrchestrationStep before after) :
    orchestrationName (actOrchestrationStep action step) =
      action.name (orchestrationName step) := by
  exact (actOrchestrationAction action step).acted_name

structure BackwardOrchestrationAction
    (action : NameAction sig Ambient)
    {before actedAfter : State catalog Ambient}
    (step : OrchestrationStep (actState action before) actedAfter) where
  originalAfter : State catalog Ambient
  original : OrchestrationStep before originalAfter
  endpoint_eq : actState action originalAfter = actedAfter
  same_kind : orchestrationKind original = orchestrationKind step
  acted_name : action.name (orchestrationName original) = orchestrationName step

def unactOrchestrationStep
    (action : NameAction sig Ambient)
    {before actedAfter : State catalog Ambient}
    (step : OrchestrationStep (actState action before) actedAfter) :
    BackwardOrchestrationAction action step := by
  let forward := actOrchestrationAction action.symm step
  let transformed := forward.acted
  let original : OrchestrationStep before (actState action.symm actedAfter) :=
    (actState_symm_apply action before) ▸ transformed
  have sameKind : orchestrationKind original = orchestrationKind step := by
    dsimp [original]
    rw [orchestrationKind_cast_before]
    exact forward.same_kind
  have originalName : orchestrationName original =
      action.name.symm (orchestrationName step) := by
    dsimp [original]
    rw [orchestrationName_cast_before]
    exact forward.acted_name
  exact {
    originalAfter := actState action.symm actedAfter
    original := original
    endpoint_eq := actState_apply_symm action actedAfter
    same_kind := sameKind
    acted_name := by
      rw [originalName]
      simp
  }

structure OrchestrationEquivariance
    (action : NameAction sig Ambient) where
  forward : ∀ {before after : State catalog Ambient},
    OrchestrationStep before after →
      OrchestrationStep (actState action before) (actState action after)
  backward : ∀ {before actedAfter : State catalog Ambient},
    (step : OrchestrationStep (actState action before) actedAfter) →
      BackwardOrchestrationAction action step

def orchestrationEquivariance
    (action : NameAction sig Ambient) : OrchestrationEquivariance
      (catalog := catalog) action where
  forward := actOrchestrationStep action
  backward := unactOrchestrationStep action

/-!
## Nontrivial finite action example
-/

namespace Example

inductive Key where
  | flag
  | token
deriving DecidableEq, Repr

inductive Component where
  | provider
  | child
deriving DecidableEq, Repr

abbrev Value : Key → Type
  | .flag => Bool
  | .token => Unit

abbrev Signature : StaticSignature where
  Name := Bool
  Key := Key
  ComponentId := Component
  Error := Bool
  IteratorCode := Bool
  ExternalUndoCode := Bool
  Value := Value
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def providerDecl : ComponentDecl Signature where
  dependencies := { keys := [], nodup := by simp }
  provision := [.flag]
  provision_nodup := by simp
  entry := false

def childDecl : ComponentDecl Signature where
  dependencies := { keys := [.flag], nodup := by simp }
  provision := [.token]
  provision_nodup := by simp
  entry := true

abbrev exampleCatalog : Catalog Signature where
  declaration
    | .provider => providerDecl
    | .child => childDecl

abbrev ExampleState := GlobalState exampleCatalog Bool

def boolNotEquiv : Equiv Bool Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

def swapAction : NameAction Signature Bool where
  name := boolNotEquiv
  ambient := boolNotEquiv
  value
    | .flag => boolNotEquiv
    | .token => Equiv.refl Unit
  error := boolNotEquiv
  iterator := Equiv.refl Bool
  externalUndo := boolNotEquiv

theorem entry_invariant : swapAction.CatalogEntryInvariant exampleCatalog := by
  intro component
  cases component <;> rfl

def emptyProviderView : CommittedView providerDecl where
  provider declared := by
    rcases declared with ⟨key, declared⟩
    simp [providerDecl] at declared

def childView : CommittedView childDecl where
  provider _ := false

def providerTable : Coeffect.Context Key Value :=
  Coeffect.setAt Coeffect.empty .flag true

def childTable : Coeffect.Context Key Value :=
  Coeffect.setAt Coeffect.empty .token ()

def providerFiber : Fiber exampleCatalog where
  component := .provider
  parent := none
  birth := 0
  table := providerTable
  table_within_provision := by
    intro key present
    cases key <;> simp [providerTable, providerDecl] at present ⊢
  retired := false
  phase := .active [] emptyProviderView

def childFiber : Fiber exampleCatalog where
  component := .child
  parent := some false
  birth := 1
  table := childTable
  table_within_provision := by
    intro key present
    cases key <;> simp [childTable, childDecl] at present ⊢
  retired := false
  phase := .active [.retire false, .external false] childView

def state : ExampleState where
  ambient := true
  nextBirth := 2
  registry := Coeffect.setAt (Coeffect.setAt Coeffect.empty false providerFiber)
    true childFiber

theorem provider_present : state.registry false = some providerFiber := rfl
theorem child_present : state.registry true = some childFiber := rfl

theorem state_wellFormed : WellFormed state := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [state] at lookup <;> subst fiber <;>
      simp [state, providerFiber, childFiber]
  · intro name fiber parent lookup parentEq
    cases name <;> simp [state] at lookup <;> subst fiber
    · simp [providerFiber] at parentEq
    · have parentIsFalse : parent = false := Option.some.inj parentEq.symm
      subst parent
      exact ⟨providerFiber, provider_present⟩
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [state] at lookup <;> subst fiber
    · simp [providerFiber] at parentEq
    · have parentIsFalse : parent = false := Option.some.inj parentEq.symm
      subst parent
      rw [provider_present] at parentLookup
      have equal := Option.some.inj parentLookup
      subst parentFiber
      decide
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases left <;> cases right <;> cases key <;>
      simp [state] at leftLookup rightLookup <;>
      subst leftFiber <;> subst rightFiber <;>
      simp [providerFiber, childFiber, providerDecl, childDecl] at leftKey rightKey ⊢
  · intro name fiber lookup committed committedEq declared
    cases name <;> simp [state] at lookup <;> subst fiber
    · rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
    · have committedIsChild : committed = childView := by
        change some childView = some committed at committedEq
        exact (Option.some.inj committedEq).symm
      subst committed
      exact ⟨providerFiber, provider_present⟩
  · intro name fiber lookup committed committedEq declared providerFiber' providerLookup
    cases name <;> simp [state] at lookup <;> subst fiber
    · rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
    · have committedIsChild : committed = childView := by
        change some childView = some committed at committedEq
        exact (Option.some.inj committedEq).symm
      subst committed
      have providerLookup' : state.registry false = some providerFiber' := by
        simpa [childFiber, childView] using providerLookup
      rw [provider_present] at providerLookup'
      have equal := Option.some.inj providerLookup'
      subst providerFiber'
      simp [providerFiber, Fiber.Installed, Phase.Installed]

abbrev actedState : ExampleState := actState swapAction state

theorem acted_child_lookup : actedState.registry false =
    some (actFiber swapAction childFiber) := by rfl

theorem acted_provider_lookup : actedState.registry true =
    some (actFiber swapAction providerFiber) := by rfl

theorem acted_child_parent : (actFiber swapAction childFiber).parent = some true := rfl

theorem acted_child_committed_provider :
    let actedView := actCommittedView swapAction childView
    actedView.provider ⟨.flag, by simp [childDecl]⟩ = true := rfl

theorem acted_child_undos :
    (actFiber swapAction childFiber).phase =
      .active [.retire true, .external true] (actCommittedView swapAction childView) := rfl

theorem acted_provider_value :
    (actFiber swapAction providerFiber).table .flag = some false := rfl

theorem acted_wellFormed : WellFormed actedState := wellFormed_act swapAction state_wellFormed

theorem state_inverse : actState swapAction.symm actedState = state :=
  actState_symm_apply swapAction state

def retireChild : OrchestrationStep state (retireFiber state true childFiber) :=
  .retire state true childFiber child_present

def actedRetireChild : OrchestrationStep actedState
    (actState swapAction (retireFiber state true childFiber)) :=
  actOrchestrationStep swapAction retireChild

theorem acted_retire_name : orchestrationName actedRetireChild = false := by
  change orchestrationName (actOrchestrationStep swapAction retireChild) = false
  rw [actOrchestrationStep_name]
  rfl

end Example

/-!
## Counterexample to the old opaque equivariance assumption
-/

namespace ConstantNameGap

open Cordis.GlobalTraceFacts.Counterexample

def badAssumption : NameEquivarianceAssumption dynamics where
  Permutation := Unit
  actName _ _ := false
  actState _ state := state
  actIterator _ code := code
  actExternalUndo _ code := code
  actComponent _ component := component
  actResult _ result := result
  run_equivariant := by
    intro permutation owner code state
    rfl

theorem bad_actName_not_injective :
    ¬Function.Injective (badAssumption.actName ()) := by
  intro injective
  have impossible : (false : Bool) = true := injective rfl
  cases impossible

end ConstantNameGap

end Cordis.GlobalNameAction
