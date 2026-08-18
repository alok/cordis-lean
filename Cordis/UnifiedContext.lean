import Cordis.Coeffect
import Std

/-!
# Isolation, interception, and bounded unified contexts

This module mechanizes the locally separable content of Definitions 27--32 of the CORDIS
paper at revision `948a07b369c62adb3b12e102458be5c18dfb69b9`.

Definitions 27--31 have direct typed models. `InPlace` wraps a witnessed `Cordis.Applied`
effect. `Derived` instead indexes a child by its unchanged parent, making discard recovery a
projection rather than pretending that derivation mutated the parent. `IsolatedContext`
implements key-to-realm resolution and its derived routing override. `InterceptionContext`
implements dependent monoidal metadata, finite provider tables, and derived metadata merging.

Definition 32 writes an equirecursive equation `mu Gamma. Gamma x (Gamma -> Gamma) x Sigma`.
Because `Gamma` occurs to the left of an arrow, that equation is not a strictly positive Lean
inductive definition. `Approximation Base Sigma depth` therefore exposes only its exact
finite unfoldings. It is a bounded model of the displayed equation, not a construction of its
recursive fixed point.

The module does not claim Definitions 33--42, observational quotienting, effect independence,
components, fibers, lifecycle scheduling, global composability, imperative aliasing, or runtime
equivalence with the TypeScript implementation.
-/

namespace Cordis.UnifiedContext

universe u v w

/-!
## Definition 27: realization forms
-/

/-- An in-place realization is exactly a witnessed effect on the state it changes. -/
structure InPlace (State : Type u) (before : State) where
  /-- The successor, concrete inverse, and recovery proof. -/
  applied : Cordis.Applied State before

namespace InPlace

variable {State : Type u} {before : State}

/-- Run the concrete inverse of an in-place realization. -/
def recover (realization : InPlace State before) : State :=
  realization.applied.undo realization.applied.after

/-- The in-place inverse recovers the state at which the realization ran. -/
@[simp]
theorem recover_eq (realization : InPlace State before) : realization.recover = before :=
  realization.applied.undo_after

end InPlace

/-- A derived realization keeps its parent as an index and supplies a separately typed child.

Allowing different parent and child types is needed for finite unfoldings of Definition 32. For
ordinary isolation and interception they are the same context type.
-/
structure Derived (Parent : Type u) (Child : Type v) (parent : Parent) where
  /-- The fresh context derived from the unchanged parent. -/
  child : Child

namespace Derived

variable {Parent : Type u} {Child : Type v} {parent : Parent}

/-- Construct a derived child by applying a pure derivation to its parent. -/
def ofFunction (derive : Parent → Child) (parent : Parent) : Derived Parent Child parent where
  child := derive parent

/-- Discarding a derived child returns its unchanged, indexed parent. -/
def discard (_realization : Derived Parent Child parent) : Parent := parent

@[simp]
theorem child_ofFunction (derive : Parent → Child) (parent : Parent) :
    (ofFunction derive parent).child = derive parent := rfl

@[simp]
theorem discard_eq (realization : Derived Parent Child parent) : realization.discard = parent :=
  rfl

end Derived

/-!
## Dependent total-family updates

Interception metadata is total rather than optional, so it uses this typed functional update.
-/

section UpdateAt

variable {Key : Type u} [DecidableEq Key] {Family : Key → Type v}

/-- Replace one member of a dependent total family. -/
def updateAt (values : (key : Key) → Family key) (target : Key)
    (replacement : Family target) : (key : Key) → Family key :=
  fun key ↦
    if same : key = target then same.symm ▸ replacement else values key

@[simp]
theorem updateAt_same (values : (key : Key) → Family key) (target : Key)
    (replacement : Family target) : updateAt values target replacement target = replacement := by
  simp [updateAt]

@[simp]
theorem updateAt_other (values : (key : Key) → Family key) (target key : Key)
    (replacement : Family target) (different : key ≠ target) :
    updateAt values target replacement key = values key := by
  simp [updateAt, different]

/-- A later total-family update at the same key overwrites the earlier one. -/
theorem updateAt_updateAt (values : (key : Key) → Family key) (target : Key)
    (first second : Family target) :
    updateAt (updateAt values target first) target second = updateAt values target second := by
  funext key
  by_cases same : key = target
  · subst key
    simp
  · simp [updateAt_other, same]

/-- Total-family updates at distinct keys commute. -/
theorem updateAt_commute (values : (key : Key) → Family key) (left right : Key)
    (different : left ≠ right) (leftValue : Family left) (rightValue : Family right) :
    updateAt (updateAt values left leftValue) right rightValue =
      updateAt (updateAt values right rightValue) left leftValue := by
  funext key
  by_cases isLeft : key = left
  · subst key
    simp [different]
  · by_cases isRight : key = right
    · subst key
      simp [Ne.symm different]
    · simp [updateAt_other, isLeft, isRight]

end UpdateAt

/-!
## Definitions 28--29: isolation
-/

/-- Definition 28's two-layer isolated coeffect context.

`routing` stores only finite overrides. If no override is present, `baseRealm key` is used.
Injectivity realizes the paper's inclusion of logical keys into realms. `store` is the finite
dependent realm-to-value table.
-/
structure IsolatedContext
    (Key : Type u) [DecidableEq Key]
    (Realm : Type v) [DecidableEq Realm]
    (baseRealm : Key → Realm) (Value : Realm → Type w) where
  /-- Distinct logical keys have distinct own realms before overrides. -/
  baseRealm_injective : Function.Injective baseRealm
  /-- Finite logical-key-to-realm overrides. -/
  routing : Coeffect.Context Key (fun _ ↦ Realm)
  /-- Finite realm-indexed dependent values. -/
  store : Coeffect.Context Realm Value

namespace IsolatedContext

variable {Key : Type u} [DecidableEq Key]
variable {Realm : Type v} [DecidableEq Realm]
variable {baseRealm : Key → Realm} {Value : Realm → Type w}

/-- Resolve a logical key through an override or its distinguished base realm. -/
def resolve (context : IsolatedContext Key Realm baseRealm Value) (key : Key) : Realm :=
  match context.routing key with
  | some realm => realm
  | none => baseRealm key

/-- Isolated contexts are equal when both finite tables are equal. -/
@[ext]
theorem ext {left right : IsolatedContext Key Realm baseRealm Value}
    (routing_eq : left.routing = right.routing) (store_eq : left.store = right.store) :
    left = right := by
  cases left
  cases right
  cases routing_eq
  cases store_eq
  rfl

/-- Definition 29's typed `get` at the realm selected by the current routing table. -/
def get (context : IsolatedContext Key Realm baseRealm Value) (key : Key)
    (present : Coeffect.Present context.store (context.resolve key)) :
    Value (context.resolve key) :=
  Coeffect.get context.store (context.resolve key) present

/-- Definition 29's derived isolation override; the value store is inherited unchanged. -/
def isolate (context : IsolatedContext Key Realm baseRealm Value) (key : Key) (realm : Realm) :
    IsolatedContext Key Realm baseRealm Value where
  baseRealm_injective := context.baseRealm_injective
  routing := Coeffect.setAt context.routing key realm
  store := context.store

/-- Package isolation as Definition 27's derived realization. -/
def deriveIsolate (context : IsolatedContext Key Realm baseRealm Value) (key : Key)
    (realm : Realm) :
    Derived (IsolatedContext Key Realm baseRealm Value)
      (IsolatedContext Key Realm baseRealm Value) context where
  child := context.isolate key realm

@[simp]
theorem isolate_routing (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (realm : Realm) : (context.isolate key realm).routing =
    Coeffect.setAt context.routing key realm := rfl

@[simp]
theorem isolate_store (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (realm : Realm) : (context.isolate key realm).store = context.store := rfl

@[simp]
theorem resolve_isolate_same (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (realm : Realm) : (context.isolate key realm).resolve key = realm := by
  simp [resolve, isolate]

@[simp]
theorem resolve_isolate_other (context : IsolatedContext Key Realm baseRealm Value)
    (target key : Key) (realm : Realm) (different : key ≠ target) :
    (context.isolate target realm).resolve key = context.resolve key := by
  simp [resolve, isolate, Coeffect.setAt_other, different]

/-- Reassigning an already isolated key overwrites its previous realm. -/
theorem isolate_reassign (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (first second : Realm) :
    (context.isolate key first).isolate key second = context.isolate key second := by
  apply ext
  · exact Coeffect.setAt_setAt context.routing key first second
  · rfl

/-- Derived isolation overrides at distinct logical keys commute. -/
theorem isolate_commute (context : IsolatedContext Key Realm baseRealm Value)
    (left right : Key) (different : left ≠ right) (leftRealm rightRealm : Realm) :
    (context.isolate left leftRealm).isolate right rightRealm =
      (context.isolate right rightRealm).isolate left leftRealm := by
  apply ext
  · exact Coeffect.setAt_commute context.routing left right different leftRealm rightRealm
  · rfl

/-- Definition 29's `set`, with absence checked after realm resolution.

The inverse follows the paper literally: it removes the realm selected by the current routing
table. At the produced successor that table is unchanged, which proves exact recovery.
-/
def setEffect (context : IsolatedContext Key Realm baseRealm Value) (key : Key)
    (value : Value (context.resolve key))
    (absent : Coeffect.Absent context.store (context.resolve key)) :
    Cordis.Applied (IsolatedContext Key Realm baseRealm Value) context where
  after :=
    { baseRealm_injective := context.baseRealm_injective
      routing := context.routing
      store := Coeffect.setAt context.store (context.resolve key) value }
  undo := fun current ↦
    { baseRealm_injective := current.baseRealm_injective
      routing := current.routing
      store := Coeffect.removeAt current.store (current.resolve key) }
  undo_after := by
    apply ext
    · rfl
    · change
        Coeffect.removeAt
          (Coeffect.setAt context.store (context.resolve key) value)
          (context.resolve key) = context.store
      exact Coeffect.removeAt_setAt_of_absent context.store (context.resolve key) value absent

@[simp]
theorem setEffect_after_routing (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (value : Value (context.resolve key))
    (absent : Coeffect.Absent context.store (context.resolve key)) :
    (setEffect context key value absent).after.routing = context.routing := rfl

@[simp]
theorem setEffect_after_store (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (value : Value (context.resolve key))
    (absent : Coeffect.Absent context.store (context.resolve key)) :
    (setEffect context key value absent).after.store =
      Coeffect.setAt context.store (context.resolve key) value := rfl

@[simp]
theorem setEffect_undo (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (value : Value (context.resolve key))
    (absent : Coeffect.Absent context.store (context.resolve key))
    (current : IsolatedContext Key Realm baseRealm Value) :
    (setEffect context key value absent).undo current =
      { baseRealm_injective := current.baseRealm_injective
        routing := current.routing
        store := Coeffect.removeAt current.store (current.resolve key) } := rfl

@[simp]
theorem setEffect_recovers (context : IsolatedContext Key Realm baseRealm Value)
    (key : Key) (value : Value (context.resolve key))
    (absent : Coeffect.Absent context.store (context.resolve key)) :
    (setEffect context key value absent).undo (setEffect context key value absent).after =
      context :=
  (setEffect context key value absent).undo_after

end IsolatedContext

/-!
## Definitions 30--31: interception
-/

/-- The key-indexed monoids required by Definition 30. -/
structure MetadataAlgebra (Key : Type u) (Meta : Key → Type v) where
  /-- Empty metadata at each key. -/
  empty : (key : Key) → Meta key
  /-- Key-specific metadata merge. -/
  combine : (key : Key) → Meta key → Meta key → Meta key
  /-- Merge is associative at each key. -/
  combine_assoc : ∀ key left middle right,
    combine key (combine key left middle) right = combine key left (combine key middle right)
  /-- Empty metadata is a left identity. -/
  empty_combine : ∀ key value, combine key (empty key) value = value
  /-- Empty metadata is a right identity. -/
  combine_empty : ∀ key value, combine key value (empty key) = value

/-- Definition 30's interception context.

Metadata is total and context-carried. Providers form a finite dependent table, with a provider
at `key` accepting exactly `Meta key` and returning exactly `Value key`.
-/
structure InterceptionContext
    (Key : Type u) [DecidableEq Key]
    (Meta : Key → Type v) (Value : Key → Type w) where
  /-- Context-carried metadata, empty by default. -/
  metadata : (key : Key) → Meta key
  /-- Finite metadata-sensitive provider table. -/
  providers : Coeffect.Context Key (fun key ↦ Meta key → Value key)

/-- Definition 30's metadata-bearing coeffect specification. -/
abbrev InterceptionSpec
    (Key : Type u) [DecidableEq Key] (Meta : Key → Type v) :=
  Coeffect.Context Key Meta

namespace InterceptionContext

variable {Key : Type u} [DecidableEq Key]
variable {Meta : Key → Type v} {Value : Key → Type w}

/-- The interception context with empty metadata and no providers. -/
def empty (algebra : MetadataAlgebra Key Meta) : InterceptionContext Key Meta Value where
  metadata := algebra.empty
  providers := Coeffect.empty

/-- Interception contexts are equal by pointwise metadata and provider-table equality. -/
@[ext]
theorem ext {left right : InterceptionContext Key Meta Value}
    (metadata_eq : ∀ key, left.metadata key = right.metadata key)
    (providers_eq : left.providers = right.providers) : left = right := by
  cases left with
  | mk leftMetadata leftProviders =>
      cases right with
      | mk rightMetadata rightProviders =>
          have functions_eq : leftMetadata = rightMetadata := funext metadata_eq
          cases functions_eq
          cases providers_eq
          rfl

/-- Definition 31's typed `get`; context metadata is rightmost and therefore has priority. -/
def get (algebra : MetadataAlgebra Key Meta) (context : InterceptionContext Key Meta Value)
    (key : Key) (declared : Meta key)
    (present : Coeffect.Present context.providers key) : Value key :=
  present.value (algebra.combine key declared (context.metadata key))

/-- Read using the metadata stored for the key in a Definition 30 specification. -/
def getDeclared (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (spec : InterceptionSpec Key Meta)
    (key : Key) (declared : Coeffect.Present spec key)
    (present : Coeffect.Present context.providers key) : Value key :=
  context.get algebra key declared.value present

/-- Definition 31's derived metadata interception; providers are inherited unchanged. -/
def intercept (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key) (metadata : Meta key) :
    InterceptionContext Key Meta Value where
  metadata := updateAt context.metadata key
    (algebra.combine key (context.metadata key) metadata)
  providers := context.providers

/-- Package interception as Definition 27's derived realization. -/
def deriveIntercept (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key) (metadata : Meta key) :
    Derived (InterceptionContext Key Meta Value) (InterceptionContext Key Meta Value) context
    where
  child := context.intercept algebra key metadata

@[simp]
theorem intercept_metadata_same (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key) (metadata : Meta key) :
    (context.intercept algebra key metadata).metadata key =
      algebra.combine key (context.metadata key) metadata := by
  simp [intercept]

@[simp]
theorem intercept_metadata_other (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (target key : Key)
    (metadata : Meta target) (different : key ≠ target) :
    (context.intercept algebra target metadata).metadata key = context.metadata key := by
  simp [intercept, updateAt_other, different]

@[simp]
theorem intercept_providers (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key) (metadata : Meta key) :
    (context.intercept algebra key metadata).providers = context.providers := rfl

/-- Repeated interception at one key accumulates metadata in paper order. -/
theorem intercept_same (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key) (first second : Meta key) :
    (context.intercept algebra key first).intercept algebra key second =
      context.intercept algebra key (algebra.combine key first second) := by
  apply ext
  · intro candidate
    by_cases same : candidate = key
    · subst candidate
      simp [algebra.combine_assoc]
    · simp [intercept_metadata_other, same]
  · rfl

/-- Interception at distinct keys commutes. -/
theorem intercept_commute (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (left right : Key)
    (different : left ≠ right) (leftMeta : Meta left) (rightMeta : Meta right) :
    (context.intercept algebra left leftMeta).intercept algebra right rightMeta =
      (context.intercept algebra right rightMeta).intercept algebra left leftMeta := by
  apply ext
  · intro candidate
    simp only [intercept]
    rw [updateAt_other context.metadata left right _ (Ne.symm different)]
    rw [updateAt_other context.metadata right left _ different]
    exact congrFun
      (updateAt_commute context.metadata left right different
        (algebra.combine left (context.metadata left) leftMeta)
        (algebra.combine right (context.metadata right) rightMeta)) candidate
  · rfl

/-- Access after interception observes declared metadata followed by inherited and new metadata. -/
theorem get_intercept_same (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key)
    (declared added : Meta key) (present : Coeffect.Present context.providers key) :
    (context.intercept algebra key added).get algebra key declared present =
      present.value
        (algebra.combine key declared (algebra.combine key (context.metadata key) added)) := by
  simp [get, intercept]

/-- Associativity exposes the right-biased order as `(declared + context) + added`. -/
theorem get_intercept_assoc (algebra : MetadataAlgebra Key Meta)
    (context : InterceptionContext Key Meta Value) (key : Key)
    (declared added : Meta key) (present : Coeffect.Present context.providers key) :
    (context.intercept algebra key added).get algebra key declared present =
      present.value
        (algebra.combine key (algebra.combine key declared (context.metadata key)) added) := by
  rw [get_intercept_same]
  rw [algebra.combine_assoc]

/-- Definition 31's provider installation as a witnessed effect. -/
def setEffect (context : InterceptionContext Key Meta Value) (key : Key)
    (provider : Meta key → Value key) (absent : Coeffect.Absent context.providers key) :
    Cordis.Applied (InterceptionContext Key Meta Value) context where
  after :=
    { metadata := context.metadata
      providers := Coeffect.setAt context.providers key provider }
  undo := fun current ↦
    { metadata := current.metadata
      providers := Coeffect.removeAt current.providers key }
  undo_after := by
    apply ext
    · intro candidate
      rfl
    · exact Coeffect.removeAt_setAt_of_absent context.providers key provider absent

@[simp]
theorem setEffect_after_metadata (context : InterceptionContext Key Meta Value) (key : Key)
    (provider : Meta key → Value key) (absent : Coeffect.Absent context.providers key) :
    (setEffect context key provider absent).after.metadata = context.metadata := rfl

@[simp]
theorem setEffect_after_providers (context : InterceptionContext Key Meta Value) (key : Key)
    (provider : Meta key → Value key) (absent : Coeffect.Absent context.providers key) :
    (setEffect context key provider absent).after.providers =
      Coeffect.setAt context.providers key provider := rfl

@[simp]
theorem setEffect_recovers (context : InterceptionContext Key Meta Value) (key : Key)
    (provider : Meta key → Value key) (absent : Coeffect.Absent context.providers key) :
    (setEffect context key provider absent).undo (setEffect context key provider absent).after =
      context :=
  (setEffect context key provider absent).undo_after

end InterceptionContext

/-!
## Definition 32: finite unfoldings of the unified context equation
-/

/-- One exact unfolding of `Gamma x (Gamma -> Gamma) x Sigma`. -/
structure Layer (Prior : Type u) (Sigma : Type v) where
  /-- The current prior-level context. -/
  current : Prior
  /-- The accumulator recovering prior-level effects. -/
  recover : Prior → Prior
  /-- The integrated coeffect context. -/
  coeffects : Sigma

/-- Exact finite-depth approximants to Definition 32's recursive equation. -/
def Approximation (Base Sigma : Type u) : Nat → Type u
  | 0 => Base
  | depth + 1 => Layer (Approximation Base Sigma depth) Sigma

/-- Depth zero is exactly the selected base context. -/
theorem approximation_zero (Base Sigma : Type u) : Approximation Base Sigma 0 = Base := rfl

/-- Each successor depth is exactly one displayed Definition 32 layer. -/
theorem approximation_succ (Base Sigma : Type u) (depth : Nat) :
    Approximation Base Sigma (depth + 1) = Layer (Approximation Base Sigma depth) Sigma := rfl

namespace Layer

variable {Prior : Type u} {Sigma : Type v}

/-- Record a witnessed effect on `current`, extending recovery in LIFO order. -/
def record (layer : Layer Prior Sigma) (step : Cordis.Applied Prior layer.current) :
    Layer Prior Sigma where
  current := step.after
  recover := layer.recover ∘ step.undo
  coeffects := layer.coeffects

@[simp]
theorem record_current (layer : Layer Prior Sigma)
    (step : Cordis.Applied Prior layer.current) : (layer.record step).current = step.after := rfl

@[simp]
theorem record_coeffects (layer : Layer Prior Sigma)
    (step : Cordis.Applied Prior layer.current) :
    (layer.record step).coeffects = layer.coeffects := rfl

/-- Recording an effect preserves the recovery endpoint represented by the accumulator. -/
theorem record_recovers (layer : Layer Prior Sigma)
    (step : Cordis.Applied Prior layer.current) :
    (layer.record step).recover (layer.record step).current = layer.recover layer.current := by
  exact congrArg layer.recover step.undo_after

/-- Two recorded effects recover in reverse order through the accumulated function. -/
theorem record_twice_recovers (layer : Layer Prior Sigma)
    (first : Cordis.Applied Prior layer.current)
    (second : Cordis.Applied Prior (layer.record first).current) :
    ((layer.record first).record second).recover
        ((layer.record first).record second).current = layer.recover layer.current := by
  exact Eq.trans (record_recovers (layer.record first) second) (record_recovers layer first)

/-- Lift a witnessed coeffect transition to the unified layer without changing prior state. -/
def liftCoeffect (layer : Layer Prior Sigma)
    (step : Cordis.Applied Sigma layer.coeffects) : Cordis.Applied (Layer Prior Sigma) layer where
  after :=
    { current := layer.current
      recover := layer.recover
      coeffects := step.after }
  undo := fun current ↦
    { current := current.current
      recover := current.recover
      coeffects := step.undo current.coeffects }
  undo_after := by
    cases layer
    simp only
    rw [step.undo_after]

@[simp]
theorem liftCoeffect_after_current (layer : Layer Prior Sigma)
    (step : Cordis.Applied Sigma layer.coeffects) :
    (layer.liftCoeffect step).after.current = layer.current := rfl

@[simp]
theorem liftCoeffect_after_recover (layer : Layer Prior Sigma)
    (step : Cordis.Applied Sigma layer.coeffects) :
    (layer.liftCoeffect step).after.recover = layer.recover := rfl

@[simp]
theorem liftCoeffect_after_coeffects (layer : Layer Prior Sigma)
    (step : Cordis.Applied Sigma layer.coeffects) :
    (layer.liftCoeffect step).after.coeffects = step.after := rfl

@[simp]
theorem liftCoeffect_recovers (layer : Layer Prior Sigma)
    (step : Cordis.Applied Sigma layer.coeffects) :
    (layer.liftCoeffect step).undo (layer.liftCoeffect step).after = layer :=
  (layer.liftCoeffect step).undo_after

end Layer

/-- Add one finite unfolding as a derived child of the previous depth. -/
def pushApproximation {Base Sigma : Type u} {depth : Nat}
    (parent : Approximation Base Sigma depth)
    (recover : Approximation Base Sigma depth → Approximation Base Sigma depth)
    (coeffects : Sigma) :
    Derived (Approximation Base Sigma depth) (Approximation Base Sigma (depth + 1)) parent where
  child :=
    { current := parent
      recover
      coeffects }

@[simp]
theorem pushApproximation_current {Base Sigma : Type u} {depth : Nat}
    (parent : Approximation Base Sigma depth)
    (recover : Approximation Base Sigma depth → Approximation Base Sigma depth)
    (coeffects : Sigma) :
    (pushApproximation parent recover coeffects).child.current = parent := rfl

@[simp]
theorem pushApproximation_discard {Base Sigma : Type u} {depth : Nat}
    (parent : Approximation Base Sigma depth)
    (recover : Approximation Base Sigma depth → Approximation Base Sigma depth)
    (coeffects : Sigma) :
    (pushApproximation parent recover coeffects).discard = parent := rfl

/-!
## Heterogeneous executable examples
-/

namespace Example

namespace Isolation

/-- Two logical dependency keys. -/
inductive Key where
  | counter
  | label
deriving DecidableEq, Repr

/-- Base and tenant-specific realms. -/
inductive Realm where
  | counterBase
  | labelBase
  | counterTenant
  | labelTenant
deriving DecidableEq, Repr

/-- Each logical key has a distinguished fallback realm. -/
def baseRealm : Key → Realm
  | .counter => .counterBase
  | .label => .labelBase

/-- Realm selection determines the stored value type. -/
def Value : Realm → Type
  | .counterBase => Nat
  | .counterTenant => Nat
  | .labelBase => String
  | .labelTenant => String

abbrev Context := IsolatedContext Key Realm baseRealm Value

def baseCounter : Value .counterBase := show Nat from 1
def tenantCounter : Value .counterTenant := show Nat from 99
def baseLabel : Value .labelBase := show String from "base"
def tenantLabel : Value .labelTenant := show String from "tenant"

/-- The shared store contains values at four differently typed realms. -/
def store : Coeffect.Context Realm Value :=
  let first := Coeffect.setAt Coeffect.empty .counterBase baseCounter
  let second := Coeffect.setAt first .counterTenant tenantCounter
  let third := Coeffect.setAt second .labelBase baseLabel
  Coeffect.setAt third .labelTenant tenantLabel

/-- With no routing overrides, logical keys resolve through `baseRealm`. -/
def root : Context where
  baseRealm_injective := by
    intro left right same
    cases left <;> cases right <;> simp [baseRealm] at same ⊢
  routing := Coeffect.empty
  store := store

/-- The counter key resolves to the `Nat`-valued base realm. -/
def rootCounterPresent : Coeffect.Present root.store (root.resolve .counter) where
  value := baseCounter
  lookup_eq := by
    change store .counterBase = some baseCounter
    simp [store]

/-- The label key resolves to the `String`-valued base realm. -/
def rootLabelPresent : Coeffect.Present root.store (root.resolve .label) where
  value := baseLabel
  lookup_eq := by
    change store .labelBase = some baseLabel
    simp [store]

/-- A derived child redirects only the logical counter key. -/
def tenant : Context := root.isolate .counter .counterTenant

/-- The redirected counter resolves to the tenant's `Nat`. -/
def tenantCounterPresent : Coeffect.Present tenant.store (tenant.resolve .counter) where
  value := tenantCounter
  lookup_eq := by
    change store .counterTenant = some tenantCounter
    simp [store]

example : root.resolve .counter = .counterBase := rfl
example : tenant.resolve .counter = .counterTenant := by simp [tenant]
example : root.get .counter rootCounterPresent = baseCounter := rfl
example : root.get .label rootLabelPresent = baseLabel := rfl
example : tenant.get .counter tenantCounterPresent = tenantCounter := rfl
example : tenant.store = root.store := rfl

/-- Discarding the isolated child returns the exact indexed parent. -/
example : (root.deriveIsolate .counter .counterTenant).discard = root := rfl

/-- A blank isolated context for checking Definition 29's reversible `set`. -/
def blank : Context where
  baseRealm_injective := root.baseRealm_injective
  routing := Coeffect.empty
  store := Coeffect.empty

theorem blankCounterAbsent : Coeffect.Absent blank.store (blank.resolve .counter) := by
  constructor
  rfl

def installCounter : Cordis.Applied Context blank :=
  blank.setEffect .counter baseCounter blankCounterAbsent

def installCounterInPlace : InPlace Context blank where
  applied := installCounter

example : installCounter.undo installCounter.after = blank := installCounter.undo_after
example : installCounterInPlace.recover = blank := by simp

end Isolation

namespace Interception

/-- Two keys with different metadata and output types. -/
inductive Key where
  | count
  | text
deriving DecidableEq, Repr

def Meta : Key → Type
  | .count => Nat
  | .text => String

def Value : Key → Type
  | .count => Nat
  | .text => String

/-- Empty metadata specialized at each dependent key. -/
def metaEmpty : (key : Key) → Meta key
  | .count => show Nat from 0
  | .text => show String from ""

/-- Key-specific metadata merge without relying on type-class search through `Meta`. -/
def metaCombine : (key : Key) → Meta key → Meta key → Meta key
  | .count => fun left right ↦ (show Nat from left) + (show Nat from right)
  | .text => fun left right ↦ (show String from left) ++ (show String from right)

/-- Addition and string concatenation form the two key-specific metadata monoids. -/
def algebra : MetadataAlgebra Key Meta where
  empty := metaEmpty
  combine := metaCombine
  combine_assoc := by
    intro key left middle right
    cases key
    · exact Nat.add_assoc left middle right
    · exact String.append_assoc
  empty_combine := by
    intro key value
    cases key with
    | count =>
        change (0 : Nat) + (show Nat from value) = value
        exact Nat.zero_add value
    | text =>
        change "" ++ (show String from value) = value
        exact String.empty_append
  combine_empty := by
    intro key value
    cases key with
    | count =>
        change (show Nat from value) + 0 = value
        exact Nat.add_zero value
    | text =>
        change (show String from value) ++ "" = value
        exact String.append_empty

abbrev Context := InterceptionContext Key Meta Value

def countProvider : Meta .count → Value .count :=
  fun metadata ↦ (show Nat from metadata) * 2

def textProvider : Meta .text → Value .text :=
  fun metadata ↦ "value:" ++ (show String from metadata)

def providers : Coeffect.Context Key (fun key ↦ Meta key → Value key) :=
  Coeffect.setAt (Coeffect.setAt Coeffect.empty .count countProvider) .text textProvider

def root : Context where
  metadata := algebra.empty
  providers := providers

def countPresent : Coeffect.Present root.providers .count where
  value := countProvider
  lookup_eq := by simp [root, providers]

def textPresent : Coeffect.Present root.providers .text where
  value := textProvider
  lookup_eq := by simp [root, providers]

def declaredCount : Meta .count := show Nat from 3
def addedCount : Meta .count := show Nat from 4
def declaredText : Meta .text := show String from "declared-"
def addedText : Meta .text := show String from "outer"
def countSix : Value .count := show Nat from 6
def countFourteen : Value .count := show Nat from 14
def textResult : Value .text := show String from "value:declared-outer"

/-- The Definition 30 specification is a finite dependent metadata map. -/
def spec : InterceptionSpec Key Meta :=
  Coeffect.setAt Coeffect.empty .count declaredCount

def declaredCountPresent : Coeffect.Present spec .count where
  value := declaredCount
  lookup_eq := by simp [spec]

example : root.get algebra .count declaredCount countPresent = countSix := rfl
example : root.getDeclared algebra spec .count declaredCountPresent countPresent = countSix := rfl

/-- Context metadata is merged after component-declared metadata. -/
def counted : Context := root.intercept algebra .count addedCount

example : counted.get algebra .count declaredCount countPresent = countFourteen := rfl

/-- The second key independently exercises string metadata and string output. -/
def texted : Context := root.intercept algebra .text addedText

example : texted.get algebra .text declaredText textPresent = textResult := rfl
example : counted.providers = root.providers := rfl
example : (root.deriveIntercept algebra .count addedCount).discard = root := rfl

/-- A blank interception context for checking provider installation recovery. -/
def blank : Context := InterceptionContext.empty algebra

theorem blankCountAbsent : Coeffect.Absent blank.providers .count := by
  constructor
  rfl

def installCountProvider : Cordis.Applied Context blank :=
  blank.setEffect .count countProvider blankCountAbsent

example : installCountProvider.undo installCountProvider.after = blank :=
  installCountProvider.undo_after

end Interception

namespace Unified

inductive Key where
  | number
deriving DecidableEq, Repr

def Value : Key → Type
  | .number => Nat

abbrev Sigma := Coeffect.Context Key Value

def sigma : Sigma := Coeffect.empty

/-- A depth-one finite unfolding with an identity accumulator. -/
def layer : Layer Nat Sigma where
  current := 10
  recover := id
  coeffects := sigma

def replacement : Cordis.Applied Nat layer.current := Cordis.Effect.replace 13 layer.current

example : (layer.record replacement).recover (layer.record replacement).current = 10 := by
  exact layer.record_recovers replacement

theorem numberAbsent : Coeffect.Absent layer.coeffects .number := by
  constructor
  rfl

def numberValue : Value .number := show Nat from 21

def installNumber : Cordis.Applied Sigma layer.coeffects :=
  Coeffect.setEffect layer.coeffects .number numberValue numberAbsent

/-- A coeffect transition lifts without changing the prior state or accumulator. -/
def liftedNumber : Cordis.Applied (Layer Nat Sigma) layer := layer.liftCoeffect installNumber

example : liftedNumber.after.current = layer.current := rfl
example : liftedNumber.after.recover = layer.recover := rfl
example : liftedNumber.undo liftedNumber.after = layer := liftedNumber.undo_after

/-- Depth zero is the selected base type; pushing produces the exact depth-one equation. -/
def depthZero : Approximation Nat Sigma 0 := show Nat from 10

def depthOne : Derived (Approximation Nat Sigma 0) (Approximation Nat Sigma 1) depthZero :=
  pushApproximation depthZero id sigma

example : depthOne.child.current = depthZero := rfl
example : depthOne.discard = depthZero := rfl

end Unified

end Example

end Cordis.UnifiedContext
