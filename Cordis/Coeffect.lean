import Cordis.Effect
import Std

/-!
# Finite reactive coeffects

This module gives a bounded Lean mechanization of Definitions 22--26 of the CORDIS paper
at revision `948a07b369c62adb3b12e102458be5c18dfb69b9`. A `Context` is a finite dependent
map, so a key determines the type of the value stored there. Presence and absence are
proof-carrying preconditions: `get` can only be called with a `Present` witness, while
`setEffect` can only install a binding proved absent. Its inverse removes that binding; it
does not restore a captured copy of the whole predecessor.

`CoeffectAt` records the equivalence and typed local-operation portion of Definition 24.
`Spec` is the finite, duplicate-free fragment of Definition 25, and `notify` executes the
three-way classification of Definition 26. The results here are local reactive coeffect
semantics. They do not mechanize Definitions 27--42, realm resolution, components, fibers,
control-flow semantics, or the paper's global spatial and temporal metatheory.
-/

namespace Cordis.Coeffect

universe u v w

section Context

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

/-- Definition 22: a finite dependent map from keys to their key-indexed value types.

Finiteness is carried as a proposition, leaving contextual equality extensional in `lookup`.
The support list is only a certificate and is not observable data.
-/
structure Context (Key : Type u) [DecidableEq Key] (Value : Key → Type v) where
  /-- The dependent map underlying the context. -/
  lookup : (key : Key) → Option (Value key)
  /-- A finite list covers every present key. -/
  finite : ∃ support : List Key, ∀ key, (lookup key).isSome = true → key ∈ support

instance : CoeFun (Context Key Value) (fun _ ↦ (key : Key) → Option (Value key)) where
  coe := Context.lookup

/-- Contexts are equal when all dependent lookups are equal. -/
@[ext]
theorem Context.ext {left right : Context Key Value}
    (lookup_eq : ∀ key, left key = right key) : left = right := by
  cases left with
  | mk leftLookup leftFinite =>
      cases right with
      | mk rightLookup rightFinite =>
          have functions_eq : leftLookup = rightLookup := funext lookup_eq
          cases functions_eq
          rfl

/-- The empty finite context. -/
def empty : Context Key Value where
  lookup := fun _ ↦ none
  finite := by
    exact ⟨[], by simp⟩

/-- Replace or introduce one dependent binding and leave all other keys unchanged. -/
def setAt (context : Context Key Value) (target : Key) (value : Value target) :
    Context Key Value where
  lookup := fun key ↦
    if same : key = target then
      same.symm ▸ some value
    else
      context key
  finite := by
    obtain ⟨support, covers⟩ := context.finite
    refine ⟨target :: support, ?_⟩
    intro key present
    by_cases same : key = target
    · exact same ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem target (covers key (by simpa [same] using present))

/-- Remove one binding and leave all other keys unchanged. -/
def removeAt (context : Context Key Value) (target : Key) : Context Key Value where
  lookup := fun key ↦
    if key = target then none else context key
  finite := by
    obtain ⟨support, covers⟩ := context.finite
    refine ⟨support, ?_⟩
    intro key present
    by_cases same : key = target
    · simp [same] at present
    · exact covers key (by simpa [same] using present)

/-- A witness that `key` is bound, carrying the value at exactly that key's type. -/
structure Present (context : Context Key Value) (key : Key) where
  /-- The value found at the indexed key. -/
  value : Value key
  /-- The value is the binding stored by the context. -/
  lookup_eq : context key = some value

/-- A witness that `key` is not bound. -/
structure Absent (context : Context Key Value) (key : Key) : Prop where
  /-- The dependent lookup is empty. -/
  lookup_eq : context key = none

/-- Definition 23's typed `get`; absence is unrepresentable at this call site. -/
def get (context : Context Key Value) (key : Key) (present : Present context key) : Value key :=
  present.value

@[simp]
theorem get_lookup (context : Context Key Value) (key : Key) (present : Present context key) :
    context key = some (get context key present) := by
  exact present.lookup_eq

@[simp]
theorem empty_lookup (key : Key) : (empty : Context Key Value) key = none := rfl

@[simp]
theorem setAt_same (context : Context Key Value) (target : Key) (value : Value target) :
    setAt context target value target = some value := by
  simp [setAt]

@[simp]
theorem setAt_other (context : Context Key Value) (target key : Key) (value : Value target)
    (different : key ≠ target) : setAt context target value key = context key := by
  simp [setAt, different]

@[simp]
theorem removeAt_same (context : Context Key Value) (target : Key) :
    removeAt context target target = none := by
  simp [removeAt]

@[simp]
theorem removeAt_other (context : Context Key Value) (target key : Key)
    (different : key ≠ target) : removeAt context target key = context key := by
  simp [removeAt, different]

/-- Reinstalling the witnessed value at an already-present key changes nothing. -/
theorem setAt_present (context : Context Key Value) (key : Key)
    (present : Present context key) : setAt context key present.value = context := by
  apply Context.ext
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    rw [setAt_same]
    exact present.lookup_eq.symm
  · simp [setAt_other, same]

/-- A later insertion at the same key overwrites the earlier insertion. -/
theorem setAt_setAt (context : Context Key Value) (key : Key)
    (first second : Value key) :
    setAt (setAt context key first) key second = setAt context key second := by
  apply Context.ext
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    simp
  · simp [setAt_other, same]

/-- The concrete remove inverse exactly restores an absent predecessor after insertion. -/
theorem removeAt_setAt_of_absent (context : Context Key Value) (key : Key)
    (value : Value key) (absent : Absent context key) :
    removeAt (setAt context key value) key = context := by
  apply Context.ext
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    rw [removeAt_same]
    exact absent.lookup_eq.symm
  · simp [removeAt_other, setAt_other, same]

/-- Reinstalling the removed witnessed binding exactly restores a present predecessor. -/
theorem setAt_removeAt_of_present (context : Context Key Value) (key : Key)
    (present : Present context key) :
    setAt (removeAt context key) key present.value = context := by
  apply Context.ext
  intro candidate
  by_cases same : candidate = key
  · subst candidate
    rw [setAt_same]
    exact present.lookup_eq.symm
  · simp [removeAt_other, setAt_other, same]

/-- Insertions at distinct dependent keys commute extensionally. -/
theorem setAt_commute (context : Context Key Value) (left right : Key)
    (different : left ≠ right) (leftValue : Value left) (rightValue : Value right) :
    setAt (setAt context left leftValue) right rightValue =
      setAt (setAt context right rightValue) left leftValue := by
  apply Context.ext
  intro candidate
  by_cases isLeft : candidate = left
  · subst candidate
    simp [different]
  · by_cases isRight : candidate = right
    · subst candidate
      simp [Ne.symm different]
    · simp [setAt_other, isLeft, isRight]

/-- Removals at distinct keys commute extensionally. -/
theorem removeAt_commute (context : Context Key Value) (left right : Key) :
    removeAt (removeAt context left) right = removeAt (removeAt context right) left := by
  apply Context.ext
  intro candidate
  by_cases isLeft : candidate = left <;>
    by_cases isRight : candidate = right <;>
      simp [removeAt, isLeft, isRight]

/-- Insertion and removal at distinct keys commute extensionally. -/
theorem setAt_removeAt_commute (context : Context Key Value) (setKey removeKey : Key)
    (different : setKey ≠ removeKey) (value : Value setKey) :
    removeAt (setAt context setKey value) removeKey =
      setAt (removeAt context removeKey) setKey value := by
  apply Context.ext
  intro candidate
  by_cases isSet : candidate = setKey
  · subst candidate
    simp [different]
  · by_cases isRemove : candidate = removeKey
    · subst candidate
      simp [Ne.symm different]
    · simp [setAt_other, removeAt_other, isSet, isRemove]

/-- Definition 23's `set` as a witnessed effect with a concrete, local remove inverse. -/
def setEffect (context : Context Key Value) (key : Key) (value : Value key)
    (absent : Absent context key) : Cordis.Applied (Context Key Value) context where
  after := setAt context key value
  undo := fun current ↦ removeAt current key
  undo_after := removeAt_setAt_of_absent context key value absent

/-- A typed removal effect whose inverse reinstalls only the witnessed prior binding. -/
def removeEffect (context : Context Key Value) (key : Key) (present : Present context key) :
    Cordis.Applied (Context Key Value) context where
  after := removeAt context key
  undo := fun current ↦ setAt current key present.value
  undo_after := setAt_removeAt_of_present context key present

@[simp]
theorem setEffect_after (context : Context Key Value) (key : Key) (value : Value key)
    (absent : Absent context key) :
    (setEffect context key value absent).after = setAt context key value := rfl

@[simp]
theorem setEffect_undo (context : Context Key Value) (key : Key) (value : Value key)
    (absent : Absent context key) (current : Context Key Value) :
    (setEffect context key value absent).undo current = removeAt current key := rfl

@[simp]
theorem setEffect_recovers (context : Context Key Value) (key : Key) (value : Value key)
    (absent : Absent context key) :
    (setEffect context key value absent).undo (setEffect context key value absent).after =
      context :=
  (setEffect context key value absent).undo_after

@[simp]
theorem removeEffect_recovers (context : Context Key Value) (key : Key)
    (present : Present context key) :
    (removeEffect context key present).undo (removeEffect context key present).after = context :=
  (removeEffect context key present).undo_after

end Context

/-!
## Typed local operations (Definition 24)

The paper gives each key an equivalence relation and a family of typed operations. The bounded
record below keeps those obligations explicit. Its local effects recover by equality, while the
four `respects` fields state the additional observational laws required by Definition 24.
-/

/-- Definition 24's coeffect payload at one key. -/
structure CoeffectAt (State : Type v) where
  /-- The observational equivalence used for values at this key. -/
  equivalence : Setoid State
  /-- The set of local operations, represented as a type. -/
  Op : Type w
  /-- Each operation chooses its own argument type. -/
  Input : Op → Type w
  /-- Each operation chooses its own outcome type. -/
  Outcome : Op → Type w
  /-- The domain of the operation's finite-state transition. -/
  Enabled : (op : Op) → Input op → State → Prop
  /-- Operation domains are executable in this bounded model. -/
  enabledDecidable : (op : Op) → (input : Input op) → (state : State) →
    Decidable (Enabled op input state)
  /-- A defined operation returns a witnessed local effect and its typed outcome. -/
  run : (op : Op) → (input : Input op) → (before : State) → Enabled op input before →
    Cordis.Applied State before × Outcome op
  /-- Related values agree on whether the operation is defined. -/
  enabled_respects : ∀ op input {left right}, equivalence.r left right →
    (Enabled op input left ↔ Enabled op input right)
  /-- Running at related values produces related successors. -/
  after_respects : ∀ op input {left right} (_related : equivalence.r left right)
    (leftEnabled : Enabled op input left) (rightEnabled : Enabled op input right),
    equivalence.r (run op input left leftEnabled).1.after
      (run op input right rightEnabled).1.after
  /-- The paired inverses map related current values to related values. -/
  undo_respects : ∀ op input {left right} (_related : equivalence.r left right)
    (leftEnabled : Enabled op input left) (rightEnabled : Enabled op input right)
    {leftCurrent rightCurrent}, equivalence.r leftCurrent rightCurrent →
    equivalence.r ((run op input left leftEnabled).1.undo leftCurrent)
      ((run op input right rightEnabled).1.undo rightCurrent)
  /-- Running at related values produces equal typed outcomes. -/
  outcome_respects : ∀ op input {left right} (_related : equivalence.r left right)
    (leftEnabled : Enabled op input left) (rightEnabled : Enabled op input right),
    (run op input left leftEnabled).2 = (run op input right rightEnabled).2

namespace CoeffectAt

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

/-- Lift a Definition 24 local operation to its binding in the whole context.

The inverse inspects the current binding and applies only the local inverse at `key`. The `none`
branch totalizes the paper's locally-defined inverse away from its specified successor; the
recovery theorem follows through the `some` branch produced by this very operation.
-/
def lift {key : Key} (coeffect : CoeffectAt (Value key)) (op : coeffect.Op)
    (input : coeffect.Input op) (context : Context Key Value)
    (present : Present context key) (enabled : coeffect.Enabled op input present.value) :
    Cordis.Applied (Context Key Value) context × coeffect.Outcome op :=
  let result := coeffect.run op input present.value enabled
  ({ after := setAt context key result.1.after
     undo := fun current ↦
       match current key with
       | none => current
       | some value => setAt current key (result.1.undo value)
     undo_after := by
       simp only [setAt_same]
       rw [result.1.undo_after]
       rw [setAt_setAt]
       exact setAt_present context key present }, result.2)

@[simp]
theorem lift_after {key : Key} (coeffect : CoeffectAt (Value key)) (op : coeffect.Op)
    (input : coeffect.Input op) (context : Context Key Value)
    (present : Present context key) (enabled : coeffect.Enabled op input present.value) :
    (lift coeffect op input context present enabled).1.after =
      setAt context key (coeffect.run op input present.value enabled).1.after := rfl

@[simp]
theorem lift_recovers {key : Key} (coeffect : CoeffectAt (Value key)) (op : coeffect.Op)
    (input : coeffect.Input op) (context : Context Key Value)
    (present : Present context key) (enabled : coeffect.Enabled op input present.value) :
    (lift coeffect op input context present enabled).1.undo
        (lift coeffect op input context present enabled).1.after = context :=
  (lift coeffect op input context present enabled).1.undo_after

end CoeffectAt

/-!
## Finite specifications and exact notifications (Definitions 25--26)
-/

section Notification

variable {Key : Type u} [DecidableEq Key] {Value : Key → Type v}

/-- A finite coeffect specification with duplicate-free keys. -/
structure Spec (Key : Type u) [DecidableEq Key] where
  /-- Dependencies declared by the component. -/
  keys : List Key
  /-- A dependency is declared at most once. -/
  nodup : keys.Nodup

/-- Equation (24)'s satisfaction predicate, executed over a finite specification. -/
def Satisfies (context : Context Key Value) (spec : Spec Key) : Prop :=
  spec.keys.all (fun key ↦ (context key).isSome) = true

instance (context : Context Key Value) (spec : Spec Key) : Decidable (Satisfies context spec) :=
  by
    unfold Satisfies
    infer_instance

/-- Satisfaction is exactly presence of every key in the finite specification. -/
theorem satisfies_iff (context : Context Key Value) (spec : Spec Key) :
    Satisfies context spec ↔
      ∀ key, key ∈ spec.keys → (context key).isSome = true := by
  simp [Satisfies]

/-- The three exact cases of Definition 26. -/
inductive Notification where
  /-- Satisfaction changed from false to true. -/
  | activating
  /-- Satisfaction changed from true to false. -/
  | deactivating
  /-- Satisfaction status did not change. -/
  | neutral
deriving DecidableEq, Repr

/-- Definition 26's executable notification classifier. -/
def notify (spec : Spec Key) (before after : Context Key Value) : Notification :=
  if Satisfies before spec then
    if Satisfies after spec then .neutral else .deactivating
  else if Satisfies after spec then .activating else .neutral

/-- A typed applied effect exposes exactly the transition classified by `notify`. -/
def notifyApplied (spec : Spec Key) {before : Context Key Value}
    (applied : Cordis.Applied (Context Key Value) before) : Notification :=
  notify spec before applied.after

/-- Activation is exact, not an approximation based on which key changed. -/
theorem activating_iff (spec : Spec Key) (before after : Context Key Value) :
    notify spec before after = .activating ↔
      ¬Satisfies before spec ∧ Satisfies after spec := by
  by_cases beforeSat : Satisfies before spec <;>
    by_cases afterSat : Satisfies after spec <;>
      simp [notify, beforeSat, afterSat]

/-- Deactivation is exact, not an approximation based on which key changed. -/
theorem deactivating_iff (spec : Spec Key) (before after : Context Key Value) :
    notify spec before after = .deactivating ↔
      Satisfies before spec ∧ ¬Satisfies after spec := by
  by_cases beforeSat : Satisfies before spec <;>
    by_cases afterSat : Satisfies after spec <;>
      simp [notify, beforeSat, afterSat]

/-- Neutrality is exactly preservation of the satisfaction status. -/
theorem neutral_iff (spec : Spec Key) (before after : Context Key Value) :
    notify spec before after = .neutral ↔
      (Satisfies before spec ↔ Satisfies after spec) := by
  by_cases beforeSat : Satisfies before spec <;>
    by_cases afterSat : Satisfies after spec <;>
      simp [notify, beforeSat, afterSat]

/-- Every transition receives one of the three notification constructors. -/
theorem notify_trichotomy (spec : Spec Key) (before after : Context Key Value) :
    notify spec before after = .activating ∨
      notify spec before after = .deactivating ∨
      notify spec before after = .neutral := by
  cases classified : notify spec before after with
  | activating => exact Or.inl rfl
  | deactivating => exact Or.inr (Or.inl rfl)
  | neutral => exact Or.inr (Or.inr rfl)

/-- Exhaustiveness associates every constructor with its exact satisfaction facts. -/
theorem notify_exhaustive (spec : Spec Key) (before after : Context Key Value) :
    (¬Satisfies before spec ∧ Satisfies after spec ∧
      notify spec before after = .activating) ∨
    (Satisfies before spec ∧ ¬Satisfies after spec ∧
      notify spec before after = .deactivating) ∨
    ((Satisfies before spec ↔ Satisfies after spec) ∧
      notify spec before after = .neutral) := by
  by_cases beforeSat : Satisfies before spec <;>
    by_cases afterSat : Satisfies after spec
  · exact Or.inr (Or.inr ⟨Iff.intro (fun _ ↦ afterSat) (fun _ ↦ beforeSat),
      (neutral_iff spec before after).2 (Iff.intro (fun _ ↦ afterSat) (fun _ ↦ beforeSat))⟩)
  · exact Or.inr (Or.inl ⟨beforeSat, afterSat,
      (deactivating_iff spec before after).2 ⟨beforeSat, afterSat⟩⟩)
  · exact Or.inl ⟨beforeSat, afterSat,
      (activating_iff spec before after).2 ⟨beforeSat, afterSat⟩⟩
  · exact Or.inr (Or.inr ⟨Iff.intro (fun satisfied ↦ False.elim (beforeSat satisfied))
      (fun satisfied ↦ False.elim (afterSat satisfied)),
      (neutral_iff spec before after).2
        (Iff.intro (fun satisfied ↦ False.elim (beforeSat satisfied))
          (fun satisfied ↦ False.elim (afterSat satisfied)))⟩)

/-- Exact activation classification specialized to a typed applied effect. -/
theorem notifyApplied_activating_iff (spec : Spec Key) {before : Context Key Value}
    (applied : Cordis.Applied (Context Key Value) before) :
    notifyApplied spec applied = .activating ↔
      ¬Satisfies before spec ∧ Satisfies applied.after spec :=
  activating_iff spec before applied.after

/-- Exact deactivation classification specialized to a typed applied effect. -/
theorem notifyApplied_deactivating_iff (spec : Spec Key) {before : Context Key Value}
    (applied : Cordis.Applied (Context Key Value) before) :
    notifyApplied spec applied = .deactivating ↔
      Satisfies before spec ∧ ¬Satisfies applied.after spec :=
  deactivating_iff spec before applied.after

/-- Setting an undeclared key cannot change satisfaction. -/
theorem satisfies_setAt_iff_of_not_mem (spec : Spec Key) (context : Context Key Value)
    (key : Key) (value : Value key) (notRequired : key ∉ spec.keys) :
    Satisfies (setAt context key value) spec ↔ Satisfies context spec := by
  simp only [satisfies_iff]
  constructor
  · intro satisfied candidate required
    have different : candidate ≠ key := by
      intro same
      subst candidate
      exact notRequired required
    simpa [setAt_other, different] using satisfied candidate required
  · intro satisfied candidate required
    have different : candidate ≠ key := by
      intro same
      subst candidate
      exact notRequired required
    simpa [setAt_other, different] using satisfied candidate required

/-- Removing an undeclared key cannot change satisfaction. -/
theorem satisfies_removeAt_iff_of_not_mem (spec : Spec Key) (context : Context Key Value)
    (key : Key) (notRequired : key ∉ spec.keys) :
    Satisfies (removeAt context key) spec ↔ Satisfies context spec := by
  simp only [satisfies_iff]
  constructor
  · intro satisfied candidate required
    have different : candidate ≠ key := by
      intro same
      subst candidate
      exact notRequired required
    simpa [removeAt_other, different] using satisfied candidate required
  · intro satisfied candidate required
    have different : candidate ≠ key := by
      intro same
      subst candidate
      exact notRequired required
    simpa [removeAt_other, different] using satisfied candidate required

/-- Setting a key outside the specification is classified as neutral. -/
theorem setting_unrelated_key_is_neutral (spec : Spec Key) (context : Context Key Value)
    (key : Key) (value : Value key) (notRequired : key ∉ spec.keys) :
    notify spec context (setAt context key value) = .neutral := by
  apply (neutral_iff spec context (setAt context key value)).2
  exact (satisfies_setAt_iff_of_not_mem spec context key value notRequired).symm

/-- Removing a key outside the specification is classified as neutral. -/
theorem removing_unrelated_key_is_neutral (spec : Spec Key) (context : Context Key Value)
    (key : Key) (notRequired : key ∉ spec.keys) :
    notify spec context (removeAt context key) = .neutral := by
  apply (neutral_iff spec context (removeAt context key)).2
  exact (satisfies_removeAt_iff_of_not_mem spec context key notRequired).symm

/-- Installing the unique missing required key activates the specification. -/
theorem setting_last_missing_key_activates (spec : Spec Key) (context : Context Key Value)
    (key : Key) (value : Value key) (required : key ∈ spec.keys)
    (absent : Absent context key)
    (othersPresent : ∀ candidate, candidate ∈ spec.keys → candidate ≠ key →
      (context candidate).isSome = true) :
    notify spec context (setAt context key value) = .activating := by
  apply (activating_iff spec context (setAt context key value)).2
  constructor
  · intro satisfied
    have targetPresent := (satisfies_iff context spec).1 satisfied key required
    simp [absent.lookup_eq] at targetPresent
  · apply (satisfies_iff (setAt context key value) spec).2
    intro candidate candidateRequired
    by_cases same : candidate = key
    · subst candidate
      simp
    · simpa [setAt_other, same] using
        othersPresent candidate candidateRequired same

/-- Removing a present required key deactivates when all other requirements are present. -/
theorem removing_required_key_deactivates (spec : Spec Key) (context : Context Key Value)
    (key : Key) (required : key ∈ spec.keys) (present : Present context key)
    (othersPresent : ∀ candidate, candidate ∈ spec.keys → candidate ≠ key →
      (context candidate).isSome = true) :
    notify spec context (removeAt context key) = .deactivating := by
  apply (deactivating_iff spec context (removeAt context key)).2
  constructor
  · apply (satisfies_iff context spec).2
    intro candidate candidateRequired
    by_cases same : candidate = key
    · subst candidate
      simp [present.lookup_eq]
    · exact othersPresent candidate candidateRequired same
  · intro satisfied
    have targetPresent := (satisfies_iff (removeAt context key) spec).1 satisfied key required
    simp at targetPresent

end Notification

/-!
## Heterogeneous executable example
-/

namespace Example

/-- Two keys selecting genuinely different value types. -/
inductive Key where
  | counter
  | label
deriving DecidableEq, Repr

/-- The value type depends on the selected key. -/
def Value : Key → Type
  | .counter => Nat
  | .label => String

/-- The empty example context. -/
def initial : Context Key Value := empty

/-- A context where only the numeric dependency is present. -/
def counterValue : Value .counter := show Nat from 7

/-- A context where only the numeric dependency is present. -/
def counterOnly : Context Key Value := setAt initial .counter counterValue

/-- The two-key specification used by the example component. -/
def dependencies : Spec Key where
  keys := [.counter, .label]
  nodup := by simp

/-- Constructive evidence that the first dependency is present with a `Nat`. -/
def counterPresent : Present counterOnly .counter where
  value := counterValue
  lookup_eq := by simp [counterOnly]

/-- Constructive evidence that the `String` dependency remains absent. -/
theorem labelAbsent : Absent counterOnly .label := by
  constructor
  simp [counterOnly, initial]

/-- The string value installed at the second dependent key. -/
def labelValue : Value .label := show String from "ready"

/-- Installing the last dependency as a witnessed reversible effect. -/
def installLabel : Cordis.Applied (Context Key Value) counterOnly :=
  setEffect counterOnly .label labelValue labelAbsent

/-- Typed `get` returns a `Nat` at the counter key. -/
example : get counterOnly .counter counterPresent = counterValue := rfl

/-- The newly installed key carries a `String`, not the counter key's `Nat`. -/
def labelPresent : Present installLabel.after .label where
  value := labelValue
  lookup_eq := by
    change setAt counterOnly .label labelValue .label = some labelValue
    simp

/-- The same `get` API specializes to `String` at the label key. -/
example : get installLabel.after .label labelPresent = labelValue := rfl

/-- Installing the last missing dependency activates the component specification. -/
example : notify dependencies counterOnly installLabel.after = .activating := by
  decide

/-- Removing that required dependency deactivates the specification. -/
example : notify dependencies installLabel.after (removeAt installLabel.after .label) =
    .deactivating := by
  decide

/-- The installed dependency's concrete remove inverse exactly recovers the predecessor. -/
example : installLabel.undo installLabel.after = counterOnly :=
  installLabel.undo_after

/-- Recovery is concretely removal of the inserted label binding. -/
example : removeAt installLabel.after .label = counterOnly :=
  installLabel.undo_after

end Example

end Cordis.Coeffect
