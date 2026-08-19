import Cordis.GlobalTemporal

/-!
# Finite global observational relations

The paper uses two incomparable global relations. Rule observation `≃` keeps the derived
coeffect context up to each key's observational relation and keeps the registry domain and every
control field. Effect observation `≈` keeps ambient state and fiber tables exactly while
forgetting lifecycle control. This module gives finite Lean candidates for both.

`StaticSignature` intentionally carries dependent value types but no value equivalences, so the
coeffect relation is parameterized by `ValueSetoids`. The effect relation uses exact Lean equality
for ambient data and table lookups. An absent registry entry is read as an empty table, capturing
the vestigial absent-versus-empty-table case without identifying nonempty tables.

Both candidates are proved to be setoids. `EffectUndoRespect` is the named extra law needed to
turn the effect candidate into `GlobalTemporal.EffectEquiv`. No rule applicability or successor
bisimulation is proved, so this module does not claim paper Lemma 55.
-/

set_option autoImplicit false

namespace Cordis.GlobalRelations

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Key-indexed value and context observation -/

/-- Explicit observational equivalence for each dependent coeffect value type. -/
structure ValueSetoids (sig : StaticSignature) where
  relation : (key : sig.Key) → Setoid (sig.Value key)

/-- Lift one value setoid through optional lookup, retaining domain equality. -/
def OptionRelated {Value : Type u} (setoid : Setoid Value) : Option Value → Option Value → Prop
  | none, none => True
  | some left, some right => setoid.r left right
  | _, _ => False

namespace OptionRelated

theorem refl {Value : Type u} (setoid : Setoid Value) (value : Option Value) :
    OptionRelated setoid value value := by
  cases value with
  | none => trivial
  | some value => exact setoid.refl value

theorem symm
    {Value : Type u} {setoid : Setoid Value} {left right : Option Value}
    (related : OptionRelated setoid left right) : OptionRelated setoid right left := by
  cases left <;> cases right <;> simp_all [OptionRelated]
  exact setoid.symm related

theorem trans
    {Value : Type u} {setoid : Setoid Value} {first second third : Option Value}
    (left : OptionRelated setoid first second)
    (right : OptionRelated setoid second third) : OptionRelated setoid first third := by
  cases first <;> cases second <;> cases third <;> simp_all [OptionRelated]
  exact setoid.trans left right

theorem isSome_eq
    {Value : Type u} {setoid : Setoid Value} {left right : Option Value}
    (related : OptionRelated setoid left right) : left.isSome = right.isSome := by
  cases left <;> cases right <;> simp_all [OptionRelated]

end OptionRelated

/-- Definition 33 on the repository's finite dependent contexts. -/
def ContextRelated
    (values : ValueSetoids sig)
    (left right : Coeffect.Context sig.Key sig.Value) : Prop :=
  ∀ key, OptionRelated (values.relation key) (left key) (right key)

theorem contextRelated_refl
    (values : ValueSetoids sig) (context : Coeffect.Context sig.Key sig.Value) :
    ContextRelated values context context := by
  intro key
  exact OptionRelated.refl (values.relation key) (context key)

theorem contextRelated_symm
    {values : ValueSetoids sig} {left right : Coeffect.Context sig.Key sig.Value}
    (related : ContextRelated values left right) : ContextRelated values right left := by
  intro key
  exact OptionRelated.symm (related key)

theorem contextRelated_trans
    {values : ValueSetoids sig}
    {first second third : Coeffect.Context sig.Key sig.Value}
    (left : ContextRelated values first second)
    (right : ContextRelated values second third) : ContextRelated values first third := by
  intro key
  exact OptionRelated.trans (left key) (right key)

theorem contextRelated_domain
    {values : ValueSetoids sig} {left right : Coeffect.Context sig.Key sig.Value}
    (related : ContextRelated values left right) (key : sig.Key) :
    (left key).isSome = (right key).isSome :=
  OptionRelated.isSome_eq (related key)

def contextSetoid (values : ValueSetoids sig) : Setoid (Coeffect.Context sig.Key sig.Value) where
  r := ContextRelated values
  iseqv := {
    refl := contextRelated_refl values
    symm := contextRelated_symm
    trans := contextRelated_trans
  }

/-! ## Rule-observation candidate `≃` -/

/-- Finite control retained by rule observation; the private table is deliberately absent. -/
structure FiberControl (catalog : Catalog sig) where
  component : sig.ComponentId
  parent : Option sig.Name
  birth : Nat
  retired : Bool
  phase : Phase (catalog.declaration component)

def fiberControl (fiber : Fiber catalog) : FiberControl catalog where
  component := fiber.component
  parent := fiber.parent
  birth := fiber.birth
  retired := fiber.retired
  phase := fiber.phase

def controlAt (state : State catalog Ambient) (name : sig.Name) : Option (FiberControl catalog) :=
  match state.registry name with
  | none => none
  | some fiber => some (fiberControl fiber)

/-- Global Equation 53 candidate: related active coeffects and exact domain/control.

The exact proof-only `nextBirth` clock is included because it is local control used by O-Insert;
the paper has no corresponding field.
-/
noncomputable def RuleRelated
    (values : ValueSetoids sig) (left right : State catalog Ambient) : Prop :=
  ContextRelated values (activeContext left) (activeContext right) ∧
    left.nextBirth = right.nextBirth ∧
    ∀ name, controlAt left name = controlAt right name

theorem ruleRelated_refl
    (values : ValueSetoids sig) (state : State catalog Ambient) :
    RuleRelated values state state := by
  exact ⟨contextRelated_refl values _, rfl, fun _ ↦ rfl⟩

theorem ruleRelated_symm
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) : RuleRelated values right left := by
  exact ⟨contextRelated_symm related.1, related.2.1.symm,
    fun name ↦ (related.2.2 name).symm⟩

theorem ruleRelated_trans
    {values : ValueSetoids sig} {first second third : State catalog Ambient}
    (left : RuleRelated values first second)
    (right : RuleRelated values second third) : RuleRelated values first third := by
  exact ⟨contextRelated_trans left.1 right.1, left.2.1.trans right.2.1,
    fun name ↦ (left.2.2 name).trans (right.2.2 name)⟩

theorem ruleRelated_registry_domain
    {values : ValueSetoids sig} {left right : State catalog Ambient}
    (related : RuleRelated values left right) (name : sig.Name) :
    (left.registry name).isSome = (right.registry name).isSome := by
  have controlEq := related.2.2 name
  cases leftLookup : left.registry name <;> cases rightLookup : right.registry name <;>
    simp [controlAt, leftLookup, rightLookup] at controlEq ⊢

noncomputable def ruleSetoid (values : ValueSetoids sig) : Setoid (State catalog Ambient) where
  r := RuleRelated values
  iseqv := {
    refl := ruleRelated_refl values
    symm := ruleRelated_symm
    trans := ruleRelated_trans
  }

/-- The genuinely missing Lemma 55 obligation: matching rules and related successors. -/
structure RuleBisimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) : Prop where
  forward : ∀ {left right leftAfter}, RuleRelated values left right →
    (step : Step dynamics inertia left leftAfter) →
    ∃ rightAfter : State catalog Ambient,
      ∃ matched : Step dynamics inertia right rightAfter,
      matched.rule = step.rule ∧ matched.actedName = step.actedName ∧
      RuleRelated values leftAfter rightAfter
  backward : ∀ {left right rightAfter}, RuleRelated values left right →
    (step : Step dynamics inertia right rightAfter) →
    ∃ leftAfter : State catalog Ambient,
      ∃ matched : Step dynamics inertia left leftAfter,
      matched.rule = step.rule ∧ matched.actedName = step.actedName ∧
      RuleRelated values leftAfter rightAfter

/-! ## Effect-observation candidate `≈` -/

/-- Read absence as the empty table, exactly as the vestigial-entry argument requires. -/
def tableAt (state : State catalog Ambient) (name : sig.Name) :
    Coeffect.Context sig.Key sig.Value :=
  match state.registry name with
  | none => Coeffect.empty
  | some fiber => fiber.table

/-- Exact effect-relevant state: ambient data and every normalized table lookup. -/
def EffectRelated (left right : State catalog Ambient) : Prop :=
  left.ambient = right.ambient ∧
    ∀ name key, tableAt left name key = tableAt right name key

theorem effectRelated_refl (state : State catalog Ambient) : EffectRelated state state := by
  exact ⟨rfl, fun _ _ ↦ rfl⟩

theorem effectRelated_symm
    {left right : State catalog Ambient}
    (related : EffectRelated left right) : EffectRelated right left := by
  exact ⟨related.1.symm, fun name key ↦ (related.2 name key).symm⟩

theorem effectRelated_trans
    {first second third : State catalog Ambient}
    (left : EffectRelated first second)
    (right : EffectRelated second third) : EffectRelated first third := by
  exact ⟨left.1.trans right.1,
    fun name key ↦ (left.2 name key).trans (right.2 name key)⟩

def effectSetoid : Setoid (State catalog Ambient) where
  r := EffectRelated
  iseqv := {
    refl := effectRelated_refl
    symm := effectRelated_symm
    trans := effectRelated_trans
  }

theorem tableAt_retireByName
    (state : State catalog Ambient) (retired observed : sig.Name) (key : sig.Key) :
    tableAt (retireByName state retired) observed key = tableAt state observed key := by
  unfold retireByName
  split
  · rfl
  · rename_i fiber lookup
    by_cases same : observed = retired
    · subst observed
      simp [tableAt, retireFiber, lookup]
    · simp [tableAt, retireFiber, Coeffect.setAt_other, same]

/-! ## Bridge to finite temporal recovery -/

/-- Named dynamics obligation: every interpreted undo respects exact effect observation. -/
structure EffectUndoRespect (dynamics : Dynamics sig catalog Ambient) : Prop where
  applyUndo_respects : ∀ undo {left right}, EffectRelated left right →
    EffectRelated (dynamics.applyUndo undo left) (dynamics.applyUndo undo right)

def temporalEffectEquiv
    (dynamics : Dynamics sig catalog Ambient) (respect : EffectUndoRespect dynamics) :
    GlobalTemporal.EffectEquiv dynamics where
  setoid := effectSetoid
  applyUndo_respects := respect.applyUndo_respects

/-! ## Concrete incomparability and arbitrary-dynamics counterexamples -/

namespace Example

abbrev ExampleSig := GlobalTraceFacts.Counterexample.exampleSignature
abbrev exampleCatalog := GlobalTraceFacts.Counterexample.exampleCatalog
abbrev ExampleState := GlobalTraceFacts.Counterexample.ExampleState

def universalNat : Setoid Nat where
  r _ _ := True
  iseqv := {
    refl := fun _ ↦ trivial
    symm := fun _ ↦ trivial
    trans := fun _ _ ↦ trivial
  }

def universalValues : ValueSetoids ExampleSig where
  relation _ := universalNat

theorem activeContext_exact (value : Nat) :
    activeContext (GlobalTraceFacts.Counterexample.state value) () = some value := by
  apply (activeContext_value_iff
    (GlobalTraceFacts.Counterexample.state_wellFormed value)).2
  exact ⟨true, GlobalTraceFacts.Counterexample.foreignFiber value,
    GlobalTraceFacts.Counterexample.state_foreign_present value,
    by simp [GlobalTraceFacts.Counterexample.foreignFiber, Fiber.Active, Phase.Active], rfl⟩

/-- Coarse key observations relate the states, while their exact effect tables differ. -/
theorem rule_related_table_difference :
    RuleRelated universalValues
      (GlobalTraceFacts.Counterexample.state 7)
      (GlobalTraceFacts.Counterexample.state 8) := by
  constructor
  · intro key
    cases key
    rw [activeContext_exact 7, activeContext_exact 8]
    trivial
  · constructor
    · rfl
    · intro name
      cases name <;> rfl

theorem effect_rejects_table_difference :
    ¬EffectRelated
      (GlobalTraceFacts.Counterexample.state 7)
      (GlobalTraceFacts.Counterexample.state 8) := by
  intro related
  have tableEq := related.2 true ()
  change some 7 = some 8 at tableEq
  have impossible : 7 = 8 := Option.some.inj tableEq
  omega

def emptyState : ExampleState where
  ambient := ()
  nextBirth := 1
  registry := Coeffect.empty

def vestigialFiber : Fiber exampleCatalog where
  component := false
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := true
  phase := .inactive none

def vestigialState : ExampleState where
  ambient := ()
  nextBirth := 1
  registry := Coeffect.setAt Coeffect.empty false vestigialFiber

/-- Normalized empty tables make a vestigial entry effect-equivalent to absence. -/
theorem effect_related_vestigial_absence : EffectRelated emptyState vestigialState := by
  constructor
  · rfl
  · intro name key
    cases name <;> cases key <;> rfl

/-- Rule observation retains the registry domain and therefore distinguishes the entry. -/
theorem rule_rejects_vestigial_absence :
    ¬RuleRelated universalValues emptyState vestigialState := by
  intro related
  have controlEq := related.2.2 false
  change none = some (fiberControl vestigialFiber) at controlEq
  cases controlEq

/-- The imported dynamics relation is universal and can hide an exact table difference. -/
theorem dynamics_relation_rejects_nothing :
    GlobalTraceFacts.Counterexample.dynamics.equivalence.r
      (GlobalTraceFacts.Counterexample.state 7)
      (GlobalTraceFacts.Counterexample.state 8) :=
  trivial

theorem dynamics_relation_not_effect_candidate :
    GlobalTraceFacts.Counterexample.dynamics.equivalence.r
        (GlobalTraceFacts.Counterexample.state 7)
        (GlobalTraceFacts.Counterexample.state 8) ∧
      ¬EffectRelated
        (GlobalTraceFacts.Counterexample.state 7)
        (GlobalTraceFacts.Counterexample.state 8) :=
  ⟨dynamics_relation_rejects_nothing, effect_rejects_table_difference⟩

theorem counterexampleUndoRespect :
    EffectUndoRespect GlobalTraceFacts.Counterexample.dynamics where
  applyUndo_respects := by
    intro undo left right related
    cases undo with
    | external code =>
        exact effectRelated_refl (GlobalTraceFacts.Counterexample.state 8)
    | retire name =>
        constructor
        · change left.ambient = right.ambient
          exact related.1
        · intro observed key
          change tableAt (retireByName left name) observed key =
            tableAt (retireByName right name) observed key
          rw [tableAt_retireByName, tableAt_retireByName]
          exact related.2 observed key

def counterexampleTemporalEffect :
    GlobalTemporal.EffectEquiv GlobalTraceFacts.Counterexample.dynamics :=
  temporalEffectEquiv GlobalTraceFacts.Counterexample.dynamics counterexampleUndoRespect

end Example

end Cordis.GlobalRelations
