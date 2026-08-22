/-!
# The paper's effect-context tower

This module implements the pinned CORDIS paper's Definitions 1--12 and Theorems 4--5,
7, 10--16.  The names are kept in a namespace because `Cordis.Effect` is the repository's
state-indexed one-step API, while this file formalizes the paper's function-level tower.

The central types are deliberately proof-carrying:

* `EffectContext Γ` is the paper's `∂Γ = Γ × (Γ → Γ)`;
* `EffectFunction Γ` returns both its successor and the inverse chosen at that application;
* `WitnessedEffect Γ` carries the one-sided inverse law at every input.

The finite indexed `Run` below makes the reverse-order context recovery part of Theorem 16
explicit.  The later paper claims about arbitrary interleavings and transformation-monoid
independence are separate modules, so this file does not smuggle those stronger hypotheses
into the tower itself.
-/

set_option autoImplicit false

namespace Cordis.EffectContext

universe u

/-- Endomorphisms of a context. -/
abbrev Transform (Γ : Type u) := Γ → Γ

/-- The paper's pair of a forward context map and a candidate left inverse. -/
abbrev TransformPair (Γ : Type u) := Transform Γ × Transform Γ

/-- The effect context `∂Γ = Γ × (Γ → Γ)`. -/
abbrev EffectContext (Γ : Type u) := Γ × Transform Γ

/-- A state-indexed effect returns a new context and the inverse chosen at that state. -/
abbrev EffectFunction (Γ : Type u) := Γ → Γ × Transform Γ

/-- Twisted multiplication of pairs: inverses accumulate in the opposite order. -/
def twistedComp {Γ : Type u} (left right : TransformPair Γ) : TransformPair Γ :=
  (left.1 ∘ right.1, right.2 ∘ left.2)

/-- The unit of the twisted composition monoid. -/
def twistedIdentity {Γ : Type u} : TransformPair Γ := (id, id)

/-- Track one forward/inverse pair in the effect context. -/
def track {Γ : Type u} (pair : TransformPair Γ) : EffectContext Γ → EffectContext Γ :=
  fun state ↦ (pair.1 state.1, state.2 ∘ pair.2)

/-- Recover the context and reset its accumulated inverse. -/
def recover {Γ : Type u} : EffectContext Γ → EffectContext Γ :=
  fun state ↦ (state.2 state.1, id)

/-- The identity effect function `ηΓ`. -/
def effectIdentity {Γ : Type u} : EffectFunction Γ :=
  fun state ↦ (state, id)

/-- Effect composition `f ⋄ g`: run `g`, then `f`, and compose inverses in LIFO order. -/
def effectComp {Γ : Type u} (left right : EffectFunction Γ) : EffectFunction Γ :=
  fun state ↦
    let rightResult := right state
    let leftResult := left rightResult.1
    (leftResult.1, rightResult.2 ∘ leftResult.2)

/-- A function-level effect together with its pointwise one-sided inverse proof. -/
structure WitnessedEffect (Γ : Type u) where
  /-- The state-indexed effect function. -/
  run : EffectFunction Γ
  /-- The inverse selected at each application recovers that application's predecessor. -/
  inverse_ok : ∀ state, (run state).2 (run state).1 = state

/-- The uniform-pair embedding from the twisted monoid into effect functions. -/
def uniform {Γ : Type u} (pair : TransformPair Γ) : EffectFunction Γ :=
  fun state ↦ (pair.1 state, pair.2)

/-- The paper's `effectΓ`, lifting an effect function one level up the tower. -/
def effectLift {Γ : Type u} (effect : EffectFunction Γ) :
    EffectFunction (EffectContext Γ) :=
  fun state ↦
    let result := effect state.1
    ((result.1, state.2 ∘ result.2), track (result.2, fun input ↦ (effect input).1))

namespace Theorems

variable {Γ : Type u}

/-- Theorem 4: tracking commutes with projection to the current context. -/
theorem track_projection (pair : TransformPair Γ) :
    (fun state : EffectContext Γ ↦ (track pair state).1) =
      pair.1 ∘ (fun state : EffectContext Γ ↦ state.1) := by
  funext state
  rfl

/-- Theorem 5(1): the twisted unit tracks to the identity. -/
theorem track_identity : track (twistedIdentity : TransformPair Γ) = id := by
  funext state
  rcases state with ⟨context, accumulator⟩
  rfl

/-- Theorem 5(2): tracking is a homomorphism for twisted composition. -/
theorem track_comp (left right : TransformPair Γ) :
    track (twistedComp left right) = track left ∘ track right := by
  funext state
  rcases state with ⟨context, accumulator⟩
  rfl

/-- Theorem 7: a locally valid inverse preserves the recovery result. -/
theorem recover_track
    (pair : TransformPair Γ) (state : EffectContext Γ)
    (inverse_ok : pair.2 (pair.1 state.1) = state.1) :
    recover (track pair state) = recover state := by
  rcases state with ⟨context, accumulator⟩
  simp [track, recover, Function.comp_def, inverse_ok]

/-- Effect composition has the left unit law. -/
theorem effectComp_identity_left (effect : EffectFunction Γ) :
    effectComp effectIdentity effect = effect := by
  funext state
  rfl

/-- Effect composition has the right unit law. -/
theorem effectComp_identity_right (effect : EffectFunction Γ) :
    effectComp effect effectIdentity = effect := by
  funext state
  rfl

/-- Effect composition is associative. -/
theorem effectComp_assoc
    (first second third : EffectFunction Γ) :
    effectComp (effectComp first second) third =
      effectComp first (effectComp second third) := by
  funext state
  rfl

/-- The uniform embedding preserves effect composition. -/
theorem uniform_effectComp (left right : TransformPair Γ) :
    effectComp (uniform left) (uniform right) = uniform (twistedComp left right) := by
  funext state
  rfl

/-- Theorem 11(1): witnessed effects are closed under effect composition. -/
def WitnessedEffect.effectComp
    (left right : WitnessedEffect Γ) : WitnessedEffect Γ where
  run := Cordis.EffectContext.effectComp left.run right.run
  inverse_ok := by
    intro state
    simpa [Cordis.EffectContext.effectComp, Function.comp_def] using
      (congrArg (right.run state).2 (left.inverse_ok (right.run state).1)).trans
        (right.inverse_ok state)

/-- The uniform embedding of a left inverse is always witnessed. -/
def WitnessedEffect.uniform
    (pair : TransformPair Γ)
    (inverse_ok : ∀ state, pair.2 (pair.1 state) = state) : WitnessedEffect Γ where
  run := Cordis.EffectContext.uniform pair
  inverse_ok := inverse_ok

/-- Theorem 11(2): a uniform left inverse gives a witnessed effect. -/
theorem uniform_is_witnessed
    (pair : TransformPair Γ)
    (inverse_ok : ∀ state, pair.2 (pair.1 state) = state) :
    (WitnessedEffect.uniform pair inverse_ok).run = Cordis.EffectContext.uniform pair := rfl

/-- Theorem 14(1), pointwise: the lifted forward map projects to the original one. -/
theorem effectLift_projection (effect : EffectFunction Γ) (state : EffectContext Γ) :
    (effectLift effect state).1.1 = (effect state.1).1 := by
  rfl

/-- Theorem 14(2), pointwise: the lifted inverse projects to the chosen inverse. -/
theorem effectLift_inverse_projection
    (effect : EffectFunction Γ) (state input : EffectContext Γ) :
    ((effectLift effect state).2 input).1 = (effect state.1).2 input.1 := by
  rfl

/-- Theorem 13: lifting preserves effect composition. -/
theorem effectLift_comp (left right : EffectFunction Γ) :
    effectComp (effectLift left) (effectLift right) =
      effectLift (effectComp left right) := by
  funext state
  rcases state with ⟨context, accumulator⟩
  rfl

/-- Theorem 15's exact lifted-inverse calculation at one application. -/
theorem effectLift_inverse_value
    (effect : WitnessedEffect Γ) (state : EffectContext Γ) :
    (effectLift effect.run state).2 ((effectLift effect.run state).1) =
      (state.1, state.2 ∘ (effect.run state.1).2 ∘ (fun input ↦ (effect.run input).1)) := by
  rcases state with ⟨context, accumulator⟩
  simp [effectLift, track, Function.comp_def, effect.inverse_ok]

/-- The lifted inverse always preserves the recovery target, even without a uniform inverse. -/
theorem effectLift_recover
    (effect : WitnessedEffect Γ) (state : EffectContext Γ) :
    recover ((effectLift effect.run state).2 ((effectLift effect.run state).1)) =
      recover state := by
  rw [effectLift_inverse_value effect state]
  rcases state with ⟨context, accumulator⟩
  simp [recover, Function.comp_def, effect.inverse_ok]

/-- The pointwise condition needed for the lifted effect to be witnessed at every state. -/
def UniformInverse (effect : EffectFunction Γ) : Prop :=
  ∀ state input, (effect state).2 ((effect input).1) = input

/-- The lifted effect is witnessed exactly when each selected inverse is uniform. -/
theorem effectLift_isWitnessed_iff
    (effect : WitnessedEffect Γ) :
    (∀ state : EffectContext Γ,
      (effectLift effect.run state).2 ((effectLift effect.run state).1) = state) ↔
      UniformInverse effect.run := by
  constructor
  · intro lifted_witnessed state input
    have equality := congrArg Prod.snd (lifted_witnessed (state, id))
    have function_equality :
        (fun value ↦ (effect.run state).2 ((effect.run value).1)) = id := by
      simpa [effectLift, track, Function.comp_def] using equality
    exact congrFun function_equality input
  · intro uniform_inverse state
    rcases state with ⟨context, accumulator⟩
    rcases effect.run context with ⟨after, inverse⟩
    apply Prod.ext
    · exact effect.inverse_ok context
    · funext input
      simp [effectLift, track, Function.comp_def]
      exact congrArg accumulator (uniform_inverse context input)

/-- The forward endpoint of one witnessed effect at a lifted context. -/
def applyEffect (effect : WitnessedEffect Γ) (state : EffectContext Γ) :
    EffectContext Γ :=
  (effectLift effect.run state).1

/-- The inverse selected by one lifted effect application. -/
def inverseAt
    (effect : WitnessedEffect Γ) (state : EffectContext Γ) :
    EffectContext Γ → EffectContext Γ :=
  (effectLift effect.run state).2

/-- A lifted application preserves the context targeted by `recover`. -/
theorem applyEffect_recovery
    (effect : WitnessedEffect Γ) (state : EffectContext Γ) :
    recover (applyEffect effect state) = recover state := by
  rcases state with ⟨context, accumulator⟩
  simp [applyEffect, effectLift, recover, Function.comp_def, effect.inverse_ok]

/-- The selected lifted inverse recovers the original context projection. -/
theorem inverseAt_application_context
    (effect : WitnessedEffect Γ) (state : EffectContext Γ) :
    (inverseAt effect state (applyEffect effect state)).1 = state.1 := by
  rcases state with ⟨context, accumulator⟩
  simp [inverseAt, applyEffect, effectLift, track, Function.comp_def, effect.inverse_ok]

/-- A finite indexed sequence of witnessed lifted effects. -/
inductive Run (Γ : Type u) : EffectContext Γ → EffectContext Γ → Type u where
  | nil (state : EffectContext Γ) : Run Γ state state
  | cons {before final : EffectContext Γ}
      (effect : WitnessedEffect Γ)
      (tail : Run Γ (applyEffect effect before) final) : Run Γ before final

namespace Run

/-- The number of effect applications in a finite run. -/
def length {before after : EffectContext Γ} : Run Γ before after → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- Every finite run preserves the recovery target. -/
theorem recovery_eq {before after : EffectContext Γ} (run : Run Γ before after) :
    recover after = recover before := by
  induction run with
  | nil => rfl
  | cons effect tail ih =>
      exact ih.trans (applyEffect_recovery effect _)

/-- Apply the selected inverses in reverse order to the raw context projection. -/
def reverseContext {before after : EffectContext Γ} : Run Γ before after → Γ
  | .nil state => state.1
  | .cons (before := before) effect tail =>
      (effect.run before.1).2 (tail.reverseContext)

/-- Reverse-order inverse application recovers the initial raw context exactly. -/
theorem reverseContext_eq {before after : EffectContext Γ} (run : Run Γ before after) :
    run.reverseContext = before.1 := by
  induction run with
  | nil => rfl
  | cons effect tail ih =>
      dsimp [reverseContext]
      rw [ih]
      exact effect.inverse_ok _

end Run

end Theorems

/-!
## Concrete witnesses

The additive successor effect is deliberately not a two-sided inverse: its captured inverse
subtracts the same amount.  The example is nevertheless a witnessed effect on the nonnegative
subtype represented by integers with a `Nat`-valued state and a fixed zero-preserving update.
The more useful fully uniform witness below uses `Int`, where addition and subtraction are total.
-/

namespace Example

def add (amount : Int) : EffectFunction Int :=
  fun state ↦ (state + amount, fun current ↦ current - amount)

def add_witnessed (amount : Int) :
    WitnessedEffect Int where
  run := add amount
  inverse_ok := by
    intro state
    simp [add]

theorem add_comp_example :
    effectComp (add 3) (add 2) = add 5 := by
  funext state
  dsimp [effectComp, add]
  apply Prod.ext
  · simp
    omega
  · funext current
    simp
    omega

theorem add_lift_recovery (amount : Int) (state : EffectContext Int) :
    recover
        ((effectLift (add amount) state).2 ((effectLift (add amount) state).1)) =
      recover state :=
  Theorems.effectLift_recover (add_witnessed amount) state

theorem add_uniform_inverse (amount : Int) :
    Theorems.UniformInverse (add amount) := by
  intro state input
  simp [add]

/-- A concrete two-step indexed run used by the executable test suite. -/
def run : Theorems.Run Int (0, id) (Theorems.applyEffect (add_witnessed 2)
    (Theorems.applyEffect (add_witnessed 3) (0, id))) :=
  .cons (add_witnessed 3) (.cons (add_witnessed 2) (.nil _))

/-- The concrete run's reverse-order inverses recover its initial context. -/
theorem run_reverse : run.reverseContext = 0 := by
  exact Theorems.Run.reverseContext_eq run

/-- The concrete run preserves its recovery target. -/
theorem run_recovery :
    recover ((Theorems.applyEffect (add_witnessed 2)
      (Theorems.applyEffect (add_witnessed 3) (0, id)))) = recover (0, id) := by
  exact Theorems.Run.recovery_eq run

end Example

end Cordis.EffectContext
