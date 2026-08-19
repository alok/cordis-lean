import Cordis.GlobalTraceFacts

/-!
# Finite global temporal recovery

The paper's Definition 60 evaluates iterator maps away from the state where a rule originally
ran. An indexed `GlobalCalculus.Step` proves only one source/endpoint fact. This module first
reifies the associated fallible state map: identity and recovery maps are total, while an iterator
landing is re-executed with its exact code and registration oracle and may fail off-source.

Temporal recovery is then proved for a finite, explicitly reified boundary. Each intervening step
has a totalization certificate, the owner's forward program has an off-source inverse-stability
law for its accumulated `UndoCode` list, and each foreign map commutes with that recovery.
Whole-replay commutation is derived by induction. A separate reorder relation records the
Definition 60 commutations needed to turn an actual interleaving into that replay. These laws are
assumptions, not consequences of the current `Dynamics` or `Step` APIs.

The terminal bridge additionally requires recovery confinement for Lemma 54's structural facts
and invisibility of the final lifecycle phase edit under the chosen state equivalence. The result is
parameterized relational recovery algebra. It becomes a finite analogue of Theorem 61 and
Corollary 62 only when the supplied `EffectEquiv` is instantiated by the paper's canonical
control-forgetting relation. It is not full pairwise iterator independence, continuation stability,
arbitrary temporal composability, or Theorem 59.

Executable counterexamples show separately that an exact iterator step need not totalize
off-source, a universal dynamics relation can hide a table failure, and structural
`RecoveryConfinement` alone does not imply temporal recovery after a foreign ambient mutation.
-/

set_option autoImplicit false

namespace Cordis.GlobalTemporal

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus
open Cordis.GlobalTraceFacts

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Partial off-source interpretation of one exact step map -/

namespace Step

private def lifecycleMap?
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : GlobalLifecycle.Transition dynamics inertia before after) :
    State catalog Ambient → Option (State catalog Ambient) :=
  match transition with
  | .begin .. => some
  | .iter _ _ _ _ code _ _ _ _ landing _ _ => fun state ↦
      match executeOne dynamics landing.oracle code state with
      | .error _ => none
      | .ok step => some step.after
  | .finish _ _ _ _ code _ _ _ _ landing _ => fun state ↦
      match executeOne dynamics landing.oracle code state with
      | .error _ => none
      | .ok step => some step.after
  | .divertAbort .. => some
  | .divertLand _ _ _ _ code _ _ _ _ landing => fun state ↦
      match executeOne dynamics landing.oracle code state with
      | .error _ => none
      | .ok step => some step.after
  | .raise .. => some
  | .leave .. => some
  | .unload _ _ _ _ undos .. => fun state ↦ some (dynamics.recover undos state)

private def lifecycleSourceImage
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : GlobalLifecycle.Transition dynamics inertia before after) :
    State catalog Ambient :=
  match transition with
  | .begin .. => before
  | .iter _ _ _ _ _ _ _ _ _ landing _ _ => landing.step.after
  | .finish _ _ _ _ _ _ _ _ _ landing _ => landing.step.after
  | .divertAbort .. => before
  | .divertLand _ _ _ _ _ _ _ _ _ landing => landing.step.after
  | .raise .. => before
  | .leave .. => before
  | .unload _ _ _ _ undos .. => dynamics.recover undos before

/-- The paper's `Ψₜ`, executable off-source where the current evidence permits it. -/
def partialMap
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Step dynamics inertia before after → State catalog Ambient → Option (State catalog Ambient)
  | .orchestration _ => some
  | .lifecycle transition => lifecycleMap? transition

/-- Exact image of the indexed source before the rule's edit footprint is applied. -/
def sourceImage
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    Step dynamics inertia before after → State catalog Ambient
  | .orchestration _ => before
  | .lifecycle transition => lifecycleSourceImage transition

/-- Although iterator maps may be undefined elsewhere, every exact step maps its own source. -/
theorem partialMap_source
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    partialMap step before = some (sourceImage step) := by
  cases step with
  | orchestration transition => rfl
  | lifecycle transition =>
      cases transition with
      | begin => rfl
      | iter owner fiber present code undos committed phase target landing next continues =>
          simp [partialMap, lifecycleMap?, sourceImage, lifecycleSourceImage,
            landing.executed]
      | finish owner fiber present code undos committed phase target landing done =>
          simp [partialMap, lifecycleMap?, sourceImage, lifecycleSourceImage,
            landing.executed]
      | divertAbort => rfl
      | divertLand owner fiber present code undos committed phase changed landing =>
          simp [partialMap, lifecycleMap?, sourceImage, lifecycleSourceImage,
            landing.executed]
      | raise => rfl
      | leave => rfl
      | unload => rfl

end Step

/-! ## Totalized foreign maps and exact trace replay -/

/-- Explicit candidate for the paper's effect-state equivalence `≈`.

`Dynamics.equivalence` is not reused: it is integrator-defined and may even be universal. A
Theorem 61 instantiation must supply the intended ambient/table equality and prove every undo
code respects it.
-/
structure EffectEquiv (dynamics : Dynamics sig catalog Ambient) where
  setoid : Setoid (State catalog Ambient)
  applyUndo_respects : ∀ undo {left right}, setoid.r left right →
    setoid.r (dynamics.applyUndo undo left) (dynamics.applyUndo undo right)

namespace EffectEquiv

theorem recover_respects
    {dynamics : Dynamics sig catalog Ambient} (effect : EffectEquiv dynamics)
    (undos : List (UndoCode sig)) {left right : State catalog Ambient}
    (related : effect.setoid.r left right) :
    effect.setoid.r (dynamics.recover undos left) (dynamics.recover undos right) := by
  induction undos generalizing left right with
  | nil => exact related
  | cons undo rest ih => exact ih (effect.applyUndo_respects undo related)

end EffectEquiv

/-- Extra evidence needed to use one fallible step map as a total transformation. -/
structure TotalStepMap
    {dynamics : Dynamics sig catalog Ambient}
    (effect : EffectEquiv dynamics)
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  apply : State catalog Ambient → State catalog Ambient
  total : ∀ state, Step.partialMap step state = some (apply state)
  edit_related : effect.setoid.r after (apply before)
  respects : ∀ {left right}, effect.setoid.r left right →
    effect.setoid.r (apply left) (apply right)

namespace TotalStepMap

theorem source_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    {effect : EffectEquiv dynamics}
    (totalMap : TotalStepMap effect step) : totalMap.apply before = Step.sourceImage step := by
  have equal := (totalMap.total before).symm.trans (Step.partialMap_source step)
  exact Option.some.inj equal

end TotalStepMap

/-- Definition 60-style commutation of one foreign map with an owner's accumulated recovery. -/
structure RecoveryCommutesWithMap
    (dynamics : Dynamics sig catalog Ambient) (effect : EffectEquiv dynamics)
    (undos : List (UndoCode sig))
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} {step : Step dynamics inertia before after}
    (map : TotalStepMap effect step) : Prop where
  commutes : ∀ state,
    effect.setoid.r
      (dynamics.recover undos (map.apply state))
      (map.apply (dynamics.recover undos state))

/-- A finite trace of steps owned by names other than `owner`, with total state-map evidence. -/
inductive Intervening
    (dynamics : Dynamics sig catalog Ambient)
    (effect : EffectEquiv dynamics)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    (owner : sig.Name) :
    {before after : State catalog Ambient} →
    GlobalCalculus.Trace dynamics inertia before after → Type (u + 1) where
  | nil (state : State catalog Ambient) : Intervening dynamics effect inertia owner (.nil state)
  | cons
      {before middle after : State catalog Ambient}
      {head : Step dynamics inertia before middle}
      {tail : GlobalCalculus.Trace dynamics inertia middle after}
      (foreign : head.actedName ≠ owner)
      (map : TotalStepMap effect head)
      (rest : Intervening dynamics effect inertia owner tail) :
      Intervening dynamics effect inertia owner (.cons head tail)

namespace Intervening

def replay
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after} :
    Intervening dynamics effect inertia owner trace →
      State catalog Ambient → State catalog Ambient
  | .nil _ => id
  | .cons _ map rest => fun state ↦ rest.replay (map.apply state)

theorem replay_respects
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (intervening : Intervening dynamics effect inertia owner trace)
    {left right : State catalog Ambient} (related : effect.setoid.r left right) :
    effect.setoid.r (intervening.replay left) (intervening.replay right) := by
  induction intervening generalizing left right with
  | nil => exact related
  | cons foreign map rest ih => exact ih (map.respects related)

theorem endpoint_related
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (intervening : Intervening dynamics effect inertia owner trace) :
    effect.setoid.r after (intervening.replay before) := by
  induction intervening with
  | nil state => exact effect.setoid.refl state
  | cons foreign map rest ih =>
      exact effect.setoid.trans ih (rest.replay_respects map.edit_related)

end Intervening

/-! ## Explicit finite Definition 60 assumptions -/

/-- One owner's finite forward contribution and accumulated inverse stability off-source. -/
structure OwnerProgram
    (dynamics : Dynamics sig catalog Ambient) (effect : EffectEquiv dynamics)
    (owner : sig.Name)
    (undos : List (UndoCode sig)) where
  forward : State catalog Ambient → State catalog Ambient
  forward_respects : ∀ {left right}, effect.setoid.r left right →
    effect.setoid.r (forward left) (forward right)
  inverse_stable : ∀ state,
    effect.setoid.r (dynamics.recover undos (forward state)) state

/-- Cross-owner commutation of the whole accumulated recovery with a foreign replay. -/
structure AccumulatedCommutes
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {undos : List (UndoCode sig)}
    {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (intervening : Intervening dynamics effect inertia owner trace) : Prop where
  recovery_commutes : ∀ state,
    effect.setoid.r
      (dynamics.recover undos (intervening.replay state))
      (intervening.replay (dynamics.recover undos state))

/-- Per-record Definition 60 commutation evidence for an exact intervening trace. -/
def PerStepCommutes
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} (undos : List (UndoCode sig))
    {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after} :
    Intervening dynamics effect inertia owner trace → Prop
  | .nil _ => True
  | .cons _ map rest => RecoveryCommutesWithMap dynamics effect undos map ∧
      PerStepCommutes undos rest

/-- Generator-wise commutation composes to the whole foreign replay. -/
theorem accumulatedCommutes_of_perStep
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {undos : List (UndoCode sig)}
    {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    (intervening : Intervening dynamics effect inertia owner trace)
    (perStep : PerStepCommutes undos intervening) :
    AccumulatedCommutes (undos := undos) intervening := by
  constructor
  intro state
  induction intervening generalizing state with
  | nil => exact effect.setoid.refl (dynamics.recover undos state)
  | cons foreign map rest ih =>
      have headCommutes := perStep.1.commutes state
      have tailCommutes := ih perStep.2 (map.apply state)
      exact effect.setoid.trans tailCommutes
        (rest.replay_respects headCommutes)

/-- Certificate that an actual interleaving can be reordered into the foreign replay. -/
structure ReorderedInterleaving
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {undos : List (UndoCode sig)}
    (program : OwnerProgram dynamics effect owner undos)
    (origin actual : State catalog Ambient) where
  reorderedEnd : State catalog Ambient
  trace : GlobalCalculus.Trace dynamics inertia (program.forward origin) reorderedEnd
  intervening : Intervening dynamics effect inertia owner trace
  reorder_related : effect.setoid.r actual reorderedEnd
  per_step_commutes : PerStepCommutes undos intervening

/-- Parameterized finite interleaved recovery under explicit Definition 60-style laws. -/
theorem recover_interleaved
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {undos : List (UndoCode sig)}
    {origin actual : State catalog Ambient}
    (program : OwnerProgram dynamics effect owner undos)
    (interleaving : ReorderedInterleaving (inertia := inertia) program origin actual) :
    effect.setoid.r
      (dynamics.recover undos actual)
      (interleaving.intervening.replay origin) := by
  have reordered := effect.recover_respects undos interleaving.reorder_related
  have replayed := effect.recover_respects undos interleaving.intervening.endpoint_related
  have commuted :=
    (accumulatedCommutes_of_perStep interleaving.intervening
      interleaving.per_step_commutes).recovery_commutes (program.forward origin)
  have inverted := interleaving.intervening.replay_respects
    (program.inverse_stable origin)
  exact effect.setoid.trans reordered <|
    effect.setoid.trans replayed <|
      effect.setoid.trans commuted inverted

/-! ## Terminal L-Unload bridge -/

/-- Structural and observational evidence missing from bare `RecoveryAdmission`. -/
structure UnloadCompatibility
    (dynamics : Dynamics sig catalog Ambient)
    (effect : EffectEquiv dynamics)
    (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
    (undos : List (UndoCode sig)) (outcome : Option sig.Error)
    (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome) :
    Prop where
  confinement : RecoveryConfinement dynamics before owner undos
  edit_invisible : effect.setoid.r admission.after
    (dynamics.recover undos before)

namespace UnloadCompatibility

theorem sufficientConfinement
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (outcome : Option sig.Error)
    (phase : fiber.phase = .unloading undos committed outcome)
    (notRelied : ¬Relied before owner)
    (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome)
    (compatible : UnloadCompatibility dynamics effect before owner fiber undos outcome admission) :
    SufficientConfinement dynamics inertia
      (.lifecycle (.unload before owner fiber present undos committed outcome phase
        notRelied admission)) :=
  .unload before owner fiber present undos committed outcome phase notRelied admission
    compatible.confinement

end UnloadCompatibility

/-- Relational terminal recovery at the admitted inactive endpoint. -/
theorem terminal_recovery
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {undos : List (UndoCode sig)}
    {origin before : State catalog Ambient}
    (program : OwnerProgram dynamics effect owner undos)
    (interleaving : ReorderedInterleaving (inertia := inertia) program origin before)
    (fiber : Fiber catalog) (outcome : Option sig.Error)
    (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome)
    (compatible : UnloadCompatibility dynamics effect before owner fiber undos outcome admission) :
    effect.setoid.r admission.after
      (interleaving.intervening.replay origin) :=
  effect.setoid.trans compatible.edit_invisible
    (recover_interleaved program interleaving)

/-- Parameterized terminal result packaged with exact L-Unload and structural confinement. -/
theorem terminal_unload_recovery
    {dynamics : Dynamics sig catalog Ambient}
    {effect : EffectEquiv dynamics}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {owner : sig.Name} {undos : List (UndoCode sig)}
    {origin before : State catalog Ambient}
    (program : OwnerProgram dynamics effect owner undos)
    (interleaving : ReorderedInterleaving (inertia := inertia) program origin before)
    (fiber : Fiber catalog) (present : before.registry owner = some fiber)
    (committed : CommittedView (catalog.declaration fiber.component))
    (outcome : Option sig.Error)
    (phase : fiber.phase = .unloading undos committed outcome)
    (notRelied : ¬Relied before owner)
    (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome)
    (compatible : UnloadCompatibility dynamics effect before owner fiber undos outcome admission) :
    effect.setoid.r admission.after (interleaving.intervening.replay origin) ∧
      SufficientConfinement dynamics inertia
        (.lifecycle (.unload before owner fiber present undos committed outcome phase
          notRelied admission)) :=
  ⟨terminal_recovery program interleaving fiber outcome admission compatible,
    compatible.sufficientConfinement before owner fiber present undos committed outcome phase
      notRelied admission⟩

/-! ## Executable evidence that exact step maps need not be total off-source -/

namespace Counterexample

theorem iterator_map_at_source :
    Step.partialMap GlobalCalculus.Example.iterStep GlobalLifecycle.Example.beginState =
      some GlobalLifecycle.Example.firstStep.after := by
  exact Step.partialMap_source GlobalCalculus.Example.iterStep

theorem iterator_map_missing_off_source :
    Step.partialMap GlobalCalculus.Example.iterStep GlobalCalculus.Example.emptyStart = none := by
  rfl

/-- The exact iterator step therefore has no global `TotalStepMap` without an added law. -/
theorem iterator_has_no_totalization :
    ∀ effect : EffectEquiv GlobalLifecycle.Example.dynamics,
      TotalStepMap effect GlobalCalculus.Example.iterStep → False := by
  intro effect
  intro totalMap
  have total := totalMap.total GlobalCalculus.Example.emptyStart
  rw [iterator_map_missing_off_source] at total
  cases total

abbrev WeakState := GlobalTraceFacts.Counterexample.ExampleState

def foreignTableObservation (state : WeakState) : Option Nat :=
  match state.registry true with
  | none => none
  | some fiber => fiber.table ()

def tableSetoid : Setoid WeakState where
  r left right := foreignTableObservation left = foreignTableObservation right
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

theorem foreignTableObservation_retire (state : WeakState) (name : Bool) :
    foreignTableObservation (retireByName state name) = foreignTableObservation state := by
  unfold retireByName
  split
  · rfl
  · rename_i fiber lookup
    cases name
    · simp [foreignTableObservation, retireFiber, Coeffect.setAt_other]
    · simp [foreignTableObservation, retireFiber, lookup]

def tableEffectEquiv : EffectEquiv GlobalTraceFacts.Counterexample.dynamics where
  setoid := tableSetoid
  applyUndo_respects := by
    intro undo left right related
    change foreignTableObservation left = foreignTableObservation right at related
    cases undo with
    | external code =>
        change foreignTableObservation GlobalTraceFacts.Counterexample.inactiveAfter =
          foreignTableObservation GlobalTraceFacts.Counterexample.inactiveAfter
        rfl
    | retire name =>
        change foreignTableObservation (retireByName left name) =
          foreignTableObservation (retireByName right name)
        rw [foreignTableObservation_retire, foreignTableObservation_retire]
        exact related

/-- A universal dynamics relation hides the foreign-table failure detected by explicit `≈`. -/
theorem universal_relation_is_vacuous_here :
    GlobalTraceFacts.Counterexample.dynamics.equivalence.r
        GlobalTraceFacts.Counterexample.inactiveAfter
        (GlobalTraceFacts.Counterexample.state 7) ∧
      ¬tableEffectEquiv.setoid.r
        GlobalTraceFacts.Counterexample.inactiveAfter
        (GlobalTraceFacts.Counterexample.state 7) := by
  constructor
  · trivial
  · intro related
    change foreignTableObservation GlobalTraceFacts.Counterexample.inactiveAfter =
      foreignTableObservation (GlobalTraceFacts.Counterexample.state 7) at related
    change some 8 = some 7 at related
    have impossible : 8 = 7 := Option.some.inj related
    omega

abbrev AmbientState := GlobalDynamics.Example.ExampleState

def doubleAmbient (state : AmbientState) : AmbientState := {
  state with ambient := state.ambient * 2
}

def ambientEffectEquiv : EffectEquiv GlobalDynamics.Example.dynamics where
  setoid := GlobalDynamics.Example.stateSetoid
  applyUndo_respects := GlobalDynamics.Example.dynamics.applyUndo_respects

/-- Example recovery changes only ambient data, so structural recovery confinement holds. -/
theorem ambientRecovery_confinement (before : AmbientState) :
    RecoveryConfinement GlobalDynamics.Example.dynamics before 0 [.external 0] := by
  constructor
  · intro name beforeFiber present different
    refine ⟨beforeFiber, ?_, rfl, ControlContinuous.refl beforeFiber⟩
    change before.registry name = some beforeFiber
    exact present
  · intro beforeFiber afterFiber beforePresent afterPresent
    change before.registry 0 = some afterFiber at afterPresent
    rw [beforePresent] at afterPresent
    have fiber_eq : beforeFiber = afterFiber := Option.some.inj afterPresent
    subst afterFiber
    exact ⟨rfl, rfl, rfl, fun retired ↦ retired⟩

def ownerForwardState : AmbientState :=
  GlobalDynamics.Example.ordinaryAfter GlobalDynamics.Example.start

def interleavedState : AmbientState := doubleAmbient ownerForwardState

def foreignReplayState : AmbientState := doubleAmbient GlobalDynamics.Example.start

/-- Recovery confinement alone does not imply temporal recovery after a foreign mutation. -/
theorem recoveryConfinement_not_temporal :
    RecoveryConfinement GlobalDynamics.Example.dynamics interleavedState 0 [.external 0] ∧
      ¬ambientEffectEquiv.setoid.r
        (GlobalDynamics.Example.dynamics.recover [.external 0] interleavedState)
        foreignReplayState := by
  refine ⟨ambientRecovery_confinement interleavedState, ?_⟩
  intro related
  change 7 = 6 at related
  omega

end Counterexample

end Cordis.GlobalTemporal
