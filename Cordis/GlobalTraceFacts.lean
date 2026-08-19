import Cordis.GlobalCalculus

/-!
# Global trace structural facts

This module audits paper Lemma 54 against the bounded global calculus. Clauses about ordinary,
registration, phase-only, and orchestration steps follow from the current exact endpoints and
Definition 48 confinement. General L-Unload is different: `RecoveryAdmission` proves endpoint
well-formedness but does not constrain an external undo interpreter from changing a foreign
fiber's table or control fields. The missing premise is exposed here as `RecoveryConfinement`.

Consequently, table and non-actor control preservation are unconditional away from L-Unload and
conditional on that named law at L-Unload. Accumulator-map uniqueness and installed-status
boundaries are unconditional. Retirement monotonicity is proved, but this module does not derive
the paper's stronger provenance claim that every retirement write came from an internal
`UndoCode.retire`; opaque external undo codes would need a further code-level law. Likewise,
`RecoveryConfinement` preserves every foreign fiber that was already present, but does not forbid
opaque recovery from adding a brand-new registry name, so clause 54(5)'s new-entry provenance is
not proved. No temporal-composability or full Theorem 59 claim is made.

Source: pinned CORDIS paper text, Lemma 54 and proof, local audit lines 2038--2082.
-/

set_option autoImplicit false

namespace Cordis.GlobalTraceFacts

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Per-fiber and per-step predicates -/

/-- Static/control continuity, allowing only the paper's monotone `false → true` retirement. -/
structure ControlContinuous (before after : Fiber catalog) : Prop where
  component_eq : after.component = before.component
  parent_eq : after.parent = before.parent
  birth_eq : after.birth = before.birth
  phase_eq : HEq after.phase before.phase
  installed_iff : before.Installed ↔ after.Installed
  committed_heq : HEq before.phase.committed? after.phase.committed?
  retired_mono : before.retired = true → after.retired = true

namespace ControlContinuous

theorem refl (fiber : Fiber catalog) : ControlContinuous fiber fiber := {
  component_eq := rfl
  parent_eq := rfl
  birth_eq := rfl
  phase_eq := HEq.rfl
  installed_iff := Iff.rfl
  committed_heq := HEq.rfl
  retired_mono := fun retired ↦ retired
}

theorem declaration_eq
    {before after : Fiber catalog} (continuous : ControlContinuous before after) :
    catalog.declaration after.component = catalog.declaration before.component :=
  congrArg catalog.declaration continuous.component_eq

theorem provision_eq
    {before after : Fiber catalog} (continuous : ControlContinuous before after) :
    (catalog.declaration after.component).provision =
      (catalog.declaration before.component).provision :=
  congrArg ComponentDecl.provision continuous.declaration_eq

theorem entry_eq
    {before after : Fiber catalog} (continuous : ControlContinuous before after) :
    (catalog.declaration after.component).entry =
      (catalog.declaration before.component).entry :=
  congrArg ComponentDecl.entry continuous.declaration_eq

end ControlContinuous

/-- Actor-side static fields and monotone retirement, excluding the intentionally edited phase. -/
structure StaticContinuous (before after : Fiber catalog) : Prop where
  component_eq : after.component = before.component
  parent_eq : after.parent = before.parent
  birth_eq : after.birth = before.birth
  retired_mono : before.retired = true → after.retired = true

namespace StaticContinuous

theorem refl (fiber : Fiber catalog) : StaticContinuous fiber fiber := {
  component_eq := rfl
  parent_eq := rfl
  birth_eq := rfl
  retired_mono := fun retired ↦ retired
}

theorem phaseUpdate
    (fiber : Fiber catalog) (phase : Phase (catalog.declaration fiber.component)) :
    StaticContinuous fiber { fiber with phase := phase } := {
  component_eq := rfl
  parent_eq := rfl
  birth_eq := rfl
  retired_mono := fun retired ↦ retired
}

theorem trans
    {first second third : Fiber catalog}
    (left : StaticContinuous first second) (right : StaticContinuous second third) :
    StaticContinuous first third := {
  component_eq := right.component_eq.trans left.component_eq
  parent_eq := right.parent_eq.trans left.parent_eq
  birth_eq := right.birth_eq.trans left.birth_eq
  retired_mono := fun retired ↦ right.retired_mono (left.retired_mono retired)
}

theorem declaration_eq
    {before after : Fiber catalog} (continuous : StaticContinuous before after) :
    catalog.declaration after.component = catalog.declaration before.component :=
  congrArg catalog.declaration continuous.component_eq

theorem provision_eq
    {before after : Fiber catalog} (continuous : StaticContinuous before after) :
    (catalog.declaration after.component).provision =
      (catalog.declaration before.component).provision :=
  congrArg ComponentDecl.provision continuous.declaration_eq

theorem entry_eq
    {before after : Fiber catalog} (continuous : StaticContinuous before after) :
    (catalog.declaration after.component).entry =
      (catalog.declaration before.component).entry :=
  congrArg ComponentDecl.entry continuous.declaration_eq

end StaticContinuous

theorem ControlContinuous.toStatic
    {before after : Fiber catalog} (continuous : ControlContinuous before after) :
    StaticContinuous before after := {
  component_eq := continuous.component_eq
  parent_eq := continuous.parent_eq
  birth_eq := continuous.birth_eq
  retired_mono := continuous.retired_mono
}

/-- Every fiber present before the step and different from its actor keeps the same table. -/
def ForeignTablesPreserved
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Prop :=
  ∀ name beforeFiber, before.registry name = some beforeFiber →
    name ≠ step.actedName →
    ∃ afterFiber, after.registry name = some afterFiber ∧
      afterFiber.table = beforeFiber.table

/-- Foreign static/lifecycle control is continuous and retirement cannot revert to `false`. -/
def ForeignControlContinuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Prop :=
  ∀ name beforeFiber, before.registry name = some beforeFiber →
    name ≠ step.actedName →
    ∃ afterFiber, after.registry name = some afterFiber ∧
      ControlContinuous beforeFiber afterFiber

/-- Stronger lookup equality used to discharge both foreign predicates before recovery. -/
def ForeignFibersExact
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Prop :=
  ∀ name fiber, before.registry name = some fiber →
    name ≠ step.actedName → after.registry name = some fiber

/-- Exact committed-view continuity whenever the acted-on fiber exists at both endpoints. -/
def CommittedViewContinuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Prop :=
  ∀ beforeFiber afterFiber,
    before.registry step.actedName = some beforeFiber →
    after.registry step.actedName = some afterFiber →
    HEq beforeFiber.phase.committed? afterFiber.phase.committed?

/-- Clause 54(5)'s actor-side parent/declaration/provision/entry and retirement continuity. -/
def ActorStaticContinuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) : Prop :=
  ∀ beforeFiber afterFiber,
    before.registry step.actedName = some beforeFiber →
    after.registry step.actedName = some afterFiber →
    StaticContinuous beforeFiber afterFiber

/-- Static continuity for an arbitrary observed name across one exact step. -/
def NamedStaticContinuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (_step : Step dynamics inertia before after) (name : sig.Name) : Prop :=
  ∀ beforeFiber afterFiber,
    before.registry name = some beforeFiber →
    after.registry name = some afterFiber →
    StaticContinuous beforeFiber afterFiber

/-- Committed-view continuity for an arbitrary observed name across one exact step. -/
def NamedCommittedContinuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (_step : Step dynamics inertia before after) (name : sig.Name) : Prop :=
  ∀ beforeFiber afterFiber,
    before.registry name = some beforeFiber →
    after.registry name = some afterFiber →
    HEq beforeFiber.phase.committed? afterFiber.phase.committed?

/-! ## The exact recovery gap -/

/-- Minimal missing confinement law for Lemma 54's already-present fibers at L-Unload.

It intentionally does not assert that the recovered registry has no brand-new names. That stronger
domain/provenance condition is not available from `RecoveryAdmission`.
-/
structure RecoveryConfinement
    (dynamics : Dynamics sig catalog Ambient) (before : State catalog Ambient)
    (owner : sig.Name) (undos : List (UndoCode sig)) : Prop where
  foreign : ∀ name beforeFiber, before.registry name = some beforeFiber →
    name ≠ owner →
    ∃ afterFiber,
      (dynamics.recover undos before).registry name = some afterFiber ∧
      afterFiber.table = beforeFiber.table ∧
      ControlContinuous beforeFiber afterFiber
  owner_static : ∀ beforeFiber afterFiber,
    before.registry owner = some beforeFiber →
    (dynamics.recover undos before).registry owner = some afterFiber →
    afterFiber.component = beforeFiber.component ∧
    afterFiber.parent = beforeFiber.parent ∧
    afterFiber.birth = beforeFiber.birth ∧
    (beforeFiber.retired = true → afterFiber.retired = true)

/-- Exact evidence surface: only an actual L-Unload constructor asks for recovery confinement. -/
inductive SufficientConfinement
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    {before after : State catalog Ambient} → Step dynamics inertia before after → Prop where
  | orchestration
      {before after : State catalog Ambient} (step : OrchestrationStep before after) :
      SufficientConfinement dynamics inertia (.orchestration step)
  | lifecycle
      {before after : State catalog Ambient}
      (step : GlobalLifecycle.Transition dynamics inertia before after)
      (notUnload :
        (Step.lifecycle step : Step dynamics inertia before after).rule ≠ .lUnload) :
      SufficientConfinement dynamics inertia (.lifecycle step)
  | unload
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (outcome : Option sig.Error)
      (phase : fiber.phase = .unloading undos committed outcome)
      (notRelied : ¬Relied before owner)
      (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome)
      (confinement : RecoveryConfinement dynamics before owner undos) :
      SufficientConfinement dynamics inertia
        (.lifecycle (.unload before owner fiber present undos committed outcome phase
          notRelied admission))

/-! ## Iterator and exact foreign lookup lemmas -/

theorem iteration_foreign_lookup
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before)
    {name : sig.Name} {fiber : Fiber catalog}
    (present : before.registry name = some fiber) (different : name ≠ owner) :
    step.after.registry name = some fiber := by
  obtain ⟨after, undo, next, source, recovers, preserves⟩ := step
  cases source with
  | ordinary result run_eq =>
      rw [(dynamics.ordinary_confined owner code before result run_eq).other_unchanged
        name different]
      exact present
  | registration request admission run_eq =>
      have childDifferent : name ≠ admission.child := by
        intro equal
        subst name
        rw [admission.fresh.lookup_eq] at present
        cases present
      change (insertFiber before admission.child (some owner) request.component).registry name =
        some fiber
      rw [insertFiber_lookup_other before admission.child name (some owner) request.component
        childDifferent]
      exact present

theorem iteration_owner_static
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before)
    {beforeFiber afterFiber : Fiber catalog}
    (beforePresent : before.registry owner = some beforeFiber)
    (afterPresent : step.after.registry owner = some afterFiber) :
    StaticContinuous beforeFiber afterFiber := by
  obtain ⟨after, undo, next, source, recovers, preserves⟩ := step
  cases source with
  | ordinary result run_eq =>
      let confinement := dynamics.ordinary_confined owner code before result run_eq
      rw [confinement.before_present] at beforePresent
      have before_eq : confinement.beforeFiber = beforeFiber :=
        Option.some.inj beforePresent
      subst beforeFiber
      rw [confinement.after_present] at afterPresent
      have after_eq : confinement.afterFiber = afterFiber := Option.some.inj afterPresent
      subst afterFiber
      exact {
        component_eq := confinement.component_eq
        parent_eq := confinement.parent_eq
        birth_eq := confinement.birth_eq
        retired_mono := by
          intro retired
          rw [confinement.retired_eq]
          exact retired
      }
  | registration request admission run_eq =>
      rw [admission.owner_present] at beforePresent
      have before_eq : admission.ownerFiber = beforeFiber := Option.some.inj beforePresent
      subst beforeFiber
      have ownerDifferent : owner ≠ admission.child := by
        intro equal
        have lookupEq := congrArg before.registry equal
        have childPresent :
            before.registry admission.child = some admission.ownerFiber := by
          rw [← lookupEq]
          exact admission.owner_present
        rw [admission.fresh.lookup_eq] at childPresent
        cases childPresent
      change (insertFiber before admission.child (some owner) request.component).registry owner =
        some afterFiber at afterPresent
      rw [insertFiber_lookup_other before admission.child owner (some owner) request.component
        ownerDifferent] at afterPresent
      rw [admission.owner_present] at afterPresent
      have after_eq : admission.ownerFiber = afterFiber := Option.some.inj afterPresent
      subst afterFiber
      exact StaticContinuous.refl admission.ownerFiber

theorem static_of_setPhase_lookup
    (state : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) (afterFiber : Fiber catalog)
    (present : (GlobalLifecycle.setPhase state owner fiber phase).registry owner =
      some afterFiber) :
    StaticContinuous fiber afterFiber := by
  rw [GlobalLifecycle.setPhase_lookup_same] at present
  have after_eq : { fiber with phase := phase } = afterFiber := Option.some.inj present
  subst afterFiber
  exact StaticContinuous.phaseUpdate fiber phase

theorem foreignExact_tables
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (exact : ForeignFibersExact step) : ForeignTablesPreserved step := by
  intro name fiber present different
  exact ⟨fiber, exact name fiber present different, rfl⟩

theorem foreignExact_control
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (exact : ForeignFibersExact step) : ForeignControlContinuous step := by
  intro name fiber present different
  exact ⟨fiber, exact name fiber present different, ControlContinuous.refl fiber⟩

private theorem orchestration_not_unload
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    (Step.orchestration step : Step dynamics inertia before after).rule ≠ .lUnload := by
  cases step <;> intro impossible <;> cases impossible

/-! ## Constructor-wise foreign preservation -/

/-- Every rule other than L-Unload preserves every pre-existing foreign fiber exactly. -/
theorem foreignExact_of_notUnload
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) (notUnload : step.rule ≠ .lUnload) :
    ForeignFibersExact step := by
  cases step with
  | orchestration transition =>
      cases transition with
      | insert name fresh parent parentPresent component provisionFresh =>
          intro foreign foreignFiber present different
          rw [insertFiber_lookup_other before name foreign parent component different]
          exact present
      | retire name fiber present =>
          intro foreign foreignFiber foreignPresent different
          rw [retireFiber_lookup_other before name foreign fiber different]
          exact foreignPresent
      | remove name fiber present retired inactive childless =>
          intro foreign foreignFiber foreignPresent different
          rw [removeFiber_lookup_other before name foreign different]
          exact foreignPresent
  | lifecycle transition =>
      cases transition with
      | begin owner fiber present entry committed target =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other before owner foreign fiber
            (.reloading (catalog.declaration fiber.component).entry [] committed) different]
          exact foreignPresent
      | iter owner fiber present code undos committed phase target landing next continues =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other landing.step.after owner foreign
            landing.afterFiber
            (.reloading next (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed)) different]
          exact iteration_foreign_lookup landing.step foreignPresent different
      | finish owner fiber present code undos committed phase target landing done =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other landing.step.after owner foreign
            landing.afterFiber
            (.active (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed)) different]
          exact iteration_foreign_lookup landing.step foreignPresent different
      | divertAbort owner fiber present code undos committed phase changed abortable =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other before owner foreign fiber
            (.unloading undos committed none) different]
          exact foreignPresent
      | divertLand owner fiber present code undos committed phase changed landing =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other landing.step.after owner foreign
            landing.afterFiber
            (.unloading (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed) none) different]
          exact iteration_foreign_lookup landing.step foreignPresent different
      | raise owner fiber present code undos committed phase error raised =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other before owner foreign fiber
            (.unloading undos committed (some error)) different]
          exact foreignPresent
      | leave owner fiber present undos committed phase changed =>
          intro foreign foreignFiber foreignPresent different
          rw [GlobalLifecycle.setPhase_lookup_other before owner foreign fiber
            (.unloading undos committed none) different]
          exact foreignPresent
      | unload owner fiber present undos committed outcome phase notRelied admission =>
          exact False.elim (notUnload rfl)

theorem foreignTables_of_notUnload
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) (notUnload : step.rule ≠ .lUnload) :
    ForeignTablesPreserved step :=
  foreignExact_tables (foreignExact_of_notUnload step notUnload)

theorem foreignControl_of_notUnload
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) (notUnload : step.rule ≠ .lUnload) :
    ForeignControlContinuous step :=
  foreignExact_control (foreignExact_of_notUnload step notUnload)

theorem unload_foreignTables
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (outcome : Option sig.Error)
    (phase : fiber.phase = .unloading undos committed outcome)
    (notRelied : ¬Relied before owner)
    (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome)
    (confinement : RecoveryConfinement dynamics before owner undos) :
    ForeignTablesPreserved
      (Step.lifecycle (.unload before owner fiber present undos committed outcome phase
        notRelied admission) : Step dynamics inertia before admission.after) := by
  intro name beforeFiber beforePresent different
  obtain ⟨afterFiber, recoveredPresent, tableEq, control⟩ :=
    confinement.foreign name beforeFiber beforePresent different
  refine ⟨afterFiber, ?_, tableEq⟩
  rw [admission.after_eq]
  rw [GlobalLifecycle.setPhase_lookup_other (dynamics.recover undos before) owner name
    admission.recoveredFiber (admission.component_eq ▸ .inactive outcome) different]
  exact recoveredPresent

theorem unload_foreignControl
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (outcome : Option sig.Error)
    (phase : fiber.phase = .unloading undos committed outcome)
    (notRelied : ¬Relied before owner)
    (admission : GlobalLifecycle.RecoveryAdmission dynamics before owner fiber undos outcome)
    (confinement : RecoveryConfinement dynamics before owner undos) :
    ForeignControlContinuous
      (Step.lifecycle (.unload before owner fiber present undos committed outcome phase
        notRelied admission) : Step dynamics inertia before admission.after) := by
  intro name beforeFiber beforePresent different
  obtain ⟨afterFiber, recoveredPresent, tableEq, control⟩ :=
    confinement.foreign name beforeFiber beforePresent different
  refine ⟨afterFiber, ?_, control⟩
  rw [admission.after_eq]
  rw [GlobalLifecycle.setPhase_lookup_other (dynamics.recover undos before) owner name
    admission.recoveredFiber (admission.component_eq ▸ .inactive outcome) different]
  exact recoveredPresent

/-- Lemma 54(1)/(5), conditional exactly where accumulated recovery lacked confinement. -/
theorem foreignTables_preserved
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (sufficient : SufficientConfinement dynamics inertia step) :
    ForeignTablesPreserved step := by
  cases sufficient with
  | orchestration step =>
      exact foreignTables_of_notUnload _ (orchestration_not_unload step)
  | lifecycle step notUnload =>
      exact foreignTables_of_notUnload _ notUnload
  | unload owner fiber present undos committed outcome phase notRelied admission
      confinement =>
      exact unload_foreignTables before owner fiber present undos committed outcome phase
        notRelied admission confinement

/-- Non-actor control/static continuity under the same minimal recovery premise. -/
theorem foreignControl_continuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (sufficient : SufficientConfinement dynamics inertia step) :
    ForeignControlContinuous step := by
  cases sufficient with
  | orchestration step =>
      exact foreignControl_of_notUnload _ (orchestration_not_unload step)
  | lifecycle step notUnload =>
      exact foreignControl_of_notUnload _ notUnload
  | unload owner fiber present undos committed outcome phase notRelied admission
      confinement =>
      exact unload_foreignControl before owner fiber present undos committed outcome phase
        notRelied admission confinement

/-- Clause 54(5) fragment: actor static fields persist and retirement is monotone. -/
theorem actorStatic_continuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (sufficient : SufficientConfinement dynamics inertia step) :
    ActorStaticContinuous step := by
  cases sufficient with
  | orchestration transition =>
      cases transition with
      | insert name fresh parent parentPresent component provisionFresh =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry name = some beforeFiber at beforePresent
          rw [fresh.lookup_eq] at beforePresent
          cases beforePresent
      | retire name fiber present =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry name = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (retireFiber before name fiber).registry name = some afterFiber at afterPresent
          rw [retireFiber_lookup_same] at afterPresent
          have after_eq : { fiber with retired := true } = afterFiber :=
            Option.some.inj afterPresent
          subst afterFiber
          exact {
            component_eq := rfl
            parent_eq := rfl
            birth_eq := rfl
            retired_mono := fun retired ↦ rfl
          }
      | remove name fiber present retired inactive childless =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change (removeFiber before name).registry name = some afterFiber at afterPresent
          rw [removeFiber_lookup_same] at afterPresent
          cases afterPresent
  | lifecycle transition notUnload =>
      cases transition with
      | begin owner fiber present entry committed target =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          exact static_of_setPhase_lookup before owner fiber
            (.reloading (catalog.declaration fiber.component).entry [] committed)
            afterFiber afterPresent
      | iter owner fiber present code undos committed phase target landing next continues =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          have iteratorStatic :=
            iteration_owner_static landing.step beforePresent landing.after_present
          change (GlobalLifecycle.setPhase landing.step.after owner landing.afterFiber
            (.reloading next (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed))).registry owner =
            some afterFiber at afterPresent
          exact iteratorStatic.trans <|
            static_of_setPhase_lookup landing.step.after owner landing.afterFiber
              (.reloading next (landing.step.undo :: undos)
                (landing.component_eq.symm ▸ committed)) afterFiber afterPresent
      | finish owner fiber present code undos committed phase target landing done =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          have iteratorStatic :=
            iteration_owner_static landing.step beforePresent landing.after_present
          change (GlobalLifecycle.setPhase landing.step.after owner landing.afterFiber
            (.active (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed))).registry owner =
            some afterFiber at afterPresent
          exact iteratorStatic.trans <|
            static_of_setPhase_lookup landing.step.after owner landing.afterFiber
              (.active (landing.step.undo :: undos)
                (landing.component_eq.symm ▸ committed)) afterFiber afterPresent
      | divertAbort owner fiber present code undos committed phase changed abortable =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          exact static_of_setPhase_lookup before owner fiber
            (.unloading undos committed none) afterFiber afterPresent
      | divertLand owner fiber present code undos committed phase changed landing =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          have iteratorStatic :=
            iteration_owner_static landing.step beforePresent landing.after_present
          change (GlobalLifecycle.setPhase landing.step.after owner landing.afterFiber
            (.unloading (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed) none)).registry owner =
            some afterFiber at afterPresent
          exact iteratorStatic.trans <|
            static_of_setPhase_lookup landing.step.after owner landing.afterFiber
              (.unloading (landing.step.undo :: undos)
                (landing.component_eq.symm ▸ committed) none) afterFiber afterPresent
      | raise owner fiber present code undos committed phase error raised =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          exact static_of_setPhase_lookup before owner fiber
            (.unloading undos committed (some error)) afterFiber afterPresent
      | leave owner fiber present undos committed phase changed =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          exact static_of_setPhase_lookup before owner fiber
            (.unloading undos committed none) afterFiber afterPresent
      | unload owner fiber present undos committed outcome phase notRelied admission =>
          exact False.elim (notUnload rfl)
  | unload owner fiber present undos committed outcome phase notRelied admission
      confinement =>
      intro beforeFiber afterFiber beforePresent afterPresent
      change before.registry owner = some beforeFiber at beforePresent
      rw [present] at beforePresent
      have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
      subst beforeFiber
      have ownerStatic := confinement.owner_static fiber admission.recoveredFiber
        present admission.recovered_present
      have recoveredStatic : StaticContinuous fiber admission.recoveredFiber := {
        component_eq := ownerStatic.1
        parent_eq := ownerStatic.2.1
        birth_eq := ownerStatic.2.2.1
        retired_mono := ownerStatic.2.2.2
      }
      change admission.after.registry owner = some afterFiber at afterPresent
      rw [admission.after_eq] at afterPresent
      exact recoveredStatic.trans <|
        static_of_setPhase_lookup (dynamics.recover undos before) owner
          admission.recoveredFiber (admission.component_eq ▸ .inactive outcome)
          afterFiber afterPresent

/-! ## Committed-view and accumulator continuity -/

private theorem committed_heq_transport
    {afterComponent beforeComponent : sig.ComponentId}
    (component_eq : afterComponent = beforeComponent)
    (committed : CommittedView (catalog.declaration beforeComponent)) :
    HEq (some committed) (some (component_eq.symm ▸ committed)) := by
  cases component_eq
  rfl

/-- Away from the two installation boundaries, the actor carries the exact committed view. -/
theorem committedView_continuous_unless_boundary
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after)
    (notBegin : step.rule ≠ .lBegin) (notUnload : step.rule ≠ .lUnload) :
    CommittedViewContinuous step := by
  cases step with
  | orchestration transition =>
      cases transition with
      | insert name fresh parent parentPresent component provisionFresh =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry name = some beforeFiber at beforePresent
          rw [fresh.lookup_eq] at beforePresent
          cases beforePresent
      | retire name fiber present =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry name = some beforeFiber at beforePresent
          change (retireFiber before name fiber).registry name = some afterFiber at afterPresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          rw [retireFiber_lookup_same] at afterPresent
          have after_eq : { fiber with retired := true } = afterFiber :=
            Option.some.inj afterPresent
          subst afterFiber
          rfl
      | remove name fiber present retired inactive childless =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change (removeFiber before name).registry name = some afterFiber at afterPresent
          rw [removeFiber_lookup_same] at afterPresent
          cases afterPresent
  | lifecycle transition =>
      cases transition with
      | begin owner fiber present entry committed target =>
          exact False.elim (notBegin rfl)
      | iter owner fiber present code undos committed phase target landing next continues =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (GlobalLifecycle.setPhase landing.step.after owner landing.afterFiber
            (.reloading next (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed))).registry owner =
            some afterFiber at afterPresent
          rw [GlobalLifecycle.setPhase_lookup_same] at afterPresent
          have after_eq := Option.some.inj afterPresent
          subst afterFiber
          rw [phase]
          simp only [Phase.committed?]
          exact committed_heq_transport landing.component_eq committed
      | finish owner fiber present code undos committed phase target landing done =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (GlobalLifecycle.setPhase landing.step.after owner landing.afterFiber
            (.active (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed))).registry owner =
            some afterFiber at afterPresent
          rw [GlobalLifecycle.setPhase_lookup_same] at afterPresent
          have after_eq := Option.some.inj afterPresent
          subst afterFiber
          rw [phase]
          simp only [Phase.committed?]
          exact committed_heq_transport landing.component_eq committed
      | divertAbort owner fiber present code undos committed phase changed abortable =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (GlobalLifecycle.setPhase before owner fiber
            (.unloading undos committed none)).registry owner = some afterFiber at afterPresent
          rw [GlobalLifecycle.setPhase_lookup_same] at afterPresent
          have after_eq := Option.some.inj afterPresent
          subst afterFiber
          rw [phase]
          rfl
      | divertLand owner fiber present code undos committed phase changed landing =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (GlobalLifecycle.setPhase landing.step.after owner landing.afterFiber
            (.unloading (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed) none)).registry owner =
            some afterFiber at afterPresent
          rw [GlobalLifecycle.setPhase_lookup_same] at afterPresent
          have after_eq := Option.some.inj afterPresent
          subst afterFiber
          rw [phase]
          simp only [Phase.committed?]
          exact committed_heq_transport landing.component_eq committed
      | raise owner fiber present code undos committed phase error raised =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (GlobalLifecycle.setPhase before owner fiber
            (.unloading undos committed (some error))).registry owner =
            some afterFiber at afterPresent
          rw [GlobalLifecycle.setPhase_lookup_same] at afterPresent
          have after_eq := Option.some.inj afterPresent
          subst afterFiber
          rw [phase]
          rfl
      | leave owner fiber present undos committed phase changed =>
          intro beforeFiber afterFiber beforePresent afterPresent
          change before.registry owner = some beforeFiber at beforePresent
          rw [present] at beforePresent
          have before_eq : fiber = beforeFiber := Option.some.inj beforePresent
          subst beforeFiber
          change (GlobalLifecycle.setPhase before owner fiber
            (.unloading undos committed none)).registry owner = some afterFiber at afterPresent
          rw [GlobalLifecycle.setPhase_lookup_same] at afterPresent
          have after_eq := Option.some.inj afterPresent
          subst afterFiber
          rw [phase]
          rfl
      | unload owner fiber present undos committed outcome phase notRelied admission =>
          exact False.elim (notUnload rfl)

theorem namedStatic_continuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (sufficient : SufficientConfinement dynamics inertia step) (name : sig.Name) :
    NamedStaticContinuous step name := by
  by_cases same : name = step.actedName
  · subst name
    exact actorStatic_continuous sufficient
  · intro beforeFiber afterFiber beforePresent afterPresent
    obtain ⟨witness, witnessPresent, control⟩ :=
      foreignControl_continuous sufficient name beforeFiber beforePresent same
    rw [afterPresent] at witnessPresent
    have witness_eq : afterFiber = witness := Option.some.inj witnessPresent
    subst witness
    exact control.toStatic

theorem namedCommitted_continuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (sufficient : SufficientConfinement dynamics inertia step)
    (name : sig.Name)
    (sameActorNoBoundary : step.actedName = name →
      step.rule ≠ .lBegin ∧ step.rule ≠ .lUnload) : NamedCommittedContinuous step name := by
  by_cases same : name = step.actedName
  · subst name
    have bounds := sameActorNoBoundary rfl
    exact committedView_continuous_unless_boundary step bounds.1 bounds.2
  · intro beforeFiber afterFiber beforePresent afterPresent
    obtain ⟨witness, witnessPresent, control⟩ :=
      foreignControl_continuous sufficient name beforeFiber beforePresent same
    rw [afterPresent] at witnessPresent
    have witness_eq : afterFiber = witness := Option.some.inj witnessPresent
    subst witness
    exact control.committed_heq

theorem installedAt_forward
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    (sufficient : SufficientConfinement dynamics inertia step)
    (name : sig.Name)
    (sameActorNoBoundary : step.actedName = name →
      step.rule ≠ .lBegin ∧ step.rule ≠ .lUnload) :
    InstalledAt before name → InstalledAt after name := by
  intro installed
  by_cases same : name = step.actedName
  · subst name
    have bounds := sameActorNoBoundary rfl
    exact (step.installedAt_preserved_unless_boundary bounds.1 bounds.2).1 installed
  · obtain ⟨beforeFiber, beforePresent, beforeInstalled⟩ := installed
    obtain ⟨afterFiber, afterPresent, control⟩ :=
      foreignControl_continuous sufficient name beforeFiber beforePresent same
    exact ⟨afterFiber, afterPresent, control.installed_iff.1 beforeInstalled⟩

/-- Lemma 54(3): accumulated recovery is selected exactly at L-Unload. -/
theorem accumulatedRecovery_iff_unload
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) :
    step.stateMap = .accumulatedRecovery ↔ step.rule = .lUnload :=
  step.recovery_map_iff

/-! ## Finite trace states and aligned step records -/

structure StepRecord
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) where
  before : State catalog Ambient
  after : State catalog Ambient
  step : Step dynamics inertia before after

namespace StepRecord

def rule
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    (record : StepRecord dynamics inertia) : Rule :=
  record.step.rule

end StepRecord

namespace Trace

def records
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    GlobalCalculus.Trace dynamics inertia before after → List (StepRecord dynamics inertia)
  | .nil _ => []
  | .cons head tail => ⟨_, _, head⟩ :: records tail

def states
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    GlobalCalculus.Trace dynamics inertia before after → List (State catalog Ambient)
  | .nil state => [state]
  | .cons head tail => before :: states tail

/-- List-level certificate that every recorded endpoint is the next recorded source. -/
inductive Aligned
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) :
    List (State catalog Ambient) → List (StepRecord dynamics inertia) → Prop where
  | terminal (state : State catalog Ambient) : Aligned dynamics inertia [state] []
  | cons
      (record : StepRecord dynamics inertia)
      {restStates : List (State catalog Ambient)}
      {restRecords : List (StepRecord dynamics inertia)}
      (next : restStates.head? = some record.after)
      (tail : Aligned dynamics inertia restStates restRecords) :
      Aligned dynamics inertia (record.before :: restStates) (record :: restRecords)

theorem states_head
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    (states trace).head? = some before := by
  cases trace <;> rfl

theorem aligned
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    Aligned dynamics inertia (states trace) (records trace) := by
  induction trace with
  | nil state => exact .terminal state
  | cons head tail ih => exact .cons ⟨_, _, head⟩ (states_head tail) ih

theorem states_length
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    (states trace).length = (records trace).length + 1 := by
  induction trace with
  | nil => rfl
  | cons head tail ih => simp [states, records, ih]

theorem rules_aligned
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    (records trace).map StepRecord.rule = trace.rules := by
  induction trace with
  | nil => rfl
  | cons head tail ih => simp [records, GlobalCalculus.Trace.rules, StepRecord.rule, ih]

def Sufficient
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) : Prop :=
  ∀ record, record ∈ records trace →
    SufficientConfinement dynamics inertia record.step

def NoBoundaryFor
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after) (name : sig.Name) : Prop :=
  ∀ record, record ∈ records trace →
    record.step.actedName = name → record.rule ≠ .lBegin ∧ record.rule ≠ .lUnload

theorem NoBoundaryFor.namedCommittedViewContinuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    {name : sig.Name} (noBoundary : NoBoundaryFor trace name)
    (sufficient : Sufficient trace)
    (record : StepRecord dynamics inertia) (member : record ∈ records trace) :
    NamedCommittedContinuous record.step name :=
  namedCommitted_continuous (sufficient record member) name (noBoundary record member)

theorem installedAt_forward
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (sufficient : Sufficient trace) (name : sig.Name)
    (noBoundary : NoBoundaryFor trace name) :
    InstalledAt before name → InstalledAt after name := by
  intro installed
  induction trace with
  | nil => exact installed
  | cons head tail ih =>
      let record : StepRecord dynamics inertia := ⟨_, _, head⟩
      have headMember : record ∈ records (.cons head tail) := by
        exact List.mem_cons_self
      have headSufficient : SufficientConfinement dynamics inertia head :=
        sufficient record headMember
      have headBounds := noBoundary record headMember
      have middleInstalled := Cordis.GlobalTraceFacts.installedAt_forward
        headSufficient name headBounds installed
      have tailSufficient : Sufficient tail := by
        intro candidate member
        exact sufficient candidate (List.mem_cons_of_mem record member)
      have tailNoBoundary : NoBoundaryFor tail name := by
        intro candidate member sameActor
        exact noBoundary candidate (List.mem_cons_of_mem record member) sameActor
      exact ih tailSufficient tailNoBoundary middleInstalled

def append
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient} :
    GlobalCalculus.Trace dynamics inertia start middle →
    GlobalCalculus.Trace dynamics inertia middle finish →
    GlobalCalculus.Trace dynamics inertia start finish
  | .nil _, tail => tail
  | .cons head rest, tail => .cons head (append rest tail)

end Trace

/-! ## A bounded episode with explicit aligned opening and closing steps -/

structure BoundedEpisode
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    (initial final : State catalog Ambient) where
  name : sig.Name
  openBefore : State catalog Ambient
  openAfter : State catalog Ambient
  closeBefore : State catalog Ambient
  closeAfter : State catalog Ambient
  beforeTrace : GlobalCalculus.Trace dynamics inertia initial openBefore
  openStep : Step dynamics inertia openBefore openAfter
  interior : GlobalCalculus.Trace dynamics inertia openAfter closeBefore
  closeStep : Step dynamics inertia closeBefore closeAfter
  afterTrace : GlobalCalculus.Trace dynamics inertia closeAfter final
  open_name : openStep.actedName = name
  close_name : closeStep.actedName = name
  open_not_installed : ¬InstalledAt openBefore name
  open_installed : InstalledAt openAfter name
  close_not_installed : ¬InstalledAt closeAfter name
  interior_sufficient : Trace.Sufficient interior
  interior_no_boundary : Trace.NoBoundaryFor interior name

namespace BoundedEpisode

def trace
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final) :
    GlobalCalculus.Trace dynamics inertia initial final :=
  Trace.append episode.beforeTrace <|
    .cons episode.openStep <|
      Trace.append episode.interior <| .cons episode.closeStep episode.afterTrace

theorem interior_close_installed
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final) :
    InstalledAt episode.closeBefore episode.name :=
  Trace.installedAt_forward episode.interior episode.interior_sufficient
    episode.name episode.interior_no_boundary episode.open_installed

theorem interior_static_continuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    (record : StepRecord dynamics inertia)
    (member : record ∈ Trace.records episode.interior) :
    NamedStaticContinuous record.step episode.name :=
  namedStatic_continuous (episode.interior_sufficient record member) episode.name

theorem interior_committed_continuous
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    (record : StepRecord dynamics inertia)
    (member : record ∈ Trace.records episode.interior) :
    NamedCommittedContinuous record.step episode.name :=
  namedCommitted_continuous (episode.interior_sufficient record member) episode.name
    (episode.interior_no_boundary record member)

theorem open_rule
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final) :
    episode.openStep.rule = .lBegin := by
  have openNot : ¬InstalledAt episode.openBefore episode.openStep.actedName := by
    simpa [episode.open_name] using episode.open_not_installed
  have openInstalled : InstalledAt episode.openAfter episode.openStep.actedName := by
    simpa [episode.open_name] using episode.open_installed
  have changed : ¬(InstalledAt episode.openBefore episode.openStep.actedName ↔
      InstalledAt episode.openAfter episode.openStep.actedName) := by
    intro continuous
    exact openNot (continuous.mpr openInstalled)
  rcases episode.openStep.installedAt_change_only_boundary changed with begin | unload
  · exact begin
  · exact False.elim (openNot (episode.openStep.unload_uninstalls_actor unload).1)

theorem close_rule
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final) :
    episode.closeStep.rule = .lUnload := by
  have closeInstalled : InstalledAt episode.closeBefore episode.closeStep.actedName := by
    simpa [episode.close_name] using episode.interior_close_installed
  have closeNot : ¬InstalledAt episode.closeAfter episode.closeStep.actedName := by
    simpa [episode.close_name] using episode.close_not_installed
  have changed : ¬(InstalledAt episode.closeBefore episode.closeStep.actedName ↔
      InstalledAt episode.closeAfter episode.closeStep.actedName) := by
    intro continuous
    exact closeNot (continuous.mp closeInstalled)
  rcases episode.closeStep.installedAt_change_only_boundary changed with begin | unload
  · exact False.elim ((episode.closeStep.begin_installs_actor begin).1 closeInstalled)
  · exact unload

end BoundedEpisode

/-! ## Kernel countermodel for bare recovery admission -/

namespace Counterexample

abbrev Value : Unit → Type
  | _ => Nat

abbrev exampleSignature : StaticSignature where
  Name := Bool
  Key := Unit
  ComponentId := Bool
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Unit
  Value := Value
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def ownerDecl : ComponentDecl exampleSignature where
  dependencies := { keys := [], nodup := by simp }
  provision := []
  provision_nodup := by simp
  entry := ()

def foreignDecl : ComponentDecl exampleSignature where
  dependencies := { keys := [], nodup := by simp }
  provision := [()]
  provision_nodup := by simp
  entry := ()

abbrev exampleCatalog : Catalog exampleSignature where
  declaration
    | false => ownerDecl
    | true => foreignDecl

def ownerView : CommittedView ownerDecl where
  provider declared := by
    rcases declared with ⟨key, declared⟩
    simp [ownerDecl] at declared

def foreignView : CommittedView foreignDecl where
  provider declared := by
    rcases declared with ⟨key, declared⟩
    simp [foreignDecl] at declared

def foreignTable (value : Nat) : Coeffect.Context Unit Value :=
  Coeffect.setAt Coeffect.empty () value

def ownerFiber : Fiber exampleCatalog where
  component := false
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .unloading [.external ()] ownerView none

def foreignFiber (value : Nat) : Fiber exampleCatalog where
  component := true
  parent := none
  birth := 1
  table := foreignTable value
  table_within_provision := by
    intro key present
    cases key
    simp [foreignDecl]
  retired := false
  phase := .active [] foreignView

abbrev ExampleState := GlobalState exampleCatalog Unit

def state (value : Nat) : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Coeffect.setAt (Coeffect.setAt Coeffect.empty false ownerFiber)
    true (foreignFiber value)

theorem state_owner_present (value : Nat) :
    (state value).registry false = some ownerFiber := by
  rfl

theorem state_foreign_present (value : Nat) :
    (state value).registry true = some (foreignFiber value) := by
  rfl

theorem state_wellFormed (value : Nat) : WellFormed (state value) := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [state] at lookup <;> subst fiber <;>
      simp [state, ownerFiber, foreignFiber]
  · intro name fiber parent lookup parent_eq
    cases name <;> simp [state] at lookup <;> subst fiber <;>
      simp [ownerFiber, foreignFiber] at parent_eq
  · intro name fiber parent parentFiber lookup parent_eq parentLookup
    cases name <;> simp [state] at lookup <;> subst fiber <;>
      simp [ownerFiber, foreignFiber] at parent_eq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    cases left <;> cases right <;> simp [state] at leftLookup rightLookup <;>
      subst leftFiber <;> subst rightFiber <;>
      simp [ownerFiber, foreignFiber, ownerDecl, foreignDecl] at leftKey rightKey ⊢
  · intro name fiber lookup committed committed_eq declared
    cases name <;> simp [state] at lookup <;> subst fiber
    · rcases declared with ⟨key, declared⟩
      change key ∈ ownerDecl.dependencies.keys at declared
      simp [ownerDecl] at declared
    · rcases declared with ⟨key, declared⟩
      change key ∈ foreignDecl.dependencies.keys at declared
      simp [foreignDecl] at declared
  · intro name fiber lookup committed committed_eq declared providerFiber providerLookup
    cases name <;> simp [state] at lookup <;> subst fiber
    · rcases declared with ⟨key, declared⟩
      change key ∈ ownerDecl.dependencies.keys at declared
      simp [ownerDecl] at declared
    · rcases declared with ⟨key, declared⟩
      change key ∈ foreignDecl.dependencies.keys at declared
      simp [foreignDecl] at declared

def runIterator (_owner : exampleSignature.Name) (_code : exampleSignature.IteratorCode)
    (_before : ExampleState) :
    Except exampleSignature.Error (IteratorResult exampleCatalog Unit) :=
  .error ()

def applyExternalUndo (_undo : exampleSignature.ExternalUndoCode)
    (_before : ExampleState) : ExampleState :=
  state 8

def universalSetoid : Setoid ExampleState where
  r _ _ := True
  iseqv := {
    refl := fun _ ↦ trivial
    symm := fun _ ↦ trivial
    trans := fun _ _ ↦ trivial
  }

def dynamics : Dynamics exampleSignature exampleCatalog Unit where
  equivalence := universalSetoid
  runIterator := runIterator
  applyExternalUndo := applyExternalUndo
  ordinary_recovers := by
    intro owner code before result run_eq
    simp [runIterator] at run_eq
  externalUndo_respects := by intros; trivial
  ordinary_confined := by
    intro owner code before result run_eq
    simp [runIterator] at run_eq
  ordinary_preserves_wellFormed := by
    intro owner code before result run_eq
    simp [runIterator] at run_eq
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact .errors rfl
  ReadEquivalent := fun _ _ _ ↦ True
  read_refl := by intros; trivial
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact .errors rfl
  retire_respects := by intros; trivial

def inertia : GlobalLifecycle.InertiaPolicy dynamics where
  canAbort _ _ _ := False

theorem recover_exact :
    dynamics.recover [.external ()] (state 7) = state 8 := rfl

theorem state_notRelied (value : Nat) : ¬Relied (state value) false := by
  rintro ⟨name, fiber, lookup, different, installed,
    committed, committed_eq, declared, resolves⟩
  cases name <;> simp [state] at lookup <;> subst fiber
  · rcases declared with ⟨key, declared⟩
    change key ∈ ownerDecl.dependencies.keys at declared
    simp [ownerDecl] at declared
  · rcases declared with ⟨key, declared⟩
    change key ∈ foreignDecl.dependencies.keys at declared
    simp [foreignDecl] at declared

def inactiveAfter : ExampleState :=
  GlobalLifecycle.setPhase (state 8) false ownerFiber (.inactive none)

theorem inactiveAfter_wellFormed : WellFormed inactiveAfter :=
  GlobalLifecycle.setPhase_inactive_preserves (state_owner_present 8) none
    (state_notRelied 8) (state_wellFormed 8)

def bareAdmission :
    GlobalLifecycle.RecoveryAdmission dynamics (state 7) false ownerFiber
      [.external ()] none where
  before_present := state_owner_present 7
  recoveredFiber := ownerFiber
  recovered_present := by rfl
  component_eq := rfl
  after := inactiveAfter
  after_eq := rfl
  preserves_wellFormed := fun _ ↦ inactiveAfter_wellFormed

def unloadTransition :
    GlobalLifecycle.Transition dynamics inertia (state 7) inactiveAfter :=
  .unload (state 7) false ownerFiber (state_owner_present 7) [.external ()]
    ownerView none rfl (state_notRelied 7) bareAdmission

def unloadStep : Step dynamics inertia (state 7) inactiveAfter :=
  .lifecycle unloadTransition

theorem inactiveAfter_foreign_present :
    inactiveAfter.registry true = some (foreignFiber 8) := rfl

/-- Bare `RecoveryAdmission` admits a well-formed unload that mutates a foreign table. -/
theorem bareAdmission_breaks_foreignTables : ¬ForeignTablesPreserved unloadStep := by
  intro preserved
  obtain ⟨afterFiber, afterPresent, tableEq⟩ :=
    preserved true (foreignFiber 7) (state_foreign_present 7) (by decide)
  rw [inactiveAfter_foreign_present] at afterPresent
  have after_eq : foreignFiber 8 = afterFiber := Option.some.inj afterPresent
  subst afterFiber
  have valueEq := congrArg (fun table ↦ table ()) tableEq
  simp [foreignFiber, foreignTable] at valueEq

/-- Therefore the new recovery law is genuinely additional, not derivable from bare admission. -/
theorem bareAdmission_not_recoveryConfinement :
    ¬RecoveryConfinement dynamics (state 7) false [.external ()] := by
  intro confinement
  have sufficient : SufficientConfinement dynamics inertia unloadStep :=
    .unload (state 7) false ownerFiber (state_owner_present 7) [.external ()]
      ownerView none rfl (state_notRelied 7) bareAdmission confinement
  exact bareAdmission_breaks_foreignTables (foreignTables_preserved sufficient)

end Counterexample

end Cordis.GlobalTraceFacts
