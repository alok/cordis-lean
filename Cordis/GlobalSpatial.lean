import Cordis.GlobalTraceFacts
import Cordis.GlobalTemporal

/-!
# Spatial episode facts

This module proves the strongest finite, exact-endpoint fragment of paper Theorems 63 and 64
supported by the current global calculus.

* `begin_dependencies_provided` is unconditional: every admitted L-Begin target is assembled
  from active providers, so every declared dependency is present in the derived active context.
* `LocatedEpisode` embeds a name-specific bounded episode in one master trace and exposes exact
  opening and closing offsets. `NestedEpisodes` is the explicit prefix/interior decomposition
  needed to turn two independently bounded episodes into Theorem 63(2)'s strict inequalities.
* `resolution_throughout_interior` proves Theorem 63(1)'s committed provider-name constancy on
  the consumer interior. L-Unload is locally impossible while that installed consumer resolves to
  its owner, giving the corresponding finite no-close consequence.
* Provider-table constancy follows from a named per-record confinement premise. Sufficient
  recovery confinement proves that premise for foreign actors, but does not by itself rule out
  same-name iterator edits. Thus Theorem 63(3) is conditional, and this file does not claim the
  paper's full nesting or table-constancy conclusions from `WellFormed` alone.
* `reloading_target_dichotomy` is the local target-stability/divert-or-raise fragment of
  Theorem 64. No use is made of the parameterized Corollary 62 statement in `GlobalTemporal`.

The missing global bridge is deliberate: the current API has bounded episodes and finite traces,
but no maximal-episode theorem saying that every installed occurrence of a name belongs to one
chosen located episode. Such a premise is represented here by `NestedEpisodes`, rather than being
silently inferred.
-/

set_option autoImplicit false

namespace Cordis.GlobalSpatial

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalCalculus
open Cordis.GlobalTraceFacts

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## L-Begin provides every declared dependency -/

/-- A named fiber is present and all dependencies of its component are in the active context. -/
def DependenciesProvided (state : State catalog Ambient) (name : sig.Name) : Prop :=
  ∃ fiber, state.registry name = some fiber ∧
    Coeffect.Satisfies (activeContext state)
      (catalog.declaration fiber.component).dependencies

/-- Exact L-Begin target evidence implies that every declared dependency is actively provided. -/
theorem begin_dependencies_provided
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after)
    (wf : WellFormed before) (beginRule : step.rule = .lBegin) :
    DependenciesProvided before step.actedName := by
  classical
  cases step with
  | orchestration orchestration =>
      cases orchestration <;> cases beginRule
  | lifecycle transition =>
      cases transition with
      | begin owner fiber present entry committed target =>
          refine ⟨fiber, present, ?_⟩
          apply (Coeffect.satisfies_iff _ _).2
          intro key required
          let declared : DeclaredKey (catalog.declaration fiber.component) :=
            ⟨key, required⟩
          obtain ⟨providerFiber, providerPresent, providerActive, tablePresent⟩ :=
            (targetView_sound wf target).resolves_active declared
          obtain ⟨value, tableEq⟩ := Option.isSome_iff_exists.mp tablePresent
          have activeValue : ActiveValue before key value :=
            ⟨committed.provider declared, providerFiber, providerPresent,
              providerActive, tableEq⟩
          rw [(activeContext_value_iff wf).2 activeValue]
          rfl
      | iter => cases beginRule
      | finish => cases beginRule
      | divertAbort => cases beginRule
      | divertLand => cases beginRule
      | raise => cases beginRule
      | leave => cases beginRule
      | unload => cases beginRule

/-! ## Episodes located in one master trace -/

namespace Trace

@[simp] theorem records_append
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : GlobalCalculus.Trace dynamics inertia start middle)
    (right : GlobalCalculus.Trace dynamics inertia middle finish) :
    GlobalTraceFacts.Trace.records (GlobalTraceFacts.Trace.append left right) =
      GlobalTraceFacts.Trace.records left ++ GlobalTraceFacts.Trace.records right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp [GlobalTraceFacts.Trace.append,
      GlobalTraceFacts.Trace.records, ih]

end Trace

/-- A bounded episode together with proof that its five pieces are exactly one master trace. -/
structure LocatedEpisode
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    {initial final : State catalog Ambient}
    (master : GlobalCalculus.Trace dynamics inertia initial final) where
  episode : BoundedEpisode dynamics inertia initial final
  trace_eq : episode.trace = master

namespace LocatedEpisode

/-- Zero-based record offset of the opening L-Begin step. -/
def openOffset
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) : Nat :=
  (GlobalTraceFacts.Trace.records located.episode.beforeTrace).length

/-- Zero-based record offset of the closing L-Unload step. -/
def closeOffset
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) : Nat :=
  located.openOffset + 1 +
    (GlobalTraceFacts.Trace.records located.episode.interior).length

/-- The master record list is the episode's explicit prefix/open/interior/close/suffix split. -/
theorem records_eq
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) :
    GlobalTraceFacts.Trace.records master =
      GlobalTraceFacts.Trace.records located.episode.beforeTrace ++
        ⟨located.episode.openBefore, located.episode.openAfter,
          located.episode.openStep⟩ ::
        (GlobalTraceFacts.Trace.records located.episode.interior ++
          ⟨located.episode.closeBefore, located.episode.closeAfter,
            located.episode.closeStep⟩ ::
          GlobalTraceFacts.Trace.records located.episode.afterTrace) := by
  simpa [BoundedEpisode.trace, GlobalTraceFacts.Trace.records] using
    congrArg (fun trace => GlobalTraceFacts.Trace.records trace) located.trace_eq.symm

theorem open_before_close
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (located : LocatedEpisode dynamics inertia master) :
    located.openOffset < located.closeOffset := by
  change (GlobalTraceFacts.Trace.records located.episode.beforeTrace).length <
    (GlobalTraceFacts.Trace.records located.episode.beforeTrace).length + 1 +
      (GlobalTraceFacts.Trace.records located.episode.interior).length
  omega

end LocatedEpisode

/--
The explicit master-trace/maximality witness missing from two independent `BoundedEpisode`s.
The consumer prefix reaches its opening through the provider opening and `betweenOpen`, while the
provider interior is exactly the consumer's whole episode surrounded by two internal traces.
-/
structure NestedEpisodes
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    (provider consumer : LocatedEpisode dynamics inertia master) where
  betweenOpen : GlobalCalculus.Trace dynamics inertia
    provider.episode.openAfter consumer.episode.openBefore
  betweenClose : GlobalCalculus.Trace dynamics inertia
    consumer.episode.closeAfter provider.episode.closeBefore
  consumerPrefix_eq : consumer.episode.beforeTrace =
    GlobalTraceFacts.Trace.append provider.episode.beforeTrace
      (.cons provider.episode.openStep betweenOpen)
  providerInterior_eq : provider.episode.interior =
    GlobalTraceFacts.Trace.append betweenOpen
      (.cons consumer.episode.openStep
        (GlobalTraceFacts.Trace.append consumer.episode.interior
          (.cons consumer.episode.closeStep betweenClose)))

namespace NestedEpisodes

/-- The provider L-Begin record strictly precedes the consumer L-Begin record. -/
theorem provider_opens_before_consumer
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    {provider consumer : LocatedEpisode dynamics inertia master}
    (nested : NestedEpisodes provider consumer) :
    provider.openOffset < consumer.openOffset := by
  have lengths := congrArg
    (fun trace => (GlobalTraceFacts.Trace.records trace).length)
    nested.consumerPrefix_eq
  simp [LocatedEpisode.openOffset, GlobalTraceFacts.Trace.records] at lengths ⊢
  omega

/-- If the provider closes in the master trace, the consumer L-Unload strictly precedes it. -/
theorem consumer_closes_before_provider
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {master : GlobalCalculus.Trace dynamics inertia initial final}
    {provider consumer : LocatedEpisode dynamics inertia master}
    (nested : NestedEpisodes provider consumer) :
    consumer.closeOffset < provider.closeOffset := by
  have prefixLengths := congrArg
    (fun trace => (GlobalTraceFacts.Trace.records trace).length)
    nested.consumerPrefix_eq
  have interiorLengths := congrArg
    (fun trace => (GlobalTraceFacts.Trace.records trace).length)
    nested.providerInterior_eq
  simp [LocatedEpisode.openOffset, LocatedEpisode.closeOffset,
    GlobalTraceFacts.Trace.records] at prefixLengths interiorLengths ⊢
  omega

end NestedEpisodes

/-! ## Local reliance and unload exclusion -/

/-- Concrete installed-consumer evidence for the global `Relied` predicate. -/
def InstalledResolution (state : State catalog Ambient)
    (consumerName provider : sig.Name) : Prop :=
  ∃ consumer, state.registry consumerName = some consumer ∧
    consumerName ≠ provider ∧ consumer.Installed ∧ ResolvesTo consumer provider

theorem InstalledResolution.relied
    {state : State catalog Ambient} {consumerName provider : sig.Name}
    (resolution : InstalledResolution state consumerName provider) :
    Relied state provider := by
  obtain ⟨consumer, present, different, installed, resolves⟩ := resolution
  exact ⟨consumerName, consumer, present, different, installed, resolves⟩

/-- Well-formedness turns every retained reliance edge into provider installation. -/
theorem relied_provider_installed
    {state : State catalog Ambient} {provider : sig.Name}
    (wf : WellFormed state) (relied : Relied state provider) :
    InstalledAt state provider := by
  obtain ⟨consumerName, consumer, consumerPresent, different, consumerInstalled,
    committed, committedEq, declared, providerEq⟩ := relied
  obtain ⟨providerFiber, providerPresent⟩ :=
    wf.committed_provider_present consumerName consumer consumerPresent committed
      committedEq declared
  have providerInstalled :=
    wf.committed_provider_installed consumerName consumer consumerPresent committed
      committedEq declared providerFiber providerPresent
  exact ⟨providerFiber, providerEq ▸ providerPresent, providerInstalled⟩

/-- Static component equality plus committed-view continuity preserves name resolution. -/
theorem resolvesTo_forward
    {beforeFiber afterFiber : Fiber catalog} {provider : sig.Name}
    (static : StaticContinuous beforeFiber afterFiber)
    (committedContinuous : HEq beforeFiber.phase.committed?
      afterFiber.phase.committed?)
    (resolves : ResolvesTo beforeFiber provider) : ResolvesTo afterFiber provider := by
  cases beforeFiber with
  | mk beforeComponent beforeParent beforeBirth beforeTable beforeWithin beforeRetired
      beforePhase =>
      cases afterFiber with
      | mk afterComponent afterParent afterBirth afterTable afterWithin afterRetired
          afterPhase =>
          simp only at static committedContinuous resolves ⊢
          cases static.component_eq
          have committedEq : beforePhase.committed? = afterPhase.committed? :=
            eq_of_heq committedContinuous
          obtain ⟨committed, beforeCommitted, declared, providerEq⟩ := resolves
          exact ⟨committed, committedEq.symm.trans beforeCommitted, declared, providerEq⟩

/-- An installed resolution survives one sufficient step with no consumer boundary. -/
theorem InstalledResolution.forward
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {step : Step dynamics inertia before after}
    {consumerName provider : sig.Name}
    (resolution : InstalledResolution before consumerName provider)
    (sufficient : SufficientConfinement dynamics inertia step)
    (consumerNoBoundary : step.actedName = consumerName →
      step.rule ≠ .lBegin ∧ step.rule ≠ .lUnload) :
    InstalledResolution after consumerName provider := by
  obtain ⟨consumer, consumerPresent, different, consumerInstalled, resolves⟩ :=
    resolution
  have beforeInstalled : InstalledAt before consumerName :=
    ⟨consumer, consumerPresent, consumerInstalled⟩
  obtain ⟨afterConsumer, afterPresent, afterInstalled⟩ :=
    Cordis.GlobalTraceFacts.installedAt_forward sufficient consumerName
      consumerNoBoundary beforeInstalled
  have static := namedStatic_continuous sufficient consumerName consumer
    afterConsumer consumerPresent afterPresent
  have committedContinuous := namedCommitted_continuous sufficient consumerName
    consumerNoBoundary consumer afterConsumer consumerPresent afterPresent
  exact ⟨afterConsumer, afterPresent, different, afterInstalled,
    resolvesTo_forward static committedContinuous resolves⟩

/-- L-Unload cannot be an admitted step while a foreign installed consumer resolves to its owner. -/
theorem unload_blocked_by_installed_consumer
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after)
    (unloadRule : step.rule = .lUnload)
    {consumerName : sig.Name}
    (resolution : InstalledResolution before consumerName step.actedName) : False := by
  cases step with
  | orchestration orchestration =>
      cases orchestration <;> cases unloadRule
  | lifecycle transition =>
      cases transition with
      | begin => cases unloadRule
      | iter => cases unloadRule
      | finish => cases unloadRule
      | divertAbort => cases unloadRule
      | divertLand => cases unloadRule
      | raise => cases unloadRule
      | leave => cases unloadRule
      | unload owner fiber present undos committed outcome phase notRelied admission =>
          exact notRelied resolution.relied

namespace Trace

/-- No record in a trace executes L-Unload for the selected name. -/
def NoUnloadFor
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (name : sig.Name) : Prop :=
  match trace with
  | .nil _ => True
  | .cons head tail =>
      (head.actedName = name → head.rule ≠ .lUnload) ∧ NoUnloadFor tail name

theorem noUnloadFor_append
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {start middle finish : State catalog Ambient}
    (left : GlobalCalculus.Trace dynamics inertia start middle)
    (right : GlobalCalculus.Trace dynamics inertia middle finish)
    (name : sig.Name) :
    NoUnloadFor (GlobalTraceFacts.Trace.append left right) name ↔
      NoUnloadFor left name ∧ NoUnloadFor right name := by
  induction left with
  | nil => simp [GlobalTraceFacts.Trace.append, NoUnloadFor]
  | cons head tail ih =>
      simp [GlobalTraceFacts.Trace.append, NoUnloadFor, ih, and_assoc]

/-- Installed resolution and committed-view continuity propagate across a bounded trace. -/
theorem installedResolution_forward
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    {consumerName provider : sig.Name}
    (sufficient : GlobalTraceFacts.Trace.Sufficient trace)
    (consumerNoBoundary : GlobalTraceFacts.Trace.NoBoundaryFor trace consumerName)
    (resolution : InstalledResolution before consumerName provider) :
    InstalledResolution after consumerName provider := by
  induction trace with
  | nil => exact resolution
  | cons head tail ih =>
      let record : StepRecord dynamics inertia := ⟨_, _, head⟩
      have headMember : record ∈ GlobalTraceFacts.Trace.records (.cons head tail) := by
        simp [record, GlobalTraceFacts.Trace.records]
      have middleResolution := resolution.forward (sufficient record headMember)
        (consumerNoBoundary record headMember)
      apply ih
      · intro candidate member
        exact sufficient candidate (by
          simp [GlobalTraceFacts.Trace.records]
          exact Or.inr member)
      · intro candidate member sameActor
        exact consumerNoBoundary candidate (by
          simp [GlobalTraceFacts.Trace.records]
          exact Or.inr member) sameActor
      · exact middleResolution

/-- The same installed provider resolution holds at every aligned state of the trace. -/
def ResolutionThroughout
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (consumerName provider : sig.Name) : Prop :=
  ∀ state, state ∈ GlobalTraceFacts.Trace.states trace →
    InstalledResolution state consumerName provider

/-- Sufficient confinement and consumer committed-view continuity imply resolution throughout. -/
theorem installedResolution_throughout
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    {consumerName provider : sig.Name}
    (sufficient : GlobalTraceFacts.Trace.Sufficient trace)
    (consumerNoBoundary : GlobalTraceFacts.Trace.NoBoundaryFor trace consumerName)
    (resolution : InstalledResolution before consumerName provider) :
    ResolutionThroughout trace consumerName provider := by
  intro state member
  induction trace with
  | nil =>
      simp [GlobalTraceFacts.Trace.states] at member
      subst state
      exact resolution
  | cons head tail ih =>
      let record : StepRecord dynamics inertia := ⟨_, _, head⟩
      have headMember : record ∈ GlobalTraceFacts.Trace.records (.cons head tail) := by
        simp [record, GlobalTraceFacts.Trace.records]
      have middleResolution := resolution.forward (sufficient record headMember)
        (consumerNoBoundary record headMember)
      simp only [GlobalTraceFacts.Trace.states, List.mem_cons] at member
      rcases member with stateEq | tailMember
      · subst state
        exact resolution
      · apply ih
        · intro candidate candidateMember
          exact sufficient candidate (by
            simp [GlobalTraceFacts.Trace.records]
            exact Or.inr candidateMember)
        · intro candidate candidateMember sameActor
          exact consumerNoBoundary candidate (by
            simp [GlobalTraceFacts.Trace.records]
            exact Or.inr candidateMember) sameActor
        · exact middleResolution
        · exact tailMember

/--
The local containment consequence of reliance: while the consumer has no episode boundary, its
resolution persists and therefore the provider cannot close with L-Unload.
-/
theorem noUnloadFor_of_installedResolution
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    {consumerName provider : sig.Name}
    (sufficient : GlobalTraceFacts.Trace.Sufficient trace)
    (consumerNoBoundary : GlobalTraceFacts.Trace.NoBoundaryFor trace consumerName)
    (resolution : InstalledResolution before consumerName provider) :
    NoUnloadFor trace provider := by
  revert resolution consumerNoBoundary sufficient
  induction trace with
  | nil =>
      intro sufficient consumerNoBoundary resolution
      trivial
  | cons head tail ih =>
      intro sufficient consumerNoBoundary resolution
      let headRecord : StepRecord dynamics inertia := ⟨_, _, head⟩
      have headMember :
          headRecord ∈ GlobalTraceFacts.Trace.records (.cons head tail) := by
        simp [headRecord, GlobalTraceFacts.Trace.records]
      have headSufficient := sufficient headRecord headMember
      have headConsumerBounds := consumerNoBoundary headRecord headMember
      have middleResolution := resolution.forward headSufficient headConsumerBounds
      have tailSufficient : GlobalTraceFacts.Trace.Sufficient tail := by
        intro candidate member
        exact sufficient candidate (by
          simp [GlobalTraceFacts.Trace.records]
          exact Or.inr member)
      have tailConsumerBounds :
          GlobalTraceFacts.Trace.NoBoundaryFor tail consumerName := by
        intro candidate member sameActor
        exact consumerNoBoundary candidate (by
          simp [GlobalTraceFacts.Trace.records]
          exact Or.inr member) sameActor
      have tailNoUnload := ih tailSufficient tailConsumerBounds middleResolution
      constructor
      · intro sameActor unloadRule
        have atActor := sameActor.symm ▸ resolution
        exact unload_blocked_by_installed_consumer head unloadRule atActor
      · exact tailNoUnload

end Trace

namespace BoundedEpisode

/-- The exact open/interior/close subtrace, excluding the surrounding master prefix and suffix. -/
def core
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final) :
    GlobalCalculus.Trace dynamics inertia episode.openBefore episode.closeAfter :=
  .cons episode.openStep <|
    GlobalTraceFacts.Trace.append episode.interior <|
      .cons episode.closeStep (.nil episode.closeAfter)

/-- The consumer's installed opening state retains a committed binding to `provider`. -/
def ReliesOnAtOpen
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    (provider : sig.Name) : Prop :=
  InstalledResolution episode.openAfter episode.name provider

/-- Consumer-view continuity retains the same provider resolution up to its closing step. -/
theorem resolution_at_closeBefore
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    {provider : sig.Name} (resolution : ReliesOnAtOpen episode provider) :
    InstalledResolution episode.closeBefore episode.name provider :=
  Trace.installedResolution_forward episode.interior episode.interior_sufficient
    episode.interior_no_boundary resolution

/-- The consumer's committed provider binding is constant at every interior trace state. -/
theorem resolution_throughout_interior
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    {provider : sig.Name} (resolution : ReliesOnAtOpen episode provider) :
    Trace.ResolutionThroughout episode.interior episode.name provider :=
  Trace.installedResolution_throughout episode.interior episode.interior_sufficient
    episode.interior_no_boundary resolution

/-- A provider relied on at consumer opening cannot execute L-Unload in the consumer interior. -/
theorem provider_noUnload_interior
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    {provider : sig.Name} (resolution : ReliesOnAtOpen episode provider) :
    Trace.NoUnloadFor episode.interior provider :=
  Trace.noUnloadFor_of_installedResolution episode.interior
    episode.interior_sufficient episode.interior_no_boundary resolution

/-- The provider cannot unload anywhere in the consumer's open/interior/close core. -/
theorem provider_noUnload_core
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    {provider : sig.Name} (resolution : ReliesOnAtOpen episode provider) :
    Trace.NoUnloadFor (core episode) provider := by
  obtain ⟨consumer, present, different, installed, resolves⟩ := resolution
  change (episode.openStep.actedName = provider → episode.openStep.rule ≠ .lUnload) ∧
    Trace.NoUnloadFor
      (GlobalTraceFacts.Trace.append episode.interior
        (.cons episode.closeStep (.nil episode.closeAfter))) provider
  constructor
  · intro sameActor
    exact False.elim (different (episode.open_name.symm.trans sameActor))
  · apply (Trace.noUnloadFor_append _ _ _).2
    constructor
    · exact provider_noUnload_interior episode
        ⟨consumer, present, different, installed, resolves⟩
    · change (episode.closeStep.actedName = provider →
          episode.closeStep.rule ≠ .lUnload) ∧ True
      constructor
      · intro sameActor
        exact False.elim (different (episode.close_name.symm.trans sameActor))
      · trivial

/-- Under `WellFormed`, the relied-on provider is still installed before the consumer closes. -/
theorem provider_installed_at_closeBefore
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    (episode : BoundedEpisode dynamics inertia initial final)
    {provider : sig.Name} (wf : WellFormed episode.openAfter)
    (resolution : ReliesOnAtOpen episode provider) :
    InstalledAt episode.closeBefore provider := by
  have closeWf := episode.interior.preservesWellFormed wf
  exact relied_provider_installed closeWf
    (resolution_at_closeBefore episode resolution).relied

end BoundedEpisode

/-! ## The exact table-confinement premise for Theorem 63(3) -/

/-- A table entry, including its dependent value, is present at a named fiber. -/
def TableValueAt (state : State catalog Ambient) (name : sig.Name)
    (key : sig.Key) (value : sig.Value key) : Prop :=
  ∃ fiber, state.registry name = some fiber ∧ fiber.table key = some value

/-- One record preserves every dependent table value at the selected name. -/
def TablePreservedFor
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    (record : StepRecord dynamics inertia) (name : sig.Name) : Prop :=
  ∀ key value, TableValueAt record.before name key value →
    TableValueAt record.after name key value

theorem tablePreservedFor_foreign
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {record : StepRecord dynamics inertia} {name : sig.Name}
    (sufficient : SufficientConfinement dynamics inertia record.step)
    (foreign : record.step.actedName ≠ name) : TablePreservedFor record name := by
  intro key value presentValue
  obtain ⟨beforeFiber, beforePresent, tableValue⟩ := presentValue
  obtain ⟨afterFiber, afterPresent, tableEq⟩ :=
    foreignTables_preserved sufficient name beforeFiber beforePresent (Ne.symm foreign)
  refine ⟨afterFiber, afterPresent, ?_⟩
  rw [tableEq, tableValue]

/-- Every record of a trace preserves the selected provider's table values. -/
def TraceTableConfinement
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (name : sig.Name) : Prop :=
  ∀ record, record ∈ GlobalTraceFacts.Trace.records trace →
    TablePreservedFor record name

/-- A trace never acts on the selected name. -/
def TraceForeignTo
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (name : sig.Name) : Prop :=
  ∀ record, record ∈ GlobalTraceFacts.Trace.records trace →
    record.step.actedName ≠ name

/-- Sufficient confinement discharges table confinement when every trace actor is foreign. -/
theorem traceTableConfinement_of_foreign
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    {trace : GlobalCalculus.Trace dynamics inertia before after}
    {name : sig.Name} (sufficient : GlobalTraceFacts.Trace.Sufficient trace)
    (foreign : TraceForeignTo trace name) : TraceTableConfinement trace name := by
  intro record member
  exact tablePreservedFor_foreign (sufficient record member) (foreign record member)

/-- The minimal per-record premise composes over an exact finite trace. -/
theorem tableValue_forward
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    {name : sig.Name} (confined : TraceTableConfinement trace name)
    {key : sig.Key} {value : sig.Value key} :
    TableValueAt before name key value → TableValueAt after name key value := by
  intro initialValue
  induction trace with
  | nil => exact initialValue
  | cons head tail ih =>
      let record : StepRecord dynamics inertia := ⟨_, _, head⟩
      have headPreserves : TablePreservedFor record name :=
        confined record (by simp [record, GlobalTraceFacts.Trace.records])
      have middleValue := headPreserves key value initialValue
      apply ih
      · intro candidate member
        exact confined candidate (by
          simp [GlobalTraceFacts.Trace.records]
          exact Or.inr member)
      · exact middleValue

/-- A table value holds at every aligned state of a finite trace. -/
def TableValueThroughout
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    (name : sig.Name) (key : sig.Key) (value : sig.Value key) : Prop :=
  ∀ state, state ∈ GlobalTraceFacts.Trace.states trace →
    TableValueAt state name key value

/-- The named table-confinement premise yields paper-style value constancy throughout the trace. -/
theorem tableValue_throughout
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : GlobalCalculus.Trace dynamics inertia before after)
    {name : sig.Name} (confined : TraceTableConfinement trace name)
    {key : sig.Key} {value : sig.Value key}
    (initialValue : TableValueAt before name key value) :
    TableValueThroughout trace name key value := by
  intro state member
  induction trace with
  | nil =>
      simp [GlobalTraceFacts.Trace.states] at member
      subst state
      exact initialValue
  | cons head tail ih =>
      let record : StepRecord dynamics inertia := ⟨_, _, head⟩
      have headPreserves : TablePreservedFor record name :=
        confined record (by simp [record, GlobalTraceFacts.Trace.records])
      have middleValue := headPreserves key value initialValue
      simp only [GlobalTraceFacts.Trace.states, List.mem_cons] at member
      rcases member with stateEq | tailMember
      · subst state
        exact initialValue
      · apply ih
        · intro candidate candidateMember
          exact confined candidate (by
            simp [GlobalTraceFacts.Trace.records]
            exact Or.inr candidateMember)
        · exact middleValue
        · exact tailMember

/-! ## Local Theorem 64 target-stability/divert dichotomy -/

/-- The acted-on name of a lifecycle transition, exposed without the global rule encoding. -/
def lifecycleOwner
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient} :
    GlobalLifecycle.Transition dynamics inertia before after → sig.Name
  | .begin _ owner .. => owner
  | .iter _ owner .. => owner
  | .finish _ owner .. => owner
  | .divertAbort _ owner .. => owner
  | .divertLand _ owner .. => owner
  | .raise _ owner .. => owner
  | .leave _ owner .. => owner
  | .unload _ owner .. => owner

/--
Classification of a lifecycle step whose acted-on source fiber is known to be reloading with a
particular committed view. Iterator/finish steps retain that target; divert steps witness target
inequality; raise is the remaining transition to unloading. This intentionally says nothing about
the later recovery result.
-/
theorem reloading_target_dichotomy
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : GlobalLifecycle.Transition dynamics inertia before after)
    (owner : sig.Name) (fiber : Fiber catalog)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (sameOwner : lifecycleOwner transition = owner)
    (present : before.registry owner = some fiber)
    (reloading : fiber.phase = .reloading code undos committed) :
    ((transition.rule = .iter ∨ transition.rule = .finish) ∧
      targetView before owner fiber = some committed) ∨
    ((transition.rule = .divertAbort ∨ transition.rule = .divertLand) ∧
      targetView before owner fiber ≠ some committed) ∨
    transition.rule = .raise := by
  cases transition with
  | begin owner' fiber' present' entry' committed' target' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      rw [entry'] at reloading
      cases reloading
  | iter owner' fiber' present' code' undos' committed' phase' target' landing' next'
      continues' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      have phaseEq := phase'.symm.trans reloading
      cases phaseEq
      exact Or.inl ⟨Or.inl rfl, target'⟩
  | finish owner' fiber' present' code' undos' committed' phase' target' landing' done' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      have phaseEq := phase'.symm.trans reloading
      cases phaseEq
      exact Or.inl ⟨Or.inr rfl, target'⟩
  | divertAbort owner' fiber' present' code' undos' committed' phase' targetChanged'
      abortable' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      have phaseEq := phase'.symm.trans reloading
      cases phaseEq
      exact Or.inr (Or.inl ⟨Or.inl rfl, targetChanged'⟩)
  | divertLand owner' fiber' present' code' undos' committed' phase' targetChanged'
      landing' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      have phaseEq := phase'.symm.trans reloading
      cases phaseEq
      exact Or.inr (Or.inl ⟨Or.inr rfl, targetChanged'⟩)
  | raise => exact Or.inr (Or.inr rfl)
  | leave owner' fiber' present' undos' committed' phase' targetChanged' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      have phaseEq := phase'.symm.trans reloading
      cases phaseEq
  | unload owner' fiber' present' undos' committed' outcome' phase' notRelied'
      admission' =>
      change owner' = owner at sameOwner
      subst owner
      have fiberEq : fiber' = fiber := Option.some.inj (present'.symm.trans present)
      subst fiber
      have phaseEq := phase'.symm.trans reloading
      cases phaseEq

end Cordis.GlobalSpatial
