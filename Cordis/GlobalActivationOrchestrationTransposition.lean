import Cordis.GlobalActivationTransposition
import Cordis.GlobalVestigial

/-!
# Corrected activation/orchestration transposition

This module implements the corrected exact representative described in
`docs/GLOBAL_ACTIVATION_ORCHESTRATION_TRANSPOSITION_SPEC.md`, against CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

The literal side condition of paper Lemma 71(2) is false for this birth-ranked calculus: a
registration may enable a later O-Insert parent without registering the O-Insert actor, and two
otherwise legal insertions allocate different birth ranks in opposite orders. The corrected
theorem therefore requires occurrence-specific exact execution framing and rejects every
registering-activation/O-Insert pair. Begin is structural; ordinary landing activation supports
all three orchestration rules; registering landing activation supports Retire and Remove when its
child differs from their actor.

The result is fixed-program, fixed-oracle, partial, occurrence-specific, and exact-state. It is not
literal paper Lemma 71(2), a birth-erasing quotient, trace rewriting, Lemma 72, confluence, or
progress.
-/

set_option autoImplicit false

namespace Cordis.GlobalActivationOrchestrationTransposition

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalIteratorIndependence Cordis.GlobalTransposition
open Cordis.GlobalActivationTransposition Cordis.GlobalLandingTransposition
open Cordis.GlobalVestigial Cordis.GlobalRelations

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Kernel refutation of the literal paper condition -/

namespace LiteralPaperGap

open Cordis.GlobalRegistry.Example

abbrev exampleCatalog := Cordis.GlobalRegistry.Example.catalog
abbrev ExampleState := GlobalState exampleCatalog Unit
abbrev Source : ExampleState := Cordis.GlobalRegistry.Example.withProvider

def registered : ExampleState :=
  insertFiber Source 1 (some 0) .consumer

@[simp] theorem source_child_absent : Source.registry 1 = none := rfl

@[simp] theorem registered_child_present :
    registered.registry 1 = some {
      component := .consumer
      parent := some 0
      birth := Source.nextBirth
      table := Coeffect.empty
      table_within_provision := by simp
      retired := false
      phase := .inactive none
    } := by
  simp [registered]

def adoptionAfter : ExampleState :=
  insertFiber registered 2 (some 1) .consumer

def adoptingInsert : OrchestrationStep registered adoptionAfter :=
  .insert registered 2 (by constructor; rfl) (some 1) (by
    intro parent equal
    have parentEq : parent = 1 := Option.some.inj equal.symm
    subst parent
    exact ⟨_, registered_child_present⟩) .consumer (by simp [consumerDecl])

theorem source_wellFormed : WellFormed Source := withProvider_wellFormed

theorem registered_wellFormed : WellFormed registered := by
  change WellFormed Cordis.GlobalRegistry.Example.withConsumer
  exact withConsumer_wellFormed

theorem adoptionAfter_wellFormed : WellFormed adoptionAfter :=
  adoptingInsert.preservesWellFormed registered_wellFormed

/-- The activation-shaped insertion registers `1`, not orchestration actor `2`. -/
theorem does_not_register_orchestration_actor : (1 : Nat) ≠ 2 := by decide

/-- Parent `1` exists after registration but not at the common predecessor. -/
theorem parent_adoption_blocks_early_insert :
    (∃ fiber, registered.registry 1 = some fiber) ∧
      ¬(∃ fiber, Source.registry 1 = some fiber) := by
  constructor
  · exact ⟨_, registered_child_present⟩
  · rintro ⟨fiber, present⟩
    rw [source_child_absent] at present
    cases present

def normal : ExampleState :=
  insertFiber registered 2 (some 0) .consumer

def registerChild : OrchestrationStep Source registered :=
  Cordis.GlobalRegistry.Example.insertConsumer

def normalInsert : OrchestrationStep registered normal :=
  .insert registered 2 (by constructor; rfl) (some 0) (by
    intro parent equal
    have parentEq : parent = 0 := Option.some.inj equal.symm
    subst parent
    exact ⟨_, rfl⟩) .consumer (by simp [consumerDecl])

def swappedFirst : ExampleState :=
  insertFiber Source 2 (some 0) .consumer

def swappedFirstInsert : OrchestrationStep Source swappedFirst :=
  .insert Source 2 (by constructor; rfl) (some 0) (by
    intro parent equal
    have parentEq : parent = 0 := Option.some.inj equal.symm
    subst parent
    exact ⟨_, rfl⟩) .consumer (by simp [consumerDecl])

def swapped : ExampleState :=
  insertFiber swappedFirst 1 (some 0) .consumer

def swappedSecondInsert : OrchestrationStep swappedFirst swapped :=
  .insert swappedFirst 1 (by constructor; rfl) (some 0) (by
    intro parent equal
    have parentEq : parent = 0 := Option.some.inj equal.symm
    subst parent
    exact ⟨_, rfl⟩) .consumer (by simp [consumerDecl])

theorem normal_wellFormed : WellFormed normal :=
  normalInsert.preservesWellFormed registered_wellFormed

theorem swapped_wellFormed : WellFormed swapped :=
  swappedSecondInsert.preservesWellFormed
    (swappedFirstInsert.preservesWellFormed source_wellFormed)

/-- Even when parent `0` is available in both orders, exact endpoints swap birth ranks. -/
theorem registration_insert_birth_order_differs : normal ≠ swapped := by
  intro equal
  have lookupEq := congrArg (fun state ↦ state.registry 1) equal
  have birthEq := congrArg (fun found ↦ found.map Fiber.birth) lookupEq
  change some Source.nextBirth = some (Source.nextBirth + 1) at birthEq
  have impossible := Option.some.inj birthEq
  omega

def exactValues : ValueSetoids Cordis.GlobalRegistry.Example.signature where
  relation _ := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

/-- The current rule relation observes birth rank, so it cannot quotient this gap away. -/
theorem birth_order_not_ruleRelated : ¬RuleRelated exactValues normal swapped := by
  intro related
  have controlEq := related.2.2 1
  have birthEq := congrArg (fun found ↦ found.map FiberControl.birth) controlEq
  change some 1 = some 2 at birthEq
  have impossible : (1 : Nat) = 2 := Option.some.inj birthEq
  omega

end LiteralPaperGap

/-! ## Registration classification and occurrence-specific frame API -/

def sourceRegisteredChild
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before after : State catalog Ambient}
    {undo : UndoCode sig} {next : Option sig.IteratorCode}
    (source : StepSource dynamics owner code before after undo next) : Option sig.Name :=
  match source with
  | .ordinary .. => none
  | .registration _ admission _ => some admission.child

def stepRegisteredChild
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) : Option sig.Name :=
  sourceRegisteredChild step.source

def ProgramActivation.registeredChild
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (activation : ProgramActivation program before) : Option sig.Name :=
  match activation with
  | .begin .. => none
  | .landing aligned => stepRegisteredChild aligned.landing.step

@[simp] theorem sourceRegisteredChild_ordinary
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (result : OrdinaryResult catalog Ambient)
    (runEq : dynamics.runIterator owner code before = .ok (.ordinary result)) :
    sourceRegisteredChild (.ordinary result runEq) = none := rfl

@[simp] theorem sourceRegisteredChild_registration
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (request : RegistrationRequest sig)
    (admission : RegistrationAdmission dynamics before owner request)
    (runEq : dynamics.runIterator owner code before = .ok (.register request)) :
    sourceRegisteredChild (.registration request admission runEq) = some admission.child := rfl

@[simp] theorem ProgramActivation.registeredChild_begin
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (fiber : Fiber catalog)
    (guard : Cordis.GlobalRuleObservations.BeginGuard before program.owner fiber)
    (rootAligned : program.root = (catalog.declaration fiber.component).entry) :
    ProgramActivation.registeredChild (.begin fiber guard rootAligned) = none := rfl

@[simp] theorem ProgramActivation.registeredChild_landing
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {before : State catalog Ambient}
    (aligned : ProgramAlignedLandingActivation program before) :
    ProgramActivation.registeredChild (.landing aligned) =
      stepRegisteredChild aligned.landing.step := rfl

theorem sourceRegisteredChild_ne_none_of_registration
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (request : RegistrationRequest sig)
    (admission : RegistrationAdmission dynamics before owner request)
    (runEq : dynamics.runIterator owner code before = .ok (.register request)) :
    sourceRegisteredChild (.registration request admission runEq) ≠ none := by
  simp

def RegistrationSafe
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) : Prop :=
  match normal with
  | .insert .. =>
      Cordis.GlobalActivationOrchestrationTransposition.ProgramActivation.registeredChild
        activation = none
  | .retire _ name .. =>
      Cordis.GlobalActivationOrchestrationTransposition.ProgramActivation.registeredChild
        activation ≠ some name
  | .remove _ name .. =>
      Cordis.GlobalActivationOrchestrationTransposition.ProgramActivation.registeredChild
        activation ≠ some name

def orchestrationReplay
    {before after : State catalog Ambient}
    (step : OrchestrationStep before after) : State catalog Ambient → State catalog Ambient :=
  match step with
  | .insert _ name _ parent _ component _ =>
      fun state ↦ insertFiber state name parent component
  | .retire _ name fiber _ => fun state ↦ retireFiber state name fiber
  | .remove _ name .. => fun state ↦ removeFiber state name

@[simp] theorem orchestrationReplay_before
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    orchestrationReplay step before = after := by
  cases step <;> rfl

structure SameOrchestrationTemplate
    {leftBefore leftAfter rightBefore rightAfter : State catalog Ambient}
    (left : OrchestrationStep leftBefore leftAfter)
    (right : OrchestrationStep rightBefore rightAfter) : Prop where
  same_kind : orchestrationKind left = orchestrationKind right
  same_actor : orchestrationName left = orchestrationName right
  replay_eq : orchestrationReplay left = orchestrationReplay right

def ExactExecutionFrame
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    {code : sig.IteratorCode} {state : State catalog Ambient}
    (step : IterationStep dynamics program.owner code state)
    (edit : State catalog Ambient → State catalog Ambient) : Prop :=
  ∃ movedStep : IterationStep dynamics program.owner code (edit state),
    executeOne dynamics program.oracle code (edit state) = .ok movedStep ∧
      LifecycleYieldAgrees movedStep step ∧
      movedStep.after = edit step.after

def ExecutionFrameFor
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) : Prop :=
  match activation with
  | .begin .. => True
  | .landing aligned =>
      ExactExecutionFrame program aligned.landing.step (orchestrationReplay normal)

structure ActivationOrchestrationSwapLaws
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) : Prop where
  registration_safe : RegistrationSafe activation normal
  execution_frame : ExecutionFrameFor activation normal

/-! ## Structural lookup facts for moving orchestration earlier -/

private theorem iteration_lookup_eq_of_nonregistering
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {origin : State catalog Ambient}
    (step : IterationStep dynamics owner code origin)
    (nonregistering : stepRegisteredChild step = none)
    (name : sig.Name) (different : name ≠ owner) :
    step.after.registry name = origin.registry name := by
  cases step with
  | mk after undo next source recovers preserves =>
      cases source with
      | ordinary result runEq =>
          exact (dynamics.ordinary_confined owner code origin result runEq).other_unchanged
            name different
      | registration request admission runEq =>
          change some admission.child = none at nonregistering
          cases nonregistering

private theorem iteration_lookup_before_of_after_of_not_registered
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {origin : State catalog Ambient}
    (step : IterationStep dynamics owner code origin)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ owner)
    (notRegistered : stepRegisteredChild step ≠ some name)
    (afterPresent : step.after.registry name = some fiber) :
    origin.registry name = some fiber := by
  cases step with
  | mk after undo next source recovers preserves =>
      cases source with
      | ordinary result runEq =>
          rw [(dynamics.ordinary_confined owner code origin result runEq).other_unchanged
            name different] at afterPresent
          exact afterPresent
      | registration request admission runEq =>
          have childDifferent : name ≠ admission.child := by
            intro same
            subst name
            exact notRegistered rfl
          change (insertFiber origin admission.child (some owner)
            request.component).registry name = some fiber at afterPresent
          rw [insertFiber_lookup_other origin admission.child name (some owner)
            request.component childDifferent] at afterPresent
          exact afterPresent

theorem ProgramActivation.lookup_after_eq_of_nonregistering
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient} (activation : ProgramActivation program origin)
    (nonregistering :
      Cordis.GlobalActivationOrchestrationTransposition.ProgramActivation.registeredChild
        activation = none)
    (name : sig.Name) (different : name ≠ program.owner) :
    activation.after.registry name = origin.registry name := by
  cases activation with
  | begin fiber guard rootAligned =>
      exact setPhase_lookup_other origin program.owner name fiber _ different
  | landing aligned =>
      rw [ProgramActivation.after, ProgramAlignedLandingActivation.after,
        setPhase_lookup_other _ program.owner name aligned.landing.afterFiber _ different]
      exact iteration_lookup_eq_of_nonregistering aligned.landing.step nonregistering
        name different

theorem ProgramActivation.lookup_before_of_after_of_not_registered
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient} (activation : ProgramActivation program origin)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ program.owner)
    (notRegistered :
      Cordis.GlobalActivationOrchestrationTransposition.ProgramActivation.registeredChild
        activation ≠ some name)
    (afterPresent : activation.after.registry name = some fiber) :
    origin.registry name = some fiber := by
  cases activation with
  | begin ownerFiber guard rootAligned =>
      rw [ProgramActivation.after,
        setPhase_lookup_other origin program.owner name ownerFiber _ different] at afterPresent
      exact afterPresent
  | landing aligned =>
      rw [ProgramActivation.after, ProgramAlignedLandingActivation.after,
        setPhase_lookup_other _ program.owner name aligned.landing.afterFiber _ different]
        at afterPresent
      exact iteration_lookup_before_of_after_of_not_registered aligned.landing.step
        different notRegistered afterPresent

theorem ProgramActivation.owner_after_static
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (activation : ProgramActivation program origin) :
    ∃ afterFiber,
      activation.after.registry program.owner = some afterFiber ∧
        Cordis.GlobalTraceFacts.StaticContinuous activation.sourceFiber afterFiber := by
  cases activation with
  | begin fiber guard rootAligned =>
      let updated : Fiber catalog := { fiber with phase :=
        (Phase.reloading (catalog.declaration fiber.component).entry [] guard.committed) }
      refine ⟨updated, ?_, ?_⟩
      · exact setPhase_lookup_same _ _ _ _
      · exact Cordis.GlobalTraceFacts.StaticContinuous.phaseUpdate _ _
  | landing aligned =>
      let updated : Fiber catalog := {
        aligned.landing.afterFiber with phase := aligned.nextPhase
      }
      refine ⟨updated, ?_, ?_⟩
      · exact setPhase_lookup_same _ _ _ _
      · exact Cordis.GlobalTraceFacts.StaticContinuous.trans
          (Cordis.GlobalTraceFacts.iteration_owner_static aligned.landing.step
            aligned.present aligned.landing.after_present)
          (Cordis.GlobalTraceFacts.StaticContinuous.phaseUpdate _ _)

theorem ProgramActivation.endpoint_component_present
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (activation : ProgramActivation program origin)
    {name : sig.Name} {fiber : Fiber catalog}
    (present : origin.registry name = some fiber) :
    ∃ afterFiber,
      activation.after.registry name = some afterFiber ∧
        afterFiber.component = fiber.component := by
  by_cases same : name = program.owner
  · subst name
    rw [activation.source_present] at present
    have fiberEq : activation.sourceFiber = fiber := Option.some.inj present
    subst fiber
    obtain ⟨afterFiber, afterPresent, continuous⟩ :=
      Cordis.GlobalActivationOrchestrationTransposition.ProgramActivation.owner_after_static
        activation
    exact ⟨afterFiber, afterPresent, continuous.component_eq⟩
  · exact ⟨fiber, activation.foreignLookupFrame.lookup present same, rfl⟩

/-! ## Reconstruction of the same orchestration occurrence at the predecessor -/

structure EarlyOrchestration
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) where
  step : OrchestrationStep origin (orchestrationReplay normal origin)
  same_template : SameOrchestrationTemplate step normal

def reconstructOrchestration
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final)
    (different : program.owner ≠ orchestrationName normal)
    (safe : RegistrationSafe activation normal) :
    EarlyOrchestration activation normal := by
  cases normal with
  | insert name fresh parent parentPresent component provisionFresh =>
      change program.owner ≠ name at different
      change ProgramActivation.registeredChild activation = none at safe
      have originFresh : Coeffect.Absent origin.registry name := by
        constructor
        cases lookup : origin.registry name with
        | none => rfl
        | some fiber =>
            have afterPresent := activation.foreignLookupFrame.lookup lookup
              (Ne.symm different)
            rw [fresh.lookup_eq] at afterPresent
            cases afterPresent
      have originParent : ∀ parentName, parent = some parentName →
          ∃ parentFiber, origin.registry parentName = some parentFiber := by
        intro parentName parentEq
        by_cases parentOwner : parentName = program.owner
        · subst parentName
          exact ⟨activation.sourceFiber, activation.source_present⟩
        · obtain ⟨parentFiber, afterPresent⟩ := parentPresent parentName parentEq
          have notRegistered :
              ProgramActivation.registeredChild activation ≠ some parentName := by
            rw [safe]
            simp
          exact ⟨parentFiber,
            ProgramActivation.lookup_before_of_after_of_not_registered activation
              parentOwner notRegistered afterPresent⟩
      have originProvision : ∀ existing existingFiber key,
          origin.registry existing = some existingFiber →
          key ∈ (catalog.declaration component).provision →
          key ∈ (catalog.declaration existingFiber.component).provision → False := by
        intro existing existingFiber key present newKey existingKey
        obtain ⟨afterFiber, afterPresent, componentEq⟩ :=
          ProgramActivation.endpoint_component_present activation present
        exact provisionFresh existing afterFiber key afterPresent newKey
          (by simpa [componentEq] using existingKey)
      let early : OrchestrationStep origin
          (insertFiber origin name parent component) :=
        .insert origin name originFresh parent originParent component originProvision
      exact {
        step := early
        same_template := ⟨rfl, rfl, rfl⟩
      }
  | retire name fiber afterPresent =>
      change program.owner ≠ name at different
      change ProgramActivation.registeredChild activation ≠ some name at safe
      have originPresent := ProgramActivation.lookup_before_of_after_of_not_registered
        activation (Ne.symm different) safe afterPresent
      let early : OrchestrationStep origin (retireFiber origin name fiber) :=
        .retire origin name fiber originPresent
      exact {
        step := early
        same_template := ⟨rfl, rfl, rfl⟩
      }
  | remove name fiber afterPresent retired inactive childless =>
      change program.owner ≠ name at different
      change ProgramActivation.registeredChild activation ≠ some name at safe
      have originPresent := ProgramActivation.lookup_before_of_after_of_not_registered
        activation (Ne.symm different) safe afterPresent
      have originChildless : ∀ child childFiber,
          origin.registry child = some childFiber → childFiber.parent ≠ some name := by
        intro child childFiber childPresent
        by_cases childOwner : child = program.owner
        · subst child
          rw [activation.source_present] at childPresent
          have fiberEq : activation.sourceFiber = childFiber := Option.some.inj childPresent
          subst childFiber
          obtain ⟨afterOwner, afterOwnerPresent, continuous⟩ :=
            ProgramActivation.owner_after_static activation
          intro parentEq
          exact (childless program.owner afterOwner afterOwnerPresent)
            (continuous.parent_eq.trans parentEq)
        · exact childless child childFiber
            (activation.foreignLookupFrame.lookup childPresent childOwner)
      let early : OrchestrationStep origin (removeFiber origin name) :=
        .remove origin name fiber originPresent retired inactive originChildless
      exact {
        step := early
        same_template := ⟨rfl, rfl, rfl⟩
      }

/-! ## Structural orchestration lookup and positive-target preservation -/

theorem orchestration_foreign_present
    {before after : State catalog Ambient} (step : OrchestrationStep before after)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ orchestrationName step)
    (present : before.registry name = some fiber) : after.registry name = some fiber := by
  cases step with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      exact insertFiber_lookup_other before inserted name parent component different
        |>.trans present
  | retire retired retiredFiber retiredPresent =>
      exact retireFiber_lookup_other before retired name retiredFiber different |>.trans present
  | remove removed removedFiber removedPresent retired inactive childless =>
      exact removeFiber_lookup_other before removed name different |>.trans present

theorem orchestrationReplay_foreign_present
    {before after : State catalog Ambient} (step : OrchestrationStep before after)
    (state : State catalog Ambient)
    {name : sig.Name} {fiber : Fiber catalog}
    (different : name ≠ orchestrationName step)
    (present : state.registry name = some fiber) :
    (orchestrationReplay step state).registry name = some fiber := by
  cases step with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      exact insertFiber_lookup_other state inserted name parent component different
        |>.trans present
  | retire retired retiredFiber retiredPresent =>
      exact retireFiber_lookup_other state retired name retiredFiber different |>.trans present
  | remove removed removedFiber removedPresent retired inactive childless =>
      exact removeFiber_lookup_other state removed name different |>.trans present

theorem orchestration_preserves_positive_target
    {before after : State catalog Ambient} (step : OrchestrationStep before after)
    (beforeWf : WellFormed before)
    {consumer : sig.Name} {consumerFiber : Fiber catalog}
    (different : consumer ≠ orchestrationName step)
    (consumerPresent : before.registry consumer = some consumerFiber)
    {committed : CommittedView (catalog.declaration consumerFiber.component)}
    (target : targetView before consumer consumerFiber = some committed) :
    after.registry consumer = some consumerFiber ∧
      targetView after consumer consumerFiber = some committed := by
  have consumerAfter := orchestration_foreign_present step different consumerPresent
  have afterWf := step.preservesWellFormed beforeWf
  let sourceTarget := targetView_sound beforeWf target
  refine ⟨consumerAfter, targetView_eq_of_isTarget afterWf ?_⟩
  exact {
    present := consumerAfter
    not_retired := sourceTarget.not_retired
    resolves_active := by
      intro declared
      obtain ⟨providerFiber, providerPresent, providerActive, tablePresent⟩ :=
        sourceTarget.resolves_active declared
      cases step with
      | insert inserted fresh parent parentPresent component provisionFresh =>
          have providerDifferent : committed.provider declared ≠ inserted := by
            intro same
            subst inserted
            rw [fresh.lookup_eq] at providerPresent
            cases providerPresent
          exact ⟨providerFiber,
            insertFiber_lookup_other before inserted (committed.provider declared) parent
              component providerDifferent |>.trans providerPresent,
            providerActive, tablePresent⟩
      | retire retired retiredFiber retiredPresent =>
          by_cases same : committed.provider declared = retired
          · subst retired
            rw [retiredPresent] at providerPresent
            have fiberEq := Option.some.inj providerPresent
            subst providerFiber
            exact ⟨{ retiredFiber with retired := true },
              retireFiber_lookup_same before (committed.provider declared) retiredFiber,
              providerActive, tablePresent⟩
          · exact ⟨providerFiber,
              retireFiber_lookup_other before retired (committed.provider declared)
                retiredFiber same |>.trans providerPresent,
              providerActive, tablePresent⟩
      | remove removed removedFiber removedPresent retired inactive childless =>
          have providerDifferent : committed.provider declared ≠ removed := by
            intro same
            subst removed
            rw [removedPresent] at providerPresent
            have fiberEq := Option.some.inj providerPresent
            subst providerFiber
            have installed : removedFiber.Installed := by
              cases phaseEq : removedFiber.phase <;>
                simp [Fiber.Active, Fiber.Installed, Phase.Active, Phase.Installed,
                  phaseEq] at providerActive ⊢
            exact inactive installed
          exact ⟨providerFiber,
            removeFiber_lookup_other before removed (committed.provider declared)
              providerDifferent |>.trans providerPresent,
            providerActive, tablePresent⟩
  }

/-! ## Pure orchestration-edit/phase commutation -/

theorem retireFiber_setPhase_commute
    (state : State catalog Ambient) (owner retired : sig.Name)
    (ownerFiber retiredFiber : Fiber catalog)
    (phase : Phase (catalog.declaration ownerFiber.component))
    (different : owner ≠ retired) :
    retireFiber (setPhase state owner ownerFiber phase) retired retiredFiber =
      setPhase (retireFiber state retired retiredFiber) owner ownerFiber phase := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [retireFiber, setPhase, GlobalState.mk.injEq]
      exact ⟨trivial, trivial,
        Coeffect.setAt_commute registry owner retired different
          { ownerFiber with phase := phase } { retiredFiber with retired := true }⟩

theorem removeFiber_setPhase_commute
    (state : State catalog Ambient) (owner removed : sig.Name)
    (ownerFiber : Fiber catalog)
    (phase : Phase (catalog.declaration ownerFiber.component))
    (different : owner ≠ removed) :
    removeFiber (setPhase state owner ownerFiber phase) removed =
      setPhase (removeFiber state removed) owner ownerFiber phase := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [removeFiber, setPhase, GlobalState.mk.injEq]
      exact ⟨trivial, trivial,
        Coeffect.setAt_removeAt_commute registry owner removed different
          { ownerFiber with phase := phase }⟩

theorem orchestrationReplay_setPhase_commute
    {before after : State catalog Ambient} (step : OrchestrationStep before after)
    (state : State catalog Ambient) (owner : sig.Name)
    (ownerFiber : Fiber catalog)
    (phase : Phase (catalog.declaration ownerFiber.component))
    (different : owner ≠ orchestrationName step) :
    orchestrationReplay step (setPhase state owner ownerFiber phase) =
      setPhase (orchestrationReplay step state) owner ownerFiber phase := by
  cases step with
  | insert inserted fresh parent parentPresent component provisionFresh =>
      exact Cordis.GlobalForeignPhase.insertFiber_setPhase_commute state inserted owner
        parent component ownerFiber phase (Ne.symm different)
  | retire retired retiredFiber retiredPresent =>
      exact retireFiber_setPhase_commute state owner retired ownerFiber retiredFiber phase
        different
  | remove removed removedFiber removedPresent retired inactive childless =>
      exact removeFiber_setPhase_commute state owner removed ownerFiber phase different

/-! ## Generalized landing and moved-activation reframing -/

namespace Landing

def reframeFromEditTemplate
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    {code : sig.IteratorCode} {origin : State catalog Ambient}
    {sourceFiber : Fiber catalog}
    (template : Landing dynamics program.owner code origin sourceFiber)
    (edit : State catalog Ambient → State catalog Ambient)
    (movedStep : IterationStep dynamics program.owner code (edit origin))
    (executed : executeOne dynamics program.oracle code (edit origin) = .ok movedStep)
    (sourcePresent : (edit origin).registry program.owner = some sourceFiber)
    (afterPresent : movedStep.after.registry program.owner = some template.afterFiber) :
    Landing dynamics program.owner code (edit origin) sourceFiber where
  RegistrationError := program.RegistrationError
  oracle := program.oracle
  step := movedStep
  executed := executed
  before_present := sourcePresent
  afterFiber := template.afterFiber
  after_present := afterPresent
  component_eq := template.component_eq
  phase_eq := template.phase_eq

end Landing

structure EditReframedActivation
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (original : ProgramAlignedLandingActivation program origin)
    (edit : State catalog Ambient → State catalog Ambient) where
  activation : ProgramAlignedLandingActivation program (edit origin)
  after_eq : activation.after =
    setPhase (edit original.landing.step.after) program.owner
      original.landing.afterFiber original.nextPhase

def reframeActivationAcrossEdit
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin : State catalog Ambient}
    (original : ProgramAlignedLandingActivation program origin)
    (edit : State catalog Ambient → State catalog Ambient)
    (movedStep : IterationStep dynamics program.owner original.code (edit origin))
    (executed : executeOne dynamics program.oracle original.code (edit origin) = .ok movedStep)
    (yieldAgrees : LifecycleYieldAgrees movedStep original.landing.step)
    (rawAfterEq : movedStep.after = edit original.landing.step.after)
    (sourcePresent : (edit origin).registry program.owner = some original.fiber)
    (targetMoved : targetView (edit origin) program.owner original.fiber =
      some original.committed)
    (afterPresent : movedStep.after.registry program.owner =
      some original.landing.afterFiber) :
    EditReframedActivation original edit := by
  let movedLanding :=
    Cordis.GlobalActivationOrchestrationTransposition.Landing.reframeFromEditTemplate
      program original.landing edit movedStep executed sourcePresent afterPresent
  let movedWitness : LandingProgramWitness program movedLanding := {
    reachable := original.program_witness.reachable
    program_executed := movedLanding.executed
  }
  cases outcomeEq : original.outcome with
  | iter next continues =>
      have movedContinues : movedLanding.step.next = some next :=
        yieldAgrees.continuation.trans continues
      let moved : ProgramAlignedLandingActivation program (edit origin) := {
        fiber := original.fiber
        present := sourcePresent
        code := original.code
        undos := original.undos
        committed := original.committed
        phase := original.phase
        target := targetMoved
        landing := movedLanding
        program_witness := movedWitness
        outcome := .iter next movedContinues
      }
      refine ⟨moved, ?_⟩
      unfold ProgramAlignedLandingActivation.after
        ProgramAlignedLandingActivation.nextPhase moved
      change setPhase movedStep.after program.owner
          original.landing.afterFiber
          (.reloading next (movedStep.undo :: original.undos)
            (original.landing.component_eq.symm ▸ original.committed)) =
        setPhase (edit original.landing.step.after) program.owner
          original.landing.afterFiber original.nextPhase
      rw [rawAfterEq]
      rw [yieldAgrees.undo_eq]
      simp [ProgramAlignedLandingActivation.nextPhase, outcomeEq]
  | finish done =>
      have movedDone : movedLanding.step.next = none := yieldAgrees.continuation.trans done
      let moved : ProgramAlignedLandingActivation program (edit origin) := {
        fiber := original.fiber
        present := sourcePresent
        code := original.code
        undos := original.undos
        committed := original.committed
        phase := original.phase
        target := targetMoved
        landing := movedLanding
        program_witness := movedWitness
        outcome := .finish movedDone
      }
      refine ⟨moved, ?_⟩
      unfold ProgramAlignedLandingActivation.after
        ProgramAlignedLandingActivation.nextPhase moved
      change setPhase movedStep.after program.owner
          original.landing.afterFiber
          (.active (movedStep.undo :: original.undos)
            (original.landing.component_eq.symm ▸ original.committed)) =
        setPhase (edit original.landing.step.after) program.owner
          original.landing.afterFiber original.nextPhase
      rw [rawAfterEq]
      rw [yieldAgrees.undo_eq]
      simp [ProgramAlignedLandingActivation.nextPhase, outcomeEq]

/-! ## Corrected exact activation/orchestration transposition -/

structure ActivationOrchestrationTransposition
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) where
  orchestrationFirstState : State catalog Ambient
  orchestrationFirst : OrchestrationStep origin orchestrationFirstState
  activationSecond : ProgramActivation program orchestrationFirstState
  same_template : SameOrchestrationTemplate orchestrationFirst normal
  endpoint_eq : activationSecond.after = final

noncomputable def transpose_activation_orchestration
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    {origin final : State catalog Ambient}
    (_inertia : InertiaPolicy dynamics)
    (originWf : WellFormed origin)
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final)
    (different : program.owner ≠ orchestrationName normal)
    (laws : ActivationOrchestrationSwapLaws activation normal) :
    ActivationOrchestrationTransposition activation normal := by
  cases activation with
  | begin fiber guard rootAligned =>
      let original : ProgramActivation program origin :=
        .begin fiber guard rootAligned
      let early := reconstructOrchestration original normal different
        laws.registration_safe
      have earlyDifferent : program.owner ≠ orchestrationName early.step := by
        rw [early.same_template.same_actor]
        exact different
      have movedSource := orchestration_preserves_positive_target early.step originWf
        earlyDifferent guard.present guard.target
      let movedGuard : Cordis.GlobalRuleObservations.BeginGuard
          (orchestrationReplay normal origin) program.owner fiber := {
        present := movedSource.1
        committed := guard.committed
        entry := guard.entry
        target := movedSource.2
      }
      let moved : ProgramActivation program (orchestrationReplay normal origin) :=
        .begin fiber movedGuard rootAligned
      refine {
        orchestrationFirstState := orchestrationReplay normal origin
        orchestrationFirst := early.step
        activationSecond := moved
        same_template := early.same_template
        endpoint_eq := ?_
      }
      change setPhase (orchestrationReplay normal origin) program.owner fiber
          (.reloading (catalog.declaration fiber.component).entry [] guard.committed) = final
      calc
        setPhase (orchestrationReplay normal origin) program.owner fiber
            (.reloading (catalog.declaration fiber.component).entry [] guard.committed) =
            orchestrationReplay normal
              (setPhase origin program.owner fiber
                (.reloading (catalog.declaration fiber.component).entry []
                  guard.committed)) :=
          (orchestrationReplay_setPhase_commute normal origin program.owner fiber _
            different).symm
        _ = final := orchestrationReplay_before normal
  | landing aligned =>
      let original : ProgramActivation program origin := .landing aligned
      let edit := orchestrationReplay normal
      let early := reconstructOrchestration original normal different
        laws.registration_safe
      have earlyDifferent : program.owner ≠ orchestrationName early.step := by
        rw [early.same_template.same_actor]
        exact different
      have movedSource := orchestration_preserves_positive_target early.step originWf
        earlyDifferent aligned.present aligned.target
      have frame := laws.execution_frame
      change ExactExecutionFrame program aligned.landing.step edit at frame
      let movedStep := Classical.choose frame
      have frameSpec := Classical.choose_spec frame
      have executed := frameSpec.1
      have yieldAgrees := frameSpec.2.1
      have rawAfterEq := frameSpec.2.2
      have afterPresent : movedStep.after.registry program.owner =
          some aligned.landing.afterFiber := by
        rw [rawAfterEq]
        exact orchestrationReplay_foreign_present normal aligned.landing.step.after
          different aligned.landing.after_present
      let movedPack := reframeActivationAcrossEdit aligned edit movedStep executed
        yieldAgrees rawAfterEq movedSource.1 movedSource.2 afterPresent
      let moved : ProgramActivation program (edit origin) := .landing movedPack.activation
      refine {
        orchestrationFirstState := edit origin
        orchestrationFirst := early.step
        activationSecond := moved
        same_template := early.same_template
        endpoint_eq := ?_
      }
      change movedPack.activation.after = final
      calc
        movedPack.activation.after =
            setPhase (edit aligned.landing.step.after) program.owner
              aligned.landing.afterFiber aligned.nextPhase := movedPack.after_eq
        _ = edit (setPhase aligned.landing.step.after program.owner
              aligned.landing.afterFiber aligned.nextPhase) :=
          (orchestrationReplay_setPhase_commute normal aligned.landing.step.after
            program.owner aligned.landing.afterFiber aligned.nextPhase different).symm
        _ = final := orchestrationReplay_before normal

/-! ## A nonregistering ordinary iterator may read the birth clock -/

namespace InsertClockGap

abbrev Signature : StaticSignature where
  Name := Bool
  Key := Unit
  ComponentId := Unit
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Nat
  Value _ := Unit
  nameDecEq := inferInstance
  keyDecEq := inferInstance
  componentDecEq := inferInstance

def declaration : ComponentDecl Signature where
  dependencies := { keys := [], nodup := by simp }
  provision := []
  provision_nodup := by simp
  entry := ()

abbrev exampleCatalog : Catalog Signature where
  declaration _ := declaration

abbrev ExampleState := GlobalState exampleCatalog Unit

def fiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def origin : ExampleState where
  ambient := ()
  nextBirth := 1
  registry := Coeffect.setAt Coeffect.empty false fiber

@[simp] theorem owner_present : origin.registry false = some fiber := by
  simp [origin]

@[simp] theorem inserted_absent : origin.registry true = none := by
  simp [origin]

theorem origin_wellFormed : WellFormed origin := by
  constructor
  · intro name current lookup
    cases name <;> simp [origin] at lookup <;> subst current <;> decide
  · intro name current parent lookup parentEq
    cases name <;> simp [origin] at lookup <;> subst current <;>
      simp [fiber] at parentEq
  · intro name current parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [origin] at lookup <;> subst current <;>
      simp [fiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    simp [declaration] at leftKey
  · intro name current lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [declaration] at required
  · intro name current lookup committed committedEq declared provider providerLookup
    rcases declared with ⟨key, required⟩
    simp [declaration] at required

def result (state : ExampleState) : OrdinaryResult exampleCatalog Unit where
  after := state
  undo := state.nextBirth
  next := none

def runIterator (owner : Bool) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Unit) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.ordinary (result state))

def stateSetoid : Setoid ExampleState where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

def dynamics : Dynamics Signature exampleCatalog Unit where
  equivalence := stateSetoid
  runIterator := runIterator
  applyExternalUndo _ state := state
  ordinary_recovers := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        rfl
  externalUndo_respects := by
    intro undo left right related
    exact related
  ordinary_confined := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        exact {
          beforeFiber := current
          afterFiber := current
          before_present := lookup
          after_present := lookup
          component_eq := rfl
          parent_eq := rfl
          birth_eq := rfl
          retired_eq := rfl
          phase_eq := rfl
          other_unchanged := by intros; rfl
          table_writes := by
            unfold WritesWithinProvision
            intros
            rfl
          nextBirth_eq := rfl
        }
  ordinary_preserves_wellFormed := by
    intro owner code state found runEq wf
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some current =>
        simp [runIterator, lookup] at runEq
        subst found
        exact wf
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    subst right
    rw [runIterator, leftPresent]
    exact .results (.ordinary rfl rfl rfl)
  ReadEquivalent _ left right := left = right
  read_refl := by intros; rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    subst right
    rw [runIterator, leftPresent]
    exact .results (.ordinary rfl rfl rfl)
  retire_respects := by
    intro name left right related
    subst right
    rfl

def oracle : RegistrationOracle dynamics false Unit where
  certify _ _ := .error ()

def program : Program dynamics where
  owner := false
  RegistrationError := Unit
  oracle := oracle
  root := ()

theorem run_success (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry false = some current) :
    dynamics.runIterator false () state = .ok (.ordinary (result state)) := by
  simp [dynamics, runIterator, present]

def step (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry false = some current) :
    IterationStep dynamics false () state where
  after := state
  undo := .external state.nextBirth
  next := none
  source := .ordinary (result state) (run_success state current present)
  recovers := rfl
  preserves_wellFormed := fun wf ↦ wf

theorem step_executed (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry false = some current) :
    executeOne dynamics oracle () state = .ok (step state current present) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success state current present)
  · rename_i found foundEq
    have resultEq : found = result state := IteratorResult.ordinary.inj
      (Except.ok.inj (foundEq.symm.trans (run_success state current present)))
    subst found
    have proofEq : foundEq = run_success state current present := Subsingleton.elim _ _
    cases proofEq
    rfl
  · rename_i found foundEq
    cases foundEq.symm.trans (run_success state current present)

def originalStep : IterationStep dynamics program.owner () origin :=
  step origin fiber owner_present

theorem original_executed :
    executeOne dynamics program.oracle () origin = .ok originalStep :=
  step_executed origin fiber owner_present

def inserted : ExampleState := insertFiber origin true none ()

def insertStep : OrchestrationStep origin inserted :=
  .insert origin true ⟨inserted_absent⟩ none (by simp) () (by simp [declaration])

@[simp] theorem inserted_owner_present : inserted.registry false = some fiber := by
  simp [inserted, origin]

theorem inserted_wellFormed : WellFormed inserted :=
  insertStep.preservesWellFormed origin_wellFormed

def movedStep : IterationStep dynamics program.owner () inserted :=
  step inserted fiber inserted_owner_present

theorem moved_executed :
    executeOne dynamics program.oracle () inserted = .ok movedStep :=
  step_executed inserted fiber inserted_owner_present

@[simp] theorem original_nonregistering : stepRegisteredChild originalStep = none := rfl

theorem exact_undo_changes : movedStep.undo ≠ originalStep.undo := by
  simp [movedStep, originalStep, step, inserted, origin]

theorem no_insert_execution_frame :
    ¬ExactExecutionFrame program originalStep (orchestrationReplay insertStep) := by
  rintro ⟨candidate, candidateExecuted, agrees, rawAfterEq⟩
  have candidateEq : candidate = movedStep :=
    Except.ok.inj (candidateExecuted.symm.trans moved_executed)
  subst candidate
  exact exact_undo_changes agrees.undo_eq

theorem wellformed_nonregistration_do_not_supply_frame :
    WellFormed origin ∧ stepRegisteredChild originalStep = none ∧
      ¬ExactExecutionFrame program originalStep (orchestrationReplay insertStep) :=
  ⟨origin_wellFormed, original_nonregistering, no_insert_execution_frame⟩

end InsertClockGap

/-! ## A fixed registration oracle may observe foreign retirement -/

namespace RetireOracleGap

inductive Name where
  | owner
  | actor
  | childBefore
  | childAfter
deriving DecidableEq, Repr

abbrev Signature : StaticSignature where
  Name := Name
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

abbrev exampleCatalog : Catalog Signature where
  declaration _ := declaration

abbrev ExampleState := GlobalState exampleCatalog Unit

def emptyView : CommittedView declaration where
  provider declared := False.elim (by
    rcases declared with ⟨key, required⟩
    simp [declaration] at required)

def ownerFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .reloading () [] emptyView

def actorFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 1
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def origin : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty .owner ownerFiber) .actor actorFiber

@[simp] theorem owner_present : origin.registry .owner = some ownerFiber := by
  simp [origin]

@[simp] theorem actor_present : origin.registry .actor = some actorFiber := by
  simp [origin]

@[simp] theorem childBefore_absent : origin.registry .childBefore = none := by
  simp [origin]

@[simp] theorem childAfter_absent : origin.registry .childAfter = none := by
  simp [origin]

theorem origin_wellFormed : WellFormed origin := by
  constructor
  · intro name current lookup
    cases name <;> simp [origin] at lookup <;> subst current <;> decide
  · intro name current parent lookup parentEq
    cases name <;> simp [origin] at lookup <;> subst current <;>
      simp [ownerFiber, actorFiber] at parentEq
  · intro name current parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [origin] at lookup <;> subst current <;>
      simp [ownerFiber, actorFiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    simp [declaration] at leftKey
  · intro name current lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [declaration] at required
  · intro name current lookup committed committedEq declared provider providerLookup
    rcases declared with ⟨key, required⟩
    simp [declaration] at required

def request : RegistrationRequest Signature where
  component := ()
  next _ := none

def runIterator (runnerOwner : Name) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Unit) :=
  match state.registry runnerOwner with
  | none => .error ()
  | some _ => .ok (.register request)

def coarseSetoid : Setoid ExampleState where
  r _ _ := True
  iseqv := ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩

def dynamics : Dynamics Signature exampleCatalog Unit where
  equivalence := coarseSetoid
  runIterator := runIterator
  applyExternalUndo _ state := state
  ordinary_recovers := by
    intro runnerOwner code state found runEq
    cases lookup : state.registry runnerOwner <;> simp [runIterator, lookup] at runEq
  externalUndo_respects := by intros; trivial
  ordinary_confined := by
    intro runnerOwner code state found runEq
    cases lookup : state.registry runnerOwner <;> simp [runIterator, lookup] at runEq
  ordinary_preserves_wellFormed := by
    intro runnerOwner code state found runEq wf
    cases lookup : state.registry runnerOwner <;> simp [runIterator, lookup] at runEq
  run_respects := by
    intro runnerOwner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.register rfl rfl)
  ReadEquivalent _ _ _ := True
  read_refl := by intros; trivial
  run_read_confined := by
    intro runnerOwner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.register rfl rfl)
  retire_respects := by intros; trivial

def selectedChild (state : ExampleState) : Name :=
  match state.registry .actor with
  | some fiber => if fiber.retired then .childAfter else .childBefore
  | none => .childAfter

def admission
    (state : ExampleState) (registration : RegistrationRequest Signature)
    (ownerCurrent : Fiber exampleCatalog)
    (ownerPresent : state.registry .owner = some ownerCurrent)
    (child : Name) (childAbsent : state.registry child = none) :
    RegistrationAdmission dynamics state .owner registration where
  child := child
  fresh := ⟨childAbsent⟩
  ownerFiber := ownerCurrent
  owner_present := ownerPresent
  provision_fresh := by
    intro existing existingFiber key present newKey existingKey
    simp [declaration] at newKey
  registration_recovers := trivial

def oracle : RegistrationOracle dynamics .owner Unit where
  certify state registration :=
    match ownerEq : state.registry .owner with
    | none => .error ()
    | some ownerCurrent =>
        let child := selectedChild state
        match childEq : state.registry child with
        | none => .ok (admission state registration ownerCurrent ownerEq child childEq)
        | some _ => .error ()

def program : Program dynamics where
  owner := .owner
  RegistrationError := Unit
  oracle := oracle
  root := ()

theorem run_success (state : ExampleState) (current : Fiber exampleCatalog)
    (present : state.registry .owner = some current) :
    dynamics.runIterator .owner () state = .ok (.register request) := by
  simp [dynamics, runIterator, present]

def originAdmission : RegistrationAdmission dynamics origin .owner request :=
  admission origin request ownerFiber owner_present .childBefore childBefore_absent

theorem origin_certified :
    oracle.certify origin request = .ok originAdmission := by
  rfl

def originalStep : IterationStep dynamics program.owner () origin where
  after := originAdmission.after
  undo := originAdmission.undo
  next := originAdmission.next
  source := .registration request originAdmission (run_success origin ownerFiber owner_present)
  recovers := originAdmission.registration_recovers
  preserves_wellFormed := originAdmission.after_wellFormed

theorem original_executed :
    executeOne dynamics program.oracle () origin = .ok originalStep := by
  rfl

def retiredOrigin : ExampleState := retireFiber origin .actor actorFiber

def retireEarly : OrchestrationStep origin retiredOrigin :=
  .retire origin .actor actorFiber actor_present

theorem retiredOrigin_wellFormed : WellFormed retiredOrigin :=
  retireEarly.preservesWellFormed origin_wellFormed

@[simp] theorem retired_owner_present :
    retiredOrigin.registry .owner = some ownerFiber := by
  simp [retiredOrigin, origin]

@[simp] theorem retired_childAfter_absent :
    retiredOrigin.registry .childAfter = none := by
  simp [retiredOrigin, origin]

def retiredAdmission : RegistrationAdmission dynamics retiredOrigin .owner request :=
  admission retiredOrigin request ownerFiber retired_owner_present .childAfter
    retired_childAfter_absent

theorem retired_certified :
    oracle.certify retiredOrigin request = .ok retiredAdmission := by
  rfl

def movedStep : IterationStep dynamics program.owner () retiredOrigin where
  after := retiredAdmission.after
  undo := retiredAdmission.undo
  next := retiredAdmission.next
  source := .registration request retiredAdmission
    (run_success retiredOrigin ownerFiber retired_owner_present)
  recovers := retiredAdmission.registration_recovers
  preserves_wellFormed := retiredAdmission.after_wellFormed

theorem moved_executed :
    executeOne dynamics program.oracle () retiredOrigin = .ok movedStep := by
  rfl

@[simp] theorem original_registered_child :
    stepRegisteredChild originalStep = some .childBefore := rfl

@[simp] theorem moved_registered_child :
    stepRegisteredChild movedStep = some .childAfter := rfl

theorem child_actor_inequality : stepRegisteredChild originalStep ≠ some .actor := by
  simp

theorem exact_undo_changes : movedStep.undo ≠ originalStep.undo := by
  simp [movedStep, originalStep, RegistrationAdmission.undo, retiredAdmission,
    originAdmission, admission]

theorem no_retire_execution_frame :
    ¬ExactExecutionFrame program originalStep
      (fun state ↦ retireFiber state .actor actorFiber) := by
  rintro ⟨candidate, candidateExecuted, agrees, rawAfterEq⟩
  have candidateEq : candidate = movedStep :=
    Except.ok.inj (candidateExecuted.symm.trans moved_executed)
  subst candidate
  exact exact_undo_changes agrees.undo_eq

theorem owner_target : targetView origin .owner ownerFiber = some emptyView := by
  apply targetView_eq_of_isTarget origin_wellFormed
  exact {
    present := owner_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [declaration] at required
  }

@[simp] theorem original_after_owner_present :
    originalStep.after.registry .owner = some ownerFiber := by
  simp [originalStep, originAdmission, RegistrationAdmission.after, admission, origin]

def landing : Cordis.GlobalLifecycle.Landing dynamics program.owner () origin ownerFiber where
  RegistrationError := Unit
  oracle := oracle
  step := originalStep
  executed := original_executed
  before_present := owner_present
  afterFiber := ownerFiber
  after_present := original_after_owner_present
  component_eq := rfl
  phase_eq := rfl

def aligned : ProgramAlignedLandingActivation program origin where
  fiber := ownerFiber
  present := owner_present
  code := ()
  undos := []
  committed := emptyView
  phase := rfl
  target := owner_target
  landing := landing
  program_witness := {
    reachable := Reach.root
    program_executed := original_executed
  }
  outcome := .finish rfl

def activation : ProgramActivation program origin := .landing aligned

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

theorem activation_after_wellFormed : WellFormed activation.after :=
  activation.preservesWellFormed inertia origin_wellFormed

theorem activation_actor_present :
    activation.after.registry .actor = some actorFiber :=
  activation.foreignLookupFrame.lookup actor_present (by decide)

def normalRetired : ExampleState := retireFiber activation.after .actor actorFiber

def normalRetire : OrchestrationStep activation.after normalRetired :=
  .retire activation.after .actor actorFiber activation_actor_present

theorem normalRetired_wellFormed : WellFormed normalRetired :=
  normalRetire.preservesWellFormed activation_after_wellFormed

theorem activation_registration_safe : RegistrationSafe activation normalRetire := by
  change stepRegisteredChild originalStep ≠ some .actor
  exact child_actor_inequality

theorem activation_execution_frame_fails : ¬ExecutionFrameFor activation normalRetire := by
  change ¬ExactExecutionFrame program originalStep
    (fun state ↦ retireFiber state .actor actorFiber)
  exact no_retire_execution_frame

theorem registration_safety_does_not_supply_frame :
    RegistrationSafe activation normalRetire ∧
      ¬ExecutionFrameFor activation normalRetire :=
  ⟨activation_registration_safe, activation_execution_frame_fails⟩

theorem raw_registration_request_is_unchanged :
    dynamics.runIterator .owner () origin = .ok (.register request) ∧
      dynamics.runIterator .owner () retiredOrigin = .ok (.register request) :=
  ⟨run_success origin ownerFiber owner_present,
    run_success retiredOrigin ownerFiber retired_owner_present⟩

end RetireOracleGap

/-! ## Positive finite instances of the corrected branch matrix -/

namespace BeginInsert

open Cordis.GlobalRegistry.Example Cordis.GlobalLifecycle.Example

abbrev dynamics := Cordis.GlobalLifecycle.Example.dynamics
abbrev inertia := Cordis.GlobalLifecycle.Example.inertia
abbrev program := Cordis.GlobalIteratorIndependence.Example.program
abbrev origin := Cordis.GlobalLifecycle.Example.start

def activation : ProgramActivation program origin :=
  .begin inactiveProvider {
    present := start_present
    committed := emptyProviderView
    entry := rfl
    target := start_target
  } rfl

theorem activation_after : activation.after = beginState := rfl

def final : GlobalState exampleCatalog Nat :=
  insertFiber activation.after 1 (some 0) .consumer

def normal : OrchestrationStep activation.after final :=
  .insert activation.after 1 (by constructor; rfl) (some 0) (by
    intro parent parentEq
    have parent_eq : parent = 0 := Option.some.inj parentEq.symm
    subst parent
    exact ⟨_, by simpa [activation_after] using begin_present⟩) .consumer (by
      simp [consumerDecl])

theorem laws : ActivationOrchestrationSwapLaws activation normal where
  registration_safe := rfl
  execution_frame := trivial

noncomputable def transposition :
    ActivationOrchestrationTransposition activation normal :=
  transpose_activation_orchestration inertia start_wellFormed activation normal
    (by decide) laws

noncomputable def exposedTags : OrchestrationKind × Nat × Rule :=
  (orchestrationKind transposition.orchestrationFirst,
    orchestrationName transposition.orchestrationFirst,
    transposition.activationSecond.rule)

/-- Computable finite projection of the concrete corrected exchange. -/
def executableTags : OrchestrationKind × Nat × Rule :=
  (.insert, 1, .begin)

theorem early_kind : orchestrationKind transposition.orchestrationFirst = .insert :=
  transposition.same_template.same_kind.trans rfl

theorem early_actor : orchestrationName transposition.orchestrationFirst = 1 :=
  transposition.same_template.same_actor.trans rfl

theorem moved_activation_rule : transposition.activationSecond.rule = .begin := by
  rfl

theorem exposedTags_eq : exposedTags = (.insert, 1, .begin) := by
  rw [Prod.ext_iff]
  exact ⟨early_kind, by
    rw [Prod.ext_iff]
    exact ⟨early_actor, moved_activation_rule⟩⟩

theorem exposedTags_eq_executableTags : exposedTags = executableTags :=
  exposedTags_eq

end BeginInsert

namespace BeginRetire

open Cordis.GlobalActivationTransposition.Example.BeginPairs

abbrev origin := beginOrigin
abbrev program := leftProgram
abbrev dynamics := Cordis.GlobalLandingTransposition.Example.dynamics
abbrev inertia := Cordis.GlobalLandingTransposition.Example.inertia

def activation : ProgramActivation program origin := beginLeft

theorem foreign_present :
    activation.after.registry true = some (inactiveFiber 1) :=
  activation.foreignLookupFrame.lookup begin_right_present (by decide)

def final : ExampleState :=
  retireFiber activation.after true (inactiveFiber 1)

def normal : OrchestrationStep activation.after final :=
  .retire activation.after true (inactiveFiber 1) foreign_present

theorem laws : ActivationOrchestrationSwapLaws activation normal where
  registration_safe := by rintro impossible; cases impossible
  execution_frame := trivial

noncomputable def transposition :
    ActivationOrchestrationTransposition activation normal :=
  transpose_activation_orchestration inertia beginOrigin_wellFormed activation normal
    (by decide) laws

theorem early_kind : orchestrationKind transposition.orchestrationFirst = .retire :=
  transposition.same_template.same_kind.trans rfl

theorem early_actor : orchestrationName transposition.orchestrationFirst = true :=
  transposition.same_template.same_actor.trans rfl

theorem moved_activation_rule : transposition.activationSecond.rule = .begin := by
  rfl

end BeginRetire

namespace OrdinaryFinishInsert

open Cordis.GlobalRegistry.Example Cordis.GlobalLifecycle.Example

abbrev dynamics := Cordis.GlobalLifecycle.Example.dynamics
abbrev inertia := Cordis.GlobalLifecycle.Example.inertia
abbrev program := Cordis.GlobalIteratorIndependence.Example.program
abbrev origin := Cordis.GlobalLifecycle.Example.iterState

def aligned : ProgramAlignedLandingActivation program origin where
  fiber := iterFiber
  present := iter_present
  code := 0
  undos := [firstStep.undo]
  committed := emptyProviderView
  phase := rfl
  target := iter_target
  landing := finalLanding
  program_witness := ⟨Cordis.GlobalIteratorIndependence.Example.continuation_reachable,
    finalStep_executed⟩
  outcome := .finish rfl

def activation : ProgramActivation program origin := .landing aligned

theorem activation_after : activation.after = finishState := rfl

def final : GlobalState exampleCatalog Nat :=
  insertFiber activation.after 1 (some 0) .consumer

def normal : OrchestrationStep activation.after final :=
  .insert activation.after 1 (by constructor; rfl) (some 0) (by
    intro parent parentEq
    have parent_eq : parent = 0 := Option.some.inj parentEq.symm
    subst parent
    exact ⟨_, by simpa [activation_after] using finish_present⟩) .consumer (by
      simp [consumerDecl])

def earlyState : GlobalState exampleCatalog Nat := orchestrationReplay normal origin

def movedResult : OrdinaryResult exampleCatalog Nat where
  after := advance earlyState
  undo := 0
  next := none

theorem movedRunEq :
    dynamics.runIterator program.owner 0 earlyState = .ok (.ordinary movedResult) := by
  rfl

def movedStep : IterationStep dynamics program.owner 0 earlyState where
  after := movedResult.after
  undo := .external movedResult.undo
  next := movedResult.next
  source := .ordinary movedResult movedRunEq
  recovers := by
    change (applyExternalUndo 0 (advance earlyState)).ambient = earlyState.ambient
    rfl
  preserves_wellFormed := fun wf ↦ advance_preserves wf

theorem movedStep_executed :
    executeOne dynamics program.oracle 0 earlyState = .ok movedStep := by
  rfl

theorem raw_after_eq :
    movedStep.after = orchestrationReplay normal finalStep.after := by
  rfl

theorem occurrenceFrame :
    ExactExecutionFrame program finalStep (orchestrationReplay normal) := by
  exact ⟨movedStep, movedStep_executed, ⟨rfl, rfl, rfl⟩, raw_after_eq⟩

theorem laws : ActivationOrchestrationSwapLaws activation normal where
  registration_safe := rfl
  execution_frame := occurrenceFrame

noncomputable def transposition :
    ActivationOrchestrationTransposition activation normal :=
  transpose_activation_orchestration inertia iterState_wellFormed activation normal
    (by decide) laws

theorem early_kind : orchestrationKind transposition.orchestrationFirst = .insert :=
  transposition.same_template.same_kind.trans rfl

theorem early_actor : orchestrationName transposition.orchestrationFirst = 1 :=
  transposition.same_template.same_actor.trans rfl

theorem moved_activation_rule : transposition.activationSecond.rule = .finish := by
  rfl

theorem exact_endpoint : transposition.activationSecond.after = final :=
  transposition.endpoint_eq

end OrdinaryFinishInsert

namespace RegisteringFinishRetire

open Cordis.GlobalRegistry.Example

abbrev Signature := Cordis.GlobalDynamics.Example.ExampleSig
abbrev exampleCatalog := Cordis.GlobalDynamics.Example.exampleCatalog
abbrev ExampleState := Cordis.GlobalDynamics.Example.ExampleState
abbrev dynamics := Cordis.GlobalDynamics.Example.dynamics

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

def actorFiber : Fiber exampleCatalog where
  component := .consumer
  parent := some 0
  birth := Cordis.GlobalDynamics.Example.start.nextBirth
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def base : ExampleState :=
  insertFiber Cordis.GlobalDynamics.Example.start 2 (some 0) .consumer

@[simp] theorem base_owner_present :
    base.registry 0 = some Cordis.GlobalLifecycle.Example.inactiveProvider := rfl

@[simp] theorem base_actor_present : base.registry 2 = some actorFiber := rfl

@[simp] theorem base_child_absent : base.registry 1 = none := rfl

def actorInsert : OrchestrationStep Cordis.GlobalDynamics.Example.start base :=
  .insert Cordis.GlobalDynamics.Example.start 2 (by constructor; rfl) (some 0) (by
    intro parent parentEq
    have parent_eq : parent = 0 := Option.some.inj parentEq.symm
    subst parent
    exact ⟨Cordis.GlobalLifecycle.Example.inactiveProvider, rfl⟩) .consumer (by
      simp [consumerDecl])

theorem base_wellFormed : WellFormed base :=
  actorInsert.preservesWellFormed Cordis.GlobalDynamics.Example.start_wellFormed

def ownerFiber : Fiber exampleCatalog := {
  Cordis.GlobalLifecycle.Example.inactiveProvider with
    phase := .reloading 1 [] emptyProviderView
}

def origin : ExampleState :=
  setPhase base 0 Cordis.GlobalLifecycle.Example.inactiveProvider
    (.reloading 1 [] emptyProviderView)

@[simp] theorem origin_owner_present : origin.registry 0 = some ownerFiber := rfl

@[simp] theorem origin_actor_present : origin.registry 2 = some actorFiber := rfl

@[simp] theorem origin_child_absent : origin.registry 1 = none := rfl

theorem origin_wellFormed : WellFormed origin := by
  apply setPhase_installed_preserves base_owner_present
    (.reloading 1 [] emptyProviderView) (by simp [Phase.Installed]) _ base_wellFormed
  intro committed committedEq
  have committed_eq : emptyProviderView = committed := Option.some.inj committedEq
  subst committed
  intro declared
  rcases declared with ⟨key, required⟩
  change key ∈ providerDecl.dependencies.keys at required
  simp [providerDecl] at required

theorem origin_target : targetView origin 0 ownerFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget origin_wellFormed
  exact {
    present := origin_owner_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      change key ∈ providerDecl.dependencies.keys at required
      simp [providerDecl] at required
  }

def program : Program dynamics where
  owner := 0
  RegistrationError := String
  oracle := Cordis.GlobalDynamics.Example.oracle
  root := 1

abbrev request := Cordis.GlobalDynamics.Example.registrationRequest

def admission : RegistrationAdmission dynamics origin program.owner request where
  child := 1
  fresh := ⟨origin_child_absent⟩
  ownerFiber := ownerFiber
  owner_present := origin_owner_present
  provision_fresh := by
    intro existing existingFiber key present newKey oldKey
    change key ∈ consumerDecl.provision at newKey
    simp [consumerDecl] at newKey
  registration_recovers := rfl

theorem raw_run :
    dynamics.runIterator program.owner 1 origin = .ok (.register request) := rfl

theorem admission_certified :
    program.oracle.certify origin request = .ok admission := rfl

def step : IterationStep dynamics program.owner 1 origin where
  after := admission.after
  undo := admission.undo
  next := admission.next
  source := .registration request admission raw_run
  recovers := admission.registration_recovers
  preserves_wellFormed := admission.after_wellFormed

theorem step_executed : executeOne dynamics program.oracle 1 origin = .ok step := rfl

def landing : Landing dynamics program.owner 1 origin ownerFiber where
  RegistrationError := String
  oracle := program.oracle
  step := step
  executed := step_executed
  before_present := origin_owner_present
  afterFiber := ownerFiber
  after_present := by rfl
  component_eq := rfl
  phase_eq := rfl

def aligned : ProgramAlignedLandingActivation program origin where
  fiber := ownerFiber
  present := origin_owner_present
  code := 1
  undos := []
  committed := emptyProviderView
  phase := rfl
  target := origin_target
  landing := landing
  program_witness := ⟨Reach.root, step_executed⟩
  outcome := .finish rfl

def activation : ProgramActivation program origin := .landing aligned

theorem actor_after_present : activation.after.registry 2 = some actorFiber :=
  activation.foreignLookupFrame.lookup origin_actor_present (by decide)

def final : ExampleState := retireFiber activation.after 2 actorFiber

def normal : OrchestrationStep activation.after final :=
  .retire activation.after 2 actorFiber actor_after_present

def movedOrigin : ExampleState := orchestrationReplay normal origin

@[simp] theorem moved_owner_present : movedOrigin.registry 0 = some ownerFiber := by
  rfl

@[simp] theorem moved_child_absent : movedOrigin.registry 1 = none := by
  rfl

def movedAdmission :
    RegistrationAdmission dynamics movedOrigin program.owner request where
  child := 1
  fresh := ⟨moved_child_absent⟩
  ownerFiber := ownerFiber
  owner_present := moved_owner_present
  provision_fresh := by
    intro existing existingFiber key present newKey oldKey
    change key ∈ consumerDecl.provision at newKey
    simp [consumerDecl] at newKey
  registration_recovers := rfl

theorem moved_raw_run :
    dynamics.runIterator program.owner 1 movedOrigin = .ok (.register request) := rfl

theorem moved_admission_certified :
    program.oracle.certify movedOrigin request = .ok movedAdmission := rfl

def movedStep : IterationStep dynamics program.owner 1 movedOrigin where
  after := movedAdmission.after
  undo := movedAdmission.undo
  next := movedAdmission.next
  source := .registration request movedAdmission moved_raw_run
  recovers := movedAdmission.registration_recovers
  preserves_wellFormed := movedAdmission.after_wellFormed

theorem movedStep_executed :
    executeOne dynamics program.oracle 1 movedOrigin = .ok movedStep := rfl

theorem insertFiber_retireFiber_commute
    (state : ExampleState) (child retired : Nat)
    (parent : Option Nat) (component : Signature.ComponentId)
    (retiredFiber : Fiber exampleCatalog) (different : retired ≠ child) :
    insertFiber (retireFiber state retired retiredFiber) child parent component =
      retireFiber (insertFiber state child parent component) retired retiredFiber := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [insertFiber, retireFiber, GlobalState.mk.injEq]
      exact ⟨trivial, trivial,
        Cordis.Coeffect.setAt_commute registry retired child different
          { retiredFiber with retired := true }
          {
            component := component
            parent := parent
            birth := nextBirth
            table := Cordis.Coeffect.empty
            table_within_provision := by simp
            retired := false
            phase := .inactive none
          }⟩

theorem raw_after_eq : movedStep.after = orchestrationReplay normal step.after := by
  change insertFiber (retireFiber origin 2 actorFiber) 1 (some 0) .consumer =
    retireFiber (insertFiber origin 1 (some 0) .consumer) 2 actorFiber
  exact insertFiber_retireFiber_commute origin 1 2 (some 0) .consumer actorFiber (by decide)

theorem occurrenceFrame :
    ExactExecutionFrame program step (orchestrationReplay normal) := by
  exact ⟨movedStep, movedStep_executed, ⟨rfl, rfl, rfl⟩, raw_after_eq⟩

theorem registration_safe : RegistrationSafe activation normal := by
  change some 1 ≠ some 2
  decide

theorem laws : ActivationOrchestrationSwapLaws activation normal where
  registration_safe := registration_safe
  execution_frame := occurrenceFrame

noncomputable def transposition :
    ActivationOrchestrationTransposition activation normal :=
  transpose_activation_orchestration inertia origin_wellFormed activation normal
    (by decide) laws

theorem early_kind : orchestrationKind transposition.orchestrationFirst = .retire :=
  transposition.same_template.same_kind.trans rfl

theorem early_actor : orchestrationName transposition.orchestrationFirst = 2 :=
  transposition.same_template.same_actor.trans rfl

theorem moved_activation_rule : transposition.activationSecond.rule = .finish := by
  rfl

theorem original_safe_child :
    ProgramActivation.registeredChild activation = some 1 ∧ (1 : Nat) ≠ 2 :=
  ⟨rfl, by decide⟩

theorem exact_endpoint : transposition.activationSecond.after = final :=
  transposition.endpoint_eq

end RegisteringFinishRetire
