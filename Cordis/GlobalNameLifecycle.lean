import Cordis.GlobalNameAction
import Cordis.GlobalLifecycleBisimulation

/-!
# Conditional name equivariance for lifecycle and unified global steps

This module completes the finite executable analogue of CORDIS paper Lemma 56 at revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, conditional only on the genuinely external
semantic laws: iterator execution, external undo, the dynamics equivalence, inertia, and fixed
catalog entry codes.

Actions on results, requests, errors, registration admissions, conjugated oracles, iteration
steps, landings, recovery admissions, lifecycle transitions, and unified steps are constructed.
No assumption mentions `Transition`, `GlobalCalculus.Step`, landing transport, recovery-admission
transport, or a rule-equivariance certificate.

This is a conditional finite-state analogue, not an unconditional derivation of paper Lemma 56
from the base `Dynamics` record. Component identifiers and the catalog remain fixed, while names
and every declared opaque payload carrier act by explicit equivalences. Registration-admission
errors are local to the conjugated oracle and therefore remain unchanged. Lifecycle and unified
transport are stated for well-formed source states because target-view uniqueness is used.
-/

set_option autoImplicit false

namespace Cordis.GlobalNameLifecycle

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
  Cordis.GlobalCalculus Cordis.GlobalRelations Cordis.GlobalNameAction
  Cordis.GlobalLifecycleBisimulation Cordis.GlobalVestigial

universe u v

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-!
## Canonical actions on external result data
-/

def actOrdinaryResult
    (action : NameAction sig Ambient) (result : OrdinaryResult catalog Ambient) :
    OrdinaryResult catalog Ambient where
  after := actState action result.after
  undo := action.externalUndo result.undo
  next := result.next.map action.iterator

def actRegistrationRequest
    (action : NameAction sig Ambient) (request : RegistrationRequest sig) :
    RegistrationRequest sig where
  component := request.component
  next actedChild := (request.next (action.name.symm actedChild)).map action.iterator

@[simp]
theorem actRegistrationRequest_next_apply
    (action : NameAction sig Ambient) (request : RegistrationRequest sig) (child : sig.Name) :
    (actRegistrationRequest action request).next (action.name child) =
      (request.next child).map action.iterator := by
  simp [actRegistrationRequest]

def actIteratorResult
    (action : NameAction sig Ambient) :
    IteratorResult catalog Ambient → IteratorResult catalog Ambient
  | .ordinary result => .ordinary (actOrdinaryResult action result)
  | .register request => .register (actRegistrationRequest action request)

def mapExcept
    {ErrorOne : Type u} {ErrorTwo : Type v} {ResultOne : Type u} {ResultTwo : Type v}
    (mapError : ErrorOne → ErrorTwo) (mapResult : ResultOne → ResultTwo) :
    Except ErrorOne ResultOne → Except ErrorTwo ResultTwo
  | .error error => .error (mapError error)
  | .ok result => .ok (mapResult result)

def actRunOutput
    (action : NameAction sig Ambient) :
    Except sig.Error (IteratorResult catalog Ambient) →
      Except sig.Error (IteratorResult catalog Ambient) :=
  mapExcept action.error (actIteratorResult action)

@[simp]
theorem actOrdinaryResult_refl (result : OrdinaryResult catalog Ambient) :
    actOrdinaryResult (NameAction.refl sig Ambient) result = result := by
  cases result with
  | mk after undo next => cases next <;> simp [actOrdinaryResult]

theorem actOrdinaryResult_trans
    (first second : NameAction sig Ambient) (result : OrdinaryResult catalog Ambient) :
    actOrdinaryResult (first.trans second) result =
      actOrdinaryResult second (actOrdinaryResult first result) := by
  cases result with
  | mk after undo next => cases next <;> simp [actOrdinaryResult, actState_trans]

@[simp]
theorem actOrdinaryResult_symm_apply
    (action : NameAction sig Ambient) (result : OrdinaryResult catalog Ambient) :
    actOrdinaryResult action.symm (actOrdinaryResult action result) = result := by
  cases result with
  | mk after undo next => cases next <;> simp [actOrdinaryResult]

@[simp]
theorem actOrdinaryResult_apply_symm
    (action : NameAction sig Ambient) (result : OrdinaryResult catalog Ambient) :
    actOrdinaryResult action (actOrdinaryResult action.symm result) = result := by
  cases result with
  | mk after undo next => cases next <;> simp [actOrdinaryResult]

@[simp]
theorem actRegistrationRequest_refl (request : RegistrationRequest sig) :
    actRegistrationRequest (NameAction.refl sig Ambient) request = request := by
  cases request with
  | mk component next =>
      simp only [actRegistrationRequest, RegistrationRequest.mk.injEq]
      refine ⟨trivial, funext ?_⟩
      intro child
      cases nextEq : next child <;> simp [nextEq]

theorem actRegistrationRequest_trans
    (first second : NameAction sig Ambient) (request : RegistrationRequest sig) :
    actRegistrationRequest (first.trans second) request =
      actRegistrationRequest second (actRegistrationRequest first request) := by
  cases request with
  | mk component next =>
      simp only [actRegistrationRequest, RegistrationRequest.mk.injEq]
      refine ⟨trivial, funext ?_⟩
      intro child
      cases nextEq : next (first.name.symm (second.name.symm child)) <;> simp [nextEq]

@[simp]
theorem actRegistrationRequest_symm_apply
    (action : NameAction sig Ambient) (request : RegistrationRequest sig) :
    actRegistrationRequest action.symm (actRegistrationRequest action request) = request := by
  cases request with
  | mk component next =>
      simp only [actRegistrationRequest, RegistrationRequest.mk.injEq]
      refine ⟨trivial, funext ?_⟩
      intro child
      cases nextEq : next child <;> simp [nextEq]

@[simp]
theorem actRegistrationRequest_apply_symm
    (action : NameAction sig Ambient) (request : RegistrationRequest sig) :
    actRegistrationRequest action (actRegistrationRequest action.symm request) = request := by
  cases request with
  | mk component next =>
      simp only [actRegistrationRequest, RegistrationRequest.mk.injEq]
      refine ⟨trivial, funext ?_⟩
      intro child
      cases nextEq : next child <;> simp [nextEq]

@[simp]
theorem actIteratorResult_refl (result : IteratorResult catalog Ambient) :
    actIteratorResult (NameAction.refl sig Ambient) result = result := by
  cases result <;> simp [actIteratorResult]

theorem actIteratorResult_trans
    (first second : NameAction sig Ambient) (result : IteratorResult catalog Ambient) :
    actIteratorResult (first.trans second) result =
      actIteratorResult second (actIteratorResult first result) := by
  cases result <;> simp [actIteratorResult, actOrdinaryResult_trans,
    actRegistrationRequest_trans]

@[simp]
theorem actIteratorResult_symm_apply
    (action : NameAction sig Ambient) (result : IteratorResult catalog Ambient) :
    actIteratorResult action.symm (actIteratorResult action result) = result := by
  cases result <;> simp [actIteratorResult]

@[simp]
theorem actIteratorResult_apply_symm
    (action : NameAction sig Ambient) (result : IteratorResult catalog Ambient) :
    actIteratorResult action (actIteratorResult action.symm result) = result := by
  cases result <;> simp [actIteratorResult]

@[simp]
theorem actRunOutput_refl
    (result : Except sig.Error (IteratorResult catalog Ambient)) :
    actRunOutput (NameAction.refl sig Ambient) result = result := by
  cases result <;> simp [actRunOutput, mapExcept]

theorem actRunOutput_trans
    (first second : NameAction sig Ambient)
    (result : Except sig.Error (IteratorResult catalog Ambient)) :
    actRunOutput (first.trans second) result =
      actRunOutput second (actRunOutput first result) := by
  cases result <;> simp [actRunOutput, mapExcept, actIteratorResult_trans]

@[simp]
theorem actRunOutput_symm_apply
    (action : NameAction sig Ambient)
    (result : Except sig.Error (IteratorResult catalog Ambient)) :
    actRunOutput action.symm (actRunOutput action result) = result := by
  cases result <;> simp [actRunOutput, mapExcept]

@[simp]
theorem actRunOutput_apply_symm
    (action : NameAction sig Ambient)
    (result : Except sig.Error (IteratorResult catalog Ambient)) :
    actRunOutput action (actRunOutput action.symm result) = result := by
  cases result <;> simp [actRunOutput, mapExcept]

/-!
## Explicit noncircular external laws
-/

structure DynamicsNameEquivariant
    (action : NameAction sig Ambient) (dynamics : Dynamics sig catalog Ambient) : Prop where
  run_equivariant : ∀ owner code state,
    dynamics.runIterator (action.name owner) (action.iterator code) (actState action state) =
      actRunOutput action (dynamics.runIterator owner code state)
  externalUndo_equivariant : ∀ code state,
    dynamics.applyExternalUndo (action.externalUndo code) (actState action state) =
      actState action (dynamics.applyExternalUndo code state)
  equivalence_iff : ∀ {left right},
    dynamics.equivalence.r (actState action left) (actState action right) ↔
      dynamics.equivalence.r left right

structure InertiaNameEquivariant
    (action : NameAction sig Ambient) (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) : Prop where
  canAbort_iff : ∀ owner code state,
    inertia.canAbort (action.name owner) (action.iterator code) (actState action state) ↔
      inertia.canAbort owner code state

structure NameLifecycleAssumptions
    (action : NameAction sig Ambient) (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) : Prop where
  entry : action.CatalogEntryInvariant catalog
  dynamics_equivariant : DynamicsNameEquivariant action dynamics
  inertia : InertiaNameEquivariant action dynamics inertia

/-!
## Built-in undo and recovery
-/

theorem retireByName_equivariant
    (action : NameAction sig Ambient) (state : State catalog Ambient) (name : sig.Name) :
    retireByName (actState action state) (action.name name) =
      actState action (retireByName state name) := by
  cases lookup : state.registry name with
  | none =>
      simp [retireByName, lookup]
  | some fiber =>
      have actedSome : (actState action state).registry (action.name name) =
          some (actFiber action fiber) := by
        change actRegistry action state.registry (action.name name) = some (actFiber action fiber)
        exact (actRegistry_lookup_some_iff action state.registry name fiber).2 lookup
      simp only [retireByName, lookup, actedSome]
      exact (actState_retireFiber action state name fiber).symm

theorem applyUndo_equivariant
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    (undo : UndoCode sig) (state : State catalog Ambient) :
    dynamics.applyUndo (actUndoCode action undo) (actState action state) =
      actState action (dynamics.applyUndo undo state) := by
  cases undo with
  | external code => exact equivariant.externalUndo_equivariant code state
  | retire name => exact retireByName_equivariant action state name

theorem recover_equivariant
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    (undos : List (UndoCode sig)) (state : State catalog Ambient) :
    dynamics.recover (undos.map (actUndoCode action)) (actState action state) =
      actState action (dynamics.recover undos state) := by
  induction undos generalizing state with
  | nil => rfl
  | cons undo rest ih =>
      simp only [List.map_cons, Dynamics.recover]
      rw [applyUndo_equivariant equivariant undo state, ih]

/-!
## Structural lifecycle edits and registration admission
-/

theorem actCommittedView_transport
    (action : NameAction sig Ambient)
    {left right : sig.ComponentId} (componentEq : left = right)
    (view : CommittedView (catalog.declaration left)) :
    actCommittedView action (componentEq ▸ view) =
      componentEq ▸ actCommittedView action view := by
  cases componentEq
  rfl

theorem actPhase_transport
    (action : NameAction sig Ambient)
    {left right : sig.ComponentId} (componentEq : left = right)
    (phase : Phase (catalog.declaration left)) :
    actPhase action (componentEq ▸ phase) = componentEq ▸ actPhase action phase := by
  cases componentEq
  rfl

theorem actState_setPhase
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (name : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) :
    actState action (setPhase state name fiber phase) =
      setPhase (actState action state) (action.name name) (actFiber action fiber)
        (actPhase action phase) := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [actState, setPhase, GlobalState.mk.injEq]
      exact ⟨trivial, trivial, by
        rw [actRegistry_setAt]
        congr 2⟩

def actRegistrationAdmission
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {before : State catalog Ambient} {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) :
    RegistrationAdmission dynamics (actState action before) (action.name owner)
      (actRegistrationRequest action request) where
  child := action.name admission.child
  fresh := by
    constructor
    change actRegistry action before.registry (action.name admission.child) = none
    exact (actRegistry_lookup_none_iff action before.registry admission.child).2
      admission.fresh.lookup_eq
  ownerFiber := actFiber action admission.ownerFiber
  owner_present := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action admission.ownerFiber)
    exact (actRegistry_lookup_some_iff action before.registry owner admission.ownerFiber).2
      admission.owner_present
  provision_fresh := by
    intro existing existingFiber key existingLookup requestKey existingKey
    change actRegistry action before.registry existing = some existingFiber at existingLookup
    obtain ⟨originalFiber, originalLookup, fiberEq⟩ :=
      originalFiber_of_actRegistry_lookup action before.registry existingLookup
    subst existingFiber
    exact admission.provision_fresh (action.name.symm existing) originalFiber key
      originalLookup requestKey existingKey
  registration_recovers := by
    change dynamics.equivalence.r
      (dynamics.applyUndo (actUndoCode action (.retire admission.child))
        (insertFiber (actState action before) (action.name admission.child)
          ((some owner).map action.name) request.component))
      (actState action before)
    rw [← actState_insertFiber action before admission.child (some owner) request.component]
    rw [applyUndo_equivariant equivariant (.retire admission.child)]
    exact equivariant.equivalence_iff.mpr admission.registration_recovers

@[simp]
theorem actRegistrationAdmission_after
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {before : State catalog Ambient} {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) :
    (actRegistrationAdmission equivariant admission).after = actState action admission.after := by
  exact (actState_insertFiber action before admission.child (some owner) request.component).symm

@[simp]
theorem actRegistrationAdmission_undo
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {before : State catalog Ambient} {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) :
    (actRegistrationAdmission equivariant admission).undo =
      actUndoCode action admission.undo := rfl

@[simp]
theorem actRegistrationAdmission_next
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {before : State catalog Ambient} {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) :
    (actRegistrationAdmission equivariant admission).next =
      admission.next.map action.iterator := by
  simp [RegistrationAdmission.next, actRegistrationRequest, actRegistrationAdmission]

/-!
## Iteration steps
-/

def actStepSource
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before after : State catalog Ambient}
    {undo : UndoCode sig} {next : Option sig.IteratorCode}
    (source : StepSource dynamics owner code before after undo next) :
    StepSource dynamics (action.name owner) (action.iterator code) (actState action before)
      (actState action after) (actUndoCode action undo) (next.map action.iterator) := by
  cases source with
  | ordinary result runEq =>
      have actedRun := equivariant.run_equivariant owner code before
      rw [runEq] at actedRun
      exact .ordinary (actOrdinaryResult action result) actedRun
  | registration request admission runEq =>
      have actedRun := equivariant.run_equivariant owner code before
      rw [runEq] at actedRun
      let actedAdmission := actRegistrationAdmission equivariant admission
      let actedSource : StepSource dynamics (action.name owner) (action.iterator code)
          (actState action before) actedAdmission.after actedAdmission.undo
            actedAdmission.next :=
        .registration (actRegistrationRequest action request) actedAdmission actedRun
      have afterEq : actedAdmission.after = actState action admission.after :=
        actRegistrationAdmission_after equivariant admission
      have undoEq : actedAdmission.undo = actUndoCode action admission.undo :=
        actRegistrationAdmission_undo equivariant admission
      have nextEq : actedAdmission.next = admission.next.map action.iterator :=
        actRegistrationAdmission_next equivariant admission
      rw [afterEq, undoEq, nextEq] at actedSource
      exact actedSource

def actIterationStep
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) :
    IterationStep dynamics (action.name owner) (action.iterator code)
      (actState action before) where
  after := actState action step.after
  undo := actUndoCode action step.undo
  next := step.next.map action.iterator
  source := actStepSource equivariant step.source
  recovers := by
    rw [applyUndo_equivariant equivariant]
    exact equivariant.equivalence_iff.mpr step.recovers
  preserves_wellFormed := by
    intro actedWf
    have sourceWf := (wellFormed_act_iff action before).1 actedWf
    exact wellFormed_act action (step.preserves_wellFormed sourceWf)

@[simp]
theorem actIterationStep_after
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) :
    (actIterationStep equivariant step).after = actState action step.after := rfl

@[simp]
theorem actIterationStep_undo
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) :
    (actIterationStep equivariant step).undo = actUndoCode action step.undo := rfl

@[simp]
theorem actIterationStep_next
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) :
    (actIterationStep equivariant step).next = step.next.map action.iterator := rfl

/-!
## Canonically conjugated registration oracle
-/

def actRegistrationOracle
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError) :
    RegistrationOracle dynamics (action.name owner) RegistrationError where
  certify actedBefore actedRequest :=
    let originalBefore := actState action.symm actedBefore
    let originalRequest := actRegistrationRequest action.symm actedRequest
    match oracle.certify originalBefore originalRequest with
    | .error error => .error error
    | .ok admission =>
        let actedAdmission := actRegistrationAdmission equivariant admission
        have beforeEq : actState action originalBefore = actedBefore := by
          dsimp [originalBefore]
          exact actState_apply_symm action actedBefore
        have requestEq : actRegistrationRequest action originalRequest = actedRequest := by
          dsimp [originalRequest]
          exact actRegistrationRequest_apply_symm action actedRequest
        let transported : RegistrationAdmission dynamics actedBefore (action.name owner)
            actedRequest := beforeEq ▸ requestEq ▸ actedAdmission
        .ok transported

private theorem conjugatedCertify_error
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    {before pulledBefore : State catalog Ambient}
    {request pulledRequest : RegistrationRequest sig}
    (beforeEq : pulledBefore = before) (requestEq : pulledRequest = request)
    (actedBeforeEq : actState action pulledBefore = actState action before)
    (actedRequestEq : actRegistrationRequest action pulledRequest =
      actRegistrationRequest action request)
    (error : RegistrationError)
    (rejected : oracle.certify before request = .error error) :
    (match oracle.certify pulledBefore pulledRequest with
      | Except.error found =>
          (Except.error found : Except RegistrationError
            (RegistrationAdmission dynamics (actState action before)
              (action.name owner) (actRegistrationRequest action request)))
      | Except.ok admission =>
          Except.ok (actedBeforeEq ▸ actedRequestEq ▸
            actRegistrationAdmission equivariant admission)) =
      Except.error error := by
  subst pulledBefore
  subst pulledRequest
  have beforeProof : actedBeforeEq = rfl := Subsingleton.elim _ _
  have requestProof : actedRequestEq = rfl := Subsingleton.elim _ _
  cases beforeProof
  cases requestProof
  simp [rejected]

private theorem conjugatedCertify_ok
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    {before pulledBefore : State catalog Ambient}
    {request pulledRequest : RegistrationRequest sig}
    (beforeEq : pulledBefore = before) (requestEq : pulledRequest = request)
    (actedBeforeEq : actState action pulledBefore = actState action before)
    (actedRequestEq : actRegistrationRequest action pulledRequest =
      actRegistrationRequest action request)
    (admission : RegistrationAdmission dynamics before owner request)
    (accepted : oracle.certify before request = .ok admission) :
    (match oracle.certify pulledBefore pulledRequest with
      | Except.error error =>
          (Except.error error : Except RegistrationError
            (RegistrationAdmission dynamics (actState action before)
              (action.name owner) (actRegistrationRequest action request)))
      | Except.ok found =>
          Except.ok (actedBeforeEq ▸ actedRequestEq ▸
            actRegistrationAdmission equivariant found)) =
      Except.ok (actRegistrationAdmission equivariant admission) := by
  subst pulledBefore
  subst pulledRequest
  have beforeProof : actedBeforeEq = rfl := Subsingleton.elim _ _
  have requestProof : actedRequestEq = rfl := Subsingleton.elim _ _
  cases beforeProof
  cases requestProof
  simp [accepted]

theorem actRegistrationOracle_certify_error
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (before : State catalog Ambient) (request : RegistrationRequest sig)
    (error : RegistrationError)
    (rejected : oracle.certify before request = .error error) :
    (actRegistrationOracle equivariant oracle).certify (actState action before)
        (actRegistrationRequest action request) = .error error := by
  exact conjugatedCertify_error equivariant oracle
    (actState_symm_apply action before)
    (actRegistrationRequest_symm_apply action request)
    (actState_apply_symm action (actState action before))
    (actRegistrationRequest_apply_symm action (actRegistrationRequest action request))
    error rejected

theorem actRegistrationOracle_certify_ok
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (before : State catalog Ambient) (request : RegistrationRequest sig)
    (admission : RegistrationAdmission dynamics before owner request)
    (accepted : oracle.certify before request = .ok admission) :
    (actRegistrationOracle equivariant oracle).certify (actState action before)
        (actRegistrationRequest action request) =
      .ok (actRegistrationAdmission equivariant admission) := by
  exact conjugatedCertify_ok equivariant oracle
    (actState_symm_apply action before)
    (actRegistrationRequest_symm_apply action request)
    (actState_apply_symm action (actState action before))
    (actRegistrationRequest_apply_symm action (actRegistrationRequest action request))
    admission accepted

/-!
## One-step execution
-/

def actRunError
    (action : NameAction sig Ambient) {RegistrationError : Type u} :
    RunError sig RegistrationError → RunError sig RegistrationError
  | .iterator error => .iterator (action.error error)
  | .registration error => .registration error

def actExecuteOneResult
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {RegistrationError : Type u} {owner : sig.Name} {code : sig.IteratorCode}
    {before : State catalog Ambient} :
    Except (RunError sig RegistrationError) (IterationStep dynamics owner code before) →
      Except (RunError sig RegistrationError)
        (IterationStep dynamics (action.name owner) (action.iterator code)
          (actState action before)) :=
  mapExcept (actRunError action) (actIterationStep equivariant)

private theorem executeOne_iterator_error
    {dynamics : Dynamics sig catalog Ambient} {RegistrationError : Type u}
    {owner : sig.Name} (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient) (error : sig.Error)
    (runEq : dynamics.runIterator owner code before = .error error) :
    executeOne dynamics oracle code before = .error (.iterator error) := by
  rw [executeOne.eq_def]
  split <;> simp_all

private def ordinaryIterationStep
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (runEq : dynamics.runIterator owner code before = .ok (.ordinary result)) :
    IterationStep dynamics owner code before where
  after := result.after
  undo := .external result.undo
  next := result.next
  source := .ordinary result runEq
  recovers := by
    change dynamics.equivalence.r
      (dynamics.applyExternalUndo result.undo result.after) before
    rw [dynamics.ordinary_recovers owner code before result runEq]
    exact dynamics.equivalence.refl before
  preserves_wellFormed :=
    dynamics.ordinary_preserves_wellFormed owner code before result runEq

private theorem executeOne_ordinary
    {dynamics : Dynamics sig catalog Ambient} {RegistrationError : Type u}
    {owner : sig.Name} (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (runEq : dynamics.runIterator owner code before = .ok (.ordinary result)) :
    executeOne dynamics oracle code before =
      .ok (ordinaryIterationStep dynamics owner code before result runEq) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    have resultEq : found = result :=
      IteratorResult.ordinary.inj (Except.ok.inj (foundEq.symm.trans runEq))
    subst found
    have proofEq : foundEq = runEq := Subsingleton.elim _ _
    cases proofEq
    rfl
  · rename_i found foundEq
    cases foundEq.symm.trans runEq

private def registrationIterationStep
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {before : State catalog Ambient} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request)
    (code : sig.IteratorCode)
    (runEq : dynamics.runIterator owner code before = .ok (.register request)) :
    IterationStep dynamics owner code before where
  after := admission.after
  undo := admission.undo
  next := admission.next
  source := .registration request admission runEq
  recovers := admission.registration_recovers
  preserves_wellFormed := admission.after_wellFormed

private theorem executeOne_registration_error
    {dynamics : Dynamics sig catalog Ambient} {RegistrationError : Type u}
    {owner : sig.Name} (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (request : RegistrationRequest sig)
    (runEq : dynamics.runIterator owner code before = .ok (.register request))
    (error : RegistrationError) (rejected : oracle.certify before request = .error error) :
    executeOne dynamics oracle code before = .error (.registration error) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    have requestEq : found = request :=
      IteratorResult.register.inj (Except.ok.inj (foundEq.symm.trans runEq))
    subst found
    have runProofEq : foundEq = runEq := Subsingleton.elim _ _
    cases runProofEq
    split
    · rename_i foundError foundErrorEq
      have errorEq : foundError = error :=
        Except.error.inj (foundErrorEq.symm.trans rejected)
      subst foundError
      rfl
    · rename_i admission admissionEq
      cases admissionEq.symm.trans rejected

private theorem executeOne_registration_ok
    {dynamics : Dynamics sig catalog Ambient} {RegistrationError : Type u}
    {owner : sig.Name} (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (request : RegistrationRequest sig)
    (runEq : dynamics.runIterator owner code before = .ok (.register request))
    (admission : RegistrationAdmission dynamics before owner request)
    (accepted : oracle.certify before request = .ok admission) :
    executeOne dynamics oracle code before =
      .ok (registrationIterationStep admission code runEq) := by
  rw [executeOne.eq_def]
  split
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    cases foundEq.symm.trans runEq
  · rename_i found foundEq
    have requestEq : found = request :=
      IteratorResult.register.inj (Except.ok.inj (foundEq.symm.trans runEq))
    subst found
    have runProofEq : foundEq = runEq := Subsingleton.elim _ _
    cases runProofEq
    split
    · rename_i foundError foundErrorEq
      cases foundErrorEq.symm.trans accepted
    · rename_i foundAdmission foundAdmissionEq
      have admissionEq : foundAdmission = admission :=
        Except.ok.inj (foundAdmissionEq.symm.trans accepted)
      subst foundAdmission
      have certificationProofEq : foundAdmissionEq = accepted := Subsingleton.elim _ _
      cases certificationProofEq
      rfl

private theorem ordinaryIterationStep_equivariant
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    (owner : sig.Name) (code : sig.IteratorCode) (before : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (runEq : dynamics.runIterator owner code before = .ok (.ordinary result))
    (actedRunEq : dynamics.runIterator (action.name owner) (action.iterator code)
      (actState action before) = .ok (.ordinary (actOrdinaryResult action result))) :
    ordinaryIterationStep dynamics (action.name owner) (action.iterator code)
        (actState action before) (actOrdinaryResult action result) actedRunEq =
      actIterationStep equivariant
        (ordinaryIterationStep dynamics owner code before result runEq) := by
  rfl

private theorem iterationStep_eq_of_fields
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (left right : IterationStep dynamics owner code before)
    (afterEq : left.after = right.after) (undoEq : left.undo = right.undo)
    (nextEq : left.next = right.next) (sourceEq : HEq left.source right.source) :
    left = right := by
  cases left with
  | mk leftAfter leftUndo leftNext leftSource leftRecovers leftWf =>
      cases right with
      | mk rightAfter rightUndo rightNext rightSource rightRecovers rightWf =>
          exact Eq.mp (IterationStep.mk.injEq leftAfter leftUndo leftNext leftSource
            leftRecovers leftWf rightAfter rightUndo rightNext rightSource rightRecovers
            rightWf).symm ⟨afterEq, undoEq, nextEq, sourceEq⟩

private theorem registrationIterationStep_equivariant
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {before : State catalog Ambient}
    {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request)
    (code : sig.IteratorCode)
    (runEq : dynamics.runIterator owner code before = .ok (.register request))
    (actedRunEq : dynamics.runIterator (action.name owner) (action.iterator code)
      (actState action before) =
        .ok (.register (actRegistrationRequest action request))) :
    registrationIterationStep (actRegistrationAdmission equivariant admission)
        (action.iterator code) actedRunEq =
      actIterationStep equivariant (registrationIterationStep admission code runEq) := by
  apply iterationStep_eq_of_fields
  · exact actRegistrationAdmission_after equivariant admission
  · exact actRegistrationAdmission_undo equivariant admission
  · exact actRegistrationAdmission_next equivariant admission
  · simp only [registrationIterationStep, actIterationStep, actStepSource]
    apply HEq.trans ?_ (cast_heq _ _).symm
    apply HEq.trans ?_ (cast_heq _ _).symm
    rfl

theorem executeOne_equivariant
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {RegistrationError : Type u} {owner : sig.Name}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient) :
    executeOne dynamics (actRegistrationOracle equivariant oracle)
        (action.iterator code) (actState action before) =
      actExecuteOneResult equivariant (executeOne dynamics oracle code before) := by
  have actedRun := equivariant.run_equivariant owner code before
  cases originalRun : dynamics.runIterator owner code before with
  | error error =>
      rw [originalRun] at actedRun
      have actedRunEq : dynamics.runIterator (action.name owner) (action.iterator code)
          (actState action before) = .error (action.error error) := by
        simpa [actRunOutput, mapExcept] using actedRun
      rw [executeOne_iterator_error (actRegistrationOracle equivariant oracle)
        (action.iterator code) (actState action before) (action.error error) actedRunEq]
      rw [executeOne_iterator_error oracle code before error originalRun]
      rfl
  | ok result =>
      cases result with
      | ordinary ordinary =>
          rw [originalRun] at actedRun
          have actedRunEq : dynamics.runIterator (action.name owner)
              (action.iterator code) (actState action before) =
                .ok (.ordinary (actOrdinaryResult action ordinary)) := by
            simpa [actRunOutput, actIteratorResult, mapExcept] using actedRun
          rw [executeOne_ordinary (actRegistrationOracle equivariant oracle)
            (action.iterator code) (actState action before)
            (actOrdinaryResult action ordinary) actedRunEq]
          rw [executeOne_ordinary oracle code before ordinary originalRun]
          rw [ordinaryIterationStep_equivariant equivariant owner code before ordinary
            originalRun actedRunEq]
          rfl
      | register request =>
          rw [originalRun] at actedRun
          have actedRunEq : dynamics.runIterator (action.name owner)
              (action.iterator code) (actState action before) =
                .ok (.register (actRegistrationRequest action request)) := by
            simpa [actRunOutput, actIteratorResult, mapExcept] using actedRun
          cases certification : oracle.certify before request with
          | error error =>
              have actedCertification := actRegistrationOracle_certify_error equivariant
                oracle before request error certification
              rw [executeOne_registration_error (actRegistrationOracle equivariant oracle)
                (action.iterator code) (actState action before)
                (actRegistrationRequest action request) actedRunEq error actedCertification]
              rw [executeOne_registration_error oracle code before request originalRun error
                certification]
              rfl
          | ok admission =>
              have actedCertification := actRegistrationOracle_certify_ok equivariant
                oracle before request admission certification
              rw [executeOne_registration_ok (actRegistrationOracle equivariant oracle)
                (action.iterator code) (actState action before)
                (actRegistrationRequest action request) actedRunEq
                (actRegistrationAdmission equivariant admission) actedCertification]
              rw [executeOne_registration_ok oracle code before request originalRun admission
                certification]
              rw [registrationIterationStep_equivariant equivariant admission code originalRun
                actedRunEq]
              rfl

/-!
## Landing and accumulated recovery
-/

def actLanding
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    Landing dynamics (action.name owner) (action.iterator code) (actState action before)
      (actFiber action beforeFiber) where
  RegistrationError := landing.RegistrationError
  oracle := actRegistrationOracle equivariant landing.oracle
  step := actIterationStep equivariant landing.step
  executed := by
    rw [executeOne_equivariant equivariant landing.oracle, landing.executed]
    rfl
  before_present := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action beforeFiber)
    exact (actRegistry_lookup_some_iff action before.registry owner beforeFiber).2
      landing.before_present
  afterFiber := actFiber action landing.afterFiber
  after_present := by
    change actRegistry action landing.step.after.registry (action.name owner) =
      some (actFiber action landing.afterFiber)
    exact (actRegistry_lookup_some_iff action landing.step.after.registry owner
      landing.afterFiber).2 landing.after_present
  component_eq := landing.component_eq
  phase_eq := by
    change landing.component_eq ▸ actPhase action landing.afterFiber.phase =
      actPhase action beforeFiber.phase
    rw [← actPhase_transport action landing.component_eq landing.afterFiber.phase]
    exact congrArg (actPhase action) landing.phase_eq

@[simp]
theorem actLanding_step_after
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    (actLanding equivariant landing).step.after = actState action landing.step.after := rfl

@[simp]
theorem actLanding_step_undo
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    (actLanding equivariant landing).step.undo =
      actUndoCode action landing.step.undo := rfl

@[simp]
theorem actLanding_step_next
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    (actLanding equivariant landing).step.next =
      landing.step.next.map action.iterator := rfl

@[simp]
theorem actLanding_afterFiber
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    (actLanding equivariant landing).afterFiber = actFiber action landing.afterFiber := rfl

@[simp]
theorem actLanding_component_eq
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {owner : sig.Name} {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber) :
    (actLanding equivariant landing).component_eq = landing.component_eq := rfl

private theorem actPhase_inactive_transport
    (action : NameAction sig Ambient) {left right : sig.ComponentId}
    (componentEq : left = right) (outcome : Option sig.Error) :
    actPhase action
        (show Phase (catalog.declaration left) from
          componentEq ▸ Phase.inactive outcome) =
      (show Phase (catalog.declaration left) from
        componentEq ▸ Phase.inactive (outcome.map action.error)) := by
  cases componentEq
  rfl

def actRecoveryAdmission
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {before : State catalog Ambient} {owner : sig.Name} {fiber : Fiber catalog}
    {undos : List (UndoCode sig)} {outcome : Option sig.Error}
    (admission : RecoveryAdmission dynamics before owner fiber undos outcome) :
    RecoveryAdmission dynamics (actState action before) (action.name owner)
      (actFiber action fiber) (undos.map (actUndoCode action))
      (outcome.map action.error) :=
  let actedComponentEq :
      (actFiber action admission.recoveredFiber).component =
        (actFiber action fiber).component := admission.component_eq
  {
  before_present := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2
      admission.before_present
  recoveredFiber := actFiber action admission.recoveredFiber
  recovered_present := by
    rw [recover_equivariant equivariant undos before]
    change actRegistry action (dynamics.recover undos before).registry (action.name owner) =
      some (actFiber action admission.recoveredFiber)
    exact (actRegistry_lookup_some_iff action (dynamics.recover undos before).registry owner
      admission.recoveredFiber).2 admission.recovered_present
  component_eq := actedComponentEq
  after := actState action admission.after
  after_eq := by
    let originalNext : Phase (catalog.declaration admission.recoveredFiber.component) :=
      admission.component_eq ▸ Phase.inactive outcome
    let actedNext :
        Phase (catalog.declaration (actFiber action admission.recoveredFiber).component) :=
      actedComponentEq ▸ Phase.inactive (outcome.map action.error)
    have originalAfter : admission.after =
        setPhase (dynamics.recover undos before) owner admission.recoveredFiber
          originalNext := admission.after_eq
    have phaseEq : actPhase action originalNext = actedNext := by
      dsimp [originalNext, actedNext, actedComponentEq]
      exact actPhase_inactive_transport action admission.component_eq outcome
    calc
      actState action admission.after =
          actState action (setPhase (dynamics.recover undos before) owner
            admission.recoveredFiber originalNext) :=
        congrArg (actState action) originalAfter
      _ = setPhase (actState action (dynamics.recover undos before))
          (action.name owner) (actFiber action admission.recoveredFiber)
          (actPhase action originalNext) :=
        actState_setPhase action (dynamics.recover undos before) owner
          admission.recoveredFiber originalNext
      _ = setPhase (dynamics.recover (undos.map (actUndoCode action))
          (actState action before)) (action.name owner)
          (actFiber action admission.recoveredFiber) actedNext := by
        rw [recover_equivariant equivariant undos before]
        exact congrArg
          (fun next : Phase (catalog.declaration
              (actFiber action admission.recoveredFiber).component) =>
            setPhase (actState action (dynamics.recover undos before))
              (action.name owner) (actFiber action admission.recoveredFiber) next)
          phaseEq
  preserves_wellFormed := by
    intro actedWf
    have originalWf := (wellFormed_act_iff action before).1 actedWf
    exact wellFormed_act action (admission.preserves_wellFormed originalWf)
  }

@[simp]
theorem actRecoveryAdmission_after
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics)
    {before : State catalog Ambient} {owner : sig.Name} {fiber : Fiber catalog}
    {undos : List (UndoCode sig)} {outcome : Option sig.Error}
    (admission : RecoveryAdmission dynamics before owner fiber undos outcome) :
    (actRecoveryAdmission equivariant admission).after =
      actState action admission.after := rfl

/-!
## Structural observations under a name action
-/

theorem activeProvider_forward
    (action : NameAction sig Ambient) {state : State catalog Ambient}
    {key : sig.Key} {name : sig.Name} :
    ActiveProvider state key name →
      ActiveProvider (actState action state) key (action.name name) := by
  rintro ⟨fiber, present, active, valuePresent⟩
  refine ⟨actFiber action fiber, ?_, ?_, ?_⟩
  · change actRegistry action state.registry (action.name name) = some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action state.registry name fiber).2 present
  · exact (actPhase_active_iff action fiber.phase).2 active
  · simpa [actTable] using valuePresent

theorem activeProvider_iff
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (key : sig.Key) (name : sig.Name) :
    ActiveProvider (actState action state) key (action.name name) ↔
      ActiveProvider state key name := by
  constructor
  · intro acted
    have original := activeProvider_forward (action := action.symm) acted
    simpa using original
  · exact activeProvider_forward action

theorem resolvesTo_forward
    (action : NameAction sig Ambient) {consumer : Fiber catalog} {provider : sig.Name} :
    ResolvesTo consumer provider →
      ResolvesTo (actFiber action consumer) (action.name provider) := by
  cases consumer with
  | mk component parent birth table tableWithin retired phase =>
      rintro ⟨committed, committedEq, declared, providerEq⟩
      refine ⟨actCommittedView action committed, ?_, declared, ?_⟩
      · change (actPhase action phase).committed? =
          some (actCommittedView action committed)
        rw [actPhase_committed, committedEq]
        rfl
      · change action.name (committed.provider declared) = action.name provider
        exact congrArg action.name providerEq

theorem resolvesTo_iff
    (action : NameAction sig Ambient) (consumer : Fiber catalog) (provider : sig.Name) :
    ResolvesTo (actFiber action consumer) (action.name provider) ↔
      ResolvesTo consumer provider := by
  constructor
  · intro acted
    have original := resolvesTo_forward (action := action.symm) acted
    simpa using original
  · exact resolvesTo_forward action

theorem relied_forward
    (action : NameAction sig Ambient) {state : State catalog Ambient}
    {provider : sig.Name} :
    Relied state provider → Relied (actState action state) (action.name provider) := by
  rintro ⟨consumerName, consumer, present, different, installed, resolves⟩
  refine ⟨action.name consumerName, actFiber action consumer, ?_, ?_, ?_, ?_⟩
  · change actRegistry action state.registry (action.name consumerName) =
      some (actFiber action consumer)
    exact (actRegistry_lookup_some_iff action state.registry consumerName consumer).2 present
  · intro equal
    exact different (action.name.injective equal)
  · exact (actPhase_installed_iff action consumer.phase).2 installed
  · exact resolvesTo_forward action resolves

theorem relied_iff
    (action : NameAction sig Ambient) (state : State catalog Ambient) (provider : sig.Name) :
    Relied (actState action state) (action.name provider) ↔ Relied state provider := by
  constructor
  · intro acted
    have original := relied_forward (action := action.symm) acted
    simpa using original
  · exact relied_forward action

theorem isTargetView_forward
    (action : NameAction sig Ambient) {state : State catalog Ambient}
    {name : sig.Name} {fiber : Fiber catalog}
    {view : CommittedView (catalog.declaration fiber.component)} :
    IsTargetView state name fiber view →
      IsTargetView (actState action state) (action.name name) (actFiber action fiber)
        (actCommittedView action view) := by
  intro target
  refine {
    present := by
      change actRegistry action state.registry (action.name name) =
        some (actFiber action fiber)
      exact (actRegistry_lookup_some_iff action state.registry name fiber).2 target.present
    not_retired := target.not_retired
    resolves_active := ?_
  }
  intro declared
  exact activeProvider_forward action (target.resolves_active declared)

theorem isTargetView_iff
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (name : sig.Name) (fiber : Fiber catalog)
    (view : CommittedView (catalog.declaration fiber.component)) :
    IsTargetView (actState action state) (action.name name) (actFiber action fiber)
        (actCommittedView action view) ↔
      IsTargetView state name fiber view := by
  constructor
  · intro acted
    refine {
      present := (actRegistry_lookup_some_iff action state.registry name fiber).1
        acted.present
      not_retired := acted.not_retired
      resolves_active := ?_
    }
    intro declared
    have provider := acted.resolves_active declared
    change ActiveProvider (actState action state) declared.key
      (action.name (view.provider declared)) at provider
    exact (activeProvider_iff action state declared.key (view.provider declared)).1 provider
  · exact isTargetView_forward action

theorem targetView_some_iff
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (wf : WellFormed state) (name : sig.Name) (fiber : Fiber catalog)
    (view : CommittedView (catalog.declaration fiber.component)) :
    targetView (actState action state) (action.name name) (actFiber action fiber) =
        some (actCommittedView action view) ↔
      targetView state name fiber = some view := by
  have actedWf := wellFormed_act action wf
  constructor
  · intro actedTarget
    have target := targetView_sound actedWf actedTarget
    exact targetView_eq_of_isTarget wf ((isTargetView_iff action state name fiber view).1
      target)
  · intro originalTarget
    have target := targetView_sound wf originalTarget
    exact targetView_eq_of_isTarget actedWf (isTargetView_forward action target)

theorem targetView_equivariant
    (action : NameAction sig Ambient) (state : State catalog Ambient)
    (wf : WellFormed state) (name : sig.Name) (fiber : Fiber catalog) :
    targetView (actState action state) (action.name name) (actFiber action fiber) =
      (targetView state name fiber).map (actCommittedView action) := by
  cases originalEq : targetView state name fiber with
  | none =>
      cases actedEq : targetView (actState action state) (action.name name)
        (actFiber action fiber) with
      | none => rfl
      | some actedView =>
          change CommittedView (catalog.declaration fiber.component) at actedView
          let originalView := actCommittedView action.symm actedView
          have actedViewEq : actCommittedView action originalView = actedView := by
            exact actCommittedView_apply_symm action actedView
          have normalized : targetView (actState action state) (action.name name)
              (actFiber action fiber) = some (actCommittedView action originalView) := by
            rw [actedViewEq]
            exact actedEq
          have impossible :=
            (targetView_some_iff action state wf name fiber originalView).1 normalized
          rw [originalEq] at impossible
          cases impossible
  | some view =>
      rw [(targetView_some_iff action state wf name fiber view).2 originalEq]
      rfl

/-!
## Lifecycle transitions
-/

structure ForwardLifecycleAction
    (action : NameAction sig Ambient)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) where
  acted : Transition dynamics inertia (actState action before) (actState action after)
  same_rule : acted.rule = transition.rule
  acted_owner : lifecycleOwner acted = action.name (lifecycleOwner transition)

@[simp]
theorem lifecycleRule_cast_after
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after next : State catalog Ambient} (equal : after = next)
    (transition : Transition dynamics inertia before after) :
    (equal ▸ transition).rule = transition.rule := by
  cases equal
  rfl

@[simp]
theorem lifecycleOwner_cast_after
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after next : State catalog Ambient} (equal : after = next)
    (transition : Transition dynamics inertia before after) :
    lifecycleOwner (equal ▸ transition) = lifecycleOwner transition := by
  cases equal
  rfl

@[simp]
theorem lifecycleRule_cast_before
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before next after : State catalog Ambient} (equal : before = next)
    (transition : Transition dynamics inertia before after) :
    (equal ▸ transition).rule = transition.rule := by
  cases equal
  rfl

@[simp]
theorem lifecycleOwner_cast_before
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before next after : State catalog Ambient} (equal : before = next)
    (transition : Transition dynamics inertia before after) :
    lifecycleOwner (equal ▸ transition) = lifecycleOwner transition := by
  cases equal
  rfl

private def forwardLifecycleActionOf
    (action : NameAction sig Ambient)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after actedAfter : State catalog Ambient}
    (transition : Transition dynamics inertia before after)
    (raw : Transition dynamics inertia (actState action before) actedAfter)
    (endpointEq : actedAfter = actState action after)
    (ruleEq : raw.rule = transition.rule)
    (ownerEq : lifecycleOwner raw = action.name (lifecycleOwner transition)) :
    ForwardLifecycleAction action transition where
  acted := endpointEq ▸ raw
  same_rule := (lifecycleRule_cast_after endpointEq raw).trans ruleEq
  acted_owner := (lifecycleOwner_cast_after endpointEq raw).trans ownerEq

private def actTransition_begin
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (entry : fiber.phase = .inactive none)
    (committed : CommittedView (catalog.declaration fiber.component))
    (target : targetView before owner fiber = some committed) :
    ForwardLifecycleAction action
      (Transition.begin (dynamics := dynamics) (inertia := inertia)
        before owner fiber present entry committed target) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedEntry : (actFiber action fiber).phase = .inactive none := by
    change actPhase action fiber.phase = .inactive none
    rw [entry]
    rfl
  have actedTarget :
      targetView (actState action before) (action.name owner) (actFiber action fiber) =
        some (actCommittedView action committed) :=
    (targetView_some_iff action before beforeWf owner fiber committed).2 target
  let raw : Transition dynamics inertia (actState action before)
      (setPhase (actState action before) (action.name owner) (actFiber action fiber)
        (.reloading (catalog.declaration fiber.component).entry []
          (actCommittedView action committed))) :=
    Transition.begin (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent actedEntry (actCommittedView action committed) actedTarget
  have endpointEq :
      setPhase (actState action before) (action.name owner) (actFiber action fiber)
          (.reloading (catalog.declaration fiber.component).entry []
            (actCommittedView action committed)) =
        actState action (setPhase before owner fiber (.reloading
          (catalog.declaration fiber.component).entry [] committed)) := by
    rw [actState_setPhase]
    simp [actPhase, assumptions.entry fiber.component]
  let exactActed := endpointEq ▸ raw
  exact {
    acted := exactActed
    same_rule := (lifecycleRule_cast_after endpointEq raw).trans rfl
    acted_owner := (lifecycleOwner_cast_after endpointEq raw).trans rfl
  }

private def actTransition_iter
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (phase : fiber.phase = .reloading code undos committed)
    (target : targetView before owner fiber = some committed)
    (landing : Landing dynamics owner code before fiber)
    (next : sig.IteratorCode) (continues : landing.step.next = some next) :
    ForwardLifecycleAction action
      (Transition.iter (dynamics := dynamics) (inertia := inertia)
        before owner fiber present code undos committed phase target landing next
        continues) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .reloading (action.iterator code) (undos.map (actUndoCode action))
        (actCommittedView action committed) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedTarget :
      targetView (actState action before) (action.name owner) (actFiber action fiber) =
        some (actCommittedView action committed) :=
    (targetView_some_iff action before beforeWf owner fiber committed).2 target
  let actedLanding := actLanding assumptions.dynamics_equivariant landing
  have actedContinues : actedLanding.step.next = some (action.iterator next) := by
    change landing.step.next.map action.iterator = some (action.iterator next)
    rw [continues]
    rfl
  let raw := Transition.iter (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (action.iterator code) (undos.map (actUndoCode action))
      (actCommittedView action committed) actedPhase actedTarget actedLanding
      (action.iterator next) actedContinues
  have endpointEq :
      setPhase actedLanding.step.after (action.name owner) actedLanding.afterFiber
          (.reloading (action.iterator next)
            (actedLanding.step.undo :: undos.map (actUndoCode action))
            (actedLanding.component_eq.symm ▸ actCommittedView action committed)) =
        actState action
          (setPhase landing.step.after owner landing.afterFiber
            (.reloading next (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed))) := by
    rw [actState_setPhase]
    simp [actedLanding, actPhase, actCommittedView_transport]
  exact forwardLifecycleActionOf action
    (Transition.iter before owner fiber present code undos committed phase target landing
      next continues) raw endpointEq rfl rfl

private def actTransition_finish
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (phase : fiber.phase = .reloading code undos committed)
    (target : targetView before owner fiber = some committed)
    (landing : Landing dynamics owner code before fiber)
    (done : landing.step.next = none) :
    ForwardLifecycleAction action
      (Transition.finish (dynamics := dynamics) (inertia := inertia)
        before owner fiber present code undos committed phase target landing done) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .reloading (action.iterator code) (undos.map (actUndoCode action))
        (actCommittedView action committed) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedTarget :
      targetView (actState action before) (action.name owner) (actFiber action fiber) =
        some (actCommittedView action committed) :=
    (targetView_some_iff action before beforeWf owner fiber committed).2 target
  let actedLanding := actLanding assumptions.dynamics_equivariant landing
  have actedDone : actedLanding.step.next = none := by
    change landing.step.next.map action.iterator = none
    rw [done]
    rfl
  let raw := Transition.finish (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (action.iterator code) (undos.map (actUndoCode action))
      (actCommittedView action committed) actedPhase actedTarget actedLanding actedDone
  have endpointEq :
      setPhase actedLanding.step.after (action.name owner) actedLanding.afterFiber
          (.active (actedLanding.step.undo :: undos.map (actUndoCode action))
            (actedLanding.component_eq.symm ▸ actCommittedView action committed)) =
        actState action
          (setPhase landing.step.after owner landing.afterFiber
            (.active (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed))) := by
    rw [actState_setPhase]
    simp [actedLanding, actPhase, actCommittedView_transport]
  exact forwardLifecycleActionOf action
    (Transition.finish before owner fiber present code undos committed phase target landing
      done) raw endpointEq rfl rfl

private def actTransition_divertAbort
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (phase : fiber.phase = .reloading code undos committed)
    (targetChanged : targetView before owner fiber ≠ some committed)
    (abortable : inertia.canAbort owner code before) :
    ForwardLifecycleAction action
      (Transition.divertAbort (dynamics := dynamics) (inertia := inertia)
        before owner fiber present code undos committed phase targetChanged abortable) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .reloading (action.iterator code) (undos.map (actUndoCode action))
        (actCommittedView action committed) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedTargetChanged :
      targetView (actState action before) (action.name owner) (actFiber action fiber) ≠
        some (actCommittedView action committed) := by
    intro actedTarget
    exact targetChanged
      ((targetView_some_iff action before beforeWf owner fiber committed).1 actedTarget)
  have actedAbortable :
      inertia.canAbort (action.name owner) (action.iterator code)
        (actState action before) :=
    (assumptions.inertia.canAbort_iff owner code before).2 abortable
  let raw := Transition.divertAbort (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (action.iterator code) (undos.map (actUndoCode action))
      (actCommittedView action committed) actedPhase actedTargetChanged actedAbortable
  have endpointEq :
      setPhase (actState action before) (action.name owner) (actFiber action fiber)
          (.unloading (undos.map (actUndoCode action))
            (actCommittedView action committed) none) =
        actState action (setPhase before owner fiber (.unloading undos committed none)) := by
    rw [actState_setPhase]
    rfl
  exact forwardLifecycleActionOf action
    (Transition.divertAbort before owner fiber present code undos committed phase
      targetChanged abortable) raw endpointEq rfl rfl

private def actTransition_divertLand
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (phase : fiber.phase = .reloading code undos committed)
    (targetChanged : targetView before owner fiber ≠ some committed)
    (landing : Landing dynamics owner code before fiber) :
    ForwardLifecycleAction action
      (Transition.divertLand (dynamics := dynamics) (inertia := inertia)
        before owner fiber present code undos committed phase targetChanged landing) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .reloading (action.iterator code) (undos.map (actUndoCode action))
        (actCommittedView action committed) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedTargetChanged :
      targetView (actState action before) (action.name owner) (actFiber action fiber) ≠
        some (actCommittedView action committed) := by
    intro actedTarget
    exact targetChanged
      ((targetView_some_iff action before beforeWf owner fiber committed).1 actedTarget)
  let actedLanding := actLanding assumptions.dynamics_equivariant landing
  let raw := Transition.divertLand (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (action.iterator code) (undos.map (actUndoCode action))
      (actCommittedView action committed) actedPhase actedTargetChanged actedLanding
  have endpointEq :
      setPhase actedLanding.step.after (action.name owner) actedLanding.afterFiber
          (.unloading (actedLanding.step.undo :: undos.map (actUndoCode action))
            (actedLanding.component_eq.symm ▸ actCommittedView action committed) none) =
        actState action
          (setPhase landing.step.after owner landing.afterFiber
            (.unloading (landing.step.undo :: undos)
              (landing.component_eq.symm ▸ committed) none)) := by
    rw [actState_setPhase]
    simp [actedLanding, actPhase, actCommittedView_transport]
  exact forwardLifecycleActionOf action
    (Transition.divertLand before owner fiber present code undos committed phase
      targetChanged landing) raw endpointEq rfl rfl

private def actTransition_raise
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (_beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (code : sig.IteratorCode) (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (phase : fiber.phase = .reloading code undos committed)
    (error : sig.Error)
    (raised : dynamics.runIterator owner code before = .error error) :
    ForwardLifecycleAction action
      (Transition.raise (dynamics := dynamics) (inertia := inertia)
        before owner fiber present code undos committed phase error raised) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .reloading (action.iterator code) (undos.map (actUndoCode action))
        (actCommittedView action committed) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedRaised : dynamics.runIterator (action.name owner) (action.iterator code)
      (actState action before) = .error (action.error error) := by
    rw [assumptions.dynamics_equivariant.run_equivariant owner code before, raised]
    rfl
  let raw := Transition.raise (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (action.iterator code) (undos.map (actUndoCode action))
      (actCommittedView action committed) actedPhase (action.error error) actedRaised
  have endpointEq :
      setPhase (actState action before) (action.name owner) (actFiber action fiber)
          (.unloading (undos.map (actUndoCode action)) (actCommittedView action committed)
            (some (action.error error))) =
        actState action
          (setPhase before owner fiber (.unloading undos committed (some error))) := by
    rw [actState_setPhase]
    rfl
  exact forwardLifecycleActionOf action
    (Transition.raise before owner fiber present code undos committed phase error raised)
    raw endpointEq rfl rfl

private def actTransition_leave
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (_assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (phase : fiber.phase = .active undos committed)
    (targetChanged : targetView before owner fiber ≠ some committed) :
    ForwardLifecycleAction action
      (Transition.leave (dynamics := dynamics) (inertia := inertia)
        before owner fiber present undos committed phase targetChanged) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .active (undos.map (actUndoCode action)) (actCommittedView action committed) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedTargetChanged :
      targetView (actState action before) (action.name owner) (actFiber action fiber) ≠
        some (actCommittedView action committed) := by
    intro actedTarget
    exact targetChanged
      ((targetView_some_iff action before beforeWf owner fiber committed).1 actedTarget)
  let raw := Transition.leave (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (undos.map (actUndoCode action)) (actCommittedView action committed)
      actedPhase actedTargetChanged
  have endpointEq :
      setPhase (actState action before) (action.name owner) (actFiber action fiber)
          (.unloading (undos.map (actUndoCode action))
            (actCommittedView action committed) none) =
        actState action (setPhase before owner fiber (.unloading undos committed none)) := by
    rw [actState_setPhase]
    rfl
  exact forwardLifecycleActionOf action
    (Transition.leave before owner fiber present undos committed phase targetChanged)
    raw endpointEq rfl rfl

private def actTransition_unload
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    (before : State catalog Ambient) (_beforeWf : WellFormed before)
    (owner : sig.Name) (fiber : Fiber catalog)
    (present : before.registry owner = some fiber)
    (undos : List (UndoCode sig))
    (committed : CommittedView (catalog.declaration fiber.component))
    (outcome : Option sig.Error)
    (phase : fiber.phase = .unloading undos committed outcome)
    (notRelied : ¬Relied before owner)
    (admission : RecoveryAdmission dynamics before owner fiber undos outcome) :
    ForwardLifecycleAction action
      (Transition.unload (dynamics := dynamics) (inertia := inertia)
        before owner fiber present undos committed outcome phase notRelied admission) := by
  have actedPresent : (actState action before).registry (action.name owner) =
      some (actFiber action fiber) := by
    change actRegistry action before.registry (action.name owner) =
      some (actFiber action fiber)
    exact (actRegistry_lookup_some_iff action before.registry owner fiber).2 present
  have actedPhase : (actFiber action fiber).phase =
      .unloading (undos.map (actUndoCode action)) (actCommittedView action committed)
        (outcome.map action.error) := by
    change actPhase action fiber.phase = _
    rw [phase]
    rfl
  have actedNotRelied : ¬Relied (actState action before) (action.name owner) := by
    intro relied
    exact notRelied ((relied_iff action before owner).1 relied)
  let actedAdmission := actRecoveryAdmission assumptions.dynamics_equivariant admission
  let raw := Transition.unload (dynamics := dynamics) (inertia := inertia)
      (actState action before) (action.name owner) (actFiber action fiber)
      actedPresent (undos.map (actUndoCode action)) (actCommittedView action committed)
      (outcome.map action.error) actedPhase actedNotRelied actedAdmission
  have endpointEq : actedAdmission.after = actState action admission.after := rfl
  exact forwardLifecycleActionOf action
    (Transition.unload before owner fiber present undos committed outcome phase notRelied
      admission) raw endpointEq rfl rfl

def actLifecycleAction
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (transition : Transition dynamics inertia before after) :
    ForwardLifecycleAction action transition := by
  cases transition with
  | begin owner fiber present entry committed target =>
      exact actTransition_begin assumptions before beforeWf owner fiber present entry
        committed target
  | iter owner fiber present code undos committed phase target landing next
      continues =>
      exact actTransition_iter assumptions before beforeWf owner fiber present code undos
        committed phase target landing next continues
  | finish owner fiber present code undos committed phase target landing done =>
      exact actTransition_finish assumptions before beforeWf owner fiber present code undos
        committed phase target landing done
  | divertAbort owner fiber present code undos committed phase targetChanged
      abortable =>
      exact actTransition_divertAbort assumptions before beforeWf owner fiber present code
        undos committed phase targetChanged abortable
  | divertLand owner fiber present code undos committed phase targetChanged landing =>
      exact actTransition_divertLand assumptions before beforeWf owner fiber present code
        undos committed phase targetChanged landing
  | raise owner fiber present code undos committed phase error raised =>
      exact actTransition_raise assumptions before beforeWf owner fiber present code undos
        committed phase error raised
  | leave owner fiber present undos committed phase targetChanged =>
      exact actTransition_leave assumptions before beforeWf owner fiber present undos
        committed phase targetChanged
  | unload owner fiber present undos committed outcome phase notRelied admission =>
      exact actTransition_unload assumptions before beforeWf owner fiber present undos
        committed outcome phase notRelied admission

def actLifecycleTransition
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (transition : Transition dynamics inertia before after) :
    Transition dynamics inertia (actState action before) (actState action after) :=
  (actLifecycleAction assumptions beforeWf transition).acted

theorem actLifecycleTransition_rule
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (transition : Transition dynamics inertia before after) :
    (actLifecycleTransition assumptions beforeWf transition).rule = transition.rule := by
  exact (actLifecycleAction assumptions beforeWf transition).same_rule

theorem actLifecycleTransition_owner
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (transition : Transition dynamics inertia before after) :
    lifecycleOwner (actLifecycleTransition assumptions beforeWf transition) =
      action.name (lifecycleOwner transition) := by
  exact (actLifecycleAction assumptions beforeWf transition).acted_owner

/-!
## Inverse laws and bidirectional lifecycle equivariance
-/

theorem DynamicsNameEquivariant.symm
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    (equivariant : DynamicsNameEquivariant action dynamics) :
    DynamicsNameEquivariant action.symm dynamics where
  run_equivariant owner code state := by
    have forward := equivariant.run_equivariant (action.name.symm owner)
      (action.iterator.symm code) (actState action.symm state)
    have mapped := congrArg (actRunOutput action.symm) forward
    simp only [Equiv.apply_symm_apply, actState_apply_symm,
      actRunOutput_symm_apply] at mapped
    exact mapped.symm
  externalUndo_equivariant code state := by
    have forward := equivariant.externalUndo_equivariant
      (action.externalUndo.symm code) (actState action.symm state)
    have mapped := congrArg (actState action.symm) forward
    simp only [Equiv.apply_symm_apply, actState_apply_symm, actState_symm_apply] at mapped
    exact mapped.symm
  equivalence_iff {left right} := by
    have forward := equivariant.equivalence_iff
      (left := actState action.symm left) (right := actState action.symm right)
    simpa using forward.symm

theorem InertiaNameEquivariant.symm
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (equivariant : InertiaNameEquivariant action dynamics inertia) :
    InertiaNameEquivariant action.symm dynamics inertia where
  canAbort_iff owner code state := by
    have forward := equivariant.canAbort_iff (action.name.symm owner)
      (action.iterator.symm code) (actState action.symm state)
    simp only [Equiv.apply_symm_apply, actState_apply_symm] at forward
    exact forward.symm

theorem catalogEntryInvariant_symm
    (action : NameAction sig Ambient) (catalog : Catalog sig)
    (invariant : action.CatalogEntryInvariant catalog) :
    action.symm.CatalogEntryInvariant catalog := by
  intro component
  have mapped := congrArg action.iterator.symm (invariant component)
  exact mapped.symm.trans (action.iterator.left_inv _)

theorem NameLifecycleAssumptions.symm
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia) :
    NameLifecycleAssumptions action.symm dynamics inertia where
  entry := catalogEntryInvariant_symm action catalog assumptions.entry
  dynamics_equivariant := assumptions.dynamics_equivariant.symm
  inertia := assumptions.inertia.symm

structure BackwardLifecycleAction
    (action : NameAction sig Ambient)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before actedAfter : State catalog Ambient}
    (transition : Transition dynamics inertia (actState action before) actedAfter) where
  originalAfter : State catalog Ambient
  original : Transition dynamics inertia before originalAfter
  endpoint_eq : actState action originalAfter = actedAfter
  same_rule : original.rule = transition.rule
  acted_owner : action.name (lifecycleOwner original) = lifecycleOwner transition

def unactLifecycleTransition
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before actedAfter : State catalog Ambient} (beforeWf : WellFormed before)
    (transition : Transition dynamics inertia (actState action before) actedAfter) :
    BackwardLifecycleAction action transition := by
  have actedWf := wellFormed_act action beforeWf
  let forward := actLifecycleAction assumptions.symm actedWf transition
  have sourceEq : actState action.symm (actState action before) = before :=
    actState_symm_apply action before
  let original : Transition dynamics inertia before (actState action.symm actedAfter) :=
    sourceEq ▸ forward.acted
  have sameRule : original.rule = transition.rule := by
    exact (lifecycleRule_cast_before sourceEq forward.acted).trans forward.same_rule
  have actedOwner : action.name (lifecycleOwner original) =
      lifecycleOwner transition := by
    have ownerEq := (lifecycleOwner_cast_before sourceEq forward.acted).trans
      forward.acted_owner
    have mapped := congrArg action.name ownerEq
    simpa [original] using mapped
  exact {
    originalAfter := actState action.symm actedAfter
    original := original
    endpoint_eq := actState_apply_symm action actedAfter
    same_rule := sameRule
    acted_owner := actedOwner
  }

structure LifecycleNameEquivariance
    (action : NameAction sig Ambient)
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) where
  forward : ∀ {before after : State catalog Ambient}, WellFormed before →
    (transition : Transition dynamics inertia before after) →
      ForwardLifecycleAction action transition
  backward : ∀ {before actedAfter : State catalog Ambient}, WellFormed before →
    (transition : Transition dynamics inertia (actState action before) actedAfter) →
      BackwardLifecycleAction action transition

def lifecycleNameEquivariance
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia) :
    LifecycleNameEquivariance action dynamics inertia where
  forward beforeWf transition := actLifecycleAction assumptions beforeWf transition
  backward beforeWf transition := unactLifecycleTransition assumptions beforeWf transition

/-!
## Unified orchestration/lifecycle steps
-/

def globalRuleOfOrchestrationKind : OrchestrationKind → GlobalCalculus.Rule
  | .insert => .oInsert
  | .retire => .oRetire
  | .remove => .oRemove

def globalRuleOfLifecycleRule : GlobalLifecycle.Rule → GlobalCalculus.Rule
  | .begin => .lBegin
  | .iter => .lIter
  | .finish => .lFinish
  | .divertAbort => .lDivert
  | .divertLand => .lDivert
  | .raise => .lRaise
  | .leave => .lLeave
  | .unload => .lUnload

@[simp]
theorem orchestrationStep_global_rule
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    (GlobalCalculus.Step.orchestration step :
      GlobalCalculus.Step dynamics inertia before after).rule =
        globalRuleOfOrchestrationKind (orchestrationKind step) := by
  cases step <;> rfl

@[simp]
theorem lifecycleStep_global_rule
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    (GlobalCalculus.Step.lifecycle transition :
      GlobalCalculus.Step dynamics inertia before after).rule =
        globalRuleOfLifecycleRule transition.rule := by
  cases transition <;> rfl

@[simp]
theorem orchestrationStep_actedName
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} (step : OrchestrationStep before after) :
    (GlobalCalculus.Step.orchestration step :
      GlobalCalculus.Step dynamics inertia before after).actedName =
        orchestrationName step := by
  cases step <;> rfl

@[simp]
theorem lifecycleStep_actedName
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    (GlobalCalculus.Step.lifecycle transition :
      GlobalCalculus.Step dynamics inertia before after).actedName =
        lifecycleOwner transition := by
  cases transition <;> rfl

structure ForwardUnifiedAction
    (action : NameAction sig Ambient)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (step : GlobalCalculus.Step dynamics inertia before after) where
  acted : GlobalCalculus.Step dynamics inertia (actState action before)
    (actState action after)
  same_rule : acted.rule = step.rule
  acted_name : acted.actedName = action.name step.actedName

def actUnifiedStep
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before after : State catalog Ambient} (beforeWf : WellFormed before)
    (step : GlobalCalculus.Step dynamics inertia before after) :
    ForwardUnifiedAction action step := by
  cases step with
  | orchestration orchestration =>
      let acted := actOrchestrationAction action orchestration
      exact {
        acted := .orchestration acted.acted
        same_rule := by
          rw [orchestrationStep_global_rule, orchestrationStep_global_rule,
            acted.same_kind]
        acted_name := by
          rw [orchestrationStep_actedName, orchestrationStep_actedName,
            acted.acted_name]
      }
  | lifecycle transition =>
      let acted := actLifecycleAction assumptions beforeWf transition
      exact {
        acted := .lifecycle acted.acted
        same_rule := by
          rw [lifecycleStep_global_rule, lifecycleStep_global_rule, acted.same_rule]
        acted_name := by
          rw [lifecycleStep_actedName, lifecycleStep_actedName, acted.acted_owner]
      }

structure BackwardUnifiedAction
    (action : NameAction sig Ambient)
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before actedAfter : State catalog Ambient}
    (step : GlobalCalculus.Step dynamics inertia (actState action before) actedAfter) where
  originalAfter : State catalog Ambient
  original : GlobalCalculus.Step dynamics inertia before originalAfter
  endpoint_eq : actState action originalAfter = actedAfter
  same_rule : original.rule = step.rule
  acted_name : action.name original.actedName = step.actedName

def unactUnifiedStep
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia)
    {before actedAfter : State catalog Ambient} (beforeWf : WellFormed before)
    (step : GlobalCalculus.Step dynamics inertia (actState action before) actedAfter) :
    BackwardUnifiedAction action step := by
  cases step with
  | orchestration orchestration =>
      let original := unactOrchestrationStep action orchestration
      exact {
        originalAfter := original.originalAfter
        original := .orchestration original.original
        endpoint_eq := original.endpoint_eq
        same_rule := by
          rw [orchestrationStep_global_rule, orchestrationStep_global_rule,
            original.same_kind]
        acted_name := by
          rw [orchestrationStep_actedName, orchestrationStep_actedName,
            original.acted_name]
      }
  | lifecycle transition =>
      let original := unactLifecycleTransition assumptions beforeWf transition
      exact {
        originalAfter := original.originalAfter
        original := .lifecycle original.original
        endpoint_eq := original.endpoint_eq
        same_rule := by
          rw [lifecycleStep_global_rule, lifecycleStep_global_rule, original.same_rule]
        acted_name := by
          rw [lifecycleStep_actedName, lifecycleStep_actedName, original.acted_owner]
      }

structure UnifiedNameEquivariance
    (action : NameAction sig Ambient)
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) where
  forward : ∀ {before after : State catalog Ambient}, WellFormed before →
    (step : GlobalCalculus.Step dynamics inertia before after) →
      ForwardUnifiedAction action step
  backward : ∀ {before actedAfter : State catalog Ambient}, WellFormed before →
    (step : GlobalCalculus.Step dynamics inertia (actState action before) actedAfter) →
      BackwardUnifiedAction action step

def unifiedNameEquivariance
    {action : NameAction sig Ambient} {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    (assumptions : NameLifecycleAssumptions action dynamics inertia) :
    UnifiedNameEquivariance action dynamics inertia where
  forward beforeWf step := actUnifiedStep assumptions beforeWf step
  backward beforeWf step := unactUnifiedStep assumptions beforeWf step

/-!
## Reflexive compatibility and an existing lifecycle path
-/

theorem DynamicsNameEquivariant.refl
    (dynamics : Dynamics sig catalog Ambient) :
    DynamicsNameEquivariant (NameAction.refl sig Ambient) dynamics where
  run_equivariant owner code state := by
    simp [actRunOutput_refl]
  externalUndo_equivariant code state := by
    simp
  equivalence_iff := by simp

theorem InertiaNameEquivariant.refl
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) :
    InertiaNameEquivariant (NameAction.refl sig Ambient) dynamics inertia where
  canAbort_iff owner code state := by simp

theorem NameLifecycleAssumptions.refl
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) :
    NameLifecycleAssumptions (NameAction.refl sig Ambient) dynamics inertia where
  entry component := by simp
  dynamics_equivariant := DynamicsNameEquivariant.refl dynamics
  inertia := InertiaNameEquivariant.refl dynamics inertia

namespace ReflexiveExample

open Cordis.GlobalLifecycle.Example

abbrev action : NameAction ExampleSig Nat := NameAction.refl ExampleSig Nat

theorem assumptions : NameLifecycleAssumptions action dynamics inertia :=
  NameLifecycleAssumptions.refl dynamics inertia

def actedBegin : ForwardLifecycleAction action beginTransition :=
  actLifecycleAction assumptions start_wellFormed beginTransition

def actedIter : ForwardLifecycleAction action iterTransition :=
  actLifecycleAction assumptions beginState_wellFormed iterTransition

def actedFinish : ForwardLifecycleAction action finishTransition :=
  actLifecycleAction assumptions iterState_wellFormed finishTransition

def actedLeave : ForwardLifecycleAction action leaveTransition :=
  actLifecycleAction assumptions retiredState_wellFormed leaveTransition

def actedUnload : ForwardLifecycleAction action unloadTransition :=
  actLifecycleAction assumptions leaveState_wellFormed unloadTransition

theorem existing_path_rules :
    actedBegin.acted.rule = .begin ∧ actedIter.acted.rule = .iter ∧
      actedFinish.acted.rule = .finish := by
  exact ⟨actedBegin.same_rule, actedIter.same_rule, actedFinish.same_rule⟩

theorem existing_path_owners :
    lifecycleOwner actedBegin.acted = 0 ∧ lifecycleOwner actedIter.acted = 0 ∧
      lifecycleOwner actedFinish.acted = 0 := by
  exact ⟨actedBegin.acted_owner, actedIter.acted_owner, actedFinish.acted_owner⟩

theorem unloading_path_rules :
    actedLeave.acted.rule = .leave ∧ actedUnload.acted.rule = .unload := by
  exact ⟨actedLeave.same_rule, actedUnload.same_rule⟩

def backwardBegin : BackwardLifecycleAction action actedBegin.acted :=
  unactLifecycleTransition assumptions start_wellFormed actedBegin.acted

theorem backward_begin_rule : backwardBegin.original.rule = .begin :=
  backwardBegin.same_rule.trans actedBegin.same_rule

def unifiedBegin : ForwardUnifiedAction action
    (GlobalCalculus.Step.lifecycle beginTransition) :=
  actUnifiedStep assumptions start_wellFormed (.lifecycle beginTransition)

theorem unified_begin_rule : unifiedBegin.acted.rule = .lBegin := unifiedBegin.same_rule

end ReflexiveExample

/-!
## Nonidentity raise and necessity witnesses
-/

namespace NonidentityRaiseExample

open Cordis.GlobalNameAction.Example

def reloadingPhase : Phase providerDecl :=
  .reloading false [] emptyProviderView

def raiseState : ExampleState :=
  setPhase state false providerFiber reloadingPhase

def raiseFiber : Fiber exampleCatalog := {
  providerFiber with phase := reloadingPhase
}

theorem raise_present : raiseState.registry false = some raiseFiber := rfl

theorem raiseState_wellFormed : WellFormed raiseState := by
  apply setPhase_installed_preserves provider_present reloadingPhase
  · trivial
  · intro committed committedEq
    have committedIsEmpty : committed = emptyProviderView := by
      change some emptyProviderView = some committed at committedEq
      exact (Option.some.inj committedEq).symm
    subst committed
    intro declared
    rcases declared with ⟨key, declared⟩
    change key ∈ providerDecl.dependencies.keys at declared
    simp [providerDecl] at declared
  · exact state_wellFormed

def stateSetoid : Setoid ExampleState where
  r left right := left.ambient = right.ambient
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

def runIterator (_owner : Signature.Name) (_code : Signature.IteratorCode)
    (before : ExampleState) :
    Except Signature.Error (IteratorResult exampleCatalog Bool) :=
  .error before.ambient

def applyExternalUndo (_code : Signature.ExternalUndoCode)
    (before : ExampleState) : ExampleState := before

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := stateSetoid
  runIterator := runIterator
  applyExternalUndo := applyExternalUndo
  ordinary_recovers := by
    intro owner code before result runEq
    simp [runIterator] at runEq
  externalUndo_respects := by
    intro undo left right related
    exact related
  ordinary_confined := by
    intro owner code before result runEq
    simp [runIterator] at runEq
  ordinary_preserves_wellFormed := by
    intro owner code before result runEq
    simp [runIterator] at runEq
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact .errors related
  ReadEquivalent _ left right := left.ambient = right.ambient
  read_refl := fun _ _ ↦ rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact .errors related
  retire_respects := by
    intro name left right related
    change left.ambient = right.ambient at related
    have leftAmbient : (retireByName left name).ambient = left.ambient := by
      unfold retireByName
      split <;> rfl
    have rightAmbient : (retireByName right name).ambient = right.ambient := by
      unfold retireByName
      split <;> rfl
    exact leftAmbient.trans (related.trans rightAmbient.symm)

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

theorem dynamics_equivariant : DynamicsNameEquivariant swapAction dynamics where
  run_equivariant owner code before := by rfl
  externalUndo_equivariant code before := by rfl
  equivalence_iff {left right} := by
    change Bool.not left.ambient = Bool.not right.ambient ↔
      left.ambient = right.ambient
    constructor
    · intro equal
      have mapped := congrArg Bool.not equal
      simpa using mapped
    · exact congrArg Bool.not

theorem inertia_equivariant : InertiaNameEquivariant swapAction dynamics inertia where
  canAbort_iff owner code before := by simp [inertia]

theorem assumptions : NameLifecycleAssumptions swapAction dynamics inertia where
  entry := entry_invariant
  dynamics_equivariant := dynamics_equivariant
  inertia := inertia_equivariant

def raiseAfter : ExampleState :=
  setPhase raiseState false raiseFiber (.unloading [] emptyProviderView (some true))

def raiseTransition : Transition dynamics inertia raiseState raiseAfter :=
  .raise raiseState false raiseFiber raise_present false [] emptyProviderView rfl true rfl

def actedRaise : ForwardLifecycleAction swapAction raiseTransition :=
  actLifecycleAction assumptions raiseState_wellFormed raiseTransition

theorem acted_raise_rule : actedRaise.acted.rule = .raise := actedRaise.same_rule

theorem acted_raise_owner : lifecycleOwner actedRaise.acted = true := by
  have owner := actedRaise.acted_owner
  change lifecycleOwner actedRaise.acted = Bool.not false at owner
  exact owner

theorem acted_raise_error :
    dynamics.runIterator true false (actState swapAction raiseState) = .error false := rfl

theorem acted_raise_endpoint :
    lifecycleOwner actedRaise.acted = true ∧
      (actState swapAction raiseAfter).registry true =
        some { actFiber swapAction raiseFiber with
          phase := .unloading [] (actCommittedView swapAction emptyProviderView)
            (some false) } := by
  exact ⟨acted_raise_owner, rfl⟩

def entryBreakingAction : NameAction Signature Bool where
  name := Equiv.refl Bool
  ambient := Equiv.refl Bool
  value key := Equiv.refl (Value key)
  error := Equiv.refl Bool
  iterator := boolNotEquiv
  externalUndo := Equiv.refl Bool

theorem entryBreakingAction_not_invariant :
    ¬entryBreakingAction.CatalogEntryInvariant exampleCatalog := by
  intro invariant
  have fixed := invariant .provider
  change Bool.not false = false at fixed
  cases fixed

theorem entryBreakingAction_begin_phase_mismatch :
    actPhase entryBreakingAction
        (.reloading providerDecl.entry [] emptyProviderView) ≠
      .reloading providerDecl.entry []
        (actCommittedView entryBreakingAction emptyProviderView) := by
  intro equal
  cases equal

def successOnlyMap
    (result : Except Signature.Error (IteratorResult exampleCatalog Bool)) :
    Except Signature.Error (IteratorResult exampleCatalog Bool) :=
  result.map (actIteratorResult swapAction)

theorem successOnlyMap_loses_error_action :
    successOnlyMap (.error false) ≠ actRunOutput swapAction (.error false) := by
  intro equal
  cases equal

def constantErrorBadRun
    (_owner : Signature.Name) (_code : Signature.IteratorCode) (_state : ExampleState) :
    Except Signature.Error (IteratorResult exampleCatalog Bool) := .error false

theorem constantErrorBadRun_not_equivariant :
    constantErrorBadRun true false (actState swapAction state) ≠
      actRunOutput swapAction (constantErrorBadRun false false state) := by
  intro equal
  cases equal

end NonidentityRaiseExample

end Cordis.GlobalNameLifecycle
