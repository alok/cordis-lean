import Cordis.GlobalTransposition

/-!
# Foreign-phase read and frame laws

This module implements the exact lower layer specified in
`docs/GLOBAL_FOREIGN_PHASE_SPEC.md`, against CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

The current `Dynamics.ReadEquivalent` relation is integrator-defined. `ForeignPhaseReadable`
states that editing one already-present foreign fiber's phase is readable-equivalent for an
iterator owner. `OrdinaryForeignPhaseFrame` refines the related successor from
`run_read_confined` to the exact point-update frame, while
`RegistrationOracleForeignPhaseFrame` separately stabilizes the admitted child. The registration
successor equation is then derived from child freshness and exact insertion/phase commutation.
Together these laws inhabit the previously assumption-only `ForeignPhaseCompatibility` contract.

One-sided framed executions and a two-sided `PhaseFramedDiamond` remain below lifecycle rules:
they combine raw iterator execution with caller-supplied phase payloads. A finite two-owner model
proves that full Definition 60 independence alone does not imply compatibility, because a
program may read a foreign phase and change its stored undo code while retaining the same
interpreted inverse.

No declaration in this module takes or returns a lifecycle `Transition` or unified `Step`. The
module does not prove target or guard stability, that supplied phases are lifecycle-rule outputs,
fixed program/oracle assignment for episodes, paper Lemma 71, mixed-trace reordering, Theorem
61, Corollary 62, confluence, or Definition 65/Theorem 66 progress.
-/

set_option autoImplicit false

namespace Cordis.GlobalForeignPhase

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalIteratorIndependence Cordis.GlobalTransposition

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-! ## Owner presence and lower frame contracts -/

private theorem source_owner_present
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before after : State catalog Ambient}
    {undo : UndoCode sig} {next : Option sig.IteratorCode}
    (source : StepSource dynamics owner code before after undo next) :
    ∃ fiber, before.registry owner = some fiber := by
  cases source with
  | ordinary result runEq =>
      let confinement := dynamics.ordinary_confined owner code before result runEq
      exact ⟨confinement.beforeFiber, confinement.before_present⟩
  | registration request admission runEq =>
      exact ⟨admission.ownerFiber, admission.owner_present⟩

namespace IterationStep

/-- Every successful proof-carrying iteration has its owner present at the source. -/
theorem owner_present
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {state : State catalog Ambient}
    (step : IterationStep dynamics owner code state) :
    ∃ fiber, state.registry owner = some fiber :=
  source_owner_present step.source

end IterationStep

/-- A distinct foreign phase edit lies inside the owner's declared read relation. -/
structure ForeignPhaseReadable
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics) : Prop where
  read_equivalent :
    ∀ {state : State catalog Ambient} {foreignName : sig.Name}
      {foreignFiber : Fiber catalog}
      {phase : Phase (catalog.declaration foreignFiber.component)},
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      dynamics.ReadEquivalent program.owner state
        (setPhase state foreignName foreignFiber phase)

/-- Exact successor framing for an ordinary result. Undo and continuation equality remain the
responsibility of `run_read_confined`. -/
structure OrdinaryForeignPhaseFrame
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics) : Prop where
  after_eq :
    ∀ {code : sig.IteratorCode} {state : State catalog Ambient}
      {foreignName : sig.Name} {foreignFiber : Fiber catalog}
      {phase : Phase (catalog.declaration foreignFiber.component)}
      {original moved : OrdinaryResult catalog Ambient},
      Reach program code →
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      dynamics.runIterator program.owner code state = .ok (.ordinary original) →
      dynamics.runIterator program.owner code
          (setPhase state foreignName foreignFiber phase) = .ok (.ordinary moved) →
      dynamics.equivalence.r original.after moved.after →
      moved.after = setPhase original.after foreignName foreignFiber phase

/-- Cross-state oracle stability for a registering iteration. -/
structure RegistrationOracleForeignPhaseFrame
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics) : Prop where
  certify :
    ∀ {code : sig.IteratorCode} {state : State catalog Ambient}
      {foreignName : sig.Name} {foreignFiber : Fiber catalog}
      {phase : Phase (catalog.declaration foreignFiber.component)}
      {originalRequest movedRequest : RegistrationRequest sig}
      {originalAdmission : RegistrationAdmission dynamics state program.owner originalRequest},
      Reach program code →
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      dynamics.runIterator program.owner code state = .ok (.register originalRequest) →
      dynamics.runIterator program.owner code
          (setPhase state foreignName foreignFiber phase) = .ok (.register movedRequest) →
      originalRequest.component = movedRequest.component →
      originalRequest.next = movedRequest.next →
      program.oracle.certify state originalRequest = .ok originalAdmission →
      ∃ movedAdmission,
        program.oracle.certify
            (setPhase state foreignName foreignFiber phase) movedRequest =
          .ok movedAdmission ∧
        movedAdmission.child = originalAdmission.child

/-- Inserting a fresh child at one name commutes with replacing a different fiber's phase. -/
theorem insertFiber_setPhase_commute
    (state : State catalog Ambient) (child foreignName : sig.Name)
    (parent : Option sig.Name) (component : sig.ComponentId)
    (foreignFiber : Fiber catalog)
    (foreignPhase : Phase (catalog.declaration foreignFiber.component))
    (different : child ≠ foreignName) :
    insertFiber (setPhase state foreignName foreignFiber foreignPhase)
        child parent component =
      setPhase (insertFiber state child parent component)
        foreignName foreignFiber foreignPhase := by
  cases state with
  | mk ambient nextBirth registry =>
      simp only [insertFiber, setPhase, GlobalState.mk.injEq]
      exact ⟨trivial, trivial,
        Coeffect.setAt_commute registry foreignName child (Ne.symm different)
          { foreignFiber with phase := foreignPhase }
          {
            component := component
            parent := parent
            birth := nextBirth
            table := Coeffect.empty
            table_within_provision := by simp
            retired := false
            phase := .inactive none
          }⟩

/-! ## Local exact `executeOne` evaluation helpers -/

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

private theorem registrationAdmission_eq
    {dynamics : Dynamics sig catalog Ambient} {before : State catalog Ambient}
    {owner : sig.Name} {request : RegistrationRequest sig}
    {left right : RegistrationAdmission dynamics before owner request}
    (childEq : left.child = right.child)
    (ownerEq : left.ownerFiber = right.ownerFiber) : left = right := by
  rw [RegistrationAdmission.mk.injEq]
  exact ⟨childEq, ownerEq⟩

private theorem certification_of_registration_execution
    {dynamics : Dynamics sig catalog Ambient} {RegistrationError : Type u}
    {owner : sig.Name} (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (request : RegistrationRequest sig)
    (runEq : dynamics.runIterator owner code before = .ok (.register request))
    (admission : RegistrationAdmission dynamics before owner request)
    (executed : executeOne dynamics oracle code before =
      .ok (registrationIterationStep admission code runEq)) :
    oracle.certify before request = .ok admission := by
  cases certification : oracle.certify before request with
  | error error =>
      have rejected := executeOne_registration_error oracle code before request runEq error
        certification
      rw [rejected] at executed
      cases executed
  | ok found =>
      have foundExecuted := executeOne_registration_ok oracle code before request runEq found
        certification
      have stepEq := Except.ok.inj (foundExecuted.symm.trans executed)
      have undoEq := congrArg IterationStep.undo stepEq
      change UndoCode.retire found.child = UndoCode.retire admission.child at undoEq
      have childEq : found.child = admission.child := UndoCode.retire.inj undoEq
      have ownerEq : found.ownerFiber = admission.ownerFiber :=
        Option.some.inj (found.owner_present.symm.trans admission.owner_present)
      have admissionEq := registrationAdmission_eq childEq ownerEq
      subst found
      rfl

/-! ## Deriving the compatibility contract -/

namespace ForeignPhaseCompatibility

theorem of_read_frames
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    (readable : ForeignPhaseReadable program)
    (ordinary : OrdinaryForeignPhaseFrame program)
    (registration : RegistrationOracleForeignPhaseFrame program) :
    ForeignPhaseCompatibility program where
  execute_setPhase := by
    intro code state step foreignName foreignFiber foreignPhase reachable foreignPresent
      different executed
    obtain ⟨ownerFiber, ownerPresent⟩ := IterationStep.owner_present step
    have movedOwnerPresent :
        (setPhase state foreignName foreignFiber foreignPhase).registry program.owner =
          some ownerFiber := by
      rw [setPhase_lookup_other state foreignName program.owner foreignFiber foreignPhase
        (Ne.symm different)]
      exact ownerPresent
    have readEquivalent := readable.read_equivalent (phase := foreignPhase)
      foreignPresent different
    have runsRelated := dynamics.run_read_confined program.owner code ownerFiber ownerFiber
      readEquivalent ownerPresent movedOwnerPresent
    obtain ⟨after, undo, next, source, recovers, preserves⟩ := step
    cases source with
    | ordinary original runEq =>
        cases movedRun : dynamics.runIterator program.owner code
          (setPhase state foreignName foreignFiber foreignPhase) with
        | error error =>
            rw [runEq, movedRun] at runsRelated
            cases runsRelated
        | ok movedResult =>
            cases movedResult with
            | register movedRequest =>
                rw [runEq, movedRun] at runsRelated
                cases runsRelated with
                | results resultRelated => cases resultRelated
            | ordinary moved =>
                rw [runEq, movedRun] at runsRelated
                cases runsRelated with
                | results resultRelated =>
                    cases resultRelated with
                    | ordinary afterRelated undoEq nextEq =>
                        let movedStep := ordinaryIterationStep dynamics program.owner code
                          (setPhase state foreignName foreignFiber foreignPhase) moved movedRun
                        have movedExecuted := executeOne_ordinary program.oracle code
                          (setPhase state foreignName foreignFiber foreignPhase) moved movedRun
                        have framedAfter := ordinary.after_eq reachable foreignPresent different
                          runEq movedRun afterRelated
                        refine ⟨movedStep, movedExecuted, ?_, ?_⟩
                        · exact {
                            undo_eq := congrArg UndoCode.external undoEq.symm
                            continuation := nextEq.symm
                            kind := rfl
                          }
                        · exact framedAfter
    | registration originalRequest originalAdmission runEq =>
        have originalExecuted : executeOne dynamics program.oracle code state =
            .ok (registrationIterationStep originalAdmission code runEq) := by
          exact executed
        have originalCertified := certification_of_registration_execution program.oracle code
          state originalRequest runEq originalAdmission originalExecuted
        cases movedRun : dynamics.runIterator program.owner code
          (setPhase state foreignName foreignFiber foreignPhase) with
        | error error =>
            rw [runEq, movedRun] at runsRelated
            cases runsRelated
        | ok movedResult =>
            cases movedResult with
            | ordinary moved =>
                rw [runEq, movedRun] at runsRelated
                cases runsRelated with
                | results resultRelated => cases resultRelated
            | register movedRequest =>
                rw [runEq, movedRun] at runsRelated
                cases runsRelated with
                | results resultRelated =>
                    cases resultRelated with
                    | register componentEq nextEq =>
                        obtain ⟨movedAdmission, movedCertified, childEq⟩ :=
                          registration.certify reachable foreignPresent different runEq movedRun
                            componentEq nextEq originalCertified
                        have requestEq : originalRequest = movedRequest := by
                          rw [RegistrationRequest.mk.injEq]
                          exact ⟨componentEq, nextEq⟩
                        have childDifferent : originalAdmission.child ≠ foreignName := by
                          intro same
                          subst foreignName
                          rw [originalAdmission.fresh.lookup_eq] at foreignPresent
                          cases foreignPresent
                        have framedAfter : movedAdmission.after =
                            setPhase originalAdmission.after foreignName foreignFiber
                              foreignPhase := by
                          cases requestEq
                          change insertFiber
                              (setPhase state foreignName foreignFiber foreignPhase)
                                movedAdmission.child (some program.owner)
                                originalRequest.component =
                            setPhase
                              (insertFiber state originalAdmission.child (some program.owner)
                                originalRequest.component)
                              foreignName foreignFiber foreignPhase
                          rw [childEq]
                          exact insertFiber_setPhase_commute state originalAdmission.child
                            foreignName (some program.owner) originalRequest.component
                            foreignFiber foreignPhase childDifferent
                        let movedStep := registrationIterationStep movedAdmission code movedRun
                        have movedExecuted := executeOne_registration_ok program.oracle code
                          (setPhase state foreignName foreignFiber foreignPhase) movedRequest
                          movedRun movedAdmission movedCertified
                        refine ⟨movedStep, movedExecuted, ?_, ?_⟩
                        · refine {
                            undo_eq := congrArg UndoCode.retire childEq
                            continuation := ?_
                            kind := ?_
                          }
                          · change movedRequest.next movedAdmission.child =
                              originalRequest.next originalAdmission.child
                            rw [childEq, ← nextEq]
                          · exact congrArg YieldKind.registration componentEq.symm
                        · exact framedAfter

end ForeignPhaseCompatibility

/-! ## One-sided phase-framed execution -/

structure PhaseFramedExecution
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    {code : sig.IteratorCode} {state : State catalog Ambient}
    (step : IterationStep dynamics program.owner code state)
    (foreignName : sig.Name) (foreignFiber : Fiber catalog)
    (foreignPhase : Phase (catalog.declaration foreignFiber.component)) where
  movedStep : IterationStep dynamics program.owner code
    (setPhase state foreignName foreignFiber foreignPhase)
  executed :
    executeOne dynamics program.oracle code
      (setPhase state foreignName foreignFiber foreignPhase) = .ok movedStep
  yield_agrees : LifecycleYieldAgrees movedStep step
  after_eq : movedStep.after =
    setPhase step.after foreignName foreignFiber foreignPhase

namespace ForeignPhaseCompatibility

noncomputable def frame
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    (compatible : ForeignPhaseCompatibility program)
    {code : sig.IteratorCode} {state : State catalog Ambient}
    (step : IterationStep dynamics program.owner code state)
    (foreignName : sig.Name) (foreignFiber : Fiber catalog)
    (foreignPhase : Phase (catalog.declaration foreignFiber.component))
    (reachable : Reach program code)
    (foreignPresent : state.registry foreignName = some foreignFiber)
    (different : foreignName ≠ program.owner)
    (executed : executeOne dynamics program.oracle code state = .ok step) :
    PhaseFramedExecution program step foreignName foreignFiber foreignPhase := by
  have existsMoved := compatible.execute_setPhase (foreignPhase := foreignPhase)
    reachable foreignPresent different executed
  let movedStep := Classical.choose existsMoved
  have movedExecuted := (Classical.choose_spec existsMoved).1
  have yieldAgrees := (Classical.choose_spec existsMoved).2.1
  have afterEq := (Classical.choose_spec existsMoved).2.2
  exact {
    movedStep := movedStep
    executed := movedExecuted
    yield_agrees := yieldAgrees
    after_eq := afterEq
  }

end ForeignPhaseCompatibility

/-! ## Two-sided phase-framed raw diamond -/

structure PhaseFramedDiamond
    {dynamics : Dynamics sig catalog Ambient} {left right : Program dynamics}
    {leftCode rightCode : sig.IteratorCode} {origin : State catalog Ambient}
    (leftStep : IterationStep dynamics left.owner leftCode origin)
    (rightStep : IterationStep dynamics right.owner rightCode origin)
    (leftFiber rightFiber : Fiber catalog)
    (leftPhase : Phase (catalog.declaration leftFiber.component))
    (rightPhase : Phase (catalog.declaration rightFiber.component)) where
  raw : ForwardDiamond leftStep rightStep
  rightAfterLeftEdit : PhaseFramedExecution right raw.rightAfterLeft
    left.owner leftFiber leftPhase
  leftAfterRightEdit : PhaseFramedExecution left raw.leftAfterRight
    right.owner rightFiber rightPhase
  right_present_before_final :
    rightAfterLeftEdit.movedStep.after.registry right.owner = some rightFiber
  left_present_before_final :
    leftAfterRightEdit.movedStep.after.registry left.owner = some leftFiber
  endpoint_eq :
    setPhase rightAfterLeftEdit.movedStep.after right.owner rightFiber rightPhase =
      setPhase leftAfterRightEdit.movedStep.after left.owner leftFiber leftPhase

noncomputable def phase_framed_diamond
    {dynamics : Dynamics sig catalog Ambient} {left right : Program dynamics}
    (independent : Independent left right)
    (leftCompatible : ForeignPhaseCompatibility left)
    (rightCompatible : ForeignPhaseCompatibility right)
    {leftCode rightCode : sig.IteratorCode} {origin : State catalog Ambient}
    (leftReachable : Reach left leftCode) (rightReachable : Reach right rightCode)
    (leftStep : IterationStep dynamics left.owner leftCode origin)
    (rightStep : IterationStep dynamics right.owner rightCode origin)
    (leftExecuted : executeOne dynamics left.oracle leftCode origin = .ok leftStep)
    (rightExecuted : executeOne dynamics right.oracle rightCode origin = .ok rightStep)
    (different : left.owner ≠ right.owner)
    (leftFiber rightFiber : Fiber catalog)
    (leftPresent : leftStep.after.registry left.owner = some leftFiber)
    (rightPresent : rightStep.after.registry right.owner = some rightFiber)
    (leftPhase : Phase (catalog.declaration leftFiber.component))
    (rightPhase : Phase (catalog.declaration rightFiber.component)) :
    PhaseFramedDiamond leftStep rightStep leftFiber rightFiber leftPhase rightPhase := by
  let raw := independent_forward_diamond independent leftReachable rightReachable
    leftStep rightStep leftExecuted rightExecuted
  let rightAfterLeftEdit :=
    Cordis.GlobalForeignPhase.ForeignPhaseCompatibility.frame rightCompatible
      raw.rightAfterLeft left.owner leftFiber leftPhase rightReachable leftPresent different
      raw.right_executed
  let leftAfterRightEdit :=
    Cordis.GlobalForeignPhase.ForeignPhaseCompatibility.frame leftCompatible raw.leftAfterRight
      right.owner rightFiber rightPhase leftReachable rightPresent (Ne.symm different)
      raw.left_executed
  have rightAtLeftAfterRight :
      raw.leftAfterRight.after.registry right.owner = some rightFiber :=
    GlobalTraceFacts.iteration_foreign_lookup raw.leftAfterRight rightPresent
      (Ne.symm different)
  have rightAtRawEndpoint :
      raw.rightAfterLeft.after.registry right.owner = some rightFiber := by
    rw [raw.endpoint_eq]
    exact rightAtLeftAfterRight
  have rightBeforeFinal :
      rightAfterLeftEdit.movedStep.after.registry right.owner = some rightFiber := by
    rw [rightAfterLeftEdit.after_eq]
    exact setPhase_lookup_other raw.rightAfterLeft.after left.owner right.owner leftFiber
      leftPhase (Ne.symm different) |>.trans rightAtRawEndpoint
  have leftAtRightAfterLeft :
      raw.rightAfterLeft.after.registry left.owner = some leftFiber :=
    GlobalTraceFacts.iteration_foreign_lookup raw.rightAfterLeft leftPresent different
  have leftAtRawEndpoint :
      raw.leftAfterRight.after.registry left.owner = some leftFiber := by
    rw [← raw.endpoint_eq]
    exact leftAtRightAfterLeft
  have leftBeforeFinal :
      leftAfterRightEdit.movedStep.after.registry left.owner = some leftFiber := by
    rw [leftAfterRightEdit.after_eq]
    exact setPhase_lookup_other raw.leftAfterRight.after right.owner left.owner rightFiber
      rightPhase different |>.trans leftAtRawEndpoint
  have endpointEq :
      setPhase rightAfterLeftEdit.movedStep.after right.owner rightFiber rightPhase =
        setPhase leftAfterRightEdit.movedStep.after left.owner leftFiber leftPhase := by
    rw [rightAfterLeftEdit.after_eq, leftAfterRightEdit.after_eq, raw.endpoint_eq]
    exact setPhase_commute raw.leftAfterRight.after left.owner right.owner leftFiber rightFiber
      leftPhase rightPhase different
  exact {
    raw := raw
    rightAfterLeftEdit := rightAfterLeftEdit
    leftAfterRightEdit := leftAfterRightEdit
    right_present_before_final := rightBeforeFinal
    left_present_before_final := leftBeforeFinal
    endpoint_eq := endpointEq
  }

/-! ## Independence does not imply foreign-phase compatibility -/

namespace IndependenceGap

abbrev Signature : StaticSignature where
  Name := Bool
  Key := Unit
  ComponentId := Unit
  Error := Unit
  IteratorCode := Unit
  ExternalUndoCode := Bool
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
  provider declared := False.elim (by simpa [declaration] using declared.declared)

def ownerFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def foreignInactive : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 1
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def foreignActive : Fiber exampleCatalog := {
  foreignInactive with phase := .active [] emptyView
}

def before : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty false ownerFiber) true foreignInactive

def afterPhaseEdit : ExampleState :=
  setPhase before true foreignInactive (.active [] emptyView)

@[simp] theorem before_owner_present : before.registry false = some ownerFiber := by
  simp [before]

@[simp] theorem before_foreign_present :
    before.registry true = some foreignInactive := by
  simp [before]

@[simp] theorem after_owner_present :
    afterPhaseEdit.registry false = some ownerFiber := by
  simp [afterPhaseEdit, before]

@[simp] theorem after_foreign_present :
    afterPhaseEdit.registry true = some foreignActive := by
  simp [afterPhaseEdit, before, foreignActive]

def phaseBit (fiber : Fiber exampleCatalog) : Bool :=
  match fiber.phase with
  | .active _ _ => true
  | _ => false

def selectedUndo (owner : Bool) (state : ExampleState) : Bool :=
  if owner then false else
    match state.registry true with
    | none => false
    | some fiber => phaseBit fiber

def result (owner : Bool) (state : ExampleState) :
    OrdinaryResult exampleCatalog Unit where
  after := state
  undo := selectedUndo owner state
  next := none

def runIterator (owner : Bool) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Unit) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.ordinary (result owner state))

def applyExternalUndo (_code : Bool) (state : ExampleState) : ExampleState := state

def stateSetoid : Setoid ExampleState where
  r := Eq
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }

theorem runRelatedRefl
    (value : Except Unit (IteratorResult exampleCatalog Unit)) :
    RunRelated (fun left right : ExampleState ↦ left = right) value value := by
  cases value with
  | error error => exact .errors rfl
  | ok value =>
      cases value with
      | ordinary ordinary => exact .results (.ordinary rfl rfl rfl)
      | register request => exact .results (.register rfl rfl)

def dynamics : Dynamics Signature exampleCatalog Unit where
  equivalence := stateSetoid
  runIterator := runIterator
  applyExternalUndo := applyExternalUndo
  ordinary_recovers := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some fiber =>
        simp [runIterator, lookup] at runEq
        subst found
        rfl
  externalUndo_respects := by
    intro undo left right related
    subst right
    rfl
  ordinary_confined := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some fiber =>
        simp [runIterator, lookup] at runEq
        subst found
        exact {
          beforeFiber := fiber
          afterFiber := fiber
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
    intro owner code state found runEq wellFormed
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some fiber =>
        simp [runIterator, lookup] at runEq
        subst found
        exact wellFormed
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    subst right
    exact runRelatedRefl _
  ReadEquivalent _ left right := left = right
  read_refl := by intros; rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    subst right
    exact runRelatedRefl _
  retire_respects := by
    intro name left right related
    subst right
    rfl

def oracle (owner : Bool) : RegistrationOracle dynamics owner Unit where
  certify _ _ := .error ()

def program (owner : Bool) : Program dynamics where
  owner := owner
  RegistrationError := Unit
  oracle := oracle owner
  root := ()

abbrev observedProgram := program false
abbrev foreignProgram := program true

theorem run_success
    (owner : Bool) (state : ExampleState) (fiber : Fiber exampleCatalog)
    (present : state.registry owner = some fiber) :
    dynamics.runIterator owner () state = .ok (.ordinary (result owner state)) := by
  simp [dynamics, runIterator, present]

def successfulStep
    (owner : Bool) (state : ExampleState) (fiber : Fiber exampleCatalog)
    (present : state.registry owner = some fiber) :
    IterationStep dynamics owner () state :=
  ordinaryIterationStep dynamics owner () state (result owner state)
    (run_success owner state fiber present)

theorem successfulStep_executed
    (owner : Bool) (state : ExampleState) (fiber : Fiber exampleCatalog)
    (present : state.registry owner = some fiber) :
    executeOne dynamics (oracle owner) () state =
      .ok (successfulStep owner state fiber present) := by
  simpa [successfulStep] using
    executeOne_ordinary (oracle owner) () state (result owner state)
      (run_success owner state fiber present)

def beforeStep : IterationStep dynamics observedProgram.owner () before :=
  successfulStep false before ownerFiber before_owner_present

def afterEditStep : IterationStep dynamics observedProgram.owner () afterPhaseEdit :=
  successfulStep false afterPhaseEdit ownerFiber after_owner_present

@[simp] theorem beforeStep_executed :
    executeOne dynamics observedProgram.oracle () before = .ok beforeStep := by
  exact successfulStep_executed false before ownerFiber before_owner_present

@[simp] theorem afterEditStep_executed :
    executeOne dynamics observedProgram.oracle () afterPhaseEdit = .ok afterEditStep := by
  exact successfulStep_executed false afterPhaseEdit ownerFiber after_owner_present

theorem forward_apply (owner : Bool) (state : ExampleState) :
    forward (program owner) () state =
      match state.registry owner with
      | none => none
      | some _ => some state := by
  unfold forward
  simp only [program]
  cases lookup : state.registry owner with
  | none =>
      have raw : dynamics.runIterator owner () state = .error () := by
        simp [dynamics, runIterator, lookup]
      rw [executeOne_iterator_error (oracle owner) () state () raw]
  | some fiber =>
      rw [successfulStep_executed owner state fiber lookup]
      rfl

theorem forward_success_eq
    (owner : Bool) (state moved : ExampleState)
    (transformed : forward (program owner) () state = some moved) : moved = state := by
  rw [forward_apply] at transformed
  cases lookup : state.registry owner with
  | none => simp [lookup] at transformed
  | some fiber =>
      simp [lookup] at transformed
      exact transformed.symm

theorem forwards_commute (left right : Bool) :
    Cordis.PartialTransformation.Commutes
      (forward (program left) ()) (forward (program right) ()) := by
  intro state
  unfold Cordis.PartialTransformation.comp
  rw [forward_apply, forward_apply]
  cases leftLookup : state.registry left <;>
    cases rightLookup : state.registry right <;>
      simp [forward_apply, leftLookup, rightLookup]

theorem executed_step_inverse_identity
    {owner : Bool} {code : Unit} {state : ExampleState}
    {step : IterationStep dynamics owner code state}
    (executed : executeOne dynamics (oracle owner) code state = .ok step) :
    total (dynamics.applyUndo step.undo) =
      (Cordis.PartialTransformation.identity : PartialMap exampleCatalog Unit) := by
  cases code
  cases lookup : state.registry owner with
  | none =>
      have raw : dynamics.runIterator owner () state = .error () := by
        simp [dynamics, runIterator, lookup]
      rw [executeOne_iterator_error (oracle owner) () state () raw] at executed
      cases executed
  | some fiber =>
      have known := successfulStep_executed owner state fiber lookup
      have stepEq : step = successfulStep owner state fiber lookup :=
        Except.ok.inj (executed.symm.trans known)
      subst step
      rfl

theorem generator_commutes
    {leftMap rightMap : PartialMap exampleCatalog Unit}
    (leftGenerated : Generator observedProgram leftMap)
    (rightGenerated : Generator foreignProgram rightMap) :
    Cordis.PartialTransformation.Commutes leftMap rightMap := by
  cases leftGenerated with
  | forward leftReachable =>
      cases rightGenerated with
      | forward rightReachable =>
          exact forwards_commute false true
      | inverse rightReachable rightExecuted =>
          rw [executed_step_inverse_identity rightExecuted]
          intro state
          simp [Cordis.PartialTransformation.comp,
            Cordis.PartialTransformation.identity]
  | inverse leftReachable leftExecuted =>
      rw [executed_step_inverse_identity leftExecuted]
      cases rightGenerated with
      | forward rightReachable =>
          intro state
          simp [Cordis.PartialTransformation.comp,
            Cordis.PartialTransformation.identity]
      | inverse rightReachable rightExecuted =>
          rw [executed_step_inverse_identity rightExecuted]
          intro state
          simp [Cordis.PartialTransformation.comp,
            Cordis.PartialTransformation.identity]

theorem generator_yield_stable
    (target : Bool) {map : PartialMap exampleCatalog Unit}
    (generated : Generator (program (!target)) map) : YieldStable (program target) map := by
  intro code reachable seed step moved executed transformed
  cases generated with
  | forward foreignReachable =>
      have movedEq := forward_success_eq (!target) seed moved transformed
      subst moved
      exact ⟨step, executed, YieldAgrees.refl step⟩
  | inverse foreignReachable foreignExecuted =>
      rw [executed_step_inverse_identity foreignExecuted] at transformed
      have movedEq := Option.some.inj transformed
      subst moved
      exact ⟨step, executed, YieldAgrees.refl step⟩

theorem programs_independent : Independent observedProgram foreignProgram :=
  Independent.of_generators generator_commutes
    (generator_yield_stable false) (generator_yield_stable true)

theorem interpreted_inverses_equal :
    dynamics.applyUndo afterEditStep.undo = dynamics.applyUndo beforeStep.undo := rfl

theorem semantic_yields_agree :
    YieldAgrees (program := observedProgram) afterEditStep beforeStep where
  inverse := rfl
  continuation := rfl
  kind := rfl

theorem undo_codes_differ : afterEditStep.undo ≠ beforeStep.undo := by
  intro equal
  cases equal

theorem lifecycle_yields_do_not_agree :
    ¬LifecycleYieldAgrees (program := observedProgram) afterEditStep beforeStep := by
  intro agrees
  exact undo_codes_differ agrees.undo_eq

theorem foreign_edit_not_readEquivalent :
    ¬dynamics.ReadEquivalent observedProgram.owner before afterPhaseEdit := by
  intro equal
  have lookupEq := congrArg (fun state ↦ state.registry true) equal
  have fiberEq : foreignInactive = foreignActive :=
    Option.some.inj (before_foreign_present.symm.trans lookupEq |>.trans after_foreign_present)
  have phaseEq : foreignInactive.phase = foreignActive.phase := by rw [fiberEq]
  cases phaseEq

theorem independent_not_foreignPhaseCompatible :
    Independent observedProgram foreignProgram ∧
      ¬ForeignPhaseCompatibility observedProgram := by
  refine ⟨programs_independent, ?_⟩
  intro compatible
  obtain ⟨movedStep, movedExecuted, agrees, framed⟩ :=
    compatible.execute_setPhase (foreignPhase := Phase.active [] emptyView)
      Reach.root before_foreign_present (by decide) beforeStep_executed
  have stepEq : movedStep = afterEditStep :=
    Except.ok.inj (movedExecuted.symm.trans afterEditStep_executed)
  subst movedStep
  exact lifecycle_yields_do_not_agree agrees

#eval (selectedUndo false before, selectedUndo false afterPhaseEdit)

end IndependenceGap

/-! ## Read confinement does not supply an exact ordinary successor frame -/

namespace OrdinaryFrameGap

abbrev Signature := IndependenceGap.Signature
abbrev exampleCatalog := IndependenceGap.exampleCatalog
abbrev ExampleState := GlobalState exampleCatalog Bool

def before : ExampleState where
  ambient := false
  nextBirth := 2
  registry := Coeffect.setAt
    (Coeffect.setAt Coeffect.empty false IndependenceGap.ownerFiber)
      true IndependenceGap.foreignInactive

def afterPhaseEdit : ExampleState :=
  setPhase before true IndependenceGap.foreignInactive
    (.active [] IndependenceGap.emptyView)

@[simp] theorem before_owner_present :
    before.registry false = some IndependenceGap.ownerFiber := by
  simp [before]

@[simp] theorem before_foreign_present :
    before.registry true = some IndependenceGap.foreignInactive := by
  simp [before]

@[simp] theorem after_owner_present :
    afterPhaseEdit.registry false = some IndependenceGap.ownerFiber := by
  simp [afterPhaseEdit, before]

def foreignPhaseBit (state : ExampleState) : Bool :=
  match state.registry true with
  | none => false
  | some fiber => IndependenceGap.phaseBit fiber

/-- The ordinary raw effect is an involution, but it branches on the foreign control phase. -/
def toggleAmbient (state : ExampleState) : ExampleState := {
  state with ambient := if foreignPhaseBit state then !state.ambient else state.ambient
}

theorem toggleAmbient_involutive (state : ExampleState) :
    toggleAmbient (toggleAmbient state) = state := by
  cases state with
  | mk ambient nextBirth registry =>
      cases lookup : registry true with
      | none => simp [toggleAmbient, foreignPhaseBit, lookup]
      | some fiber =>
          cases phaseEq : fiber.phase <;>
            cases ambient <;>
              simp [toggleAmbient, foreignPhaseBit, IndependenceGap.phaseBit, lookup, phaseEq]

def result (state : ExampleState) : OrdinaryResult exampleCatalog Bool where
  after := toggleAmbient state
  undo := false
  next := none

def runIterator (owner : Bool) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Bool) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.ordinary (result state))

def universalSetoid : Setoid ExampleState where
  r _ _ := True
  iseqv := {
    refl := fun _ ↦ trivial
    symm := fun _ ↦ trivial
    trans := fun _ _ ↦ trivial
  }

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := universalSetoid
  runIterator := runIterator
  applyExternalUndo _ := toggleAmbient
  ordinary_recovers := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some fiber =>
        simp [runIterator, lookup] at runEq
        subst found
        exact toggleAmbient_involutive state
  externalUndo_respects := by intros; trivial
  ordinary_confined := by
    intro owner code state found runEq
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some fiber =>
        simp [runIterator, lookup] at runEq
        subst found
        exact {
          beforeFiber := fiber
          afterFiber := fiber
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
    intro owner code state found runEq wellFormed
    cases lookup : state.registry owner with
    | none => simp [runIterator, lookup] at runEq
    | some fiber =>
        simp [runIterator, lookup] at runEq
        subst found
        change WellFormed (toggleAmbient state)
        unfold toggleAmbient
        split
        · exact {
            birth_bounded := wellFormed.birth_bounded
            parent_present := wellFormed.parent_present
            parent_older := wellFormed.parent_older
            provisions_unique := wellFormed.provisions_unique
            committed_provider_present := wellFormed.committed_provider_present
            committed_provider_installed := wellFormed.committed_provider_installed
          }
        · exact wellFormed
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.ordinary trivial rfl rfl)
  ReadEquivalent _ _ _ := True
  read_refl := by intros; trivial
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.ordinary trivial rfl rfl)
  retire_respects := by intros; trivial

def oracle : RegistrationOracle dynamics false Unit where
  certify _ _ := .error ()

def program : Program dynamics where
  owner := false
  RegistrationError := Unit
  oracle := oracle
  root := ()

theorem original_run :
    dynamics.runIterator program.owner () before = .ok (.ordinary (result before)) := by
  simp [dynamics, runIterator, program, before_owner_present]

theorem moved_run :
    dynamics.runIterator program.owner () afterPhaseEdit =
      .ok (.ordinary (result afterPhaseEdit)) := by
  simp [dynamics, runIterator, program, after_owner_present]

theorem readable : ForeignPhaseReadable program where
  read_equivalent := by intros; trivial

theorem run_read_confined_at_edit :
    RunRelated dynamics.equivalence.r
      (dynamics.runIterator program.owner () before)
      (dynamics.runIterator program.owner () afterPhaseEdit) :=
  dynamics.run_read_confined program.owner () IndependenceGap.ownerFiber
    IndependenceGap.ownerFiber trivial before_owner_present after_owner_present

theorem exact_undo_and_continuation_preserved :
    (result before).undo = (result afterPhaseEdit).undo ∧
      (result before).next = (result afterPhaseEdit).next := ⟨rfl, rfl⟩

theorem exact_frame_fails :
    (result afterPhaseEdit).after ≠
      setPhase (result before).after true IndependenceGap.foreignInactive
        (.active [] IndependenceGap.emptyView) := by
  intro equal
  have ambientEq := congrArg GlobalState.ambient equal
  cases ambientEq

theorem no_ordinary_frame : ¬OrdinaryForeignPhaseFrame program := by
  intro frame
  have framed := frame.after_eq Reach.root before_foreign_present (by decide)
    original_run moved_run trivial
  exact exact_frame_fails framed

theorem readability_does_not_supply_ordinary_frame :
    ForeignPhaseReadable program ∧ ¬OrdinaryForeignPhaseFrame program :=
  ⟨readable, no_ordinary_frame⟩

end OrdinaryFrameGap

/-! ## Raw registration stability does not stabilize a state-dependent oracle -/

namespace OracleGap

abbrev Signature : StaticSignature where
  Name := Nat
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

def view : CommittedView declaration where
  provider declared := False.elim (by simpa [declaration] using declared.declared)

def ownerFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def foreignFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 1
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

def activePhase : Phase declaration := .active [] view

def before : ExampleState where
  ambient := ()
  nextBirth := 2
  registry := Coeffect.setAt (Coeffect.setAt Coeffect.empty 0 ownerFiber) 1 foreignFiber

@[simp] theorem before_owner : before.registry 0 = some ownerFiber := by
  simp [before]

@[simp] theorem before_foreign : before.registry 1 = some foreignFiber := by
  simp [before]

@[simp] theorem before_child_absent : before.registry 2 = none := by
  simp [before]

def request : RegistrationRequest Signature where
  component := ()
  next _ := none

def universalSetoid : Setoid ExampleState where
  r _ _ := True
  iseqv := {
    refl := fun _ ↦ trivial
    symm := fun _ ↦ trivial
    trans := fun _ _ ↦ trivial
  }

def runIterator (owner : Nat) (_code : Unit) (state : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Unit) :=
  match state.registry owner with
  | none => .error ()
  | some _ => .ok (.register request)

def dynamics : Dynamics Signature exampleCatalog Unit where
  equivalence := universalSetoid
  runIterator := runIterator
  applyExternalUndo _ state := state
  ordinary_recovers := by
    intro owner code state found runEq
    cases present : state.registry owner <;> simp [runIterator, present] at runEq
  externalUndo_respects := by intros; trivial
  ordinary_confined := by
    intro owner code state found runEq
    cases present : state.registry owner <;> simp [runIterator, present] at runEq
  ordinary_preserves_wellFormed := by
    intro owner code state found runEq
    cases present : state.registry owner <;> simp [runIterator, present] at runEq
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    simp [runIterator, leftPresent, rightPresent]
    exact .results (.register rfl rfl)
  ReadEquivalent _ _ _ := True
  read_refl := by intros; trivial
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    simp [runIterator, leftPresent, rightPresent]
    exact .results (.register rfl rfl)
  retire_respects := by intros; trivial

def certify (state : ExampleState) (candidate : RegistrationRequest Signature) :
    Except Unit (RegistrationAdmission dynamics state 0 candidate) :=
  match ownerPresent : state.registry 0 with
  | none => .error ()
  | some foundOwner =>
      match childFresh : state.registry 2 with
      | some _ => .error ()
      | none =>
          match foreignPresent : state.registry 1 with
          | none => .error ()
          | some foundForeign =>
              match foundForeign.phase with
              | .inactive _ => .ok {
                  child := 2
                  fresh := ⟨childFresh⟩
                  ownerFiber := foundOwner
                  owner_present := ownerPresent
                  provision_fresh := by simp [declaration]
                  registration_recovers := trivial
                }
              | _ => .error ()

def oracle : RegistrationOracle dynamics 0 Unit where
  certify := certify

def program : Program dynamics where
  owner := 0
  RegistrationError := Unit
  oracle := oracle
  root := ()

def edited : ExampleState := setPhase before 1 foreignFiber activePhase

theorem raw_before :
    dynamics.runIterator 0 () before = .ok (.register request) := by
  simp [dynamics, runIterator]

theorem raw_edited :
    dynamics.runIterator 0 () edited = .ok (.register request) := by
  simp [dynamics, runIterator, edited]

theorem raw_request_stable :
    ResultRelated dynamics.equivalence.r (.register request) (.register request) :=
  .register rfl rfl

theorem readable : ForeignPhaseReadable program where
  read_equivalent := by intros; trivial

theorem accepts_before :
    ∃ admission, oracle.certify before request = .ok admission := by
  simp [oracle, certify, before, ownerFiber, foreignFiber, Coeffect.setAt]

theorem rejects_edited : oracle.certify edited request = .error () := by
  simp [oracle, certify, edited, before, ownerFiber, foreignFiber, activePhase,
    setPhase, Coeffect.setAt]

theorem moved_executeOne_rejected :
    executeOne dynamics oracle () edited = .error (.registration ()) := by
  rfl

theorem executeOne_succeeds_before :
    ∃ step, executeOne dynamics oracle () before = .ok step := by
  obtain ⟨admission, accepted⟩ := accepts_before
  refine ⟨registrationIterationStep admission () raw_before, ?_⟩
  exact executeOne_registration_ok oracle () before request raw_before admission accepted

theorem no_success_after_edit :
    ∀ step, executeOne dynamics oracle () edited ≠ .ok step := by
  intro step equal
  rw [moved_executeOne_rejected] at equal
  cases equal

theorem raw_read_stability_does_not_imply_oracle_frame :
    ForeignPhaseReadable program ∧
      ¬RegistrationOracleForeignPhaseFrame program := by
  refine ⟨readable, ?_⟩
  intro frame
  obtain ⟨admission, accepted⟩ := accepts_before
  obtain ⟨movedAdmission, movedAccepted, childEq⟩ :=
    frame.certify Reach.root before_foreign (by decide) raw_before raw_edited rfl rfl
      accepted
  change oracle.certify edited request = .ok movedAdmission at movedAccepted
  rw [rejects_edited] at movedAccepted
  cases movedAccepted

end OracleGap

end Cordis.GlobalForeignPhase
