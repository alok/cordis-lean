import Cordis.GlobalActivationTransposition
import Cordis.GlobalSpatial

/-!
# Conditional global progress

This module implements the strongest state-local progress theorem supported by the bounded global
calculus, following CORDIS paper Definition 65 and auditing Theorem 66 at revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`.

Two kernel counterexamples precede the positive theorem. A configured program may be unable to
activate when its fixed registration oracle rejects even though the raw lifecycle relation can
silently choose a different oracle. More strongly, a finite exhausted name carrier can make every
registration admission impossible and leave a well-formed nonquiescent state with no lifecycle
transition at all.

The positive result is conditional and occurrence-minimal. It assumes an explicit finite increasing
rank for provider precedence, static soundness of committed providers, one fixed reachable
landing-or-raise witness at each exact reloading occurrence, and recovery admission at each exact
unrelied unloading occurrence. Under those authorities, every well-formed nonquiescent state has an
applicable lifecycle rule.

This is not the paper's full Theorem 66. In particular, it proves neither the quantitative
`(K + 4)` bound nor target-turn finiteness, maximal-execution termination, fairness, trace-wide
program assignment, or any support/confluence theorem.
-/

set_option autoImplicit false

namespace Cordis.GlobalProgress

open Cordis.GlobalRegistry Cordis.GlobalDynamics Cordis.GlobalLifecycle
open Cordis.GlobalIteratorIndependence Cordis.GlobalLandingTransposition
open Cordis.GlobalActivationTransposition


universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-- Narrow applicability of the fixed-program Begin/Iter/Finish activation fragment. -/
def FixedActivationApplicable
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    (state : State catalog Ambient) : Prop :=
  Nonempty (ProgramActivation program state)


/-! ## Fixed-program and raw-relation progress gaps -/

namespace RegistrationRejectionGap

open Cordis.GlobalForeignPhase.OracleGap

def reloadingOwnerFiber : Fiber exampleCatalog := {
  ownerFiber with phase := .reloading () [] view
}

def stuck : ExampleState :=
  setPhase edited 0 ownerFiber (.reloading () [] view)

def activeForeignFiber : Fiber exampleCatalog := {
  foreignFiber with phase := activePhase
}

@[simp] theorem stuck_owner_present : stuck.registry 0 = some reloadingOwnerFiber := by
  rfl

@[simp] theorem stuck_foreign_present : stuck.registry 1 = some {
    foreignFiber with phase := activePhase
  } := by
  rfl

theorem lookup_cases {name : Nat} {fiber : Fiber exampleCatalog}
    (present : stuck.registry name = some fiber) :
    (name = 0 ∧ fiber = reloadingOwnerFiber) ∨
      (name = 1 ∧ fiber = activeForeignFiber) := by
  cases name with
  | zero =>
      left
      constructor
      · rfl
      · rw [stuck_owner_present] at present
        exact Option.some.inj present.symm
  | succ name =>
      cases name with
      | zero =>
          right
          constructor
          · rfl
          · rw [stuck_foreign_present] at present
            exact Option.some.inj present.symm
      | succ name => simp [stuck, edited, before] at present

theorem stuck_wellFormed : WellFormed stuck := by
  constructor
  · intro name fiber lookup
    cases name with
    | zero => simp at lookup; subst fiber; decide
    | succ name =>
        cases name with
        | zero => simp at lookup; subst fiber; decide
        | succ name => simp [stuck, edited, before] at lookup
  · intro name fiber parent lookup parentEq
    cases name with
    | zero => simp at lookup; subst fiber; simp [reloadingOwnerFiber, ownerFiber] at parentEq
    | succ name =>
        cases name with
        | zero =>
            simp at lookup
            subst fiber
            simp [foreignFiber] at parentEq
        | succ name => simp [stuck, edited, before] at lookup
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name with
    | zero => simp at lookup; subst fiber; simp [reloadingOwnerFiber, ownerFiber] at parentEq
    | succ name =>
        cases name with
        | zero =>
            simp at lookup
            subst fiber
            simp [foreignFiber] at parentEq
        | succ name => simp [stuck, edited, before] at lookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    simp [declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    rcases declared with ⟨key, required⟩
    simp [declaration] at required

theorem stuck_target : targetView stuck 0 reloadingOwnerFiber = some view := by
  apply targetView_eq_of_isTarget stuck_wellFormed
  exact {
    present := stuck_owner_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [declaration] at required
  }

theorem stuck_foreign_target : targetView stuck 1 activeForeignFiber = some view := by
  apply targetView_eq_of_isTarget stuck_wellFormed
  exact {
    present := stuck_foreign_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [declaration] at required
  }

theorem raw_register :
    dynamics.runIterator 0 () stuck = .ok (.register request) := by
  simp [dynamics, runIterator, stuck_owner_present]

theorem oracle_rejects : oracle.certify stuck request = .error () := by
  rfl

theorem execution_rejected :
    executeOne dynamics oracle () stuck = .error (.registration ()) := by
  rfl

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

theorem no_fixed_program_activation :
    ¬FixedActivationApplicable program stuck := by
  rintro ⟨activation⟩
  cases activation with
  | begin fiber guard rootAligned =>
      have present := guard.present
      change stuck.registry 0 = some fiber at present
      rw [stuck_owner_present] at present
      have fiberEq : reloadingOwnerFiber = fiber := Option.some.inj present
      subst fiber
      have entry := guard.entry
      simp [reloadingOwnerFiber] at entry
  | landing aligned =>
      have executed := aligned.program_witness.program_executed
      cases aligned.code
      change executeOne dynamics oracle () stuck = .ok aligned.landing.step at executed
      rw [execution_rejected] at executed
      cases executed

theorem not_quiescent : ¬Quiescent stuck := by
  intro quiet
  have atOwner := quiet 0 reloadingOwnerFiber stuck_owner_present
  exact atOwner

theorem fixed_program_rejection_gap :
    WellFormed stuck ∧ ¬Quiescent stuck ∧
      ¬FixedActivationApplicable program stuck :=
  ⟨stuck_wellFormed, not_quiescent, no_fixed_program_activation⟩

def permissiveAdmission
    (before : ExampleState) (candidate : RegistrationRequest Signature)
    (current : Fiber exampleCatalog) (ownerPresent : before.registry 0 = some current)
    (childAbsent : before.registry 2 = none) :
    RegistrationAdmission dynamics before 0 candidate where
  child := 2
  fresh := ⟨childAbsent⟩
  ownerFiber := current
  owner_present := ownerPresent
  provision_fresh := by simp [declaration]
  registration_recovers := trivial

def permissiveOracle : RegistrationOracle dynamics 0 Unit where
  certify before candidate :=
    match ownerEq : before.registry 0 with
    | none => .error ()
    | some current =>
        match childEq : before.registry 2 with
        | some _ => .error ()
        | none => .ok (permissiveAdmission before candidate current ownerEq childEq)

@[simp] theorem stuck_child_absent : stuck.registry 2 = none := by
  simp [stuck, edited, before]

def admitted : RegistrationAdmission dynamics stuck 0 request :=
  permissiveAdmission stuck request reloadingOwnerFiber stuck_owner_present stuck_child_absent

theorem permissive_certified : permissiveOracle.certify stuck request = .ok admitted := by
  rfl

def permissiveStep : IterationStep dynamics 0 () stuck where
  after := admitted.after
  undo := admitted.undo
  next := admitted.next
  source := .registration request admitted raw_register
  recovers := admitted.registration_recovers
  preserves_wellFormed := admitted.after_wellFormed

theorem permissive_executed :
    executeOne dynamics permissiveOracle () stuck = .ok permissiveStep := by
  rfl

@[simp] theorem permissive_after_owner :
    permissiveStep.after.registry 0 = some reloadingOwnerFiber := by
  rfl

def permissiveLanding : Landing dynamics 0 () stuck reloadingOwnerFiber where
  RegistrationError := Unit
  oracle := permissiveOracle
  step := permissiveStep
  executed := permissive_executed
  before_present := stuck_owner_present
  afterFiber := reloadingOwnerFiber
  after_present := permissive_after_owner
  component_eq := rfl
  phase_eq := rfl

def permissiveFinishAfter : ExampleState :=
  setPhase permissiveStep.after 0 reloadingOwnerFiber (.active [permissiveStep.undo] view)

def permissiveFinish : Transition dynamics inertia stuck permissiveFinishAfter :=
  .finish stuck 0 reloadingOwnerFiber stuck_owner_present () [] view rfl stuck_target
    permissiveLanding rfl

theorem raw_relation_can_change_oracle :
    ∃ after, Nonempty (Transition dynamics inertia stuck after) :=
  ⟨permissiveFinishAfter, ⟨permissiveFinish⟩⟩

def StableExecutionReady (state : ExampleState) : Prop :=
  (∃ step, executeOne dynamics program.oracle () state = .ok step) ∨
    ∃ error, dynamics.runIterator program.owner () state = .error error

def ChangedExecutionReady
    (policy : InertiaPolicy dynamics) (state : ExampleState) : Prop :=
  StableExecutionReady state ∨ policy.canAbort program.owner () state

theorem stable_execution_not_ready : ¬StableExecutionReady stuck := by
  rintro (⟨step, executed⟩ | ⟨error, raised⟩)
  · change executeOne dynamics oracle () stuck = .ok step at executed
    rw [execution_rejected] at executed
    cases executed
  · change dynamics.runIterator 0 () stuck = .error error at raised
    rw [raw_register] at raised
    cases raised

def changedFiber : Fiber exampleCatalog := { reloadingOwnerFiber with retired := true }

def changed : ExampleState := retireFiber stuck 0 reloadingOwnerFiber

def retireOwner : OrchestrationStep stuck changed :=
  .retire stuck 0 reloadingOwnerFiber stuck_owner_present

theorem changed_wellFormed : WellFormed changed :=
  retireOwner.preservesWellFormed stuck_wellFormed

@[simp] theorem changed_owner_present : changed.registry 0 = some changedFiber := by
  rfl

theorem changed_target : targetView changed 0 changedFiber = none :=
  targetView_none_of_retired rfl

theorem changed_target_differs : targetView changed 0 changedFiber ≠ some view := by
  rw [changed_target]
  simp

theorem changed_raw_register :
    dynamics.runIterator 0 () changed = .ok (.register request) := by
  simp [dynamics, runIterator, changed_owner_present]

theorem changed_execution_rejected :
    executeOne dynamics oracle () changed = .error (.registration ()) := by
  rfl

theorem changed_execution_not_ready : ¬ChangedExecutionReady inertia changed := by
  rintro ((⟨step, executed⟩ | ⟨error, raised⟩) | abortable)
  · change executeOne dynamics oracle () changed = .ok step at executed
    rw [changed_execution_rejected] at executed
    cases executed
  · change dynamics.runIterator 0 () changed = .error error at raised
    rw [changed_raw_register] at raised
    cases raised
  · exact abortable

def alwaysAbort : InertiaPolicy dynamics where
  canAbort _ _ _ := True

def changedAbortAfter : ExampleState :=
  setPhase changed 0 changedFiber (.unloading [] view none)

def changedAbort : Transition dynamics alwaysAbort changed changedAbortAfter :=
  .divertAbort changed 0 changedFiber changed_owner_present () [] view rfl
    changed_target_differs trivial

theorem aborting_inertia_restores_a_rule :
    ∃ after, Nonempty (Transition dynamics alwaysAbort changed after) :=
  ⟨changedAbortAfter, ⟨changedAbort⟩⟩

end RegistrationRejectionGap

namespace FreshnessExhaustionGap

open Cordis.GlobalLandingTransposition.YieldSyntaxGap

def view : CommittedView declaration where
  provider declared := False.elim (by
    rcases declared with ⟨key, required⟩
    simp [declaration] at required)

def ownerFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 0
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .reloading () [] view

def otherFiber : Fiber exampleCatalog where
  component := ()
  parent := none
  birth := 1
  table := Cordis.Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .active [] view

def state : ExampleState where
  ambient := false
  nextBirth := 2
  registry := Cordis.Coeffect.setAt
    (Cordis.Coeffect.setAt Cordis.Coeffect.empty false ownerFiber) true otherFiber

@[simp] theorem owner_present : state.registry false = some ownerFiber := by
  simp [state]

@[simp] theorem other_present : state.registry true = some otherFiber := by
  simp [state]

theorem state_wellFormed : WellFormed state := by
  constructor
  · intro name fiber lookup
    cases name <;> simp [state] at lookup <;> subst fiber <;> decide
  · intro name fiber parent lookup parentEq
    cases name <;> simp [state] at lookup <;> subst fiber <;>
      simp [ownerFiber, otherFiber] at parentEq
  · intro name fiber parent parentFiber lookup parentEq parentLookup
    cases name <;> simp [state] at lookup <;> subst fiber <;>
      simp [ownerFiber, otherFiber] at parentEq
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    simp [declaration] at leftKey
  · intro name fiber lookup committed committedEq declared
    rcases declared with ⟨key, required⟩
    simp [declaration] at required
  · intro name fiber lookup committed committedEq declared providerFiber providerLookup
    rcases declared with ⟨key, required⟩
    simp [declaration] at required

theorem owner_target : targetView state false ownerFiber = some view := by
  apply targetView_eq_of_isTarget state_wellFormed
  exact {
    present := owner_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [declaration] at required
  }

theorem other_target : targetView state true otherFiber = some view := by
  apply targetView_eq_of_isTarget state_wellFormed
  exact {
    present := other_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, required⟩
      simp [declaration] at required
  }

def request : RegistrationRequest Signature where
  component := ()
  next _ := none

def runIterator (owner : Bool) (_code : Unit) (before : ExampleState) :
    Except Unit (IteratorResult exampleCatalog Bool) :=
  match before.registry owner with
  | none => .error ()
  | some _ => .ok (.register request)

def universalSetoid : Setoid ExampleState where
  r _ _ := True
  iseqv := ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩

def dynamics : Dynamics Signature exampleCatalog Bool where
  equivalence := universalSetoid
  runIterator := runIterator
  applyExternalUndo _ before := before
  ordinary_recovers := by
    intro owner code before result runEq
    cases lookup : before.registry owner <;> simp [runIterator, lookup] at runEq
  externalUndo_respects := by intros; trivial
  ordinary_confined := by
    intro owner code before result runEq
    cases lookup : before.registry owner <;> simp [runIterator, lookup] at runEq
  ordinary_preserves_wellFormed := by
    intro owner code before result runEq wf
    cases lookup : before.registry owner <;> simp [runIterator, lookup] at runEq
  run_respects := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.register rfl rfl)
  ReadEquivalent _ _ _ := True
  read_refl := by intros; trivial
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    rw [runIterator, leftPresent, runIterator, rightPresent]
    exact .results (.register rfl rfl)
  retire_respects := by intros; trivial

theorem raw_register (owner : Bool) :
    dynamics.runIterator owner () state = .ok (.register request) := by
  cases owner <;> simp [dynamics, runIterator]

theorem no_admission
    (admission : RegistrationAdmission dynamics state false request) : False := by
  have absent := admission.fresh.lookup_eq
  cases childEq : admission.child with
  | false =>
      have absentAtFalse := absent
      rw [childEq] at absentAtFalse
      rw [owner_present] at absentAtFalse
      cases absentAtFalse
  | true =>
      have absentAtTrue := absent
      rw [childEq] at absentAtTrue
      rw [other_present] at absentAtTrue
      cases absentAtTrue

theorem executeOne_ne_ok
    {Error : Type} (oracle : RegistrationOracle dynamics false Error)
    (step : IterationStep dynamics false () state) :
    executeOne dynamics oracle () state ≠ .ok step := by
  intro executed
  rw [executeOne.eq_def] at executed
  split at executed
  · rename_i error runEq
    rw [raw_register false] at runEq
    cases runEq
  · rename_i result runEq
    rw [raw_register false] at runEq
    cases runEq
  · rename_i foundRequest runEq
    have requestEq : foundRequest = request :=
      IteratorResult.register.inj (Except.ok.inj (runEq.symm.trans (raw_register false)))
    subst foundRequest
    split at executed
    · cases executed
    · rename_i admission certified
      exact no_admission admission

theorem no_owner_landing
    (landing : Landing dynamics false () state ownerFiber) : False :=
  executeOne_ne_ok landing.oracle landing.step landing.executed

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

theorem not_quiescent : ¬Quiescent state := by
  intro quiet
  exact quiet false ownerFiber owner_present

theorem no_lifecycle_transition :
    ¬∃ after, Nonempty (Transition dynamics inertia state after) := by
  rintro ⟨after, ⟨transition⟩⟩
  cases transition with
  | begin owner fiber present entry committed target =>
      cases owner
      · rw [owner_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [ownerFiber] at entry
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [otherFiber] at entry
  | iter owner fiber present code undos committed phase target landing next continues =>
      cases owner
      · cases code
        rw [owner_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        exact no_owner_landing landing
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [otherFiber] at phase
  | finish owner fiber present code undos committed phase target landing done =>
      cases owner
      · cases code
        rw [owner_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        exact no_owner_landing landing
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [otherFiber] at phase
  | divertAbort owner fiber present code undos committed phase targetChanged abortable =>
      cases owner
      · exact abortable
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [otherFiber] at phase
  | divertLand owner fiber present code undos committed phase targetChanged landing =>
      cases owner
      · cases code
        rw [owner_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        exact no_owner_landing landing
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [otherFiber] at phase
  | raise owner fiber present code undos committed phase error raised =>
      cases owner <;> cases code <;> rw [raw_register] at raised <;> cases raised
  | leave owner fiber present undos committed phase targetChanged =>
      cases owner
      · rw [owner_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [ownerFiber] at phase
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        cases phase
        exact targetChanged other_target
  | unload owner fiber present undos committed outcome phase notRelied admission =>
      cases owner
      · rw [owner_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [ownerFiber] at phase
      · rw [other_present] at present
        have fiberEq := Option.some.inj present.symm
        subst fiber
        simp [otherFiber] at phase

theorem raw_progress_fails :
    WellFormed state ∧ ¬Quiescent state ∧
      ¬∃ after, Nonempty (Transition dynamics inertia state after) :=
  ⟨state_wellFormed, not_quiescent, no_lifecycle_transition⟩

theorem no_freshSupply_bool : ¬Nonempty (FreshSupply Bool) := by
  rintro ⟨supply⟩
  let chosen := @FreshSupply.fresh Bool supply [false, true]
  have fresh := chosen.property
  cases valueEq : chosen.val <;> simp [valueEq] at fresh

end FreshnessExhaustionGap

/-! ## Definition 65 provider precedence and finite ranking -/

/-- State-local Definition 65, oriented from a possible provider to its consumer. -/
def PrecedesAt
    (state : State catalog Ambient) (provider consumer : sig.Name) : Prop :=
  ∃ providerFiber consumerFiber key,
    state.registry provider = some providerFiber ∧
      state.registry consumer = some consumerFiber ∧
      key ∈ (catalog.declaration providerFiber.component).provision ∧
      key ∈ (catalog.declaration consumerFiber.component).dependencies.keys

/-- Finite explicit acyclicity authority for the current registry's precedence graph. -/
structure FinitePrecedenceRank (state : State catalog Ambient) where
  names : List sig.Name
  nodup : names.Nodup
  covers : ∀ name fiber, state.registry name = some fiber → name ∈ names
  rank : sig.Name → Nat
  increases : ∀ {provider consumer}, PrecedesAt state provider consumer →
    rank provider < rank consumer

namespace FinitePrecedenceRank

theorem wellFounded
    {state : State catalog Ambient} (order : FinitePrecedenceRank state) :
    WellFounded (PrecedesAt state) := by
  apply Subrelation.wf order.increases
  exact (measure order.rank).wf

theorem transGen_rank_lt
    {state : State catalog Ambient} (order : FinitePrecedenceRank state)
    {provider consumer : sig.Name}
    (path : Relation.TransGen (PrecedesAt state) provider consumer) :
    order.rank provider < order.rank consumer := by
  induction path with
  | single edge => exact order.increases edge
  | tail path edge ih => exact Nat.lt_trans ih (order.increases edge)

theorem no_transGen_self
    {state : State catalog Ambient} (order : FinitePrecedenceRank state)
    (name : sig.Name) : ¬Relation.TransGen (PrecedesAt state) name name := by
  intro cycle
  exact Nat.lt_irrefl _ (order.transGen_rank_lt cycle)

end FinitePrecedenceRank

/-! ## Fixed-program landing-or-raise authority -/

/-- Every reachable raw registration request of this fixed program is admitted. -/
structure OracleTotal
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics) : Prop where
  admits : ∀ {code state request}, Reach program code →
    dynamics.runIterator program.owner code state = .ok (.register request) →
    ∃ admission, program.oracle.certify state request = .ok admission

/-- Exact occurrence readiness: the fixed program lands, or its raw iterator raises. -/
def LandingOrRaiseAt
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics)
    (code : sig.IteratorCode) (state : State catalog Ambient)
    (fiber : Fiber catalog) : Prop :=
  (∃ landing : Landing dynamics program.owner code state fiber,
      LandingProgramWitness program landing) ∨
    ∃ error, dynamics.runIterator program.owner code state = .error error

/-- Program-wide convenience authority deriving exact occurrence readiness. -/
structure LandingOrRaiseTotal
    {dynamics : Dynamics sig catalog Ambient} (program : Program dynamics) : Prop where
  ready : ∀ {code state fiber}, Reach program code →
    state.registry program.owner = some fiber →
    LandingOrRaiseAt program code state fiber

private def ordinaryStep
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (state : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (runEq : dynamics.runIterator owner code state = .ok (.ordinary result)) :
    IterationStep dynamics owner code state where
  after := result.after
  undo := .external result.undo
  next := result.next
  source := .ordinary result runEq
  recovers := by
    change dynamics.equivalence.r
      (dynamics.applyExternalUndo result.undo result.after) state
    rw [dynamics.ordinary_recovers owner code state result runEq]
    exact dynamics.equivalence.refl state
  preserves_wellFormed :=
    dynamics.ordinary_preserves_wellFormed owner code state result runEq

private theorem executeOne_ordinary
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (state : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (runEq : dynamics.runIterator owner code state = .ok (.ordinary result)) :
    executeOne dynamics oracle code state =
      .ok (ordinaryStep dynamics owner code state result runEq) := by
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

private def registrationStep
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {state : State catalog Ambient} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics state owner request)
    (code : sig.IteratorCode)
    (runEq : dynamics.runIterator owner code state = .ok (.register request)) :
    IterationStep dynamics owner code state where
  after := admission.after
  undo := admission.undo
  next := admission.next
  source := .registration request admission runEq
  recovers := admission.registration_recovers
  preserves_wellFormed := admission.after_wellFormed

private theorem executeOne_registration
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {RegistrationError : Type u}
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (state : State catalog Ambient)
    (request : RegistrationRequest sig)
    (runEq : dynamics.runIterator owner code state = .ok (.register request))
    (admission : RegistrationAdmission dynamics state owner request)
    (certified : oracle.certify state request = .ok admission) :
    executeOne dynamics oracle code state =
      .ok (registrationStep admission code runEq) := by
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
    rw [certified]
    have runProofEq : foundEq = runEq := Subsingleton.elim _ _
    have certProofEq : certified = certified := rfl
    cases runProofEq
    cases certProofEq
    rfl

theorem OracleTotal.toLandingOrRaiseTotal
    {dynamics : Dynamics sig catalog Ambient} {program : Program dynamics}
    (total : OracleTotal program) : LandingOrRaiseTotal program where
  ready := by
    intro code state fiber reachable present
    cases runEq : dynamics.runIterator program.owner code state with
    | error error => exact Or.inr ⟨error, runEq⟩
    | ok result =>
        cases result with
        | ordinary result =>
            let confinement :=
              dynamics.ordinary_confined program.owner code state result runEq
            have beforePresent := confinement.before_present
            rw [present] at beforePresent
            have fiberEq : fiber = confinement.beforeFiber :=
              Option.some.inj beforePresent
            subst fiber
            let step := ordinaryStep dynamics program.owner code state result runEq
            have executed := executeOne_ordinary program.oracle code state result runEq
            let landing : Landing dynamics program.owner code state
                confinement.beforeFiber := {
              RegistrationError := program.RegistrationError
              oracle := program.oracle
              step := step
              executed := executed
              before_present := confinement.before_present
              afterFiber := confinement.afterFiber
              after_present := confinement.after_present
              component_eq := confinement.component_eq
              phase_eq := confinement.phase_eq
            }
            exact Or.inl ⟨landing, ⟨reachable, landing.executed⟩⟩
        | register request =>
            obtain ⟨admission, certified⟩ := total.admits reachable runEq
            have ownerPresent := admission.owner_present
            rw [present] at ownerPresent
            have fiberEq : fiber = admission.ownerFiber :=
              Option.some.inj ownerPresent
            subst fiber
            let step := registrationStep admission code runEq
            have executed := executeOne_registration program.oracle code state request runEq
              admission certified
            have ownerDifferent : program.owner ≠ admission.child := by
              intro equal
              have ownerAtChild : state.registry admission.child = some admission.ownerFiber := by
                rw [← equal]
                exact admission.owner_present
              rw [admission.fresh.lookup_eq] at ownerAtChild
              cases ownerAtChild
            have afterPresent : step.after.registry program.owner =
                some admission.ownerFiber := by
              change (insertFiber state admission.child (some program.owner)
                request.component).registry program.owner = some admission.ownerFiber
              rw [insertFiber_lookup_other state admission.child program.owner
                (some program.owner) request.component ownerDifferent]
              exact admission.owner_present
            let landing : Landing dynamics program.owner code state admission.ownerFiber := {
              RegistrationError := program.RegistrationError
              oracle := program.oracle
              step := step
              executed := executed
              before_present := admission.owner_present
              afterFiber := admission.ownerFiber
              after_present := afterPresent
              component_eq := rfl
              phase_eq := rfl
            }
            exact Or.inl ⟨landing, ⟨reachable, landing.executed⟩⟩

/-! ## Recovery and committed-provider authorities -/

/-- Global convenience law providing recovery admission at every eligible unload occurrence. -/
structure RecoveryTotal (dynamics : Dynamics sig catalog Ambient) : Prop where
  admits : ∀ {state owner fiber undos committed outcome},
    WellFormed state →
    state.registry owner = some fiber →
    fiber.phase = .unloading undos committed outcome →
    ¬Relied state owner →
    Nonempty (RecoveryAdmission dynamics state owner fiber undos outcome)

/-- Occurrence-minimal recovery authority for one current state. -/
def RecoveryReadyAt
    (dynamics : Dynamics sig catalog Ambient) (state : State catalog Ambient) : Prop :=
  ∀ {owner fiber undos committed outcome},
    WellFormed state →
    state.registry owner = some fiber →
    fiber.phase = .unloading undos committed outcome →
    ¬Relied state owner →
    Nonempty (RecoveryAdmission dynamics state owner fiber undos outcome)

theorem RecoveryTotal.readyAt
    {dynamics : Dynamics sig catalog Ambient} (total : RecoveryTotal dynamics)
    (state : State catalog Ambient) : RecoveryReadyAt dynamics state := by
  intro owner fiber undos committed outcome
  exact total.admits

/-- Every committed provider statically provides the selected declared dependency. -/
def CommittedProvisionSound (state : State catalog Ambient) : Prop :=
  ∀ consumerName consumer
    (committed : CommittedView (catalog.declaration consumer.component))
    (declared : DeclaredKey (catalog.declaration consumer.component)) providerFiber,
    state.registry consumerName = some consumer →
    consumer.phase.committed? = some committed →
    state.registry (committed.provider declared) = some providerFiber →
    declared.key ∈ (catalog.declaration providerFiber.component).provision

/-- An unloading fiber cannot still be the active provider named by a committed target. -/
theorem unloading_provider_changes_committed_target
    {state : State catalog Ambient} {provider consumerName : sig.Name}
    {providerFiber consumer : Fiber catalog}
    {providerUndos : List (UndoCode sig)}
    {providerView : CommittedView (catalog.declaration providerFiber.component)}
    {outcome : Option sig.Error}
    {committed : CommittedView (catalog.declaration consumer.component)}
    (declared : DeclaredKey (catalog.declaration consumer.component))
    (wf : WellFormed state)
    (providerPresent : state.registry provider = some providerFiber)
    (providerUnloading : providerFiber.phase =
      .unloading providerUndos providerView outcome)
    (chosen : committed.provider declared = provider) :
    targetView state consumerName consumer ≠ some committed := by
  intro target
  obtain ⟨activeFiber, activePresent, active, tablePresent⟩ :=
    (targetView_sound wf target).resolves_active declared
  rw [chosen] at activePresent
  rw [providerPresent] at activePresent
  have fiberEq : providerFiber = activeFiber := Option.some.inj activePresent
  subst activeFiber
  change providerFiber.phase.Active at active
  rw [providerUnloading] at active
  exact active

theorem relied_precedes
    {state : State catalog Ambient} {provider : sig.Name}
    (wf : WellFormed state) (sound : CommittedProvisionSound state)
    (relied : Relied state provider) :
    ∃ consumer, PrecedesAt state provider consumer := by
  obtain ⟨consumerName, consumer, consumerPresent, different, installed,
    committed, committedEq, declared, providerEq⟩ := relied
  obtain ⟨providerFiber, providerPresent⟩ :=
    wf.committed_provider_present consumerName consumer consumerPresent committed
      committedEq declared
  have providerAtName : state.registry provider = some providerFiber := by
    rw [← providerEq]
    exact providerPresent
  have provided := sound consumerName consumer committed declared providerFiber
    consumerPresent committedEq providerPresent
  exact ⟨consumerName, providerFiber, consumer, declared.key, providerAtName,
    consumerPresent, provided, declared.declared⟩

/-! ## Occurrence-local progress laws -/

/-- One current reloading fiber is assigned a root-aligned, reachable, ready fixed program. -/
structure ReloadingReadyAt
    (dynamics : Dynamics sig catalog Ambient) (state : State catalog Ambient)
    (name : sig.Name) (fiber : Fiber catalog) (code : sig.IteratorCode) where
  program : Program dynamics
  owner_eq : program.owner = name
  root_aligned : program.root = (catalog.declaration fiber.component).entry
  reachable : Reach program code
  ready : LandingOrRaiseAt program code state fiber

def ReloadingReadyAt.ofTotal
    {dynamics : Dynamics sig catalog Ambient} {state : State catalog Ambient}
    {name : sig.Name} {fiber : Fiber catalog} {code : sig.IteratorCode}
    (program : Program dynamics) (ownerEq : program.owner = name)
    (rootAligned : program.root = (catalog.declaration fiber.component).entry)
    (reachable : Reach program code) (present : state.registry name = some fiber)
    (total : LandingOrRaiseTotal program) :
    ReloadingReadyAt dynamics state name fiber code := by
  have programPresent : state.registry program.owner = some fiber := by
    rw [ownerEq]
    exact present
  exact ⟨program, ownerEq, rootAligned, reachable,
    total.ready reachable programPresent⟩

/-- Exactly the state-local authorities missing from the raw lifecycle calculus. -/
structure LocalProgressLaws
    (dynamics : Dynamics sig catalog Ambient) (state : State catalog Ambient) where
  precedence : FinitePrecedenceRank state
  committed_sound : CommittedProvisionSound state
  reloading_ready : ∀ {name fiber code undos committed},
    state.registry name = some fiber →
    fiber.phase = .reloading code undos committed →
    ReloadingReadyAt dynamics state name fiber code
  recovery : RecoveryReadyAt dynamics state

private theorem list_exists_rank_maximal
    {Name : Type u} (rank : Name → Nat) (predicate : Name → Prop)
    (names : List Name)
    (existsWitness : ∃ name, name ∈ names ∧ predicate name) :
    ∃ maximal,
      maximal ∈ names ∧ predicate maximal ∧
        ∀ candidate, candidate ∈ names → predicate candidate →
          rank candidate ≤ rank maximal := by
  classical
  induction names with
  | nil => simp at existsWitness
  | cons head tail ih =>
      by_cases headSatisfies : predicate head
      · by_cases tailExists : ∃ name, name ∈ tail ∧ predicate name
        · obtain ⟨tailMax, tailMember, tailSatisfies, tailBound⟩ := ih tailExists
          by_cases headBelow : rank head ≤ rank tailMax
          · refine ⟨tailMax, by simp [tailMember], tailSatisfies, ?_⟩
            intro candidate member satisfies
            simp only [List.mem_cons] at member
            cases member with
            | inl equal => simpa [equal] using headBelow
            | inr inTail => exact tailBound candidate inTail satisfies
          · have tailBelow : rank tailMax ≤ rank head :=
              Nat.le_of_lt (Nat.lt_of_not_ge headBelow)
            refine ⟨head, by simp, headSatisfies, ?_⟩
            intro candidate member satisfies
            simp only [List.mem_cons] at member
            cases member with
            | inl equal => simp [equal]
            | inr inTail => exact Nat.le_trans (tailBound candidate inTail satisfies) tailBelow
        · refine ⟨head, by simp, headSatisfies, ?_⟩
          intro candidate member satisfies
          simp only [List.mem_cons] at member
          cases member with
          | inl equal => simp [equal]
          | inr inTail => exact False.elim (tailExists ⟨candidate, inTail, satisfies⟩)
      · have tailExists : ∃ name, name ∈ tail ∧ predicate name := by
          obtain ⟨name, member, satisfies⟩ := existsWitness
          simp only [List.mem_cons] at member
          cases member with
          | inl equal => exact False.elim (headSatisfies (equal ▸ satisfies))
          | inr inTail => exact ⟨name, inTail, satisfies⟩
        obtain ⟨tailMax, tailMember, tailSatisfies, tailBound⟩ := ih tailExists
        exact ⟨tailMax, by simp [tailMember], tailSatisfies, fun candidate member satisfies ↦
          tailBound candidate (by
            simp only [List.mem_cons] at member
            cases member with
            | inl equal => exact False.elim (headSatisfies (equal ▸ satisfies))
            | inr inTail => exact inTail) satisfies⟩

theorem FinitePrecedenceRank.exists_rank_maximal
    {state : State catalog Ambient} (order : FinitePrecedenceRank state)
    (predicate : sig.Name → Prop)
    (existsWitness : ∃ name, name ∈ order.names ∧ predicate name) :
    ∃ maximal,
      maximal ∈ order.names ∧ predicate maximal ∧
        ∀ candidate, candidate ∈ order.names → predicate candidate →
          order.rank candidate ≤ order.rank maximal :=
  list_exists_rank_maximal order.rank predicate order.names existsWitness

theorem FinitePrecedenceRank.successor_not_maximal
    {state : State catalog Ambient} (order : FinitePrecedenceRank state)
    {provider consumer : sig.Name}
    (edge : PrecedesAt state provider consumer)
    (consumerBound : order.rank consumer ≤ order.rank provider) : False :=
  Nat.not_lt_of_ge consumerBound (order.increases edge)

/-! ## Conditional no-deadlock theorem -/

/-- Some actual lifecycle constructor is applicable at the current state. -/
def LifecycleApplicable
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics)
    (state : State catalog Ambient) : Prop :=
  ∃ after, Nonempty (Transition dynamics inertia state after)

private theorem reloading_applicable
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {state : State catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    {code : sig.IteratorCode} {undos : List (UndoCode sig)}
    {committed : CommittedView (catalog.declaration fiber.component)}
    (present : state.registry name = some fiber)
    (phase : fiber.phase = .reloading code undos committed)
    (ready : ReloadingReadyAt dynamics state name fiber code) :
    LifecycleApplicable dynamics inertia state := by
  obtain ⟨program, ownerEq, _rootAligned, reachable, executionReady⟩ := ready
  subst name
  rcases executionReady with ⟨landing, _programWitness⟩ | ⟨error, raised⟩
  · by_cases target : targetView state program.owner fiber = some committed
    · cases nextEq : landing.step.next with
      | none =>
          exact ⟨_, ⟨.finish state program.owner fiber present code undos committed phase
            target landing nextEq⟩⟩
      | some next =>
          exact ⟨_, ⟨.iter state program.owner fiber present code undos committed phase
            target landing next nextEq⟩⟩
    · exact ⟨_, ⟨.divertLand state program.owner fiber present code undos committed phase
        target landing⟩⟩
  · exact ⟨_, ⟨.raise state program.owner fiber present code undos committed phase
      error raised⟩⟩

private def IsUnloadingName
    (state : State catalog Ambient) (name : sig.Name) : Prop :=
  ∃ fiber undos committed outcome,
    state.registry name = some fiber ∧
      fiber.phase = .unloading undos committed outcome

/-- Corrected state-local no-deadlock result; this is not quantitative termination. -/
theorem lifecycle_progress
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {state : State catalog Ambient}
    (wf : WellFormed state) (laws : LocalProgressLaws dynamics state)
    (notQuiet : ¬Quiescent state) :
    LifecycleApplicable dynamics inertia state := by
  classical
  apply Classical.byContradiction
  intro noApplicable
  have reject {after : State catalog Ambient}
      (transition : Transition dynamics inertia state after) : False :=
    noApplicable ⟨after, ⟨transition⟩⟩
  have noUnloading : ¬∃ name, IsUnloadingName state name := by
    rintro ⟨first, firstUnloading⟩
    have firstMember : first ∈ laws.precedence.names := by
      obtain ⟨fiber, undos, committed, outcome, present, phase⟩ := firstUnloading
      exact laws.precedence.covers first fiber present
    obtain ⟨maximal, maximalMember, maximalUnloading, maximalBound⟩ :=
      laws.precedence.exists_rank_maximal (IsUnloadingName state)
        ⟨first, firstMember, firstUnloading⟩
    obtain ⟨maximalFiber, maximalUndos, maximalCommitted, maximalOutcome,
      maximalPresent, maximalPhase⟩ := maximalUnloading
    by_cases notRelied : ¬Relied state maximal
    · obtain ⟨admission⟩ := laws.recovery wf maximalPresent maximalPhase notRelied
      exact reject (.unload state maximal maximalFiber maximalPresent maximalUndos
        maximalCommitted maximalOutcome maximalPhase notRelied admission)
    · have relied : Relied state maximal := Classical.not_not.mp notRelied
      obtain ⟨consumerName, consumer, consumerPresent, consumerDifferent,
        consumerInstalled, resolvedCommitted, resolvedCommittedEq, declared,
        providerEq⟩ := relied
      have providerAtMaximal : state.registry maximal = some maximalFiber := maximalPresent
      have providerAtCommitted :
          state.registry (resolvedCommitted.provider declared) = some maximalFiber := by
        rw [providerEq]
        exact providerAtMaximal
      have targetChanged := unloading_provider_changes_committed_target
        (consumerName := consumerName) (consumer := consumer) declared wf maximalPresent
          maximalPhase providerEq
      cases consumerPhase : consumer.phase with
      | inactive error =>
          change consumer.phase.Installed at consumerInstalled
          rw [consumerPhase] at consumerInstalled
          exact consumerInstalled
      | reloading code undos committed =>
          have committedSomeEq := resolvedCommittedEq
          rw [consumerPhase] at committedSomeEq
          change some committed = some resolvedCommitted at committedSomeEq
          have committedEq : committed = resolvedCommitted := Option.some.inj committedSomeEq
          subst resolvedCommitted
          have ready := laws.reloading_ready consumerPresent consumerPhase
          exact noApplicable (reloading_applicable consumerPresent consumerPhase ready)
      | active undos committed =>
          have committedSomeEq := resolvedCommittedEq
          rw [consumerPhase] at committedSomeEq
          change some committed = some resolvedCommitted at committedSomeEq
          have committedEq : committed = resolvedCommitted := Option.some.inj committedSomeEq
          subst resolvedCommitted
          exact reject (.leave state consumerName consumer consumerPresent undos committed
            consumerPhase targetChanged)
      | unloading undos committed outcome =>
          have consumerIsUnloading : IsUnloadingName state consumerName :=
            ⟨consumer, undos, committed, outcome, consumerPresent, consumerPhase⟩
          have consumerMember := laws.precedence.covers consumerName consumer consumerPresent
          have consumerBound := maximalBound consumerName consumerMember consumerIsUnloading
          have provided := laws.committed_sound consumerName consumer resolvedCommitted declared
            maximalFiber consumerPresent resolvedCommittedEq providerAtCommitted
          have edge : PrecedesAt state maximal consumerName :=
            ⟨maximalFiber, consumer, declared.key, maximalPresent, consumerPresent,
              provided, declared.declared⟩
          exact laws.precedence.successor_not_maximal edge consumerBound
  have quiet : Quiescent state := by
    intro name fiber present
    cases phaseEq : fiber.phase with
    | inactive outcome =>
        cases outcome with
        | some error => exact Or.inl rfl
        | none =>
            right
            cases targetEq : targetView state name fiber with
            | none => rfl
            | some committed =>
                exact False.elim (reject (.begin state name fiber present phaseEq committed
                  targetEq))
    | reloading code undos committed =>
        have ready := laws.reloading_ready present phaseEq
        exact False.elim (noApplicable (reloading_applicable present phaseEq ready))
    | active undos committed =>
        apply Classical.byContradiction
        intro targetChanged
        exact reject (.leave state name fiber present undos committed phaseEq targetChanged)
    | unloading undos committed outcome =>
        exact False.elim (noUnloading ⟨name, fiber, undos, committed, outcome,
          present, phaseEq⟩)
  exact notQuiet quiet

/-! ## Positive finite evidence -/


/-! ## One-fiber finite precedence and state-local progress -/

namespace BeginExample

open Cordis.GlobalActivationTransposition.Example.BeginPairs

abbrev state := beginOrigin

theorem lookup_cases {name : Bool} {fiber : Fiber exampleCatalog}
    (present : state.registry name = some fiber) :
    (name = false ∧ fiber = inactiveFiber 0) ∨
      (name = true ∧ fiber = inactiveFiber 1) := by
  cases name <;> simp_all [state]

def precedence : FinitePrecedenceRank state where
  names := [false, true]
  nodup := by simp
  covers := by
    intro name fiber present
    cases name <;> simp
  rank
    | false => 0
    | true => 1
  increases := by
    rintro provider consumer ⟨providerFiber, consumerFiber, key, providerPresent,
      consumerPresent, providerKey, consumerKey⟩
    cases provider <;> cases consumer <;>
      simp_all [Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration]

theorem precedence_wellFounded : WellFounded (PrecedesAt state) :=
  precedence.wellFounded

theorem precedence_acyclic (name : Bool) :
    ¬Relation.TransGen (PrecedesAt state) name name :=
  precedence.no_transGen_self name

theorem true_rank_maximal :
    ∀ name fiber, state.registry name = some fiber →
      precedence.rank name ≤ precedence.rank true := by
  intro name fiber present
  cases name <;> simp [precedence]

theorem no_precedence_successor :
    ¬∃ successor, PrecedesAt state true successor := by
  rintro ⟨successor, edge⟩
  exact precedence.successor_not_maximal edge (by
    cases successor <;> simp [precedence])

theorem committed_sound : CommittedProvisionSound state := by
  intro consumerName consumer committed declared providerFiber consumerPresent
    committedEq providerPresent
  rcases declared with ⟨key, required⟩
  cases consumerName <;>
    simp [state, inactiveFiber,
      Cordis.GlobalLandingTransposition.YieldSyntaxGap.declaration] at consumerPresent <;>
    subst consumer <;>
    simp [Phase.committed?] at committedEq

def reloading_ready
    {name fiber code undos committed}
    (present : state.registry name = some fiber)
    (phase : fiber.phase = .reloading code undos committed) :
    ReloadingReadyAt dynamics state name fiber code := by
  cases name <;> simp [state] at present <;> subst fiber <;>
    simp [inactiveFiber] at phase

theorem recovery_ready : RecoveryReadyAt dynamics state := by
  intro owner fiber undos committed outcome wf present phase notRelied
  cases owner <;> simp [state] at present <;> subst fiber <;>
    simp [inactiveFiber] at phase

def laws : LocalProgressLaws dynamics state where
  precedence := precedence
  committed_sound := committed_sound
  reloading_ready := reloading_ready
  recovery := recovery_ready

theorem not_quiescent : ¬Quiescent state := by
  intro quiet
  have leftQuiet := quiet false (inactiveFiber 0) begin_left_present
  have targetNone := leftQuiet.resolve_left (by simp)
  rw [begin_left_target] at targetNone
  cases targetNone

theorem progress : LifecycleApplicable dynamics inertia state :=
  lifecycle_progress beginOrigin_wellFormed laws not_quiescent

def explicitTransition : Transition dynamics inertia state beginLeft.after :=
  beginLeft.transition inertia

def executableRule : Rule := explicitTransition.rule

def executableSourcePhase : Bool :=
  match (inactiveFiber 0).phase with
  | .inactive none => true
  | _ => false

theorem executableRule_eq : executableRule = .begin := rfl

theorem executableSourcePhase_eq : executableSourcePhase = true := rfl

theorem explicitTransition_witnesses_progress :
    LifecycleApplicable dynamics inertia state :=
  ⟨beginLeft.after, ⟨explicitTransition⟩⟩

end BeginExample

/-! ## Program-wide totality deriving exact occurrence readiness -/

namespace OracleExample

open Cordis.GlobalLandingTransposition.Example

abbrev selectedProgram := leftProgram

theorem oracleTotal : OracleTotal selectedProgram where
  admits := by
    intro code state request reachable runEq
    cases code
    cases lookup : state.registry selectedProgram.owner with
    | none => simp [Cordis.GlobalLandingTransposition.Example.dynamics,
        Cordis.GlobalLandingTransposition.Example.runIterator, lookup] at runEq
    | some fiber =>
        simp [Cordis.GlobalLandingTransposition.Example.dynamics,
          Cordis.GlobalLandingTransposition.Example.runIterator, lookup] at runEq

theorem total : LandingOrRaiseTotal selectedProgram :=
  oracleTotal.toLandingOrRaiseTotal

theorem origin_ready :
    LandingOrRaiseAt selectedProgram () origin (reloadingFiber 0) :=
  total.ready Cordis.GlobalIteratorIndependence.Reach.root left_present

theorem concrete_landing :
    ∃ landing : Landing dynamics selectedProgram.owner () origin (reloadingFiber 0),
      LandingProgramWitness selectedProgram landing :=
  ⟨leftLanding, leftActivation.program_witness⟩

end OracleExample
