import Cordis.GlobalDynamics

/-!
# Phase-indexed global lifecycle rules

This module adds the seven lifecycle rule names of paper Sections 4.3.1--4.3.4 on top of the
external iterator semantics in `GlobalDynamics`: L-Begin, L-Iter, L-Finish, L-Divert, L-Raise,
L-Leave, and L-Unload. L-Divert has distinct aborting and landing alternatives, so the intrinsic
relation has eight constructors. It does not add O-Insert/O-Retire/O-Remove to the same relation,
so it does not claim the paper's full ten-rule Definition 53 calculus or Theorem 59.

Target stability and mismatch are exact equalities against the committed view. Iterator-landing
rules consume a proof-carrying `IterationStep`; newly yielded undo codes are prepended to the
newest-first accumulator. Aborting diversion requires an explicit `InertiaPolicy` witness, while a
landing diversion is always permitted.

L-Unload is the only edge that interprets the whole accumulated recovery list. Global temporal
composability has not yet shown that recovery remains valid after arbitrary interleaving, so this
edge consumes a named `RecoveryAdmission` containing the recovered owner, inactive successor,
and global well-formedness preservation. Nothing is hidden behind trusted recursion or an
unproved scheduler convention.

The external registration-admission error type remains distinct from the iterator's structured
error type. This bounded relation intentionally has no edge for an iterator that returns a
registration request whose oracle then rejects it: such a failure is neither an L-Raise iterator
error nor a successful landing, and a later integration layer must choose its lifecycle policy.
-/

set_option autoImplicit false

namespace Cordis.GlobalLifecycle

open Cordis.GlobalRegistry Cordis.GlobalDynamics

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-- Replace exactly one registered fiber's phase. -/
def setPhase
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) : State catalog Ambient := {
  state with registry := Coeffect.setAt state.registry name { fiber with phase := phase }
}

@[simp] theorem setPhase_lookup_same
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) :
    (setPhase state name fiber phase).registry name = some { fiber with phase := phase } := by
  simp [setPhase]

@[simp] theorem setPhase_lookup_other
    (state : State catalog Ambient) (name other : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) (different : other ≠ name) :
    (setPhase state name fiber phase).registry other = state.registry other := by
  simp [setPhase, Coeffect.setAt_other, different]

@[simp] theorem setPhase_nextBirth
    (state : State catalog Ambient) (name : sig.Name) (fiber : Fiber catalog)
    (phase : Phase (catalog.declaration fiber.component)) :
    (setPhase state name fiber phase).nextBirth = state.nextBirth := rfl

/-- Every provider named by one committed view is currently registered and installed. -/
def ViewSafe
    (state : State catalog Ambient) {decl : ComponentDecl sig}
    (view : CommittedView decl) : Prop :=
  ∀ declared, ∃ providerFiber,
    state.registry (view.provider declared) = some providerFiber ∧ providerFiber.Installed

/-- A target view is safe because each of its bindings resolves to an active provider. -/
theorem isTargetView_viewSafe
    {state : State catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    {view : CommittedView (catalog.declaration fiber.component)}
    (target : IsTargetView state name fiber view) : ViewSafe state view := by
  intro declared
  obtain ⟨providerFiber, lookup, active, present⟩ := target.resolves_active declared
  refine ⟨providerFiber, lookup, ?_⟩
  change providerFiber.phase.Active at active
  change providerFiber.phase.Installed
  cases phase_eq : providerFiber.phase <;>
    simp_all [Phase.Active, Phase.Installed]

/-- Any committed view retained by a well-formed state resolves to installed providers. -/
theorem wellFormed_viewSafe
    {state : State catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    {committed : CommittedView (catalog.declaration fiber.component)}
    (wf : WellFormed state) (present : state.registry name = some fiber)
    (committed_eq : fiber.phase.committed? = some committed) :
    ViewSafe state committed := by
  intro declared
  obtain ⟨providerFiber, providerLookup⟩ :=
    wf.committed_provider_present name fiber present committed committed_eq declared
  exact ⟨providerFiber, providerLookup,
    wf.committed_provider_installed name fiber present committed committed_eq
      declared providerFiber providerLookup⟩

/-- Updating to an installed, provider-safe phase preserves the global registry invariant. -/
theorem setPhase_installed_preserves
    {state : State catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    (present : state.registry name = some fiber)
    (next : Phase (catalog.declaration fiber.component))
    (nextInstalled : next.Installed)
    (nextSafe : ∀ committed, next.committed? = some committed → ViewSafe state committed)
    (wf : WellFormed state) : WellFormed (setPhase state name fiber next) := by
  classical
  let updated : Fiber catalog := { fiber with phase := next }
  constructor
  · intro candidate current lookup
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      exact wf.birth_bounded name fiber present
    · rw [setPhase_lookup_other state name candidate fiber next same] at lookup
      exact wf.birth_bounded candidate current lookup
  · intro candidate current parent lookup parent_eq
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      obtain ⟨parentFiber, parentLookup⟩ :=
        wf.parent_present name fiber parent present parent_eq
      by_cases parentSame : parent = name
      · subst parent
        exact ⟨updated, setPhase_lookup_same state name fiber next⟩
      · exact ⟨parentFiber, by
          simpa [setPhase_lookup_other, parentSame] using parentLookup⟩
    · rw [setPhase_lookup_other state name candidate fiber next same] at lookup
      obtain ⟨parentFiber, parentLookup⟩ :=
        wf.parent_present candidate current parent lookup parent_eq
      by_cases parentSame : parent = name
      · subst parent
        exact ⟨updated, setPhase_lookup_same state name fiber next⟩
      · exact ⟨parentFiber, by
          simpa [setPhase_lookup_other, parentSame] using parentLookup⟩
  · intro candidate current parent parentFiber lookup parent_eq parentLookup
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      by_cases parentSame : parent = name
      · subst parent
        rw [setPhase_lookup_same] at parentLookup
        have parentFiber_eq : updated = parentFiber := Option.some.inj parentLookup
        subst parentFiber
        exact wf.parent_older name fiber name fiber present parent_eq present
      · rw [setPhase_lookup_other state name parent fiber next parentSame] at parentLookup
        exact wf.parent_older name fiber parent parentFiber present parent_eq parentLookup
    · rw [setPhase_lookup_other state name candidate fiber next same] at lookup
      by_cases parentSame : parent = name
      · subst parent
        rw [setPhase_lookup_same] at parentLookup
        have parentFiber_eq : updated = parentFiber := Option.some.inj parentLookup
        subst parentFiber
        simpa [updated] using wf.parent_older candidate current name fiber
          lookup parent_eq present
      · rw [setPhase_lookup_other state name parent fiber next parentSame] at parentLookup
        exact wf.parent_older candidate current parent parentFiber lookup parent_eq parentLookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    by_cases leftSame : left = name
    · subst left
      rw [setPhase_lookup_same] at leftLookup
      have leftFiber_eq : updated = leftFiber := Option.some.inj leftLookup
      subst leftFiber
      by_cases rightSame : right = name
      · exact rightSame.symm
      · rw [setPhase_lookup_other state name right fiber next rightSame] at rightLookup
        simpa [updated] using wf.provisions_unique name fiber right rightFiber key
          present rightLookup leftKey rightKey
    · rw [setPhase_lookup_other state name left fiber next leftSame] at leftLookup
      by_cases rightSame : right = name
      · subst right
        rw [setPhase_lookup_same] at rightLookup
        have rightFiber_eq : updated = rightFiber := Option.some.inj rightLookup
        subst rightFiber
        simpa [updated] using wf.provisions_unique left leftFiber name fiber key
          leftLookup present leftKey rightKey
      · rw [setPhase_lookup_other state name right fiber next rightSame] at rightLookup
        exact wf.provisions_unique left leftFiber right rightFiber key
          leftLookup rightLookup leftKey rightKey
  · intro candidate current lookup committed committed_eq declared
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      obtain ⟨providerFiber, providerLookup, providerInstalled⟩ :=
        nextSafe committed committed_eq declared
      by_cases providerSame : committed.provider declared = name
      · exact ⟨updated, by
          rw [providerSame]
          exact setPhase_lookup_same state name fiber next⟩
      · exact ⟨providerFiber, by
          simpa [setPhase_lookup_other, providerSame] using providerLookup⟩
    · rw [setPhase_lookup_other state name candidate fiber next same] at lookup
      obtain ⟨providerFiber, providerLookup⟩ :=
        wf.committed_provider_present candidate current lookup committed committed_eq declared
      by_cases providerSame : committed.provider declared = name
      · exact ⟨updated, by
          rw [providerSame]
          exact setPhase_lookup_same state name fiber next⟩
      · exact ⟨providerFiber, by
          simpa [setPhase_lookup_other, providerSame] using providerLookup⟩
  · intro candidate current lookup committed committed_eq declared providerFiber providerLookup
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      by_cases providerSame : committed.provider declared = name
      · rw [providerSame, setPhase_lookup_same] at providerLookup
        have providerFiber_eq : updated = providerFiber := Option.some.inj providerLookup
        subst providerFiber
        exact nextInstalled
      · rw [setPhase_lookup_other state name (committed.provider declared) fiber next
          providerSame] at providerLookup
        obtain ⟨safeFiber, safeLookup, safeInstalled⟩ :=
          nextSafe committed committed_eq declared
        rw [providerLookup] at safeLookup
        have safeFiber_eq : providerFiber = safeFiber := Option.some.inj safeLookup
        simpa [safeFiber_eq] using safeInstalled
    · rw [setPhase_lookup_other state name candidate fiber next same] at lookup
      by_cases providerSame : committed.provider declared = name
      · rw [providerSame, setPhase_lookup_same] at providerLookup
        have providerFiber_eq : updated = providerFiber := Option.some.inj providerLookup
        subst providerFiber
        exact nextInstalled
      · rw [setPhase_lookup_other state name (committed.provider declared) fiber next
          providerSame] at providerLookup
        exact wf.committed_provider_installed candidate current lookup committed committed_eq
          declared providerFiber providerLookup

/-- Deactivating an unrelied fiber preserves all committed-provider obligations. -/
theorem setPhase_inactive_preserves
    {state : State catalog Ambient} {name : sig.Name} {fiber : Fiber catalog}
    (present : state.registry name = some fiber) (outcome : Option sig.Error)
    (notRelied : ¬Relied state name) (wf : WellFormed state) :
    WellFormed (setPhase state name fiber (.inactive outcome)) := by
  classical
  let updated : Fiber catalog := { fiber with phase := .inactive outcome }
  constructor
  · intro candidate current lookup
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      exact wf.birth_bounded name fiber present
    · rw [setPhase_lookup_other state name candidate fiber (.inactive outcome) same] at lookup
      exact wf.birth_bounded candidate current lookup
  · intro candidate current parent lookup parent_eq
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      obtain ⟨parentFiber, parentLookup⟩ :=
        wf.parent_present name fiber parent present parent_eq
      by_cases parentSame : parent = name
      · subst parent
        exact ⟨updated, setPhase_lookup_same state name fiber (.inactive outcome)⟩
      · exact ⟨parentFiber, by
          simpa [setPhase_lookup_other, parentSame] using parentLookup⟩
    · rw [setPhase_lookup_other state name candidate fiber (.inactive outcome) same] at lookup
      obtain ⟨parentFiber, parentLookup⟩ :=
        wf.parent_present candidate current parent lookup parent_eq
      by_cases parentSame : parent = name
      · subst parent
        exact ⟨updated, setPhase_lookup_same state name fiber (.inactive outcome)⟩
      · exact ⟨parentFiber, by
          simpa [setPhase_lookup_other, parentSame] using parentLookup⟩
  · intro candidate current parent parentFiber lookup parent_eq parentLookup
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      by_cases parentSame : parent = name
      · subst parent
        rw [setPhase_lookup_same] at parentLookup
        have parentFiber_eq : updated = parentFiber := Option.some.inj parentLookup
        subst parentFiber
        exact wf.parent_older name fiber name fiber present parent_eq present
      · rw [setPhase_lookup_other state name parent fiber (.inactive outcome)
          parentSame] at parentLookup
        exact wf.parent_older name fiber parent parentFiber present parent_eq parentLookup
    · rw [setPhase_lookup_other state name candidate fiber (.inactive outcome) same] at lookup
      by_cases parentSame : parent = name
      · subst parent
        rw [setPhase_lookup_same] at parentLookup
        have parentFiber_eq : updated = parentFiber := Option.some.inj parentLookup
        subst parentFiber
        simpa [updated] using wf.parent_older candidate current name fiber
          lookup parent_eq present
      · rw [setPhase_lookup_other state name parent fiber (.inactive outcome)
          parentSame] at parentLookup
        exact wf.parent_older candidate current parent parentFiber lookup parent_eq parentLookup
  · intro left leftFiber right rightFiber key leftLookup rightLookup leftKey rightKey
    by_cases leftSame : left = name
    · subst left
      rw [setPhase_lookup_same] at leftLookup
      have leftFiber_eq : updated = leftFiber := Option.some.inj leftLookup
      subst leftFiber
      by_cases rightSame : right = name
      · exact rightSame.symm
      · rw [setPhase_lookup_other state name right fiber (.inactive outcome)
          rightSame] at rightLookup
        simpa [updated] using wf.provisions_unique name fiber right rightFiber key
          present rightLookup leftKey rightKey
    · rw [setPhase_lookup_other state name left fiber (.inactive outcome)
        leftSame] at leftLookup
      by_cases rightSame : right = name
      · subst right
        rw [setPhase_lookup_same] at rightLookup
        have rightFiber_eq : updated = rightFiber := Option.some.inj rightLookup
        subst rightFiber
        simpa [updated] using wf.provisions_unique left leftFiber name fiber key
          leftLookup present leftKey rightKey
      · rw [setPhase_lookup_other state name right fiber (.inactive outcome)
          rightSame] at rightLookup
        exact wf.provisions_unique left leftFiber right rightFiber key
          leftLookup rightLookup leftKey rightKey
  · intro candidate current lookup committed committed_eq declared
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      simp [updated, Phase.committed?] at committed_eq
    · rw [setPhase_lookup_other state name candidate fiber (.inactive outcome) same] at lookup
      obtain ⟨providerFiber, providerLookup⟩ :=
        wf.committed_provider_present candidate current lookup committed committed_eq declared
      by_cases providerSame : committed.provider declared = name
      · exact ⟨updated, by
          rw [providerSame]
          exact setPhase_lookup_same state name fiber (.inactive outcome)⟩
      · exact ⟨providerFiber, by
          simpa [setPhase_lookup_other, providerSame] using providerLookup⟩
  · intro candidate current lookup committed committed_eq declared providerFiber providerLookup
    by_cases same : candidate = name
    · subst candidate
      rw [setPhase_lookup_same] at lookup
      have current_eq : updated = current := Option.some.inj lookup
      subst current
      simp [updated, Phase.committed?] at committed_eq
    · rw [setPhase_lookup_other state name candidate fiber (.inactive outcome) same] at lookup
      by_cases providerSame : committed.provider declared = name
      · exact False.elim <| notRelied ⟨candidate, current, lookup, same,
          Phase.installed_of_committed_some committed_eq,
          ⟨committed, committed_eq, declared, providerSame⟩⟩
      · rw [setPhase_lookup_other state name (committed.provider declared) fiber
          (.inactive outcome) providerSame] at providerLookup
        exact wf.committed_provider_installed candidate current lookup committed committed_eq
          declared providerFiber providerLookup

/-! ## Iterator landing and asynchronous policy -/

/-- One proof-carrying iterator step plus the exact owner retained at its successor. -/
structure Landing
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (beforeFiber : Fiber catalog) where
  RegistrationError : Type u
  oracle : RegistrationOracle dynamics owner RegistrationError
  step : IterationStep dynamics owner code before
  executed : executeOne dynamics oracle code before = .ok step
  before_present : before.registry owner = some beforeFiber
  afterFiber : Fiber catalog
  after_present : step.after.registry owner = some afterFiber
  component_eq : afterFiber.component = beforeFiber.component
  phase_eq : component_eq ▸ afterFiber.phase = beforeFiber.phase

namespace Landing

private theorem committed_transport
    {left right : sig.ComponentId} (component_eq : left = right)
    (leftPhase : Phase (catalog.declaration left))
    (rightPhase : Phase (catalog.declaration right))
    (phase_eq : component_eq ▸ leftPhase = rightPhase)
    {committed : CommittedView (catalog.declaration right)}
    (committed_eq : rightPhase.committed? = some committed) :
    leftPhase.committed? = some (component_eq.symm ▸ committed) := by
  cases component_eq
  subst rightPhase
  exact committed_eq

/-- A landing retains the owner's committed view, so successor well-formedness makes it safe. -/
theorem committedSafe
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    {beforeFiber : Fiber catalog}
    (landing : Landing dynamics owner code before beforeFiber)
    (wf : WellFormed landing.step.after)
    {committed : CommittedView (catalog.declaration beforeFiber.component)}
    (committed_eq : beforeFiber.phase.committed? = some committed) :
    ViewSafe landing.step.after (landing.component_eq.symm ▸ committed) := by
  exact wellFormed_viewSafe wf landing.after_present
    (committed_transport landing.component_eq landing.afterFiber.phase beforeFiber.phase
      landing.phase_eq committed_eq)

end Landing

/-- Explicit host policy for whether a launched iteration may be aborted before landing. -/
structure InertiaPolicy
    (dynamics : Dynamics sig catalog Ambient) where
  canAbort : sig.Name → sig.IteratorCode → State catalog Ambient → Prop

/-! ## Recovery admission for L-Unload -/

/-- Named evidence needed until global temporal composability proves accumulated recovery safe. -/
structure RecoveryAdmission
    (dynamics : Dynamics sig catalog Ambient)
    (before : State catalog Ambient) (owner : sig.Name)
    (fiber : Fiber catalog) (undos : List (UndoCode sig))
    (outcome : Option sig.Error) where
  before_present : before.registry owner = some fiber
  recoveredFiber : Fiber catalog
  recovered_present : (dynamics.recover undos before).registry owner = some recoveredFiber
  component_eq : recoveredFiber.component = fiber.component
  after : State catalog Ambient
  after_eq : after = setPhase (dynamics.recover undos before) owner recoveredFiber
    (component_eq ▸ Phase.inactive outcome)
  preserves_wellFormed : WellFormed before → WellFormed after

/-! ## Lifecycle relation -/

inductive Rule where
  | begin
  | iter
  | finish
  | divertAbort
  | divertLand
  | raise
  | leave
  | unload
  deriving DecidableEq, Repr

/-- The state-map source used before the mandatory owner-phase rewrite. -/
inductive MapKind where
  | identity
  | iterator
  | accumulatedRecovery
  deriving DecidableEq, Repr

/-- All lifecycle rules, intrinsically indexed by exact global endpoints. -/
inductive Transition
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    State catalog Ambient → State catalog Ambient → Type (u + 1) where
  | begin
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (entry : fiber.phase = .inactive none)
      (committed : CommittedView (catalog.declaration fiber.component))
      (target : targetView before owner fiber = some committed) :
      Transition dynamics inertia before
        (setPhase before owner fiber (.reloading
          (catalog.declaration fiber.component).entry [] committed))
  | iter
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (target : targetView before owner fiber = some committed)
      (landing : Landing dynamics owner code before fiber)
      (next : sig.IteratorCode) (continues : landing.step.next = some next) :
      Transition dynamics inertia before
        (setPhase landing.step.after owner landing.afterFiber
          (.reloading next (landing.step.undo :: undos)
            (landing.component_eq.symm ▸ committed)))
  | finish
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (target : targetView before owner fiber = some committed)
      (landing : Landing dynamics owner code before fiber)
      (done : landing.step.next = none) :
      Transition dynamics inertia before
        (setPhase landing.step.after owner landing.afterFiber
          (.active (landing.step.undo :: undos)
            (landing.component_eq.symm ▸ committed)))
  | divertAbort
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (targetChanged : targetView before owner fiber ≠ some committed)
      (abortable : inertia.canAbort owner code before) :
      Transition dynamics inertia before
        (setPhase before owner fiber (.unloading undos committed none))
  | divertLand
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (targetChanged : targetView before owner fiber ≠ some committed)
      (landing : Landing dynamics owner code before fiber) :
      Transition dynamics inertia before
        (setPhase landing.step.after owner landing.afterFiber
          (.unloading (landing.step.undo :: undos)
            (landing.component_eq.symm ▸ committed) none))
  | raise
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (code : sig.IteratorCode) (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .reloading code undos committed)
      (error : sig.Error)
      (raised : dynamics.runIterator owner code before = .error error) :
      Transition dynamics inertia before
        (setPhase before owner fiber (.unloading undos committed (some error)))
  | leave
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (phase : fiber.phase = .active undos committed)
      (targetChanged : targetView before owner fiber ≠ some committed) :
      Transition dynamics inertia before
        (setPhase before owner fiber (.unloading undos committed none))
  | unload
      (before : State catalog Ambient) (owner : sig.Name) (fiber : Fiber catalog)
      (present : before.registry owner = some fiber)
      (undos : List (UndoCode sig))
      (committed : CommittedView (catalog.declaration fiber.component))
      (outcome : Option sig.Error)
      (phase : fiber.phase = .unloading undos committed outcome)
      (notRelied : ¬Relied before owner)
      (admission : RecoveryAdmission dynamics before owner fiber undos outcome) :
      Transition dynamics inertia before admission.after

namespace Transition

def rule
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} : Transition dynamics inertia before after → Rule
  | .begin .. => .begin
  | .iter .. => .iter
  | .finish .. => .finish
  | .divertAbort .. => .divertAbort
  | .divertLand .. => .divertLand
  | .raise .. => .raise
  | .leave .. => .leave
  | .unload .. => .unload

def mapKind
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient} : Transition dynamics inertia before after → MapKind
  | .iter .. => .iterator
  | .finish .. => .iterator
  | .divertLand .. => .iterator
  | .unload .. => .accumulatedRecovery
  | _ => .identity

/-- Every admitted lifecycle edge preserves the strengthened global registry invariant. -/
theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    WellFormed before → WellFormed after := by
  intro wf
  cases transition with
  | begin owner fiber present entry committed target =>
      apply setPhase_installed_preserves present _ (by simp [Phase.Installed]) _ wf
      intro candidate candidate_eq
      have candidate_eq_committed : candidate = committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact isTargetView_viewSafe (targetView_sound wf target)
  | iter owner fiber present code undos committed phase target landing next continues =>
      have landedWf : WellFormed landing.step.after := landing.step.preservesWellFormed wf
      have sourceCommitted : fiber.phase.committed? = some committed := by
        rw [phase]
        rfl
      have landedSafe :
          ViewSafe landing.step.after (landing.component_eq.symm ▸ committed) :=
        landing.committedSafe landedWf sourceCommitted
      apply setPhase_installed_preserves landing.after_present _
        (by simp [Phase.Installed]) _ landedWf
      intro candidate candidate_eq
      have candidate_eq_committed :
          candidate = landing.component_eq.symm ▸ committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact landedSafe
  | finish owner fiber present code undos committed phase target landing done =>
      have landedWf : WellFormed landing.step.after := landing.step.preservesWellFormed wf
      have sourceCommitted : fiber.phase.committed? = some committed := by
        rw [phase]
        rfl
      have landedSafe :
          ViewSafe landing.step.after (landing.component_eq.symm ▸ committed) :=
        landing.committedSafe landedWf sourceCommitted
      apply setPhase_installed_preserves landing.after_present _
        (by simp [Phase.Installed]) _ landedWf
      intro candidate candidate_eq
      have candidate_eq_committed :
          candidate = landing.component_eq.symm ▸ committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact landedSafe
  | divertAbort owner fiber present code undos committed phase targetChanged abortable =>
      have sourceCommitted : fiber.phase.committed? = some committed := by
        rw [phase]
        rfl
      have safe : ViewSafe before committed :=
        wellFormed_viewSafe wf present sourceCommitted
      apply setPhase_installed_preserves present _ (by simp [Phase.Installed]) _ wf
      intro candidate candidate_eq
      have candidate_eq_committed : candidate = committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact safe
  | divertLand owner fiber present code undos committed phase targetChanged landing =>
      have landedWf : WellFormed landing.step.after := landing.step.preservesWellFormed wf
      have sourceCommitted : fiber.phase.committed? = some committed := by
        rw [phase]
        rfl
      have landedSafe :
          ViewSafe landing.step.after (landing.component_eq.symm ▸ committed) :=
        landing.committedSafe landedWf sourceCommitted
      apply setPhase_installed_preserves landing.after_present _
        (by simp [Phase.Installed]) _ landedWf
      intro candidate candidate_eq
      have candidate_eq_committed :
          candidate = landing.component_eq.symm ▸ committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact landedSafe
  | raise owner fiber present code undos committed phase error raised =>
      have sourceCommitted : fiber.phase.committed? = some committed := by
        rw [phase]
        rfl
      have safe : ViewSafe before committed :=
        wellFormed_viewSafe wf present sourceCommitted
      apply setPhase_installed_preserves present _ (by simp [Phase.Installed]) _ wf
      intro candidate candidate_eq
      have candidate_eq_committed : candidate = committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact safe
  | leave owner fiber present undos committed phase targetChanged =>
      have sourceCommitted : fiber.phase.committed? = some committed := by
        rw [phase]
        rfl
      have safe : ViewSafe before committed :=
        wellFormed_viewSafe wf present sourceCommitted
      apply setPhase_installed_preserves present _ (by simp [Phase.Installed]) _ wf
      intro candidate candidate_eq
      have candidate_eq_committed : candidate = committed := by
        simpa [Phase.committed?] using (Option.some.inj candidate_eq).symm
      subst candidate
      exact safe
  | unload owner fiber present undos committed outcome phase notRelied admission =>
      exact admission.preserves_wellFormed wf

/-- The eight constructors are the complete rule inventory of this bounded relation. -/
theorem rule_inventory
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    transition.rule = .begin ∨ transition.rule = .iter ∨
    transition.rule = .finish ∨ transition.rule = .divertAbort ∨
    transition.rule = .divertLand ∨ transition.rule = .raise ∨
    transition.rule = .leave ∨ transition.rule = .unload := by
  cases transition <;> simp [rule]

/-- Exactly the landing rules expose an external iterator-state write footprint. -/
theorem iterator_map_iff
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    transition.mapKind = .iterator ↔
      transition.rule = .iter ∨ transition.rule = .finish ∨
      transition.rule = .divertLand := by
  cases transition <;> simp [mapKind, rule]

/-- Exactly L-Unload interprets the accumulated recovery program. -/
theorem recovery_map_iff
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    transition.mapKind = .accumulatedRecovery ↔ transition.rule = .unload := by
  cases transition <;> simp [mapKind, rule]

/-- The four non-landing rules use the source state directly, then rewrite only the owner phase. -/
theorem identity_map_iff
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (transition : Transition dynamics inertia before after) :
    transition.mapKind = .identity ↔
      transition.rule = .begin ∨ transition.rule = .divertAbort ∨
      transition.rule = .raise ∨ transition.rule = .leave := by
  cases transition <;> simp [mapKind, rule]

end Transition

/-! ## Finite intrinsic lifecycle traces -/

/-- A finite lifecycle execution with exact start and endpoint indices. -/
inductive Trace
    (dynamics : Dynamics sig catalog Ambient) (inertia : InertiaPolicy dynamics) :
    State catalog Ambient → State catalog Ambient → Type (u + 1) where
  | nil (state : State catalog Ambient) : Trace dynamics inertia state state
  | cons
      {before middle after : State catalog Ambient}
      (head : Transition dynamics inertia before middle)
      (tail : Trace dynamics inertia middle after) :
      Trace dynamics inertia before after

namespace Trace

/-- Rule-by-rule preservation composes over exact finite lifecycle traces. -/
theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {inertia : InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (trace : Trace dynamics inertia before after) :
    WellFormed before → WellFormed after := by
  intro wf
  induction trace with
  | nil => exact wf
  | cons head tail ih => exact ih (head.preservesWellFormed wf)

end Trace

/-! ## Concrete heterogeneous lifecycle path -/

namespace Example

abbrev ExampleSig := Cordis.GlobalRegistry.Example.signature
abbrev exampleCatalog := Cordis.GlobalRegistry.Example.catalog
abbrev ExampleState := State exampleCatalog Nat

open Cordis.GlobalRegistry.Example

/-- Advance only the external ambient cell; the heterogeneous registry is unchanged. -/
def advance (before : ExampleState) : ExampleState := {
  before with ambient := before.ambient + 1
}

/-- Code `0` is the exact inverse emitted by both ordinary example iterations. -/
def applyExternalUndo : ExampleSig.ExternalUndoCode → ExampleState → ExampleState
  | 0, current => { current with ambient := current.ambient - 1 }
  | _ + 1, current => current

/-- Entry code `10` continues at `0`; code `0` then completes. -/
def runIterator (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) :
    Except ExampleSig.Error (IteratorResult exampleCatalog Nat) :=
  match before.registry owner with
  | none => .error "missing owner"
  | some _ =>
      if code = 10 then
        .ok (.ordinary { after := advance before, undo := 0, next := some 0 })
      else if code = 0 then
        .ok (.ordinary { after := advance before, undo := 0, next := none })
      else
        .error "unsupported iterator"

def stateSetoid : Setoid ExampleState where
  r := fun left right ↦ left.ambient = right.ambient
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

theorem advance_preserves
    {before : ExampleState} (wf : WellFormed before) : WellFormed (advance before) := {
  birth_bounded := wf.birth_bounded
  parent_present := wf.parent_present
  parent_older := wf.parent_older
  provisions_unique := wf.provisions_unique
  committed_provider_present := wf.committed_provider_present
  committed_provider_installed := wf.committed_provider_installed
}

theorem ordinary_recovers
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) (result : OrdinaryResult exampleCatalog Nat)
    (run_eq : runIterator owner code before = .ok (.ordinary result)) :
    applyExternalUndo result.undo result.after = before := by
  cases ownerLookup : before.registry owner with
  | none => simp [runIterator, ownerLookup] at run_eq
  | some ownerFiber =>
      by_cases first : code = 10
      · simp [runIterator, ownerLookup, first] at run_eq
        subst result
        cases before
        simp [advance, applyExternalUndo]
      · by_cases last : code = 0
        · simp [runIterator, ownerLookup, last] at run_eq
          subst result
          cases before
          simp [advance, applyExternalUndo]
        · simp [runIterator, ownerLookup, first, last] at run_eq

def ordinary_confined
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) (result : OrdinaryResult exampleCatalog Nat)
    (run_eq : runIterator owner code before = .ok (.ordinary result)) :
    OrdinaryConfinement before result.after owner := by
  cases ownerLookup : before.registry owner with
  | none => simp [runIterator, ownerLookup] at run_eq
  | some ownerFiber =>
      by_cases first : code = 10
      · simp [runIterator, ownerLookup, first] at run_eq
        subst result
        exact {
          beforeFiber := ownerFiber
          afterFiber := ownerFiber
          before_present := ownerLookup
          after_present := ownerLookup
          component_eq := rfl
          parent_eq := rfl
          birth_eq := rfl
          retired_eq := rfl
          phase_eq := rfl
          other_unchanged := by intros; rfl
          table_writes := by
            intro key outside
            rfl
          nextBirth_eq := rfl
        }
      · by_cases last : code = 0
        · simp [runIterator, ownerLookup, last] at run_eq
          subst result
          exact {
            beforeFiber := ownerFiber
            afterFiber := ownerFiber
            before_present := ownerLookup
            after_present := ownerLookup
            component_eq := rfl
            parent_eq := rfl
            birth_eq := rfl
            retired_eq := rfl
            phase_eq := rfl
            other_unchanged := by intros; rfl
            table_writes := by
              intro key outside
              rfl
            nextBirth_eq := rfl
          }
        · simp [runIterator, ownerLookup, first, last] at run_eq

theorem ordinary_preserves
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) (result : OrdinaryResult exampleCatalog Nat)
    (run_eq : runIterator owner code before = .ok (.ordinary result)) :
    WellFormed before → WellFormed result.after := by
  intro wf
  cases ownerLookup : before.registry owner with
  | none => simp [runIterator, ownerLookup] at run_eq
  | some ownerFiber =>
      by_cases first : code = 10
      · simp [runIterator, ownerLookup, first] at run_eq
        subst result
        exact advance_preserves wf
      · by_cases last : code = 0
        · simp [runIterator, ownerLookup, last] at run_eq
          subst result
          exact advance_preserves wf
        · simp [runIterator, ownerLookup, first, last] at run_eq

theorem externalUndo_respects
    (undo : ExampleSig.ExternalUndoCode) {left right : ExampleState}
    (related : stateSetoid.r left right) :
    stateSetoid.r (applyExternalUndo undo left) (applyExternalUndo undo right) := by
  cases undo with
  | zero => exact congrArg (fun value ↦ value - 1) related
  | succ => exact related

theorem run_respects
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    {left right : ExampleState} (leftFiber rightFiber : Fiber exampleCatalog)
    (related : stateSetoid.r left right)
    (leftPresent : left.registry owner = some leftFiber)
    (rightPresent : right.registry owner = some rightFiber) :
    RunRelated stateSetoid.r (runIterator owner code left) (runIterator owner code right) := by
  simp only [runIterator, leftPresent, rightPresent]
  by_cases first : code = 10
  · simp only [if_pos first]
    exact .results (.ordinary (congrArg (fun value ↦ value + 1) related) rfl rfl)
  · simp only [if_neg first]
    by_cases last : code = 0
    · simp only [if_pos last]
      exact .results (.ordinary (congrArg (fun value ↦ value + 1) related) rfl rfl)
    · simp only [if_neg last]
      exact .errors rfl

theorem retire_respects
    (name : ExampleSig.Name) {left right : ExampleState}
    (related : stateSetoid.r left right) :
    stateSetoid.r (retireByName left name) (retireByName right name) := by
  change left.ambient = right.ambient at related
  change (retireByName left name).ambient = (retireByName right name).ambient
  unfold retireByName
  split <;> split <;> simpa [retireFiber] using related

def dynamics : Dynamics ExampleSig exampleCatalog Nat where
  equivalence := stateSetoid
  runIterator := runIterator
  applyExternalUndo := applyExternalUndo
  ordinary_recovers := ordinary_recovers
  externalUndo_respects := externalUndo_respects
  ordinary_confined := ordinary_confined
  ordinary_preserves_wellFormed := ordinary_preserves
  run_respects := run_respects
  ReadEquivalent := fun _ left right ↦ left.ambient = right.ambient
  read_refl := fun _ _ ↦ rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact run_respects owner code leftFiber rightFiber related leftPresent rightPresent
  retire_respects := retire_respects

def oracle : RegistrationOracle dynamics 0 String where
  certify _ _ := .error "registration is outside this example path"

def inertia : InertiaPolicy dynamics where
  canAbort _ _ _ := False

def start : ExampleState := Cordis.GlobalDynamics.Example.start

theorem start_wellFormed : WellFormed start :=
  Cordis.GlobalDynamics.Example.start_wellFormed

def inactiveProvider : Fiber exampleCatalog where
  component := .provider
  parent := none
  birth := 0
  table := Coeffect.empty
  table_within_provision := by simp
  retired := false
  phase := .inactive none

theorem start_present : start.registry 0 = some inactiveProvider := rfl

theorem start_target :
    targetView start 0 inactiveProvider = some emptyProviderView := by
  apply targetView_eq_of_isTarget start_wellFormed
  exact {
    present := start_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

def beginState : ExampleState :=
  setPhase start 0 inactiveProvider (.reloading 10 [] emptyProviderView)

def beginTransition : Transition dynamics inertia start beginState :=
  .begin start 0 inactiveProvider start_present rfl emptyProviderView start_target

theorem beginState_wellFormed : WellFormed beginState :=
  beginTransition.preservesWellFormed start_wellFormed

def beginFiber : Fiber exampleCatalog := {
  inactiveProvider with phase := .reloading 10 [] emptyProviderView
}

theorem begin_present : beginState.registry 0 = some beginFiber := rfl

theorem begin_target :
    targetView beginState 0 beginFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget beginState_wellFormed
  exact {
    present := begin_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

def firstResult : OrdinaryResult exampleCatalog Nat where
  after := advance beginState
  undo := 0
  next := some 0

def firstStep : IterationStep dynamics 0 10 beginState where
  after := firstResult.after
  undo := .external firstResult.undo
  next := firstResult.next
  source := .ordinary firstResult rfl
  recovers := by
    change (applyExternalUndo 0 (advance beginState)).ambient = beginState.ambient
    rfl
  preserves_wellFormed := fun wf ↦ advance_preserves wf

theorem firstStep_executed :
    executeOne dynamics oracle 10 beginState = .ok firstStep := by
  rfl

def firstLanding : Landing dynamics 0 10 beginState beginFiber where
  RegistrationError := String
  oracle := oracle
  step := firstStep
  executed := firstStep_executed
  before_present := begin_present
  afterFiber := beginFiber
  after_present := begin_present
  component_eq := rfl
  phase_eq := rfl

def iterState : ExampleState :=
  setPhase firstStep.after 0 firstLanding.afterFiber
    (.reloading 0 [firstStep.undo] emptyProviderView)

def iterTransition : Transition dynamics inertia beginState iterState :=
  .iter beginState 0 beginFiber begin_present 10 [] emptyProviderView rfl begin_target
    firstLanding 0 rfl

theorem iterState_wellFormed : WellFormed iterState :=
  iterTransition.preservesWellFormed beginState_wellFormed

def iterFiber : Fiber exampleCatalog := {
  beginFiber with phase := .reloading 0 [.external 0] emptyProviderView
}

theorem iter_present : iterState.registry 0 = some iterFiber := rfl

theorem iter_target :
    targetView iterState 0 iterFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget iterState_wellFormed
  exact {
    present := iter_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

def finalResult : OrdinaryResult exampleCatalog Nat where
  after := advance iterState
  undo := 0
  next := none

def finalStep : IterationStep dynamics 0 0 iterState where
  after := finalResult.after
  undo := .external finalResult.undo
  next := finalResult.next
  source := .ordinary finalResult rfl
  recovers := by
    change (applyExternalUndo 0 (advance iterState)).ambient = iterState.ambient
    rfl
  preserves_wellFormed := fun wf ↦ advance_preserves wf

theorem finalStep_executed :
    executeOne dynamics oracle 0 iterState = .ok finalStep := by
  rfl

def finalLanding : Landing dynamics 0 0 iterState iterFiber where
  RegistrationError := String
  oracle := oracle
  step := finalStep
  executed := finalStep_executed
  before_present := iter_present
  afterFiber := iterFiber
  after_present := iter_present
  component_eq := rfl
  phase_eq := rfl

def finishState : ExampleState :=
  setPhase finalStep.after 0 finalLanding.afterFiber
    (.active (finalStep.undo :: [firstStep.undo]) emptyProviderView)

def finishTransition : Transition dynamics inertia iterState finishState :=
  .finish iterState 0 iterFiber iter_present 0 [firstStep.undo] emptyProviderView rfl
    iter_target finalLanding rfl

theorem finishState_wellFormed : WellFormed finishState :=
  finishTransition.preservesWellFormed iterState_wellFormed

def activeFiber : Fiber exampleCatalog := {
  iterFiber with phase := .active [.external 0, .external 0] emptyProviderView
}

theorem finish_present : finishState.registry 0 = some activeFiber := rfl

/-- L-Iter prepends its yielded undo code to the formerly empty accumulator. -/
theorem iter_accumulator_exact :
    iterFiber.phase = .reloading 0 [.external 0] emptyProviderView := rfl

/-- L-Finish prepends the second yielded code, preserving newest-first order. -/
theorem finish_accumulator_exact :
    activeFiber.phase = .active [.external 0, .external 0] emptyProviderView := rfl

def installedTrace : Trace dynamics inertia start finishState :=
  .cons beginTransition (.cons iterTransition (.cons finishTransition (.nil _)))

theorem installedTrace_wellFormed : WellFormed finishState :=
  installedTrace.preservesWellFormed start_wellFormed

/-!
Target change cannot arise from the two confined ordinary iterations: their registry control is
frozen. The example therefore exposes, rather than hides, the orchestration retirement between
the installed lifecycle trace and L-Leave.
-/

def retiredState : ExampleState := retireFiber finishState 0 activeFiber

def retireTransition : OrchestrationStep finishState retiredState :=
  .retire finishState 0 activeFiber finish_present

theorem retiredState_wellFormed : WellFormed retiredState :=
  retireTransition.preservesWellFormed finishState_wellFormed

def retiredFiber : Fiber exampleCatalog := {
  activeFiber with retired := true
}

theorem retired_present : retiredState.registry 0 = some retiredFiber := rfl

theorem retired_target_none : targetView retiredState 0 retiredFiber = none :=
  targetView_none_of_retired rfl

def leaveState : ExampleState :=
  setPhase retiredState 0 retiredFiber
    (.unloading [.external 0, .external 0] emptyProviderView none)

def leaveTransition : Transition dynamics inertia retiredState leaveState :=
  .leave retiredState 0 retiredFiber retired_present [.external 0, .external 0]
    emptyProviderView rfl (by simp [retired_target_none])

theorem leaveState_wellFormed : WellFormed leaveState :=
  leaveTransition.preservesWellFormed retiredState_wellFormed

def unloadingFiber : Fiber exampleCatalog := {
  retiredFiber with
    phase := .unloading [.external 0, .external 0] emptyProviderView none
}

theorem leave_present : leaveState.registry 0 = some unloadingFiber := rfl

theorem leave_notRelied : ¬Relied leaveState 0 := by
  rintro ⟨consumerName, consumer, lookup, different, installed, resolves⟩
  by_cases same : consumerName = 0
  · exact different same
  · simp [leaveState, setPhase, Coeffect.setAt_other, same, retiredState,
      retireFiber, finishState, finalStep, finalResult, advance, iterState,
      firstStep, firstResult, beginState, start,
      Cordis.GlobalDynamics.Example.start, Cordis.GlobalRegistry.Example.withProvider,
      Cordis.GlobalRegistry.Example.initial, insertFiber, Coeffect.empty] at lookup

def recoveredState : ExampleState :=
  dynamics.recover [.external 0, .external 0] leaveState

theorem recovered_present : recoveredState.registry 0 = some unloadingFiber := rfl

theorem recovery_preservesWellFormed :
    WellFormed leaveState → WellFormed recoveredState := by
  intro wf
  exact {
    birth_bounded := wf.birth_bounded
    parent_present := wf.parent_present
    parent_older := wf.parent_older
    provisions_unique := wf.provisions_unique
    committed_provider_present := wf.committed_provider_present
    committed_provider_installed := wf.committed_provider_installed
  }

theorem recovered_notRelied : ¬Relied recoveredState 0 := by
  intro relied
  exact leave_notRelied relied

def unloadedState : ExampleState :=
  setPhase recoveredState 0 unloadingFiber (.inactive none)

def recoveryAdmission :
    RecoveryAdmission dynamics leaveState 0 unloadingFiber
      [.external 0, .external 0] none where
  before_present := leave_present
  recoveredFiber := unloadingFiber
  recovered_present := recovered_present
  component_eq := rfl
  after := unloadedState
  after_eq := rfl
  preserves_wellFormed := by
    intro wf
    exact setPhase_inactive_preserves recovered_present none recovered_notRelied
      (recovery_preservesWellFormed wf)

def unloadTransition : Transition dynamics inertia leaveState unloadedState :=
  .unload leaveState 0 unloadingFiber leave_present [.external 0, .external 0]
    emptyProviderView none rfl leave_notRelied recoveryAdmission

theorem unloadedState_wellFormed : WellFormed unloadedState :=
  unloadTransition.preservesWellFormed leaveState_wellFormed

def unloadingTrace : Trace dynamics inertia retiredState unloadedState :=
  .cons leaveTransition (.cons unloadTransition (.nil _))

theorem unloadingTrace_wellFormed : WellFormed unloadedState :=
  unloadingTrace.preservesWellFormed retiredState_wellFormed

/-- The two lifecycle traces compose safely across the explicitly exposed O-Retire bridge. -/
theorem bridgedPath_wellFormed : WellFormed unloadedState :=
  unloadingTrace.preservesWellFormed <|
    retireTransition.preservesWellFormed <|
      installedTrace.preservesWellFormed start_wellFormed

/-- The example reaches the inactive success outcome after exact two-code LIFO recovery. -/
theorem unloaded_phase_exact :
    unloadedState.registry 0 = some { unloadingFiber with phase := .inactive none } := rfl

/-- Both ordinary ambient writes are recovered exactly. -/
theorem unloaded_ambient_exact : unloadedState.ambient = start.ambient := rfl

/-- The five lifecycle edges occur in the requested order around the explicit retirement gap. -/
theorem lifecycle_rule_sequence :
    [beginTransition.rule, iterTransition.rule, finishTransition.rule,
      leaveTransition.rule, unloadTransition.rule] =
    [.begin, .iter, .finish, .leave, .unload] := rfl

theorem finish_target :
    targetView finishState 0 activeFiber = some emptyProviderView := by
  apply targetView_eq_of_isTarget finishState_wellFormed
  exact {
    present := finish_present
    not_retired := rfl
    resolves_active := by
      intro declared
      rcases declared with ⟨key, declared⟩
      change key ∈ providerDecl.dependencies.keys at declared
      simp [providerDecl] at declared
  }

/-- Exact rejection: L-Leave's target-mismatch guard is false before retirement. -/
theorem stable_leave_guard_rejected :
    ¬(targetView finishState 0 activeFiber ≠ some emptyProviderView) := by
  intro changed
  exact changed finish_target

/-- Exact rejection: this host policy never authorizes abort-before-landing diversion. -/
theorem abort_guard_rejected (code : Nat) (state : ExampleState) :
    ¬inertia.canAbort 0 code state := by
  simp [inertia]

/-- Exact rejection: a successful final iterator cannot satisfy L-Raise's error premise. -/
theorem raise_guard_rejected (error : String) :
    runIterator 0 0 iterState ≠ .error error := by
  simp [runIterator, iter_present]

/-- The catalog used by the full path remains genuinely heterogeneous. -/
theorem path_catalog_heterogeneous :
    (exampleCatalog.declaration .consumer).dependencies.keys = [.counter, .label] := rfl

end Example

end Cordis.GlobalLifecycle
