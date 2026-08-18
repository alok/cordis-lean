import Cordis.GlobalRegistry

/-!
# External global iterator dynamics

`GlobalRegistry` deliberately stores only codes. This module is defined afterwards and interprets
those codes without placing a function over `GlobalState` inside `GlobalState` itself.

An iterator step either performs one ordinary mutation or requests Definition 47 registration.
Ordinary mutations carry exact recovery and Definition 48 write-confinement laws. Registration
selects a fresh name through an explicit admission witness, inserts an inactive child under the
owner, hands the name to the continuation, and yields `UndoCode.retire child`. Retirement leaves
a vestigial entry rather than the exact predecessor, so registration recovery is stated in the
dynamics-supplied state setoid, as the paper requires.

Read confinement and name equivariance are not inferred from the paper's prose. `Dynamics`
requires a named `ReadEquivalent` relation plus an executable agreement law. The optional
`NameEquivarianceAssumption` records explicit actions and a run-equivariance equation; no theorem
in this module assumes such an action implicitly.

`runFuel` is a total Definition 52 boundary. It executes at most `fuel` iterations and returns an
intrinsic trace plus an accumulated LIFO recovery certificate. Reaching zero fuel with a remaining
iterator is an explicit `exhausted` result, never silent success. The full fiber lifecycle and its
phase updates remain outside this module.
-/

set_option autoImplicit false

namespace Cordis.GlobalDynamics

open Cordis.GlobalRegistry

universe u

variable {sig : StaticSignature} {catalog : Catalog sig} {Ambient : Type u}

abbrev State (catalog : Catalog sig) (Ambient : Type u) := GlobalState catalog Ambient

/-- One ordinary iterator yield before its proof obligations are attached. -/
structure OrdinaryResult (catalog : Catalog sig) (Ambient : Type u) where
  after : State catalog Ambient
  undo : sig.ExternalUndoCode
  next : Option sig.IteratorCode

/-- Definition 47 registration request; the continuation may depend on the chosen fresh name. -/
structure RegistrationRequest (sig : StaticSignature) where
  component : sig.ComponentId
  next : sig.Name → Option sig.IteratorCode

/-- External iterator output prior to admission and proof reconstruction. -/
inductive IteratorResult (catalog : Catalog sig) (Ambient : Type u) where
  | ordinary (result : OrdinaryResult catalog Ambient)
  | register (request : RegistrationRequest sig)

/-- Two iterator outputs agree modulo a supplied state relation. -/
inductive ResultRelated
    (relation : State catalog Ambient → State catalog Ambient → Prop) :
    IteratorResult catalog Ambient → IteratorResult catalog Ambient → Prop where
  | ordinary {left right : OrdinaryResult catalog Ambient} :
      relation left.after right.after → left.undo = right.undo → left.next = right.next →
      ResultRelated relation (.ordinary left) (.ordinary right)
  | register {left right : RegistrationRequest sig} :
      left.component = right.component → left.next = right.next →
      ResultRelated relation (.register left) (.register right)

/-- Agreement of iterator executions, including equal failures. -/
inductive RunRelated
    (relation : State catalog Ambient → State catalog Ambient → Prop) :
    Except sig.Error (IteratorResult catalog Ambient) →
    Except sig.Error (IteratorResult catalog Ambient) → Prop where
  | errors {left right : sig.Error} : left = right →
      RunRelated relation (.error left) (.error right)
  | results {left right : IteratorResult catalog Ambient} :
      ResultRelated relation left right → RunRelated relation (.ok left) (.ok right)

/-- Definition 48 write footprint for an ordinary iteration owned by `owner`.

`Ambient` is intentionally unrestricted: Definition 45 says effects may mutate state outside
fiber tables and track that mutation in their inverses. Confinement freezes the registry and all
owner control fields while restricting the owner's table writes to its provision.
-/
structure OrdinaryConfinement
    (before after : State catalog Ambient) (owner : sig.Name) where
  beforeFiber : Fiber catalog
  afterFiber : Fiber catalog
  before_present : before.registry owner = some beforeFiber
  after_present : after.registry owner = some afterFiber
  component_eq : afterFiber.component = beforeFiber.component
  parent_eq : afterFiber.parent = beforeFiber.parent
  birth_eq : afterFiber.birth = beforeFiber.birth
  retired_eq : afterFiber.retired = beforeFiber.retired
  phase_eq : component_eq ▸ afterFiber.phase = beforeFiber.phase
  other_unchanged : ∀ name, name ≠ owner → after.registry name = before.registry name
  table_writes : WritesWithinProvision (catalog.declaration beforeFiber.component)
    beforeFiber.table afterFiber.table
  nextBirth_eq : after.nextBirth = before.nextBirth

/-- Total interpretation of a registration inverse; absence makes it a no-op off its domain. -/
def retireByName (state : State catalog Ambient) (name : sig.Name) : State catalog Ambient :=
  match state.registry name with
  | none => state
  | some fiber => retireFiber state name fiber

/-- External interpreter and every law needed by one-step and finite-run refinement. -/
structure Dynamics (sig : StaticSignature) (catalog : Catalog sig) (Ambient : Type u) where
  equivalence : Setoid (State catalog Ambient)
  runIterator : sig.Name → sig.IteratorCode → State catalog Ambient →
    Except sig.Error (IteratorResult catalog Ambient)
  applyExternalUndo : sig.ExternalUndoCode → State catalog Ambient → State catalog Ambient
  ordinary_recovers : ∀ owner code before result,
    runIterator owner code before = .ok (.ordinary result) →
      applyExternalUndo result.undo result.after = before
  externalUndo_respects : ∀ undo {left right}, equivalence.r left right →
    equivalence.r (applyExternalUndo undo left) (applyExternalUndo undo right)
  ordinary_confined : ∀ owner code before result,
    runIterator owner code before = .ok (.ordinary result) →
      OrdinaryConfinement before result.after owner
  ordinary_preserves_wellFormed : ∀ owner code before result,
    runIterator owner code before = .ok (.ordinary result) →
    WellFormed before → WellFormed result.after
  run_respects : ∀ owner code {left right} leftFiber rightFiber,
    equivalence.r left right →
    left.registry owner = some leftFiber → right.registry owner = some rightFiber →
    RunRelated equivalence.r (runIterator owner code left) (runIterator owner code right)
  ReadEquivalent : sig.Name → State catalog Ambient → State catalog Ambient → Prop
  read_refl : ∀ owner state, ReadEquivalent owner state state
  run_read_confined : ∀ owner code {left right} leftFiber rightFiber,
    ReadEquivalent owner left right →
    left.registry owner = some leftFiber → right.registry owner = some rightFiber →
    RunRelated equivalence.r (runIterator owner code left) (runIterator owner code right)
  retire_respects : ∀ name {left right}, equivalence.r left right →
    equivalence.r (retireByName left name) (retireByName right name)

namespace Dynamics

/-- Interpret either external recovery or the built-in registration retirement inverse. -/
def applyUndo (dynamics : Dynamics sig catalog Ambient) :
    UndoCode sig → State catalog Ambient → State catalog Ambient
  | .external code, state => dynamics.applyExternalUndo code state
  | .retire name, state => retireByName state name

/-- Every interpreted undo code respects the dynamics' state equivalence. -/
theorem applyUndo_respects (dynamics : Dynamics sig catalog Ambient)
    (undo : UndoCode sig) {left right : State catalog Ambient}
    (related : dynamics.equivalence.r left right) :
    dynamics.equivalence.r (dynamics.applyUndo undo left) (dynamics.applyUndo undo right) := by
  cases undo with
  | external code => exact dynamics.externalUndo_respects code related
  | retire name => exact dynamics.retire_respects name related

/-- Apply newest-first undo codes in LIFO order. -/
def recover (dynamics : Dynamics sig catalog Ambient) :
    List (UndoCode sig) → State catalog Ambient → State catalog Ambient
  | [], state => state
  | undo :: rest, state => dynamics.recover rest (dynamics.applyUndo undo state)

/-- A complete accumulated recovery map respects the state equivalence. -/
theorem recover_respects (dynamics : Dynamics sig catalog Ambient)
    (undos : List (UndoCode sig)) {left right : State catalog Ambient}
    (related : dynamics.equivalence.r left right) :
    dynamics.equivalence.r (dynamics.recover undos left) (dynamics.recover undos right) := by
  induction undos generalizing left right with
  | nil => exact related
  | cons undo rest inductionHypothesis =>
      exact inductionHypothesis (dynamics.applyUndo_respects undo related)

/-- Recovery over appended lists runs the left (newer) segment before the right segment. -/
theorem recover_append (dynamics : Dynamics sig catalog Ambient)
    (newer older : List (UndoCode sig)) (state : State catalog Ambient) :
    dynamics.recover (newer ++ older) state =
      dynamics.recover older (dynamics.recover newer state) := by
  induction newer generalizing state with
  | nil => rfl
  | cons undo rest inductionHypothesis =>
      simp only [List.cons_append, recover]
      exact inductionHypothesis (dynamics.applyUndo undo state)

end Dynamics

/-! ## Explicit under-specified assumptions -/

/--
Optional nominal action required before claiming paper Lemma 56. The action and result mapping are
integrator-supplied because the paper does not specify how opaque program codes carry names.
-/
structure NameEquivarianceAssumption (dynamics : Dynamics sig catalog Ambient) where
  Permutation : Type u
  actName : Permutation → sig.Name → sig.Name
  actState : Permutation → State catalog Ambient → State catalog Ambient
  actIterator : Permutation → sig.IteratorCode → sig.IteratorCode
  actExternalUndo : Permutation → sig.ExternalUndoCode → sig.ExternalUndoCode
  actComponent : Permutation → sig.ComponentId → sig.ComponentId
  actResult : Permutation → IteratorResult catalog Ambient → IteratorResult catalog Ambient
  run_equivariant : ∀ permutation owner code state,
    dynamics.runIterator (actName permutation owner) (actIterator permutation code)
        (actState permutation state) =
      (dynamics.runIterator owner code state).map (actResult permutation)

/-! ## Registration admission and one-step semantics -/

/-- Exact premises and observational recovery evidence for one Definition 47 registration. -/
structure RegistrationAdmission
    (dynamics : Dynamics sig catalog Ambient)
    (before : State catalog Ambient) (owner : sig.Name)
    (request : RegistrationRequest sig) where
  child : sig.Name
  fresh : Coeffect.Absent before.registry child
  ownerFiber : Fiber catalog
  owner_present : before.registry owner = some ownerFiber
  provision_fresh : ∀ existing existingFiber key,
    before.registry existing = some existingFiber →
    key ∈ (catalog.declaration request.component).provision →
    key ∈ (catalog.declaration existingFiber.component).provision → False
  registration_recovers :
    dynamics.equivalence.r
      (dynamics.applyUndo (.retire child)
        (insertFiber before child (some owner) request.component)) before

namespace RegistrationAdmission

def after
    {dynamics : Dynamics sig catalog Ambient} {before : State catalog Ambient}
    {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) : State catalog Ambient :=
  insertFiber before admission.child (some owner) request.component

def undo
    {dynamics : Dynamics sig catalog Ambient} {before : State catalog Ambient}
    {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) : UndoCode sig :=
  .retire admission.child

def next
    {dynamics : Dynamics sig catalog Ambient} {before : State catalog Ambient}
    {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request) : Option sig.IteratorCode :=
  request.next admission.child

theorem after_wellFormed
    {dynamics : Dynamics sig catalog Ambient} {before : State catalog Ambient}
    {owner : sig.Name} {request : RegistrationRequest sig}
    (admission : RegistrationAdmission dynamics before owner request)
    (beforeWellFormed : WellFormed before) :
    WellFormed admission.after := by
  apply preserve_insert before admission.child admission.fresh (some owner)
    (by
      intro parent equal
      have parent_eq : parent = owner := Option.some.inj equal.symm
      subst parent
      exact ⟨admission.ownerFiber, admission.owner_present⟩)
    request.component admission.provision_fresh beforeWellFormed

end RegistrationAdmission

/-- Caller-owned admission policy for every registration request reached during a run. -/
structure RegistrationOracle
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name) (Error : Type u) where
  certify : (before : State catalog Ambient) → (request : RegistrationRequest sig) →
    Except Error (RegistrationAdmission dynamics before owner request)

/-- Exact source of one validated iterator step. -/
inductive StepSource
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (before : State catalog Ambient) :
    State catalog Ambient → UndoCode sig → Option sig.IteratorCode → Type u where
  | ordinary (result : OrdinaryResult catalog Ambient)
      (run_eq : dynamics.runIterator owner code before = .ok (.ordinary result)) :
      StepSource dynamics owner code before result.after (.external result.undo) result.next
  | registration (request : RegistrationRequest sig)
      (admission : RegistrationAdmission dynamics before owner request)
      (run_eq : dynamics.runIterator owner code before = .ok (.register request)) :
      StepSource dynamics owner code before admission.after admission.undo admission.next

/-- One Definition 47/48/51 step with its local observational recovery proof. -/
structure IterationStep
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (before : State catalog Ambient) where
  after : State catalog Ambient
  undo : UndoCode sig
  next : Option sig.IteratorCode
  source : StepSource dynamics owner code before after undo next
  recovers : dynamics.equivalence.r (dynamics.applyUndo undo after) before
  preserves_wellFormed : WellFormed before → WellFormed after

namespace IterationStep

/-- Each reconstructed iterator step composes with the global registry invariant. -/
theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) :
    WellFormed before → WellFormed step.after := by
  exact step.preserves_wellFormed

end IterationStep

theorem ordinary_exact
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (run_eq : dynamics.runIterator owner code before = .ok (.ordinary result)) :
    dynamics.applyExternalUndo result.undo result.after = before :=
  dynamics.ordinary_recovers owner code before result run_eq

def ordinaryConfinementWitness
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (code : sig.IteratorCode) (before : State catalog Ambient)
    (result : OrdinaryResult catalog Ambient)
    (run_eq : dynamics.runIterator owner code before = .ok (.ordinary result)) :
    OrdinaryConfinement before result.after owner :=
  dynamics.ordinary_confined owner code before result run_eq

/-- Runtime failures distinguish iterator failure from registration admission failure. -/
inductive RunError (sig : StaticSignature) (RegistrationError : Type u) where
  | iterator (error : sig.Error)
  | registration (error : RegistrationError)

/-- Execute one external iterator code and reconstruct all proof obligations. -/
def executeOne
    {RegistrationError : Type u}
    {owner : sig.Name}
    (dynamics : Dynamics sig catalog Ambient)
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (code : sig.IteratorCode) (before : State catalog Ambient) :
    Except (RunError sig RegistrationError) (IterationStep dynamics owner code before) :=
  match run_eq : dynamics.runIterator owner code before with
  | .error error => .error (.iterator error)
  | .ok (.ordinary result) =>
      .ok {
        after := result.after
        undo := .external result.undo
        next := result.next
        source := .ordinary result run_eq
        recovers := by
          change dynamics.equivalence.r
            (dynamics.applyExternalUndo result.undo result.after) before
          rw [dynamics.ordinary_recovers owner code before result run_eq]
          exact dynamics.equivalence.refl before
        preserves_wellFormed :=
          dynamics.ordinary_preserves_wellFormed owner code before result run_eq
      }
  | .ok (.register request) =>
      match oracle.certify before request with
      | .error error => .error (.registration error)
      | .ok admission => .ok {
          after := admission.after
          undo := admission.undo
          next := admission.next
          source := .registration request admission run_eq
          recovers := admission.registration_recovers
          preserves_wellFormed := admission.after_wellFormed
        }

/-! ## Proof-carrying accumulation and fueled Definition 52 runner -/

/-- Newest-first undo codes whose interpretation recovers `origin` from `current` up to `≈`. -/
structure Accumulator
    (dynamics : Dynamics sig catalog Ambient)
    (origin current : State catalog Ambient) where
  undos : List (UndoCode sig)
  recovers : dynamics.equivalence.r (dynamics.recover undos current) origin

namespace Accumulator

def empty (dynamics : Dynamics sig catalog Ambient) (state : State catalog Ambient) :
    Accumulator dynamics state state where
  undos := []
  recovers := dynamics.equivalence.refl state

def singleton
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {before : State catalog Ambient}
    (step : IterationStep dynamics owner code before) : Accumulator dynamics before step.after where
  undos := [step.undo]
  recovers := step.recovers

/-- Compose an earlier prefix with a later suffix, retaining newest-first LIFO order. -/
def seq
    {dynamics : Dynamics sig catalog Ambient}
    {start middle finish : State catalog Ambient}
    (first : Accumulator dynamics start middle)
    (second : Accumulator dynamics middle finish) : Accumulator dynamics start finish where
  undos := second.undos ++ first.undos
  recovers := by
    rw [dynamics.recover_append]
    exact dynamics.equivalence.trans
      (dynamics.recover_respects first.undos second.recovers)
      first.recovers

end Accumulator

/-- Total fueled runner stop status. -/
inductive StopReason (sig : StaticSignature) where
  | completed
  | exhausted (next : sig.IteratorCode)

/-- Intrinsic iterator trace indexed by initial code, endpoints, and exact stop reason. -/
inductive Trace
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name) :
    sig.IteratorCode → State catalog Ambient → State catalog Ambient →
      StopReason sig → Type u where
  | exhausted (code : sig.IteratorCode) (state : State catalog Ambient) :
      Trace dynamics owner code state state (.exhausted code)
  | completed {code before}
      (step : IterationStep dynamics owner code before)
      (done : step.next = none) :
      Trace dynamics owner code before step.after .completed
  | cons {code next before finish stop}
      (step : IterationStep dynamics owner code before)
      (continues : step.next = some next)
      (rest : Trace dynamics owner next step.after finish stop) :
      Trace dynamics owner code before finish stop

namespace Trace

theorem preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {code : sig.IteratorCode} {start finish : State catalog Ambient} {stop : StopReason sig}
    (trace : Trace dynamics owner code start finish stop) :
    WellFormed start → WellFormed finish := by
  intro wf
  induction trace with
  | exhausted => exact wf
  | completed step done => exact step.preservesWellFormed wf
  | cons step continues rest inductionHypothesis =>
      exact inductionHypothesis (step.preservesWellFormed wf)

end Trace

/-- A fueled run, its intrinsic trace, and complete accumulated recovery. -/
structure RunResult
    (dynamics : Dynamics sig catalog Ambient) (owner : sig.Name)
    (origin : State catalog Ambient) (initialCode : sig.IteratorCode) where
  final : State catalog Ambient
  stop : StopReason sig
  trace : Trace dynamics owner initialCode origin final stop
  accumulator : Accumulator dynamics origin final

/-- Execute at most `fuel` iterator steps; zero fuel is explicit exhaustion. -/
def runFuel
    {RegistrationError : Type u}
    {owner : sig.Name}
    (dynamics : Dynamics sig catalog Ambient)
    (oracle : RegistrationOracle dynamics owner RegistrationError) :
    (fuel : Nat) → (before : State catalog Ambient) → (code : sig.IteratorCode) →
      Except (RunError sig RegistrationError) (RunResult dynamics owner before code)
  | 0, before, code => .ok {
      final := before
      stop := .exhausted code
      trace := .exhausted code before
      accumulator := .empty dynamics before
    }
  | fuel + 1, before, code => do
      let step ← executeOne dynamics oracle code before
      let first := Accumulator.singleton step
      match continues : step.next with
      | none => .ok {
          final := step.after
          stop := .completed
          trace := .completed step continues
          accumulator := first
        }
      | some next =>
          let tail ← runFuel dynamics oracle fuel step.after next
          .ok {
            final := tail.final
            stop := tail.stop
            trace := .cons step continues tail.trace
            accumulator := first.seq tail.accumulator
          }

theorem runFuel_zero
    {RegistrationError : Type u}
    {owner : sig.Name}
    (dynamics : Dynamics sig catalog Ambient)
    (oracle : RegistrationOracle dynamics owner RegistrationError)
    (before : State catalog Ambient) (code : sig.IteratorCode) :
    (runFuel dynamics oracle 0 before code).map (fun result ↦ result.stop) =
      .ok (StopReason.exhausted code) := by
  rfl

/-- Every successful or exhausted fueled run carries recovery to its exact indexed origin. -/
theorem RunResult.recovers
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {origin : State catalog Ambient} {code : sig.IteratorCode}
    (result : RunResult dynamics owner origin code) :
    dynamics.equivalence.r
      (dynamics.recover result.accumulator.undos result.final) origin :=
  result.accumulator.recovers

theorem RunResult.preservesWellFormed
    {dynamics : Dynamics sig catalog Ambient} {owner : sig.Name}
    {origin : State catalog Ambient} {code : sig.IteratorCode}
    (result : RunResult dynamics owner origin code) :
    WellFormed origin → WellFormed result.final :=
  result.trace.preservesWellFormed

/-! ## Concrete heterogeneous ordinary and registration run -/

namespace Example

abbrev ExampleSig := Cordis.GlobalRegistry.Example.signature
abbrev exampleCatalog := Cordis.GlobalRegistry.Example.catalog

abbrev ExampleState := State exampleCatalog Nat

def start : ExampleState where
  ambient := 3
  nextBirth := Cordis.GlobalRegistry.Example.withProvider.nextBirth
  registry := Cordis.GlobalRegistry.Example.withProvider.registry

theorem start_wellFormed : WellFormed start := by
  let wf := Cordis.GlobalRegistry.Example.withProvider_wellFormed
  exact {
    birth_bounded := wf.birth_bounded
    parent_present := wf.parent_present
    parent_older := wf.parent_older
    provisions_unique := wf.provisions_unique
    committed_provider_present := wf.committed_provider_present
    committed_provider_installed := wf.committed_provider_installed
  }

def ordinaryAfter (before : ExampleState) : ExampleState := {
  before with ambient := before.ambient + 1
}

def applyExternalUndo : ExampleSig.ExternalUndoCode → ExampleState → ExampleState
  | 0, current => { current with ambient := current.ambient - 1 }
  | _ + 1, current => current

def registrationRequest : RegistrationRequest ExampleSig where
  component := Cordis.GlobalRegistry.Example.Component.consumer
  next := fun _ ↦ none

def runIterator (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) :
    Except ExampleSig.Error (IteratorResult exampleCatalog Nat) :=
  match before.registry owner with
  | none => .error "missing owner"
  | some _ =>
      match code with
      | 0 => .ok (.ordinary {
          after := ordinaryAfter before
          undo := 0
          next := some 1
        })
      | _ + 1 => .ok (.register registrationRequest)

def stateSetoid : Setoid ExampleState where
  r := fun left right ↦ left.ambient = right.ambient
  iseqv := {
    refl := fun _ ↦ rfl
    symm := Eq.symm
    trans := Eq.trans
  }

theorem ordinary_recovers
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) (result : OrdinaryResult exampleCatalog Nat)
    (run_eq : runIterator owner code before = .ok (.ordinary result)) :
    applyExternalUndo result.undo result.after = before := by
  cases ownerLookup : before.registry owner with
  | none => simp [runIterator, ownerLookup] at run_eq
  | some ownerFiber =>
      cases code with
      | zero =>
          simp [runIterator, ownerLookup] at run_eq
          subst result
          cases before
          simp [ordinaryAfter, applyExternalUndo]
      | succ code => simp [runIterator, ownerLookup] at run_eq

theorem ordinary_preserves_wellFormed
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) (result : OrdinaryResult exampleCatalog Nat)
    (run_eq : runIterator owner code before = .ok (.ordinary result))
    (wf : WellFormed before) : WellFormed result.after := by
  cases ownerLookup : before.registry owner with
  | none => simp [runIterator, ownerLookup] at run_eq
  | some ownerFiber =>
      cases code with
      | zero =>
          simp [runIterator, ownerLookup] at run_eq
          subst result
          exact {
            birth_bounded := wf.birth_bounded
            parent_present := wf.parent_present
            parent_older := wf.parent_older
            provisions_unique := wf.provisions_unique
            committed_provider_present := wf.committed_provider_present
            committed_provider_installed := wf.committed_provider_installed
          }
      | succ code => simp [runIterator, ownerLookup] at run_eq

def ordinaryConfinementWitness
    (owner : ExampleSig.Name) (code : ExampleSig.IteratorCode)
    (before : ExampleState) (result : OrdinaryResult exampleCatalog Nat)
    (run_eq : runIterator owner code before = .ok (.ordinary result)) :
    OrdinaryConfinement before result.after owner := by
  cases ownerLookup : before.registry owner with
  | none => simp [runIterator, ownerLookup] at run_eq
  | some ownerFiber =>
      cases code with
      | zero =>
          simp [runIterator, ownerLookup] at run_eq
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
            table_writes := by intro key outside; rfl
            nextBirth_eq := rfl
          }
      | succ code => simp [runIterator, ownerLookup] at run_eq

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
  cases code with
  | zero =>
      simp only [runIterator, leftPresent, rightPresent]
      apply RunRelated.results
      apply ResultRelated.ordinary
      · exact congrArg (fun value ↦ value + 1) related
      · rfl
      · rfl
  | succ code =>
      simp only [runIterator, leftPresent, rightPresent]
      exact .results (.register rfl rfl)

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
  ordinary_confined := ordinaryConfinementWitness
  ordinary_preserves_wellFormed := ordinary_preserves_wellFormed
  run_respects := run_respects
  ReadEquivalent := fun _ left right ↦ left.ambient = right.ambient
  read_refl := fun _ _ ↦ rfl
  run_read_confined := by
    intro owner code left right leftFiber rightFiber related leftPresent rightPresent
    exact run_respects owner code leftFiber rightFiber related leftPresent rightPresent
  retire_respects := retire_respects

def oracle : RegistrationOracle dynamics 0 String where
  certify before request :=
    match request with
    | ⟨.provider, _⟩ => .error "unsupported component"
    | ⟨.consumer, _⟩ =>
        match owner_eq : before.registry 0 with
        | none => .error "missing owner"
        | some ownerFiber =>
            if fresh_eq : before.registry 1 = none then
              .ok {
                child := 1
                fresh := ⟨fresh_eq⟩
                ownerFiber
                owner_present := owner_eq
                provision_fresh := by
                  simp [Cordis.GlobalRegistry.Example.consumerDecl]
                registration_recovers := rfl
              }
            else
              .error "child name already used"

structure StepSummary where
  ambient : Nat
  childPresent : Bool
  externalUndo : Bool
  nextPresent : Bool
  deriving DecidableEq, Repr

def summarizeStep {code : ExampleSig.IteratorCode} {before : ExampleState} :
    Except (RunError ExampleSig String) (IterationStep dynamics 0 code before) →
      Option StepSummary
  | .error _ => none
  | .ok step => some {
      ambient := step.after.ambient
      childPresent := (step.after.registry 1).isSome
      externalUndo := match step.undo with
        | .external _ => true
        | .retire _ => false
      nextPresent := step.next.isSome
    }

theorem ordinary_step_exact :
    summarizeStep (executeOne dynamics oracle 0 start) = some {
      ambient := 4
      childPresent := false
      externalUndo := true
      nextPresent := true
    } := by
  rfl

def afterOrdinary : ExampleState := ordinaryAfter start

theorem afterOrdinary_wellFormed : WellFormed afterOrdinary := by
  let wf := Cordis.GlobalRegistry.Example.withProvider_wellFormed
  exact {
    birth_bounded := wf.birth_bounded
    parent_present := wf.parent_present
    parent_older := wf.parent_older
    provisions_unique := wf.provisions_unique
    committed_provider_present := wf.committed_provider_present
    committed_provider_installed := wf.committed_provider_installed
  }

theorem registration_step_exact :
    summarizeStep (executeOne dynamics oracle 1 afterOrdinary) = some {
      ambient := 4
      childPresent := true
      externalUndo := false
      nextPresent := false
    } := by
  rfl

def registrationUndoChild :
    Except (RunError ExampleSig String) (IterationStep dynamics 0 1 afterOrdinary) → Option Nat
  | .error _ => none
  | .ok step => match step.undo with
    | .retire child => some child
    | .external _ => none

theorem registration_yields_child_retirement :
    registrationUndoChild (executeOne dynamics oracle 1 afterOrdinary) = some 1 := by
  rfl

structure RunSummary where
  ambient : Nat
  childPresent : Bool
  undoCount : Nat
  completed : Bool
  deriving DecidableEq, Repr

def summarize {origin : ExampleState} {code : ExampleSig.IteratorCode} :
    Except (RunError ExampleSig String) (RunResult dynamics 0 origin code) → Option RunSummary
  | .error _ => none
  | .ok result => some {
      ambient := result.final.ambient
      childPresent := (result.final.registry 1).isSome
      undoCount := result.accumulator.undos.length
      completed := match result.stop with
        | .completed => true
        | .exhausted _ => false
    }

theorem ordinary_then_registration :
    summarize (runFuel dynamics oracle 2 start 0) = some {
      ambient := 4
      childPresent := true
      undoCount := 2
      completed := true
    } := by
  rfl

theorem one_fuel_is_explicit_exhaustion :
    summarize (runFuel dynamics oracle 1 start 0) = some {
      ambient := 4
      childPresent := false
      undoCount := 1
      completed := false
    } := by
  rfl

def exhaustedCode {origin : ExampleState} {code : ExampleSig.IteratorCode} :
    Except (RunError ExampleSig String) (RunResult dynamics 0 origin code) →
      Option (Option ExampleSig.IteratorCode)
  | .error _ => none
  | .ok result => some <| match result.stop with
    | .completed => none
    | .exhausted code => some code

theorem one_fuel_retains_next_code :
    exhaustedCode (runFuel dynamics oracle 1 start 0) = some (some 1) := by
  rfl

/-- The heterogeneous catalog retains both a numeric and textual declared dependency. -/
theorem registration_is_heterogeneous :
    (exampleCatalog.declaration
      Cordis.GlobalRegistry.Example.Component.consumer).dependencies.keys =
      [Cordis.GlobalRegistry.Example.Key.counter,
        Cordis.GlobalRegistry.Example.Key.label] := rfl

/-- Registration insertion preserves global well-formedness once its explicit admission is used. -/
theorem registered_state_wellFormed :
    WellFormed (insertFiber afterOrdinary 1 (some 0)
      Cordis.GlobalRegistry.Example.Component.consumer) := by
  apply preserve_insert afterOrdinary 1 (by constructor; rfl) (some 0)
    (by
      intro parent equal
      have parent_eq : parent = 0 := Option.some.inj equal.symm
      subst parent
      exact ⟨_, rfl⟩)
    Cordis.GlobalRegistry.Example.Component.consumer
    (by simp [Cordis.GlobalRegistry.Example.consumerDecl])
    afterOrdinary_wellFormed

/-- The accumulated observational recovery returns the initial ambient observation. -/
def recoveredAmbient {origin : ExampleState} {code : ExampleSig.IteratorCode} :
    Except (RunError ExampleSig String) (RunResult dynamics 0 origin code) → Option Nat
  | .error _ => none
  | .ok result => some (dynamics.recover result.accumulator.undos result.final).ambient

theorem complete_run_recovers_ambient :
    recoveredAmbient (runFuel dynamics oracle 2 start 0) = some start.ambient := by
  rfl

end Example

end Cordis.GlobalDynamics
