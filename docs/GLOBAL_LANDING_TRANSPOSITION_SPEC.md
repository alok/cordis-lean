# Program-aligned landing transposition: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: next implementation slice after `Cordis.GlobalForeignPhase`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 48,
Definition 60, and Lemma 71(1).

## 1. Goal

Implement `Cordis.GlobalLandingTransposition`, an exact common-source diamond
for the four combinations of L-Iter and L-Finish.

The theorem must receive two complete, program-aligned landing activations at
the same well-formed predecessor, semantic program independence, exact
cross-forward lifecycle-yield stability, and both foreign-phase compatibility
certificates. It must construct both lifecycle orders with one exact shared
final state.

This is not full paper Lemma 71(1). The module intentionally omits every
L-Begin-containing pair, arbitrary trace-step assignment, and episode-level
fixed-program provenance.

## 2. Why a landing needs program provenance

`GlobalLifecycle.Landing` existentially stores its own:

- registration-error type;
- registration oracle;
- dependent `IterationStep`; and
- exact `executeOne` equation.

Nothing requires that oracle to be the fixed oracle in the `Program` used by
`Independent` and `ForeignPhaseCompatibility`.

Define the smallest noncircular witness:

```lean
structure LandingProgramWitness
    (program : Program dynamics)
    (landing : Landing dynamics program.owner code before beforeFiber) : Prop where
  reachable : Reach program code
  program_executed :
    executeOne dynamics program.oracle code before = .ok landing.step
```

Do not compare the landing's oracle record or its dependent registration-error
carrier with the program's fields. Reproduction of the exact stored step is the
only provenance required by this local theorem.

Do not add the stronger episode-level root condition here. A future trace theorem
will additionally need:

```lean
program.root = (catalog.declaration fiber.component).entry
```

and one program occurrence reused through the whole episode.

## 3. Exact cross-forward lifecycle-yield stability

Ordinary `Independent` is not enough for exact lifecycle endpoints. Its
cross-forward yield law returns semantic `YieldAgrees`: equality of interpreted
inverse functions, continuation, and source kind. L-Iter/L-Finish phases store
the syntactic `UndoCode` itself.

Define the narrow representation-strengthened law:

```lean
def LifecycleYieldStable
    (program : Program dynamics)
    (foreign : PartialMap catalog Ambient) : Prop :=
  ∀ {code}, Reach program code →
    ∀ seed step moved,
      executeOne dynamics program.oracle code seed = .ok step →
      foreign seed = some moved →
      ∃ movedStep,
        executeOne dynamics program.oracle code moved = .ok movedStep ∧
          LifecycleYieldAgrees movedStep step
```

Package only the cross-forward instances needed by landing transposition:

```lean
structure ForwardLifecycleIndependent
    (left right : Program dynamics) : Prop where
  independent : Independent left right
  left_under_right :
    ∀ {rightCode}, Reach right rightCode →
      LifecycleYieldStable left (forward right rightCode)
  right_under_left :
    ∀ {leftCode}, Reach left leftCode →
      LifecycleYieldStable right (forward left leftCode)
```

Do not replace semantic Definition 60 independence globally. This is a separate
exact-representation premise only for cross-forward iterator applications.

Prove `LifecycleYieldAgrees.refl` and `.trans`, then construct a strengthened
raw diamond:

```lean
structure LifecycleForwardDiamond ... extends ForwardDiamond leftStep rightStep where
  right_exact : LifecycleYieldAgrees rightAfterLeft rightStep
  left_exact : LifecycleYieldAgrees leftAfterRight leftStep
```

The constructor must use `independent_forward_diamond` for the raw endpoint and
identify the exact-yield witnesses with its chosen off-axis steps through their
equal `executeOne` equations.

Add a finite counterexample distinct from the foreign-phase edit model:

- the foreign raw forward changes a state observation read by the other
  iterator;
- the observed iterator therefore chooses a different syntactic external undo
  code after that raw forward;
- both codes interpret as the same state function;
- ordinary `Independent` and semantic yield stability hold; but
- `LifecycleYieldStable` for that cross-forward map fails.

This proves the strengthened premise is genuinely extra and cannot be recovered
from noninjective semantic inverse equality.

## 4. Landing outcome and aligned activation

Represent exactly the two covered rule kinds:

```lean
inductive LandingOutcome
    (step : IterationStep dynamics owner code before) where
  | iter (next : sig.IteratorCode) (continues : step.next = some next)
  | finish (done : step.next = none)
```

Package one complete common-source activation:

```lean
structure ProgramAlignedLandingActivation
    (program : Program dynamics) (before : State catalog Ambient) where
  fiber : Fiber catalog
  present : before.registry program.owner = some fiber
  code : sig.IteratorCode
  undos : List (UndoCode sig)
  committed : CommittedView (catalog.declaration fiber.component)
  phase : fiber.phase = .reloading code undos committed
  target : targetView before program.owner fiber = some committed
  landing : Landing dynamics program.owner code before fiber
  program_witness : LandingProgramWitness program landing
  outcome : LandingOutcome landing.step
```

Define, from these fields:

- the exact lifecycle phase written after the landing;
- the exact endpoint;
- the corresponding `Transition.iter` or `Transition.finish` witness;
- its lifecycle rule; and
- well-formedness preservation.

The phase must be constructed from the actual landing data:

```text
Iter:
  reloading next
    (landing.step.undo :: undos)
    (landing.component_eq.symm ▸ committed)

Finish:
  active
    (landing.step.undo :: undos)
    (landing.component_eq.symm ▸ committed)
```

Do not accept an arbitrary phase payload and later call it an Iter/Finish phase.

## 5. Foreign source-fiber preservation

Prove that an aligned landing activation at owner `m` preserves the exact source
fiber of every distinct name `n`:

```lean
theorem foreign_present_after
    (activation : ProgramAlignedLandingActivation program before)
    (different : name ≠ program.owner)
    (present : before.registry name = some fiber) :
    activation.after.registry name = some fiber
```

Use:

- `GlobalTraceFacts.iteration_foreign_lookup` for the raw landing; and
- `setPhase_lookup_other` for the final owner phase edit.

This exact result transports the other activation's source fiber, reloading
phase, code, undo list, and committed view without a new assumption.

## 6. Foreign target preservation

Under source well-formedness, prove that a foreign aligned landing activation
preserves an already existing target view:

```lean
theorem targetView_preserved_by_foreign_landing
    (wf : WellFormed before)
    (activation : ProgramAlignedLandingActivation program before)
    (different : program.owner ≠ consumer)
    (consumerPresent : before.registry consumer = some consumerFiber)
    (target :
      targetView before consumer consumerFiber = some committed) :
    activation.after.registry consumer = some consumerFiber ∧
      targetView activation.after consumer consumerFiber = some committed
```

Proof obligations:

1. turn `target` into `IsTargetView` using `targetView_sound`;
1. retain the consumer fiber with `foreign_present_after`;
1. for each dependency, obtain its active provider from the source target;
1. prove that provider is not the activation owner because the owner source
   phase is reloading while the provider is active;
1. preserve that provider through the raw iteration and owner phase edit;
1. rebuild `IsTargetView` at the successor; and
1. use `Transition.preservesWellFormed` plus `targetView_eq_of_isTarget` for the
   exact chosen view.

Do not add an external target-stability law. The theorem must derive this fact
from current confinement, source phase, and well-formedness.

## 7. Reframing a landing under a fixed program

Given one `PhaseFramedExecution`, construct the actual moved `Landing` using:

- the fixed program's registration-error type and oracle;
- the framed moved step and exact program execution;
- the exact source owner-fiber lookup after the foreign activation;
- the retained post-raw owner fiber from `PhaseFramedDiamond`; and
- the original landing's component and phase equalities.

A helper must use the common-source landing only as a control/fiber template;
the framed execution is based on the distinct off-axis raw step:

```lean
def Landing.reframeFromTemplate
    (program : Program dynamics)
    (template : Landing dynamics program.owner code origin sourceFiber)
    {baseState : State catalog Ambient}
    {baseStep : IterationStep dynamics program.owner code baseState}
    {foreignName : sig.Name}
    {foreignFiber : Fiber catalog}
    {foreignPhase : Phase (catalog.declaration foreignFiber.component)}
    (framed : PhaseFramedExecution program baseStep
      foreignName foreignFiber foreignPhase)
    (sourcePresent :
      (setPhase baseState foreignName foreignFiber foreignPhase).registry
        program.owner = some sourceFiber)
    (afterPresent : framed.movedStep.after.registry program.owner =
      some template.afterFiber) :
    Landing dynamics program.owner code
      (setPhase baseState foreignName foreignFiber foreignPhase)
      sourceFiber
```

No new dynamics or oracle law is allowed in this helper. Those laws have already
been consumed by `ForeignPhaseCompatibility`. Reuse `template.afterFiber`,
`component_eq`, and `phase_eq`; take the moved step/execution from `framed`.
Do not assume that `baseStep = template.step`—their source states differ.

## 8. Constructing the moved activation

From an original aligned activation and one appropriate side of a
`PhaseFramedDiamond`, construct an aligned activation after the foreign first
step.

The construction must derive:

- the unchanged source fiber and exact reloading phase;
- the unchanged target view from Section 6;
- the moved program-aligned landing from Section 7;
- exact equality from the common-source landing to the off-axis raw step via
  `LifecycleForwardDiamond`;
- exact equality from the off-axis raw step to the phase-framed moved step via
  `PhaseFramedExecution.yield_agrees`;
- their transitive `LifecycleYieldAgrees`, including exact undo-code equality;
- exact equality of the moved landing's continuation;
- the same Iter versus Finish outcome;
- the actual dependent phase payload from the moved landing; and
- equality between the moved transition endpoint and the corresponding endpoint
  stored by `PhaseFramedDiamond`.

Dependent committed-view transports must be proved coherent. Reuse or adapt the
transport helpers in `GlobalLifecycleBisimulation`; do not assume equality of
casts as an external premise.

## 9. Exact landing-activation diamond

Package the result:

```lean
structure LandingActivationDiamond
    (left : ProgramAlignedLandingActivation leftProgram origin)
    (right : ProgramAlignedLandingActivation rightProgram origin) where
  leftFirst : Transition dynamics inertia origin left.after
  rightFirst : Transition dynamics inertia origin right.after
  rightAfterLeft :
    ProgramAlignedLandingActivation rightProgram left.after
  leftAfterRight :
    ProgramAlignedLandingActivation leftProgram right.after
  final : State catalog Ambient
  left_then_right : rightAfterLeft.after = final
  right_then_left : leftAfterRight.after = final
```

Prove a noncomputable constructor or theorem:

```lean
theorem landing_activation_diamond
    (wf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (exact : ForwardLifecycleIndependent leftProgram rightProgram)
    (leftCompatible : ForeignPhaseCompatibility leftProgram)
    (rightCompatible : ForeignPhaseCompatibility rightProgram)
    (left : ProgramAlignedLandingActivation leftProgram origin)
    (right : ProgramAlignedLandingActivation rightProgram origin) :
    LandingActivationDiamond left right
```

The proof must:

1. construct `LifecycleForwardDiamond` from `exact`;
1. instantiate or align `phase_framed_diamond` using `exact.independent`, the
   two actual landing after-fibers, and actual Iter/Finish phase payloads;
1. preserve both foreign source fibers and target views;
1. construct both moved program-aligned landings;
1. preserve each exact Iter/Finish outcome using `LifecycleYieldAgrees`;
1. construct both moved lifecycle transitions; and
1. use the framed endpoint equality as the one shared exact final state.

The four constructor combinations—Iter/Iter, Iter/Finish, Finish/Iter, and
Finish/Finish—must all compile through this one surface or four explicitly named
theorems.

## 10. Required necessity evidence

### Exact cross-forward yield syntax

Give a finite model where two programs satisfy ordinary `Independent`, and one
program's raw forward changes an observation used by the other iterator to pick
between two distinct external undo codes. Interpret both codes as the same state
function. Prove semantic cross-forward `YieldAgrees`, but refute
`LifecycleYieldStable` and therefore `ForwardLifecycleIndependent`.

This model must use a foreign raw iterator execution, not a foreign phase edit;
the latter gap is already covered by `GlobalForeignPhase.IndependenceGap`.

### Common-source applicability

Give a finite well-formed model where a provider L-Finish makes a consumer
L-Begin available, but the consumer Begin target is absent at the predecessor.
This proves the common-source applicability premise cannot be dropped from a
future full activation theorem.

### Fixed program/oracle provenance

Give a finite model with two legal `Landing` witnesses for the same owner/code
whose state-dependent oracles choose different registration children. Prove that
the bare landing type does not determine a `LandingProgramWitness` for an
arbitrarily selected fixed program.

The counterexample should attack provenance, not repeat the foreign-phase oracle
counterexample already in `GlobalForeignPhase`.

### Well-formedness boundary

If a compact model is practical, show that without `WellFormed`, ambiguous active
providers prevent reconstructing the same chosen target view. Otherwise retain
this as an explicit nonclaim and make the target-preservation theorem's
well-formedness premise visible in every public wrapper.

## 11. Explicit non-claims

This slice does not prove:

- any L-Begin-containing transposition pair;
- the full activation relation of paper Lemma 71(1);
- activation/orchestration exchange from Lemma 71(2);
- that an arbitrary `Landing` belongs to a chosen program;
- that ordinary Definition 60 `Independent` preserves the syntactic undo code
  across a foreign raw forward map;
- episode-level fixed program/root/oracle provenance;
- that the second step of an existing trace equals the program-aligned moved step
  constructed by the diamond;
- arbitrary adjacent trace swapping or mixed-trace reordering;
- Theorem 61, Corollary 62, confluence, or canonical forms; or
- Definition 65/Theorem 66 progress.

The exact claim is:

> Under explicit source well-formedness, distinct owners, program-aligned
> common-source L-Iter/L-Finish activations, semantic program independence plus
> exact cross-forward lifecycle-yield stability, and foreign-phase
> compatibility, both landing-activation orders exist and have one exact final
> state.

Do not call this result paper Lemma 71.

## 12. Verification requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalLandingTransposition
lake env lean Cordis/GlobalLandingTransposition.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalLandingTransposition.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, and compiler implementation
overrides. Add an executable rule-pair example, a guarded rejection of bare
landing/program provenance, and selected axiom entries before importing the
module through `Cordis.lean`.
