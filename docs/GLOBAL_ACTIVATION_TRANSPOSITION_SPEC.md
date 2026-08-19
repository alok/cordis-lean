# Fixed-program activation transposition: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: implemented by `Cordis.GlobalActivationTransposition`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 48,
Definition 60, and Lemma 71(1).

## 1. Goal

Implement `Cordis.GlobalActivationTransposition`, a fixed-program exact-state
transposition theorem for all nine common-source combinations of L-Begin,
L-Iter, and L-Finish.

The module must build on, rather than restate:

- `GlobalIteratorIndependence.Program`, `Reach`, and `Independent`;
- `GlobalTransposition.ForeignPhaseCompatibility` and exact phase-edit
  commutation;
- `GlobalForeignPhase.PhaseFramedExecution` and `PhaseFramedDiamond`; and
- `GlobalLandingTransposition.ProgramAlignedLandingActivation`,
  `ForwardLifecycleIndependent`, and the four-case landing diamond.

The central public theorem receives two complete activations that are already
applicable at one well-formed common source. It must reconstruct both execution
orders and prove that they have one exact final state. A second theorem receives
an actual normal-order second activation and uses endpoint determinism to turn
the common-source diamond into the local adjacent-transposition conclusion of
paper Lemma 71(1).

This is still a bounded refinement of the paper result. Iterator execution is
partial, registration uses a fixed explicit oracle, reachability is witnessed,
and lifecycle-visible syntactic undo equality is stronger than semantic
equality of interpreted inverse functions.

## 2. Exact source target

For two adjacent paper steps `t` and `t + 1`, Lemma 71(1) assumes:

- a well-formed registry at the predecessor;
- distinct acted-on fibers;
- both rules are in `{L-Begin, L-Iter, L-Finish}`;
- pairwise iterator independence; and
- the later step is already applicable at the predecessor.

It concludes that the first step remains applicable after executing the later
step first and that the two orders have the same endpoint.

The bounded executable calculus separates the proof obligations that the paper
packages into “independence”:

1. `ForwardLifecycleIndependent` supplies semantic iterator independence and,
   only for two iterator-backed activations, exact cross-forward syntactic
   yield stability.
1. `ForeignPhaseCompatibility` supplies exact execution framing through the
   other fiber's lifecycle phase edit.
1. structural lookup and positive-target preservation transport applicability;
1. `setPhase_commute` commutes distinct-owner control edits; and
1. fixed program/oracle provenance makes each activation endpoint
   deterministic.

The new API must preserve this separation. No premise may mention a swapped
transition, a swapped endpoint, a unified `Step`, or the desired diamond.

## 3. Reuse the program-aligned landing layer

Do not introduce a second landing representation. Reuse:

```lean
ProgramAlignedLandingActivation program before
```

Its fields already retain:

- the exact owner fiber and reloading guard;
- the reachable iterator code;
- the exact `Landing`;
- reproduction of that landing by `program.oracle`; and
- the exact Iter or Finish outcome.

This is the fixed-program/fixed-oracle provenance that a bare
`GlobalLifecycle.Landing` lacks. In particular, the new theorem must not infer
program membership from an arbitrary existing lifecycle transition.

For Begin, add the corresponding missing provenance explicitly:

```lean
program.root = (catalog.declaration fiber.component).entry
```

Without this equation, an arbitrary program with the same owner could be
attached to the Begin step even though its root iterator is not the iterator
installed by L-Begin.

## 4. Complete fixed-program activation

Define one proof-carrying activation representation with exactly one Begin
constructor and one constructor wrapping the existing landing activation:

```lean
inductive ProgramActivation
    {dynamics : Dynamics sig catalog Ambient}
    (program : Program dynamics)
    (before : State catalog Ambient) : Type (u + 1) where
  | begin
      (fiber : Fiber catalog)
      (guard : BeginGuard before program.owner fiber)
      (root_aligned :
        program.root = (catalog.declaration fiber.component).entry)
  | landing
      (activation : ProgramAlignedLandingActivation program before)
```

The landing constructor has two effective rule branches through
`activation.outcome`; therefore case analysis covers exactly Begin, Iter, and
Finish.

Derive, rather than accept as caller data:

```lean
def ProgramActivation.after : State catalog Ambient
def ProgramActivation.rule : GlobalLifecycle.Rule
def ProgramActivation.sourceFiber : Fiber catalog
def ProgramActivation.UsesIterator : Prop
def ProgramActivation.transition
    (inertia : InertiaPolicy dynamics) :
    Transition dynamics inertia before activation.after
```

The endpoint is:

- Begin: the exact L-Begin `setPhase` endpoint with the catalog entry, empty
  undo accumulator, and the guard's committed view;
- Iter/Finish: `ProgramAlignedLandingActivation.after`.

`UsesIterator` must reduce to `False` for Begin and `True` for the landing
constructor. It is a branch-indexing proposition, not a new semantic
assumption.

Also prove:

```lean
theorem ProgramActivation.source_present :
  before.registry program.owner = some activation.sourceFiber

theorem ProgramActivation.source_not_active :
  ¬activation.sourceFiber.Active

theorem ProgramActivation.preservesWellFormed
    (inertia : InertiaPolicy dynamics) :
    WellFormed before → WellFormed activation.after
```

`source_not_active` is structural: Begin starts inactive, while Iter/Finish
starts reloading.

## 5. Foreign lookup and positive-target framing

Define the lower, transition-free exact lookup frame:

```lean
structure ForeignLookupFrame
    (before after : State catalog Ambient) (actor : sig.Name) : Prop where
  lookup :
    ∀ {name : sig.Name} {fiber : Fiber catalog},
      before.registry name = some fiber →
      name ≠ actor →
      after.registry name = some fiber
```

Every `ProgramActivation` must construct such a frame:

- Begin uses `setPhase_lookup_other`;
- Iter/Finish uses
  `ProgramAlignedLandingActivation.foreign_present_after`.

From an actor lookup, `source_not_active`, and a `ForeignLookupFrame`, prove
that every source `ActiveProvider` at a distinct name survives exactly. Then
prove the one-way positive target theorem:

```lean
theorem ForeignLookupFrame.targetView_some_forward
    (frame : ForeignLookupFrame before after actor)
    (beforeWf : WellFormed before)
    (afterWf : WellFormed after)
    (actorPresent : before.registry actor = some actorFiber)
    (actorNotActive : ¬actorFiber.Active)
    (different : name ≠ actor)
    (namePresent : before.registry name = some fiber)
    (target : targetView before name fiber = some committed) :
    after.registry name = some fiber ∧
      targetView after name fiber = some committed
```

The proof must use `targetView_sound`, exact provider lookup preservation, and
`targetView_eq_of_isTarget` at the well-formed endpoint. Do not assume a new
target-stability law.

Do not claim full target-view equality. In particular, L-Finish may activate a
previously private table and change a foreign target from `none` to `some`.
Only an already-valid positive target is preserved.

Use this theorem to reconstruct another activation's exact Begin or reloading
guard after a foreign activation, retaining the same fiber, code, undo list,
committed view, and positive target.

## 6. Fixed-program endpoint determinism

Prove that a fixed program and fixed predecessor determine the endpoint:

```lean
theorem ProgramActivation.after_unique
    (left right : ProgramActivation program before) :
    left.after = right.after
```

The proof obligations are:

- the source registry lookup determines the owner fiber;
- the source phase separates Begin from reloading and fixes the reloading code,
  accumulated undos, and committed view;
- `targetView` is a function, so successful targets agree;
- `executeOne dynamics program.oracle code before` is deterministic;
- the successful step's owner lookup determines the post-raw owner fiber;
- `step.next` separates Iter from Finish and fixes the next code; and
- proof fields are irrelevant to the computed endpoint.

This theorem is false for arbitrary bare `Landing` values because two landings
may carry different registration oracles. The proof must consume the existing
`LandingProgramWitness` equations rather than assume equality of landing
records.

Add a stronger convenience theorem if useful:

```lean
theorem ProgramActivation.rule_unique
    (left right : ProgramActivation program before) :
    left.rule = right.rule
```

Endpoint determinism is the bridge from a constructed common-source diamond to
an already-given normal-order second step. It is not an assumption field.

## 7. Branch-minimal swap laws

The semantic package must request no iterator laws for Begin/Begin, only the
landing program's phase compatibility for a one-sided Begin/Landing pair, and
the full exact landing law for Landing/Landing:

```lean
structure ActivationSwapLaws
    {dynamics : Dynamics sig catalog Ambient}
    {left right : Program dynamics}
    {origin : State catalog Ambient}
    (leftActivation : ProgramActivation left origin)
    (rightActivation : ProgramActivation right origin) : Prop where
  left_phase :
    leftActivation.UsesIterator →
      ForeignPhaseCompatibility left
  right_phase :
    rightActivation.UsesIterator →
      ForeignPhaseCompatibility right
  exact :
    leftActivation.UsesIterator →
    rightActivation.UsesIterator →
      ForwardLifecycleIndependent left right
```

The final field must return `ForwardLifecycleIndependent`, not bare
`Independent`. Semantic equality of interpreted undo functions cannot identify
the syntactic `UndoCode` stored in L-Iter/L-Finish phases.

The structure is intentionally directional in its program order. Its exact
field already contains the two cross-forward directions needed by the landing
diamond.

## 8. Exact common-source diamond

Package both reconstructed orders:

```lean
structure ProgramActivationDiamond
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin) where
  rightAfterLeft : ProgramActivation rightProgram left.after
  leftAfterRight : ProgramActivation leftProgram right.after
  endpoint_eq : rightAfterLeft.after = leftAfterRight.after
```

Implement:

```lean
noncomputable def program_activation_diamond
    (inertia : InertiaPolicy dynamics)
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (left : ProgramActivation leftProgram origin)
    (right : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws left right) :
    ProgramActivationDiamond left right
```

All resulting `ProgramActivation`s must convert to actual
`GlobalLifecycle.Transition`s. The certificate therefore proves both
applicability directions, not merely equality between state expressions.

## 9. Exact nine-branch proof matrix

| Left at origin | Right at origin | Required semantic laws                                  | Endpoint construction                             |
| -------------- | --------------- | ------------------------------------------------------- | ------------------------------------------------- |
| Begin          | Begin           | none                                                    | structural guard transport and `setPhase_commute` |
| Begin          | Iter            | right compatibility                                     | frame right through left phase edit               |
| Begin          | Finish          | right compatibility                                     | frame right through left phase edit               |
| Iter           | Begin           | left compatibility                                      | frame left through right phase edit               |
| Finish         | Begin           | left compatibility                                      | frame left through right phase edit               |
| Iter           | Iter            | both compatibilities plus `ForwardLifecycleIndependent` | existing landing diamond                          |
| Iter           | Finish          | both compatibilities plus `ForwardLifecycleIndependent` | existing landing diamond                          |
| Finish         | Iter            | both compatibilities plus `ForwardLifecycleIndependent` | existing landing diamond                          |
| Finish         | Finish          | both compatibilities plus `ForwardLifecycleIndependent` | existing landing diamond                          |

### Begin versus Begin

Transport each positive Begin target through the other activation's lookup
frame, construct both moved Begin activations with the same root-alignment
proofs, and conclude with `setPhase_commute` for distinct owners.

### Begin versus Landing

For the landing program:

1. obtain its compatibility certificate from the corresponding branch of
   `ActivationSwapLaws`;
1. call `ForeignPhaseCompatibility.frame` on the common-source landing step and
   the Begin phase payload;
1. structurally transport the landing owner's source lookup and positive target
   through the Begin activation;
1. obtain the same post-raw owner fiber by rewriting `framed.after_eq` and using
   `setPhase_lookup_other`;
1. call `reframeActivation` with
   `LifecycleYieldAgrees.refl` because the framed base step is definitionally
   the original common-source landing step;
1. preserve the exact Iter/Finish outcome from the framed continuation; and
1. use `framed.after_eq` followed by `setPhase_commute` to identify the two
   lifecycle endpoints.

For the moved Begin, transport its guard through the landing activation using
the structural positive-target theorem. Reuse the same root-alignment proof.

The opposite orientation is symmetric but should remain visible in the
constructor case analysis.

### Landing versus Landing

Extract from `laws.exact`:

- `ForwardLifecycleIndependent leftProgram rightProgram`;
- its semantic `Independent` projection; and
- exact cross-forward lifecycle yield stability.

Extract both `ForeignPhaseCompatibility` certificates and call the existing
`landing_activation_diamond`. Wrap its two moved landing activations back into
`ProgramActivation.landing`; its exact final-state equations discharge the new
diamond endpoint.

Do not duplicate the raw framed-diamond proof in this module.

## 10. Paper-shaped adjacent transposition

Represent the actual normal-order second activation and the common-source
applicability witness separately:

```lean
structure ProgramActivationTransposition
    (leftAtOrigin : ProgramActivation leftProgram origin)
    (rightAfterLeft : ProgramActivation rightProgram leftAtOrigin.after)
    (rightAtOrigin : ProgramActivation rightProgram origin) where
  leftAfterRight : ProgramActivation leftProgram rightAtOrigin.after
  endpoint_eq : leftAfterRight.after = rightAfterLeft.after
```

Implement:

```lean
noncomputable def transpose_program_activations
    (inertia : InertiaPolicy dynamics)
    (originWf : WellFormed origin)
    (different : leftProgram.owner ≠ rightProgram.owner)
    (leftAtOrigin : ProgramActivation leftProgram origin)
    (rightAfterLeft :
      ProgramActivation rightProgram leftAtOrigin.after)
    (rightAtOrigin : ProgramActivation rightProgram origin)
    (laws : ActivationSwapLaws leftAtOrigin rightAtOrigin) :
    ProgramActivationTransposition
      leftAtOrigin rightAfterLeft rightAtOrigin
```

Proof:

1. construct the common-source `ProgramActivationDiamond`;
1. apply `ProgramActivation.after_unique` to identify the constructed
   `rightAfterLeft` endpoint with the supplied actual normal-order second
   activation endpoint; and
1. compose that equation with the common-source diamond equation.

Derive the actual swapped lifecycle transition without accepting one as an
assumption:

```lean
def ProgramActivationTransposition.swappedTransition
    (result : ProgramActivationTransposition
      leftAtOrigin rightAfterLeft rightAtOrigin)
    (inertia : InertiaPolicy dynamics) :
    Transition dynamics inertia rightAtOrigin.after rightAfterLeft.after
```

This is the bounded local content of paper Lemma 71(1): the later activation is
explicitly applicable at the earlier state, the first activation is
reconstructed after it, and the final endpoint is unchanged.

## 11. Required executable and negative evidence

### Positive all-branch coverage

Compile witnesses for at least:

- Begin/Begin;
- Begin/Finish;
- Iter/Finish; and
- Finish/Finish.

At least one theorem must instantiate `transpose_program_activations` with a
supplied actual normal-order second activation and produce the swapped
transition. Add a small executable projection that distinguishes the rule pair
without placing `#eval` in a library module.

The generic constructor's exhaustive case split is the proof that all nine
combinations are covered; examples need not duplicate every symmetric branch.

### Root provenance

Give a finite witness where a Begin guard is valid for a fiber whose catalog
entry is `false`, while a same-owner program has root `true`. Prove that the
guard alone cannot construct `ProgramActivation.begin` for that program.

### Distinct-owner necessity

Give a finite same-owner witness with two different phase payloads and prove
that the two point updates do not commute. This isolates why the public diamond
requires `leftProgram.owner ≠ rightProgram.owner`.

### Reuse existing necessity models

Do not clone the landing module's countermodels. Reference or instantiate its
existing evidence for:

- common-source applicability;
- fixed program/oracle landing provenance; and
- semantic versus syntactic undo agreement.

The new module may expose concise bridge theorems showing these models block the
corresponding omitted premises.

## 12. Explicit non-claims

This slice does not prove:

- paper Lemma 71 verbatim in its total/quotient setting;
- L-Divert, L-Raise, L-Leave, L-Unload, or orchestration exchange;
- Lemma 71(2) activation/orchestration transposition;
- assignment of arbitrary existing lifecycle transitions to programs;
- global episode-level root/oracle provenance;
- preservation of absent targets or full target-view equality;
- totality of off-source iterator execution;
- that semantic `Independent` alone preserves syntactic undo codes;
- that `Independent` alone implies foreign-phase compatibility;
- arbitrary adjacent rewriting of a stored trace;
- support acyclicity, Lemma 68, or Lemma 70;
- Theorem 61, Corollary 62, Lemma 72, Theorem 73, or confluence; or
- Definition 65/Theorem 66 progress.

The exact claim is:

> At a well-formed common source, two distinct-owner fixed-program activations
> in `{L-Begin, L-Iter, L-Finish}` commute to one exact final state when the
> branch-relevant foreign-phase and exact lifecycle-yield obligations are
> supplied. If an actual normal-order second activation is also supplied,
> fixed-program endpoint determinism yields an actual swapped first activation
> with the same final endpoint.

## 13. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalActivationTransposition
lake env lean Cordis/GlobalActivationTransposition.lean
uv run scripts/check_lean_hygiene.py \
  Cordis/GlobalActivationTransposition.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. add positive runtime projections in `Cordis.TestSuite`;
1. add root/provenance or branch-law failures to `Cordis.NegativeTests`;
1. add selected endpoint, diamond, transposition, and necessity declarations to
   `Cordis.AxiomAudit`;
1. change this specification's status to implemented and update `README.md`,
   `SPEC.md`, `docs/PAPER_MAP.md`, `docs/V0_2_SPEC.md`,
   `docs/TRUST_BOUNDARY.md`, and `docs/IMPLEMENTATION_GUIDE.md`;
1. run the complete strict build, runtime suite, demo, hygiene, documentation,
   link, and selected-axiom gates; and
1. repeat the gates from a clean `git archive` before pushing.
