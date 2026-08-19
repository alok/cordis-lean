# Corrected activation/orchestration transposition: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: implemented by `Cordis.GlobalActivationOrchestrationTransposition`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 47,
Definition 53, Definition 60, and Lemma 71(2).

## 1. Goal

Implement `Cordis.GlobalActivationOrchestrationTransposition`, a corrected
exact-state exchange theorem for:

```text
fixed-program activation at m;
then orchestration at n;
m != n.
```

The module must begin by kernel-refuting the literal paper side condition that
the activation merely “does not register `n`.” Two independent obstructions
exist:

1. the activation may register a distinct name `r` that the following O-Insert
   uses as `n`'s parent, so that O-Insert is unavailable before the activation;
1. even when both insertion orders are available, registration and O-Insert
   consume the local proof-only birth clock in opposite orders, so their exact
   `GlobalState`s differ.

After exposing those failures, prove the strongest source-honest exact theorem
available in the current birth-ranked representative:

- Begin exchanges structurally with O-Insert, O-Retire, and O-Remove;
- ordinary Iter/Finish exchanges with all three under the corresponding exact
  execution-frame law;
- registering Iter/Finish exchanges with O-Retire and O-Remove under exact
  execution framing and child/actor inequality; and
- registering Iter/Finish is deliberately excluded from exact O-Insert
  exchange.

This is a corrected bounded analogue, not paper Lemma 71(2) verbatim.

## 2. Why the literal paper clause is false

The pinned statement assumes that the activation does not register the name on
which the following orchestration step acts. Its proof says the O-Insert
premises “only relax” in the smaller registry before the activation.

That argument omits O-Insert's parent premise:

```text
parent in dom(registry) or parent = root.
```

### 2.1 Parent-enablement gap

Construct a well-formed predecessor with activation owner `m`. Let its
registering iteration create child `r`. Then apply:

```text
O-Insert n with parent = r
```

for `r != n`.

The literal paper condition holds—the activation registered `r`, not `n`—but
the O-Insert is applicable only after the activation. Prove at least:

```lean
theorem parent_adoption_blocks_early_insert :
  (∃ fiber, registered.registry r = some fiber) ∧
    ¬(∃ fiber, origin.registry r = some fiber)
```

Prefer a full `ProgramActivation` followed by an `OrchestrationStep.insert`
witness if it can be kept compact; otherwise retain the exact `insertFiber`
states plus well-formedness and all O-Insert premises.

### 2.2 Birth-order gap

`GlobalState` contains a proof-oriented `nextBirth`, and every inserted fiber
stores the current rank. For two distinct insertions:

```text
normal:  register r at b; O-Insert n at b + 1
swapped: O-Insert n at b; register r at b + 1
```

both orders may be applicable, use the same child, parent, and component, and
still have unequal exact endpoints. Prove this by projecting `Fiber.birth`:

```lean
theorem registration_insert_birth_order_differs : normal ≠ swapped
```

Current `RuleRelated` also observes fiber birth and the global clock; it does
not erase this difference. Name equivariance does not repair fixed actor
identities plus swapped rank assignments. A birth-erasing quotient would be a
separate theorem surface.

These counterexamples must remain public evidence, not only documentation.

## 3. Classify the name registered by one activation

Dependent elimination over `IterationStep.source` is easiest through a
source-indexed helper:

```lean
def sourceRegisteredChild
    (source :
      StepSource dynamics owner code before after undo next) :
    Option sig.Name :=
  match source with
  | .ordinary .. => none
  | .registration _ admission _ => some admission.child
```

Then define:

```lean
def stepRegisteredChild
    (step : IterationStep dynamics owner code before) : Option sig.Name :=
  sourceRegisteredChild step.source

def ProgramActivation.registeredChild
    (activation : ProgramActivation program before) : Option sig.Name :=
  match activation with
  | .begin .. => none
  | .landing aligned => stepRegisteredChild aligned.landing.step
```

Because `ProgramActivation` is imported from another module, either define this
extension explicitly inside:

```lean
namespace Cordis.GlobalActivationTransposition.ProgramActivation
```

or use the new module's fully qualified declaration everywhere. Do not rely on
ambiguous relative dot-notation namespace lookup.

Do not match directly on `step.source` with a motive that retains the entire
dependent `IterationStep` if Lean requires the indexed helper above.

Useful exact facts must include:

- Begin registers no child;
- an ordinary landing registers no child;
- a registration landing returns exactly `some admission.child`; and
- `registeredChild = none` rules out the registration source constructor.

## 4. Orchestration-sensitive registration safety

Define the smallest condition supporting exact representative exchange:

```lean
def RegistrationSafe
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) : Prop :=
  match normal with
  | .insert .. => activation.registeredChild = none
  | .retire _ name .. => activation.registeredChild ≠ some name
  | .remove _ name .. => activation.registeredChild ≠ some name
```

The asymmetry is intentional:

- O-Insert requires the activation to register no child at all. This removes
  both parent enablement and exact birth-rank exchange.
- O-Retire/O-Remove require only the paper-style fact that their actor was not
  created by the activation.

Do not weaken the O-Insert branch to:

```lean
activation.registeredChild ≠ some orchestrationActor
```

because both kernel counterexamples satisfy that weaker premise.

## 5. Reify the exact orchestration edit and template

For one actual orchestration occurrence, expose the pure total state edit it
represents:

```lean
def orchestrationReplay
    (step : OrchestrationStep before after) :
    State catalog Ambient → State catalog Ambient :=
  match step with
  | .insert _ name _ parent _ component _ =>
      fun state => insertFiber state name parent component
  | .retire _ name fiber _ =>
      fun state => retireFiber state name fiber
  | .remove _ name .. =>
      fun state => removeFiber state name
```

Prove:

```lean
@[simp] theorem orchestrationReplay_before
    (step : OrchestrationStep before after) :
    orchestrationReplay step before = after
```

Two occurrences count as the same orchestration operation only when endpoint-
relevant data agree:

```lean
structure SameOrchestrationTemplate
    (left : OrchestrationStep leftBefore leftAfter)
    (right : OrchestrationStep rightBefore rightAfter) : Prop where
  same_kind : orchestrationKind left = orchestrationKind right
  same_actor : orchestrationName left = orchestrationName right
  replay_eq : orchestrationReplay left = orchestrationReplay right
```

Use the standalone `orchestrationReplay` name, or deliberately enter
`Cordis.GlobalRegistry.OrchestrationStep`; do not accidentally create a second
relative `OrchestrationStep` namespace in the new module.

For O-Retire, `replay_eq` must retain the exact `Fiber` payload, not merely kind
and name. It is acceptable instead to use an inductive template with explicit
same-name/parent/component/fiber constructors, provided it implies exact replay
equality.

Reuse the existing `OrchestrationKind`, `orchestrationKind`, and
`orchestrationName` declarations from `GlobalVestigial` rather than inventing
incompatible public classifications.

## 6. Exact off-source execution framing

An orchestration edit is not an iterator-family generator. Neither
`Independent` nor `ForeignPhaseCompatibility` says that `runIterator` or the
fixed oracle ignores it.

Define the lower noncircular exact frame as an existential proposition:

```lean
def ExactExecutionFrame
    (program : Program dynamics)
    (step : IterationStep dynamics program.owner code state)
    (edit : State catalog Ambient → State catalog Ambient) : Prop :=
  ∃ movedStep :
      IterationStep dynamics program.owner code (edit state),
    executeOne dynamics program.oracle code (edit state) = .ok movedStep ∧
      LifecycleYieldAgrees movedStep step ∧
      movedStep.after = edit step.after
```

Do not declare a `Prop`-valued structure with a computational `movedStep`
field; Lean forbids data elimination from such a proposition. The existential
form keeps compatibility laws in `Prop`, and the theorem may choose the moved
step noncomputably. A `Type`-valued frame is also sound but would force every
containing record into `Type`.

The frame mentions no lifecycle `Transition`, orchestration guard, swapped
endpoint, or exchange conclusion.

## 7. Occurrence-minimal branch-specific law

Do not make the public theorem require a program-wide compatibility law over
illegal orchestration edits. Such a law would unnecessarily quantify insertions
without freshness/parent/provision guards and removals of absent, installed, or
parented fibers.

Instead define the exact frame required by this one supplied normal occurrence:

```lean
def ExecutionFrameFor
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) : Prop :=
  match activation with
  | .begin .. => True
  | .landing aligned =>
      ExactExecutionFrame program aligned.landing.step
        (orchestrationReplay normal)
```

The public swap certificate is therefore exactly:

```lean
structure ActivationOrchestrationSwapLaws
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) : Prop where
  registration_safe : RegistrationSafe activation normal
  execution_frame : ExecutionFrameFor activation normal
```

This surface is compiler-checked and occurrence-minimal:

- Begin reduces `execution_frame` to `True` and needs no semantic law;
- a landing carries exactly one moved raw execution under the concrete normal
  orchestration replay; and
- `RegistrationSafe` separately rules out the exact registration/Insert branch.

No `Independent` or `ForwardLifecycleIndependent` premise is needed: the
orchestration rule's raw map is identity, and its registry edit is handled
directly.

Optional reusable program-scoped Insert/Retire/Remove compatibility records may
be added only as convenience constructors for `ExecutionFrameFor`. If added,
they must quantify legal orchestration guard premises and retain the source
registration restrictions; they are not part of the minimal theorem authority.

## 8. Backward transport of orchestration applicability

From the actual normal-order orchestration step, actor inequality, and
`RegistrationSafe`, reconstruct the same template at the common predecessor.

Prove structural lookup lemmas classifying the activation endpoint:

- a name other than a registered child was present after the activation only
  if it was present before;
- every pre-existing foreign fiber is preserved exactly;
- the source owner remains present with the same component, parent, birth, and
  retirement fields; and
- when no child was registered, registry domain and component declarations are
  unchanged.

### 8.1 O-Insert

`registeredChild = none` makes the activation either Begin or ordinary
Iter/Finish. It creates no name.

Transport backward:

- inserted-name freshness, by contradiction through exact foreign lookup;
- parent presence, splitting whether the parent is the activation owner or a
  foreign name;
- component/provision freshness, because no component declaration or registry
  name changed; and
- the same name, parent, and component template.

An ordinary iteration may still read `nextBirth`; that is why the exact insert
execution frame remains necessary even though the step does not write the
clock.

### 8.2 O-Retire

Normal O-Retire supplies the exact actor fiber at `activation.after`. Because
the activation did not create that actor, derive that the same exact fiber was
already present at `origin`. Reconstruct:

```lean
OrchestrationStep.retire origin name normalFiber ...
```

and retain identical replay functions.

### 8.3 O-Remove

Transport the exact actor fiber, retirement, and inactive phase backward.
Childlessness also transports:

- Begin/ordinary activation creates no child;
- a registering activation adds only one child whose parent is the activation
  owner;
- distinct actors imply that child is not a child of the removed actor; and
- if the activation owner itself were a child of the removed actor, the actual
  normal O-Remove would already violate childlessness.

No extra childlessness premise is allowed in the corrected law package.

## 9. Preserve activation applicability after early orchestration

Every early orchestration edit preserves the activation owner's exact source
fiber because the actors are distinct.

Preserve the activation's already-valid positive target structurally:

- O-Insert adds an inactive empty-table fiber, so it supplies no value;
- O-Retire changes only retirement, not the fiber's active phase or table; and
- O-Remove may remove only an inactive fiber, so it was not an active provider.

Use `targetView_sound`, orchestration well-formedness preservation, and
`targetView_eq_of_isTarget`. Do not assume target equality as an external law,
and do not claim preservation of an absent target.

For Begin, these facts alone reconstruct the moved activation with the same
root-alignment proof.

## 10. Reframe an iterator-backed activation

Generalize the existing landing helper to an arbitrary exact edit frame:

```lean
def Landing.reframeFromEditTemplate
    (program : Program dynamics)
    (template : Landing dynamics program.owner code origin sourceFiber)
    (edit : State catalog Ambient → State catalog Ambient)
    (movedStep :
      IterationStep dynamics program.owner code (edit origin))
    (executed :
      executeOne dynamics program.oracle code (edit origin) = .ok movedStep)
    (sourcePresent : (edit origin).registry program.owner = some sourceFiber)
    (afterPresent : movedStep.after.registry program.owner =
      some template.afterFiber) :
    Landing dynamics program.owner code (edit origin) sourceFiber
```

The theorem must destruct the existential frame and pass its chosen
`movedStep` and execution equation to this `Type`-valued helper. Retain the
frame's yield agreement and raw endpoint equation in the caller, where they are
used to reconstruct the moved high-level activation and final endpoint.

Reuse from the common landing:

- `afterFiber`;
- `component_eq`;
- `phase_eq`.

Take the moved step and exact program execution from the frame. Each
orchestration replay preserves the distinct owner lookup, so `afterPresent`
must be derived rather than assumed by the public theorem.

Use `LifecycleYieldAgrees` to preserve:

- exact stored `UndoCode`;
- continuation and therefore Iter versus Finish; and
- ordinary versus registration source kind/component.

Construct the actual moved `ProgramAlignedLandingActivation` and prove its
endpoint equals:

```text
setPhase (orchestrationReplay normal originalRawAfter)
  program.owner originalAfterFiber originalNextPhase.
```

## 11. Structural edit/phase commutation

Prove or reuse:

- `insertFiber_setPhase_commute` for distinct names;
- `retireFiber_setPhase_commute`, derived from `Coeffect.setAt_commute`; and
- `removeFiber_setPhase_commute`, derived from
  `Coeffect.setAt_removeAt_commute`.

For a registering activation followed by Retire or Remove, the execution frame
handles insertion of the stable selected child before replaying the
orchestration edit. Registering activation followed by Insert is excluded.

## 12. Corrected exact theorem

Package only conclusions:

```lean
structure ActivationOrchestrationTransposition
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final) where
  orchestrationFirstState : State catalog Ambient
  orchestrationFirst : OrchestrationStep origin orchestrationFirstState
  activationSecond : ProgramActivation program orchestrationFirstState
  same_template :
    SameOrchestrationTemplate orchestrationFirst normal
  endpoint_eq : activationSecond.after = final
```

Implement:

```lean
noncomputable def transpose_activation_orchestration
    (inertia : InertiaPolicy dynamics)
    (originWf : WellFormed origin)
    (activation : ProgramActivation program origin)
    (normal : OrchestrationStep activation.after final)
    (different :
      program.owner ≠ orchestrationName normal)
    (laws : ActivationOrchestrationSwapLaws activation normal) :
    ActivationOrchestrationTransposition activation normal
```

The result must construct:

- the early orchestration step at `origin`;
- the moved actual Begin/Iter/Finish activation;
- exact same-kind, same-actor, same-replay evidence; and
- exact equality with the supplied normal-order final state.

No swapped transition, swapped endpoint, common-source orchestration witness,
or replay equation may enter an assumption record.

## 13. Exact proof matrix

| Activation source       | O-Insert                    | O-Retire                        | O-Remove                        |
| ----------------------- | --------------------------- | ------------------------------- | ------------------------------- |
| Begin                   | structural; no frame        | structural; no frame            | structural; no frame            |
| ordinary Iter/Finish    | restricted insert frame     | retire frame                    | remove frame                    |
| registering Iter/Finish | excluded from exact theorem | retire frame and child != actor | remove frame and child != actor |

The high-level Iter versus Finish outcome is independent of the raw source kind.
Classify ordinary versus registration through `landing.step.source`, not through
`LandingOutcome`.

## 14. Required necessity evidence

### Parent enablement

Kernel-prove the Section 2.1 counterexample, including the distinct registered
child/orchestration actor inequality.

### Birth-rank order

Kernel-prove the Section 2.2 exact-state inequality. Also prove that the current
`RuleRelated` candidate cannot identify the endpoints if a compact witness is
practical.

### Insert-sensitive ordinary execution

Give a nonregistering ordinary iterator that reads `nextBirth` to choose its
exact undo code or continuation. O-Insert changes `nextBirth`, while
`OrdinaryConfinement.nextBirth_eq` remains satisfied because the iterator does
not write it. Prove that well-formedness plus nonregistration does not imply
the required occurrence-specific `ExactExecutionFrame`.

### Orchestration-sensitive oracle

Give at least one fixed-oracle registration model for Retire or Remove:

- Retire variant: choose different children depending on the foreign actor's
  retired flag; or
- Remove variant: choose the removed actor only after that name becomes absent.

The original activation must satisfy the paper child/actor inequality, while
the moved execution changes child, undo, continuation, or definedness. Prove
that registration safety alone does not imply the required exact frame.

## 15. Positive executable evidence

Compile at least:

- Begin followed by O-Insert;
- Begin followed by O-Retire or O-Remove;
- ordinary Finish followed by O-Insert; and
- registering Finish followed by O-Retire or O-Remove.

At least one example must instantiate the public corrected theorem with an
independently constructed actual normal-order `OrchestrationStep`, then expose
the early orchestration kind/actor and moved activation rule as executable data.

Runtime tests may inspect only these finite tags and endpoints. Attribute the
universal theorem and premise separations to kernel declarations.

## 16. Explicit non-claims

This slice does not prove:

- literal paper Lemma 71(2), whose side condition is kernel-refuted;
- exact registration/O-Insert exchange in the birth-ranked state;
- a birth-erasing or name/rank quotient theorem;
- derivation of insert/retire/remove execution framing from base `Dynamics`,
  `Independent`, `ForeignPhaseCompatibility`, or well-formedness;
- that the fixed oracle accepts or selects the same child after an arbitrary
  registry edit;
- preservation of absent targets or full target-view equality;
- assignment of arbitrary lifecycle transitions to fixed programs;
- arbitrary adjacent rewriting of a stored trace;
- episode-level program/oracle provenance;
- Lemma 72, Theorem 73, canonical forms, or confluence; or
- Definition 65/Theorem 66 progress.

The exact claim is:

> A fixed-program Begin or safely framed Iter/Finish activation can be moved
> after an earlier distinct-name orchestration occurrence with the same
> orchestration template and exact final state, provided O-Insert is paired only
> with a nonregistering activation and Retire/Remove do not target the child the
> activation registered. The literal weaker paper premise is false.

## 17. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalActivationOrchestrationTransposition
lake env lean Cordis/GlobalActivationOrchestrationTransposition.lean
uv run scripts/check_lean_hygiene.py \
  Cordis/GlobalActivationOrchestrationTransposition.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. add representative rule/actor projections to `Cordis.TestSuite`;
1. add a guarded rejection of the literal unsafe O-Insert registration premise
   or a type-level frame mismatch to `Cordis.NegativeTests`;
1. add selected theorem and counterexample declarations to `Cordis.AxiomAudit`;
1. update `README.md`, `SPEC.md`, `docs/PAPER_MAP.md`,
   `docs/V0_2_SPEC.md`, `docs/TRUST_BOUNDARY.md`, and
   `docs/IMPLEMENTATION_GUIDE.md`;
1. change this specification's status to implemented;
1. run the complete strict/default build, runtime suite, demo, hygiene,
   documentation, link, and selected-axiom gates; and
1. repeat all gates from a clean `git archive` before pushing.
