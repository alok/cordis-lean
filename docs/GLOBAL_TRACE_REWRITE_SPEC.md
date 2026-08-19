# Exact global trace rewriting: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: implemented by `Cordis.GlobalTraceRewrite`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Lemma 71 and the
trace-reordering prerequisites of Lemma 72 and Theorem 73.

Dependencies:

- `Cordis.GlobalCalculus` for exact indexed `Step` and `Trace`;
- `Cordis.GlobalTraceFacts` for trace append, records, states, and alignment;
- `Cordis.GlobalActivationTransposition` for the corrected fixed-program
  activation/activation swap; and
- `Cordis.GlobalActivationOrchestrationTransposition` for the corrected
  occurrence-specific activation/orchestration swap.

## 1. Goal

Implement `Cordis.GlobalTraceRewrite`, the first layer that turns the existing
two-step transposition theorems into actual rewrites of an intrinsic stored
global trace.

The module has three responsibilities:

1. identify an exact adjacent two-step window inside a supplied
   `GlobalCalculus.Trace`;
1. replace that window with another exact two-step path having the same indexed
   source and endpoint; and
1. retain enough fixed-program occurrence evidence to justify the existing
   activation transposition theorems without inferring an oracle or program
   from a bare lifecycle transition.

This is deliberately not Lemma 72 or Theorem 73. Those statements require
trace-wide deletion, support provenance, episode selection, and a relation
that forgets allocator birth ranks. This slice remains exact-state and only
rewrites pairs for which the existing corrected theorems already prove exact
endpoint equality.

## 2. Preserve the intrinsic trace index

The core trace is already the right representation:

```lean
inductive GlobalCalculus.Trace ... : State → State → Type where
  | nil
  | cons (head : Step before middle) (tail : Trace middle after)
```

Do not flatten it to a list and later revalidate adjacency. Every rewrite must
return:

```lean
GlobalCalculus.Trace dynamics inertia initial final
```

with the same `initial` and `final` indices as the supplied trace. Agreement of
the replaced pair's endpoint with the suffix source is therefore enforced by
the type checker rather than by a post-hoc proposition.

## 3. Exact two-step paths

Define the smallest exact pair:

```lean
structure StepPair
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (before after : State catalog Ambient) where
  middle : State catalog Ambient
  first : Step dynamics inertia before middle
  second : Step dynamics inertia middle after
```

The intermediate state is existential data. Source and endpoint are indices.

Derive:

```lean
def StepPair.trace : Trace dynamics inertia before after
def StepPair.rules : List GlobalCalculus.Rule
def StepPair.actors : List (GlobalCalculus.Actor sig.Name)
```

The trace is exactly two constructors followed by `nil`.

## 4. Exact adjacent swap certificate

Define:

```lean
structure ExactAdjacentSwap
    (normal : StepPair dynamics inertia before after) where
  swapped : StepPair dynamics inertia before after
  first_rule : swapped.first.rule = normal.second.rule
  second_rule : swapped.second.rule = normal.first.rule
  first_actor : swapped.first.actor = normal.second.actor
  second_actor : swapped.second.actor = normal.first.actor
```

The common exact endpoint is not a field: it is already the `after` index of
both pairs. The four projection equations record that this is a transposition
of the two supplied occurrences, not merely an unrelated alternative path
between the same states.

Do not require equality of the dependent `Step` values themselves. Their
sources differ after transposition. Do not require equality of intermediate
states; changing that state is the point of the rewrite.

If compiler repair shows that rule/actor preservation is best factored from
endpoint construction, use two records:

```lean
structure ExactPairReplacement ... where
  replacement : StepPair ...

structure ExactAdjacentSwap extends ExactPairReplacement normal where
  ... projection equations ...
```

The public activation adapters must still return the stronger
`ExactAdjacentSwap`.

## 5. Locate a pair inside one actual trace

Use an exact decomposition rather than a numeric list index:

```lean
structure AdjacentOccurrence
    (trace : GlobalCalculus.Trace dynamics inertia initial final) where
  windowStart : State catalog Ambient
  windowEnd : State catalog Ambient
  beforeTrace : GlobalCalculus.Trace dynamics inertia initial windowStart
  pair : StepPair dynamics inertia windowStart windowEnd
  afterTrace : GlobalCalculus.Trace dynamics inertia windowEnd final
  decomposition :
    trace = GlobalTraceFacts.Trace.append beforeTrace
      (.cons pair.first (.cons pair.second afterTrace))
```

The names `prefix` and `suffix` are Lean parser keywords in this toolchain; use
`beforeTrace` and `afterTrace`.

Define the actual rewrite:

```lean
def AdjacentOccurrence.rewrite
    (occurrence : AdjacentOccurrence trace)
    (swap : ExactAdjacentSwap occurrence.pair) :
    GlobalCalculus.Trace dynamics inertia initial final :=
  GlobalTraceFacts.Trace.append occurrence.beforeTrace
    (.cons swap.swapped.first
      (.cons swap.swapped.second occurrence.afterTrace))
```

This declaration is the central API-as-type-signature result: callers cannot
splice a pair whose source or endpoint fails to match the retained context.

## 6. Trace-level consequences

First prove append equations for the existing projections:

```lean
theorem Trace.rules_append ...
theorem Trace.actors_append ...
theorem Trace.records_append ...
```

Expose the exact selected records:

```lean
def StepPair.firstRecord : StepRecord dynamics inertia
def StepPair.secondRecord : StepRecord dynamics inertia

theorem AdjacentOccurrence.first_mem_records :
  occurrence.pair.firstRecord ∈ Trace.records trace

theorem AdjacentOccurrence.second_mem_records :
  occurrence.pair.secondRecord ∈ Trace.records trace
```

These membership theorems connect the dependent window to the existing
record-list audit surface.

Then prove exact window equations:

```lean
theorem AdjacentOccurrence.original_rules :
  trace.rules =
    occurrence.beforeTrace.rules ++
      occurrence.pair.first.rule ::
      occurrence.pair.second.rule ::
      occurrence.afterTrace.rules

theorem AdjacentOccurrence.rewrite_rules :
  (occurrence.rewrite swap).rules =
    occurrence.beforeTrace.rules ++
      occurrence.pair.second.rule ::
      occurrence.pair.first.rule ::
      occurrence.afterTrace.rules
```

Prove the analogous actor equation.

Also prove:

- original and rewritten rule-list lengths agree;
- original and rewritten actor-list lengths agree;
- original and rewritten rules are `List.Perm`;
- original and rewritten actors are `List.Perm`;
- `GlobalTraceFacts.Trace.aligned` holds for the rewritten trace;
- the rewritten state-list length is the rewritten record-list length plus
  one; and
- `Trace.preservesWellFormed` transports source well-formedness to the same
  exact final state.

The alignment and well-formedness facts should be applications of the generic
existing theorems, not new assumptions on `ExactAdjacentSwap`.

Do not claim equality or permutation of the state lists: the local midpoint is
intentionally replaced. In proofs involving `occurrence.decomposition`, avoid
`rw` on the dependent `trace` index while the goal also projects from
`occurrence`. Use `congrArg Trace.rules`, `congrArg Trace.actors`, or
`congrArg Trace.records` and then calculate from the resulting equality.

## 7. Fixed-program occurrence evidence

A bare lifecycle `Transition` does not determine:

- one `GlobalIteratorIndependence.Program`;
- the configured registration oracle;
- root alignment for Begin;
- reachability of a stored iterator code; or
- reproduction of a landing by that oracle.

Define a dependent bridge from one actual unified step to the existing
`ProgramActivation` evidence:

```lean
structure ProgramOccurrence
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  program : Program dynamics
  activation : ProgramActivation program before
  after_eq : activation.after = after
  step_eq :
    step = after_eq ▸ Step.lifecycle (activation.transition inertia)
```

This exact transport shape is compiler-checked. Do not replace `step_eq` with
rule equality or endpoint equality alone.

Derive:

```lean
theorem ProgramOccurrence.rule_eq :
  step.rule = (Step.lifecycle (activation.transition inertia)).rule
theorem ProgramOccurrence.actor_eq : step.actedName = program.owner
```

`activation.rule` is a `GlobalLifecycle.Rule`, while `step.rule` is the lifted
ten-name `GlobalCalculus.Rule`; do not equate those two types directly. A later
helper may export the lifecycle-to-global rule lift, but the first theorem can
state equality with the generated unified lifecycle step exactly as above.

Also define the exact orchestration bridge:

```lean
structure OrchestrationOccurrence
    {before after : State catalog Ambient}
    (step : Step dynamics inertia before after) where
  orchestration : OrchestrationStep before after
  step_eq : step = Step.orchestration orchestration
```

This prevents the activation/orchestration adapter from silently replacing an
arbitrary unified step with an unrelated orchestration witness.

## 8. Trace-wide program assignment

Define the exact activation-rule classifier:

```lean
def IsProgramActivationRule : GlobalCalculus.Rule → Prop
  | .lBegin | .lIter | .lFinish => True
  | _ => False
```

For each step, require occurrence evidence whenever that classifier is true:

```lean
structure StepProgramAssignment
    (step : Step dynamics inertia before after) where
  occurrence :
    IsProgramActivationRule step.rule → ProgramOccurrence step
```

Then mirror the intrinsic trace:

```lean
inductive TraceProgramAssignment :
    (trace : GlobalCalculus.Trace dynamics inertia before after) → Type where
  | nil ...
  | cons
      (headAssignment : StepProgramAssignment head)
      (tailAssignment : TraceProgramAssignment tail)
```

This assignment is intentionally supplied. The module must not claim that an
arbitrary existing trace admits it. Later deletion/canonical-form work may use
it to recover the fixed program and oracle at each activation occurrence.

Because rewriting changes both pair steps, the original assignment is not
definitionally an assignment for the rewritten trace. Define the stronger
result:

```lean
structure AssignedAdjacentSwap
    (normal : StepPair dynamics inertia before after)
    extends ExactAdjacentSwap normal where
  swappedFirstAssignment :
    StepProgramAssignment toExactAdjacentSwap.swapped.first
  swappedSecondAssignment :
    StepProgramAssignment toExactAdjacentSwap.swapped.second
```

The exact field names may follow Lean's generated parent projection, but the
meaning must remain this explicit.

Also define an assigned located window carrying:

- `TraceProgramAssignment` for `beforeTrace`;
- `StepProgramAssignment` for both original pair steps; and
- `TraceProgramAssignment` for `afterTrace`.

From those values derive both:

- a `TraceProgramAssignment trace`, transported through `decomposition`; and
- a `TraceProgramAssignment (occurrence.rewrite swap)`, using the two swapped
  assignments.

This prevents the trace-wide ledger from becoming ornamental and makes one
adjacent rewrite iterable without inventing new program/oracle provenance.

Provide constructors for:

- a known `ProgramActivation` step;
- an orchestration step, whose activation premise is impossible; and
- a nonactivation lifecycle step with an explicit proof that its rule is not
  Begin, Iter, or Finish.

## 9. Activation/activation adapter

The adapter must consume the actual stored pair, not construct a new
definitionally convenient pair beside it. Its core inputs are:

```lean
(normal : StepPair dynamics inertia origin final)
(leftAtOrigin : ProgramOccurrence normal.first)
(rightAfterLeft : ProgramOccurrence normal.second)
(rightAtOrigin :
  ProgramActivation rightAfterLeft.program origin)
```

The first occurrence's `after_eq` identifies its activation endpoint with
`normal.middle`. Transport the second occurrence's activation back across that
equality to obtain the exact input shape required by
`transpose_program_activations`. Compose the transported activation endpoint
with the second occurrence's `after_eq` to recover `normal`'s actual `final`
index.

Do not eliminate the first endpoint equality directly inside the fixed
dependent `StepPair`; that creates a dependent-elimination failure in Lean.
Factor named helpers for:

- transporting `ProgramActivation` across equality of source states;
- proving its derived `.after` is unchanged by that transport; and
- transporting a unified `Step` across equality of endpoint states while
  preserving its rule and acted name.

Use the theorem's swapped activation and `swappedTransition` to construct:

```lean
def transposeActivationPair ... : AssignedAdjacentSwap normal
```

The adapter must derive, not assume:

- the swapped first rule is the supplied normal second rule;
- the swapped second rule is the original first rule;
- the first actor is the right program owner; and
- the second actor is the left program owner.

Neither the current `ProgramActivationDiamond` nor
`ProgramActivationTransposition` result record stores moved-rule coherence.
Rule preservation must therefore be proved by constructor analysis over the
concrete `program_activation_diamond` or `transpose_program_activations`
function, or packaged in a derived coherent wrapper built from that function.
Do not infer it from the old result structure alone and do not strengthen the
input with a caller-supplied rule-equality law.

Require named derived theorems with the following content:

```lean
theorem program_activation_diamond_right_rule_eq ... :
  (program_activation_diamond ... left right laws).rightAfterLeft.rule =
    right.rule

theorem transpose_program_activations_left_rule_eq ... :
  (transpose_program_activations ...).leftAfterRight.rule =
    leftAtOrigin.rule

theorem transpose_program_activations_right_rule_eq ... :
  rightAtOrigin.rule = rightAfterLeft.rule
```

The last theorem must combine canonical-diamond rule coherence with
`ProgramActivation.rule_unique` for the supplied actual normal-order second
activation. Endpoint equality alone is not its proof.

Factor unified-step projections through:

```lean
def ProgramActivation.globalStep ... : Step ... :=
  .lifecycle (activation.transition inertia)

theorem ProgramActivation.globalStep_actor :
  activation.globalStep.actor = .fiber program.owner

theorem ProgramActivation.globalStep_rule_eq_of_rule_eq
    (same : left.rule = right.rule) :
  left.globalStep.rule = right.globalStep.rule
```

The last helper is a finite constructor proof that crosses from
`GlobalLifecycle.Rule` to `GlobalCalculus.Rule`; it must not identify those
types definitionally.

Every original-pair identification must come from
`ProgramOccurrence.step_eq`, and every swapped pair step must be a real
`GlobalCalculus.Step.lifecycle` containing the actual
`GlobalLifecycle.Transition` produced by the activation evidence. This wiring
is what connects the trace-wide assignment layer to rewriting an arbitrary
stored occurrence.

## 10. Activation/orchestration adapter

Again consume an actual stored pair:

```lean
(normal : StepPair dynamics inertia origin final)
(activation : ProgramOccurrence normal.first)
(orchestration : OrchestrationOccurrence normal.second)
```

Transport `orchestration.orchestration` from `normal.middle` back to
`activation.activation.after` using `activation.after_eq.symm`. Name this
transported occurrence so that `RegistrationSafe`, `ExecutionFrameFor`, and
the corrected transposition theorem all refer to the same exact step.

The swapped pair must contain:

```text
transposition.orchestrationFirst;
transposition.activationSecond.transition.
```

Transport the second unified step across `transposition.endpoint_eq` so its
endpoint is definitionally the normal final state.

Define:

```lean
def transposeActivationOrchestrationPair ... : AssignedAdjacentSwap normal
```

Derive orchestration rule/actor equality from
`SameOrchestrationTemplate.same_kind` and `.same_actor`. Derive activation
rule/actor equality from the concrete transposition construction; do not add a
new semantic law.

Export the constructor theorem explicitly:

```lean
theorem transpose_activation_orchestration_rule_eq ... :
  (transpose_activation_orchestration ...).activationSecond.rule =
    activation.activation.rule
```

Also expose one `SameOrchestrationTemplate.global_tags` theorem that lifts the
template's kind/name equations to equality of unified step rules and actors.

This adapter retains the existing exact restrictions:

- Begin supports every legal distinct-actor orchestration step;
- an ordinary landing supports Insert, Retire, and Remove;
- a registering landing supports Retire or Remove only when its child differs
  from the orchestration actor; and
- registering landing followed by O-Insert is excluded.

## 11. Whole-trace adapter theorems

For both pair adapters, provide a theorem that accepts an
`AdjacentOccurrence`, the `ProgramOccurrence` evidence for its relevant pair
steps, and the remaining semantic laws, then returns the rewritten complete
trace plus the projection equations.

The semantic adapters should construct `AssignedAdjacentSwap`, not merely the
endpoint-only parent, so that the moved activation steps retain exact fixed
program evidence and the moved orchestration step receives the vacuous
nonactivation assignment.

At the head of a recursively assigned trace, obtain those occurrence values by
pattern matching `TraceProgramAssignment.cons` and applying the stored
`StepProgramAssignment.occurrence` to the known activation-rule proof. This is
the first explicit connection between trace-wide assignment and a semantic
swap adapter. Automatic numeric lookup of an arbitrary internal assigned
window may remain a derived future convenience; do not flatten the primary
assignment merely to obtain it.

Derive the local source `WellFormed` premise from
`occurrence.beforeTrace.preservesWellFormed initialWf`; do not accept an
unrelated proof of the same state when the whole trace source is already known
well formed.

The implementation may expose the generic `occurrence.rewrite swap` directly;
do not duplicate before/after-context recursion in each semantic adapter.

At least one positive example must use a nonempty retained context or a generic
context theorem. A two-step trace with both contexts `nil` is useful but does
not by itself demonstrate internal-window splicing.

## 12. Birth ranks and relation boundary

Do not define a birth-erased relation in this module.

The existing corrected swaps all prove exact endpoint equality. The known
registering-activation/O-Insert pair does not: opposite insertion orders assign
different birth ranks, and current `GlobalRelations.RuleRelated` observes both
fiber birth and `nextBirth`.

A later relation must make an explicit choice among:

- quotienting only fresh allocator ranks while retaining registry domain,
  lifecycle control, tables, components, parent pointers, and active context;
- carrying a finite order-preserving renaming of birth ranks; or
- changing allocation semantics.

Introducing that relation here would mix two separate obligations and risk
silently weakening the exact trace theorem. Preserve the existing kernel
counterexample and keep registering/O-Insert outside the exact adapter.

## 13. Why this still does not prove deletion or confluence

An adjacent rewrite API is necessary but not sufficient for Lemma 72 or
Theorem 73.

The later layers still need:

- preservation and lookup of the trace occurrence/program assignment through
  an arbitrary sequence of rewrites;
- proof that the relevant branch-specific swap laws hold at each occurrence;
- an intrinsic finite permutation/rewrite sequence;
- corrected deletion safety closed under surviving parent pointers;
- component and episode provenance for registered children and retirement
  inverses;
- support well-foundedness and active-parent closure;
- the temporal recovery conclusions still isolated behind explicit
  `GlobalTemporal` certificates;
- a fresh-name bijection or birth-erased relation for schedules that change
  registration order; and
- a termination measure for the normalization procedure.

In particular, deleting a registered child while retaining a later O-Insert
that names that child as parent produces an ill-typed would-be trace. The
rewrite layer must not hide this counterexample behind list filtering.

## 14. Positive and negative evidence

Compile at least:

- one activation/activation `ExactAdjacentSwap` from an existing positive
  example;
- one activation/orchestration `ExactAdjacentSwap` from an existing positive
  example;
- an exact complete-trace rewrite and reversed rule/actor projections;
- one `ProgramOccurrence` whose step equality reduces in the kernel;
- one nontrivial `TraceProgramAssignment`; and
- the existing registering/O-Insert birth-order counterexample as the explicit
  reason no exact adapter exists for that branch.

Add a computable projection of a rewritten example's two rule names or actors,
then bridge it by theorem to the actual rewritten trace. Do not add library
`#eval` commands.

## 15. Explicit non-claims

This slice does not prove:

- paper Lemma 71 in its unrestricted total/quotient setting;
- that every arbitrary trace has a fixed-program occurrence assignment;
- branch laws, oracle stability, or off-source execution totality from base
  dynamics;
- registering activation/O-Insert exchange;
- a birth-erased or name-renamed rule relation;
- arbitrary permutation normalization;
- deletion of vestigial registrations;
- Lemma 72;
- canonical form or confluence in Theorem 73;
- recovery of an interleaved episode without the explicit temporal
  certificates; or
- progress, termination, fairness, or scheduler completeness.

The exact positive claim is:

> An exact adjacent pair inside an intrinsic global trace can be replaced by a
> certified exact transposed pair with the same source and endpoint, producing
> another intrinsically aligned trace with the same outer indices. Existing
> corrected activation/activation and activation/orchestration theorems supply
> such certificates under their explicit fixed-program, oracle, independence,
> framing, registration-safety, well-formedness, and distinct-actor premises.

## 16. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalTraceRewrite
lake env lean Cordis/GlobalTraceRewrite.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalTraceRewrite.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. add the finite rewritten rule/actor projection to `Cordis.TestSuite`;
1. add guarded wrong-program and excluded registering/O-Insert attempts to
   `Cordis.NegativeTests` where they add evidence beyond existing tests;
1. add selected occurrence, splice, projection, adapter, and counterexample
   declarations to `Cordis.AxiomAudit`;
1. change this specification's status to implemented;
1. update `README.md`, `SPEC.md`, `docs/PAPER_MAP.md`,
   `docs/V0_2_SPEC.md`, `docs/TRUST_BOUNDARY.md`, and
   `docs/IMPLEMENTATION_GUIDE.md`;
1. run strict/default builds, runtime suite, demo, hygiene, documentation,
   link, and selected-axiom gates; and
1. repeat every gate from a clean `git archive` before pushing.
