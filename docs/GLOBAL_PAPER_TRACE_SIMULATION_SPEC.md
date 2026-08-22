# Birth-erased assigned trace simulation: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: implemented (bounded conditional trace layer)

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Equation 53,
Lemma 55, Lemma 71, the replay premise used by Lemma 72, and the
trace-reordering prerequisites of Theorem 73.

Dependencies:

- `Cordis.GlobalPaperRelation` for `BirthErasedRuleRelated`, the proved
  bidirectional orchestration simulation, the conditional lifecycle assigned
  simulation frontier, and the clock-sensitive lifecycle obstruction;
- `Cordis.GlobalDeletion` for `RetainedStep`, `DeletionReplay`, and
  `DeletionResult`;
- `Cordis.GlobalTraceRewrite` for `StepPair`, `AdjacentOccurrence`, exact
  assigned swaps, step assignments, and trace assignments; and
- `Cordis.GlobalCalculus` and `Cordis.GlobalTraceFacts` for intrinsic steps,
  traces, append, rule projections, actors, and well-formedness preservation.

Implementation checkpoint: `Cordis/GlobalPaperTraceSimulation.lean` now provides
the detailed-rule tags, coherent forward/backward assigned-step matches,
all-keep replay, forward/backward orchestration-only replay constructors, related-endpoint suffix replay,
assignment transport, trace-local forward/backward lifecycle evidence, a concrete leave/unload
replay witness, the positive orchestration witness, and the clock-sensitive lifecycle obstruction
described below. The unified lifecycle bridge remains an explicit caller-supplied
`BirthErasedLifecycleAssignedSimulation`; trace-local evidence is occurrence-specific and does not
strengthen that global premise.

## 1. Goal

The implemented `Cordis.GlobalPaperTraceSimulation` is the first layer that lifts the
paper-visible birth-erased state relation from one-step simulation to complete
finite assigned traces.

The module has three responsibilities:

1. combine the proved O-Insert/O-Retire/O-Remove simulation with a supplied
   lifecycle assigned-simulation law into a local unified-step simulator;
1. use only that local law to construct an intrinsic, all-keep replay of an
   arbitrary finite trace from a related well-formed source; and
1. replace one assigned adjacent window whose two local endpoints are merely
   birth-erased related, then actually replay the old suffix from the new
   endpoint.

The crucial distinction from `Cordis.GlobalTraceRewrite` is endpoint equality.
An exact adjacent swap reuses the original suffix because both local paths have
the same indexed endpoint. A paper-visible swap may change allocator birth
ranks, so its new endpoint is related but not equal to the old endpoint. A
relation proof cannot cast the old suffix. This module must construct a new
suffix by structural simulation.

The result remains conditional and finite. It is not a normalization plan,
canonical-form theorem, confluence theorem, Lemma 72, or Theorem 73.

## 2. Preserve exact lifecycle rule identity

`GlobalCalculus.Rule` deliberately presents ten paper rule names. Its
`lDivert` constructor combines the two exact lifecycle constructors:

- `GlobalLifecycle.Rule.divertAbort`; and
- `GlobalLifecycle.Rule.divertLand`.

That public projection is appropriate for the combined calculus, but it is too
coarse for assigned simulation. A replay of L-DivertAbort must not be justified
by a peer L-DivertLand merely because both project to `lDivert`.

Define the constructor-sensitive tag:

```lean
inductive DetailedRule where
  | orchestration : GlobalVestigial.OrchestrationKind -> DetailedRule
  | lifecycle : GlobalLifecycle.Rule -> DetailedRule
deriving DecidableEq, Repr
```

Define its public projection:

```lean
def DetailedRule.global : DetailedRule -> GlobalCalculus.Rule
```

Define tags for exact steps and traces:

```lean
def detailedRule
    (step : GlobalCalculus.Step dynamics inertia before after) : DetailedRule

def detailedRules
    (trace : GlobalCalculus.Trace dynamics inertia before after) :
    List DetailedRule
```

Prove:

```lean
theorem detailedRule_global :
  (detailedRule step).global = step.rule

theorem detailedRules_append :
  detailedRules (GlobalTraceFacts.Trace.append left right) =
    detailedRules left ++ detailedRules right
```

Every local replay result and related adjacent swap must preserve
`DetailedRule`. Coarse `Rule` preservation must be derived through
`detailedRule_global`, not used as a substitute.

## 3. Forward local assigned-step match

Define:

```lean
structure ForwardAssignedStepMatch
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    {sourceBefore shadowBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  matched : Step dynamics inertia shadowBefore shadowAfter
  same_detailedRule : detailedRule matched = detailedRule source
  same_actor : matched.actor = source.actor
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed shadowAfter
  successors_related :
    BirthErasedRuleRelated values sourceAfter shadowAfter
  transportAssignment :
    StepProgramAssignment source -> StepProgramAssignment matched
```

The result owns one actual peer step. Its endpoint is existential data. The
two source states and the original endpoint remain indices.

Derive, rather than independently store, the generic replay certificate:

```lean
def ForwardAssignedStepMatch.toRetainedStep
    (matched : ForwardAssignedStepMatch values dynamics inertia
      (shadowBefore := shadowBefore) source) :
    GlobalDeletion.RetainedStep
      (shadowBefore := shadowBefore) source
```

Its fields must be definitionally tied to `matched.shadowAfter` and
`matched.matched`. Derive the required coarse rule equality from
`same_detailedRule` and `detailedRule_global`.

Do not add a second unconstrained `RetainedStep` field alongside the explicit
peer endpoint and peer step. That would permit the generic replay witness to
refer to different data than the relation-specific result.

## 4. Backward local assigned-step match

Define the mirrored result:

```lean
structure BackwardAssignedStepMatch
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    {shadowBefore sourceBefore sourceAfter : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  matched : Step dynamics inertia shadowBefore shadowAfter
  same_detailedRule : detailedRule matched = detailedRule source
  same_actor : matched.actor = source.actor
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed shadowAfter
  successors_related :
    BirthErasedRuleRelated values shadowAfter sourceAfter
  transportAssignment :
    StepProgramAssignment source -> StepProgramAssignment matched
```

Derive its `toRetainedStep` with the same coherence discipline. The relation
orientation is shadow successor to source successor because the initial
relation is supplied in that orientation.

The backward surface is useful for bidirectional rule simulation and mirrored
trace replay. The relation-aware suffix rewrite below consumes only the
forward surface.

## 5. Minimal local simulation bundles

Separate the premise actually consumed by forward trace replay from the
larger bidirectional interface.

Define:

```lean
structure ForwardAssignedStepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics) where
  forward : forall {sourceBefore shadowBefore sourceAfter},
    WellFormed sourceBefore ->
    WellFormed shadowBefore ->
    BirthErasedRuleRelated values sourceBefore shadowBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      ForwardAssignedStepMatch values dynamics inertia
        (shadowBefore := shadowBefore) source
```

Define the bidirectional extension:

```lean
structure AssignedStepSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : GlobalLifecycle.InertiaPolicy dynamics)
    extends ForwardAssignedStepSimulation values dynamics inertia where
  backward : forall {shadowBefore sourceBefore sourceAfter},
    WellFormed shadowBefore ->
    WellFormed sourceBefore ->
    BirthErasedRuleRelated values shadowBefore sourceBefore ->
    (source : Step dynamics inertia sourceBefore sourceAfter) ->
      BackwardAssignedStepMatch values dynamics inertia
        (shadowBefore := shadowBefore) source
```

Neither bundle may contain a trace, a preassembled replay, a rewritten final
state, or a normalization schedule.

## 6. Constructor-specific local matching

### 6.1 Orchestration

Define:

```lean
noncomputable def matchOrchestrationStepForward ... :
  ForwardAssignedStepMatch values dynamics inertia
    (shadowBefore := shadowBefore) (.orchestration step)
```

It must delegate to:

```lean
GlobalPaperRelation.matchOrchestrationForward
```

and derive:

- the actual matched orchestration step;
- exact `OrchestrationKind` equality, lifted to `DetailedRule` equality;
- actor equality;
- both successor well-formedness proofs;
- successor birth-erased relation; and
- the matched orchestration assignment through
  `StepProgramAssignment.ofOrchestration`.

Define the backward orchestration branch from
`matchOrchestrationBackward`.

This branch needs no lifecycle assumption.

### 6.2 Lifecycle

Define:

```lean
noncomputable def matchLifecycleStepForward
    (lifecycle :
      BirthErasedLifecycleAssignedSimulation values dynamics inertia)
    ... :
  ForwardAssignedStepMatch values dynamics inertia
    (shadowBefore := shadowBefore) (.lifecycle transition)
```

It must delegate to `lifecycle.forward`. Preserve the exact
`GlobalLifecycle.Rule` by lifting `same_lifecycle_rule` to `DetailedRule`.
Copy the actual assignment transporter supplied by the lifecycle frontier; do
not infer a program, root code, oracle, or reach witness from the bare
transition.

Define the backward branch from `lifecycle.backward`.

### 6.3 Unified step

Define:

```lean
noncomputable def matchStepForward
    (lifecycle :
      BirthErasedLifecycleAssignedSimulation values dynamics inertia)
    ...
    (source : Step dynamics inertia sourceBefore sourceAfter) :
  ForwardAssignedStepMatch values dynamics inertia
    (shadowBefore := shadowBefore) source
```

The proof is constructor elimination on `source`: orchestration uses the
proved relation theorem; lifecycle uses the explicit frontier.

Package:

```lean
noncomputable def ForwardAssignedStepSimulation.ofLifecycle ...

noncomputable def AssignedStepSimulation.ofLifecycle ...
```

The full constructor consumes the existing
`BirthErasedLifecycleAssignedSimulation`; it does not prove that frontier from
base `Dynamics` or `InertiaPolicy`.

## 7. All-keep replay certificate

The existing deletion machinery is deliberately relation-polymorphic. Reuse
it with the impossible drop predicate:

```lean
fun _ => False
```

First prove generic projection facts:

```lean
theorem replay_rules_eq
    (replay : DeletionReplay Related (fun _ => False) source shadow) :
  shadow.rules = source.rules

theorem replay_actors_eq
    (replay : DeletionReplay Related (fun _ => False) source shadow) :
  shadow.actors = source.actors
```

The `.drop` induction branch must be eliminated by its `False` witness. These
theorems are not claims that arbitrary `DeletionReplay` preserves the lists.

Define the minimal structural builder:

```lean
noncomputable def ForwardAssignedStepSimulation.replayTrace
    (simulation : ForwardAssignedStepSimulation values dynamics inertia)
    (sourceWf : WellFormed sourceBefore)
    (shadowWf : WellFormed shadowBefore)
    (related :
      BirthErasedRuleRelated values sourceBefore shadowBefore)
    (source : Trace dynamics inertia sourceBefore sourceAfter) :
  ForwardPaperTraceReplay values source shadowBefore
```

The construction must recurse on the intrinsic source trace.

For `.nil`:

```lean
shadow := .nil shadowBefore
certificate := .nil related
```

For `.cons head tail`:

1. call `simulation.forward` on `head`;
1. derive `headMatch.toRetainedStep`;
1. recursively replay `tail` from `headMatch.shadowAfter`, using the two
   successor well-formedness proofs and `successors_related`;
1. construct the shadow with `Trace.cons`; and
1. construct the certificate with `DeletionReplay.keep`.

No `.drop` constructor may appear in the builder. No caller may supply the
shadow trace, output endpoint, or replay certificate.

## 8. Full trace replay result

Package the stronger trace information:

```lean
structure ForwardPaperTraceReplay
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {sourceBefore sourceAfter : State catalog Ambient}
    (source : GlobalCalculus.Trace dynamics inertia sourceBefore sourceAfter)
    (shadowBefore : State catalog Ambient) where
  result :
    DeletionResult
      (BirthErasedRuleRelated values)
      (fun _ => False)
      source shadowBefore
  sourceAfter_wellFormed : WellFormed sourceAfter
  shadowAfter_wellFormed : WellFormed result.shadowAfter
  detailedRules_eq : detailedRules result.shadow = detailedRules source
```

`replayTrace` packages the structural `DeletionResult` together with source
and shadow well-formedness and the detailed-rule equality. It is a structural
proof from the local simulator, not a wrapper around a caller-provided
`DeletionResult`.

Derive:

```lean
theorem ForwardPaperTraceReplay.final_related ...

noncomputable def ForwardPaperTraceReplay.transportAssignment
    (replay : ForwardPaperTraceReplay values source shadowBefore)
    (assignment : TraceProgramAssignment dynamics inertia source) :
  TraceProgramAssignment dynamics inertia replay.result.shadow

theorem ForwardPaperTraceReplay.rules_eq ...
theorem ForwardPaperTraceReplay.actors_eq ...
```

The assignment is transported one retained occurrence at a time by the
certificate. It must not be assumed as a result field.

Also expose convenient final-relation, shadow-WF, and assignment functions on
`ForwardAssignedStepSimulation.replayTrace` when they make the smaller result
easier to use.

## 9. Related assigned adjacent swap

Define the local replacement primitive:

```lean
structure RelatedAssignedAdjacentSwap
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {before after : State catalog Ambient}
    (normal : StepPair dynamics inertia before after) where
  swappedAfter : State catalog Ambient
  swapped : StepPair dynamics inertia before swappedAfter
  first_detailedRule :
    detailedRule swapped.first = detailedRule normal.second
  second_detailedRule :
    detailedRule swapped.second = detailedRule normal.first
  first_actor : swapped.first.actor = normal.second.actor
  second_actor : swapped.second.actor = normal.first.actor
  endpoints_related :
    BirthErasedRuleRelated values after swappedAfter
  swappedFirstAssignment : StepProgramAssignment swapped.first
  swappedSecondAssignment : StepProgramAssignment swapped.second
```

This certificate stores only the replacement pair and its local evidence. It
must not contain a complete rewritten trace, a suffix replay, or the eventual
final relation.

The relation orientation is intentional:

```text
normal local endpoint -> swapped local endpoint
```

The original suffix starts at the normal endpoint and will be simulated from
the swapped endpoint.

Derive the coarse rule equations:

```lean
theorem RelatedAssignedAdjacentSwap.first_rule ...
theorem RelatedAssignedAdjacentSwap.second_rule ...
```

Provide an exact-swap embedding:

```lean
noncomputable def RelatedAssignedAdjacentSwap.ofExact
    (swap : AssignedAdjacentSwap normal)
    (firstDetailed :
      detailedRule swap.swapped.first = detailedRule normal.second)
    (secondDetailed :
      detailedRule swap.swapped.second = detailedRule normal.first) :
  RelatedAssignedAdjacentSwap values normal
```

The two detailed-rule premises are necessary because the existing exact swap
surface exposes only coarse `GlobalCalculus.Rule` equations. Do not silently
derive exact divert-branch identity from an `lDivert` equality.

## 10. Replay a suffix after a related swap

Define:

```lean
structure RelatedAdjacentRewrite
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : GlobalLifecycle.InertiaPolicy dynamics}
    {initial final : State catalog Ambient}
    {source : Trace dynamics inertia initial final}
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair) where
  suffixReplay :
    ForwardPaperTraceReplay values occurrence.afterTrace swap.swappedAfter
```

The complete rewritten trace must be derived:

```lean
def RelatedAdjacentRewrite.trace ... :
  Trace dynamics inertia initial result.suffixReplay.result.shadowAfter
```

Its exact construction is:

```lean
GlobalTraceFacts.Trace.append occurrence.beforeTrace
  (.cons swap.swapped.first
    (.cons swap.swapped.second result.suffixReplay.result.shadow))
```

Derive:

```lean
theorem RelatedAdjacentRewrite.final_related ...
theorem RelatedAdjacentRewrite.final_wellFormed ...

noncomputable def RelatedAdjacentRewrite.assignment
    (assigned : AssignedAdjacentOccurrence occurrence)
    (result : RelatedAdjacentRewrite values occurrence swap) :
  TraceProgramAssignment dynamics inertia result.trace

theorem RelatedAdjacentRewrite.rules_perm ...
theorem RelatedAdjacentRewrite.detailedRules_perm ...
theorem RelatedAdjacentRewrite.actors_perm ...
```

The output assignment is reconstructed from:

- the original `beforeAssignment`;
- the two swapped step assignments; and
- the simulated suffix assignment obtained by transporting the original
  `afterAssignment`.

The public rewrite constructor is:

```lean
noncomputable def ForwardAssignedStepSimulation.rewriteAdjacent
    (simulation : ForwardAssignedStepSimulation values dynamics inertia)
    (initialWf : WellFormed initial)
    (occurrence : AdjacentOccurrence source)
    (swap : RelatedAssignedAdjacentSwap values occurrence.pair) :
  RelatedAdjacentRewrite values occurrence swap
```

It must derive, in order:

1. the window-start WF proof from `occurrence.beforeTrace`;
1. the normal local endpoint WF proof from `occurrence.pair.trace`;
1. the swapped local endpoint WF proof from `swap.swapped.trace`;
1. a fresh suffix replay by calling `simulation.replayTrace` on the old
   `occurrence.afterTrace`; and
1. the result from that constructed replay.

The theorem must not accept a caller-provided suffix replay as its primary
interface. The local simulator is the noncircular premise; the suffix replay
is the theorem's work product.

## 11. Exact positive orchestration witness

Provide a nonreflexive positive trace witness without assuming lifecycle
simulation.

Use the existing opposite-birth-order states and matched O-Retire step from:

```lean
GlobalPaperRelation.BirthGap
```

Construct:

- a one-step source trace from `normal`;
- an actual shadow trace from `swapped`;
- a `DeletionReplay (BirthErasedRuleRelated exactValues) (fun _ => False)`;
- a transported complete `TraceProgramAssignment`;
- the final birth-erased relation; and
- exact rule and actor list equalities.

This witness demonstrates the unconditional orchestration branch and a
genuinely non-equal pair of related source states. It must not invent a
lifecycle frontier merely to replay an orchestration-only trace.

If a suitable existing exact assigned adjacent swap has readily available
detailed-rule coherence, also instantiate `RelatedAssignedAdjacentSwap.ofExact`
and the empty-suffix case. This is useful evidence, but it is not required if
it would force a broad new lifecycle assumption solely for an example.

## 12. Kernel boundary: lifecycle simulation is not automatic

Strengthen the existing clock-sensitive obstruction to the new local surface.

Using:

```lean
GlobalPaperRelation.ClockLifecycleGap
```

prove:

```lean
theorem ClockGap.no_shifted_detailedDivertAbort :
  not (Exists fun after =>
    Exists fun step : Step dynamics clockInertia shifted after =>
      detailedRule step = .lifecycle .divertAbort)

theorem ClockGap.no_forward_step_simulation :
  not (Nonempty
    (ForwardAssignedStepSimulation values dynamics clockInertia))
```

The second theorem must:

1. assume a forward local simulator;
1. apply it to the actual original `L-DivertAbort` step and the related
   `changed`/`shifted` sources;
1. use `same_detailedRule` to force a peer exact L-DivertAbort; and
1. contradict the existing no-peer-transition theorem.

This countermodel explains both explicit premises in the positive theorem:

- the lifecycle simulation frontier cannot be derived from the state relation
  alone; and
- coarse global rule equality is insufficient.

## 13. Additional negative boundaries

The module documentation and negative tests must preserve these facts.

### 13.1 Endpoint relation does not create a local swap

A related endpoint alone does not prove the proposed first moved step is
applicable. Existing registration-parent counterexamples show that a later
O-Insert can depend on the child created by the preceding activation.

Therefore no constructor may have the shape:

```lean
BirthErasedRuleRelated values normalAfter swappedAfter ->
  RelatedAssignedAdjacentSwap values normal
```

The actual swapped `StepPair`, detailed-rule equations, actors, and assignments
remain explicit evidence.

### 13.2 Coarse tags do not transport assignments

Equal public rule and actor tags do not identify the fixed program, root code,
oracle, reach witness, or selected continuation of a lifecycle occurrence.
Assignment transport remains part of the lifecycle simulation law and the
local swap certificate.

### 13.3 Related endpoints cannot index-cast a suffix

`AdjacentOccurrence.afterTrace` begins at the exact normal endpoint. A
`BirthErasedRuleRelated` proof is not equality. No `cast`, `Eq.ndrec`, or
proof-irrelevance trick may reuse the old suffix at the swapped endpoint.

The only supported bridge is actual structural replay from the local simulator.

### 13.4 One-sided WF is insufficient

`BirthErasedRuleRelated` deliberately forgets allocator witnesses used by the
strengthened Lean invariant. Both source states require independent
`WellFormed` proofs. Do not infer peer WF from the relation.

## 14. Exact claim boundary

The implemented positive claim must read:

> Given independently well-formed birth-erased-related states and a local
> assignment-preserving simulation for every unified step, every finite
> intrinsic source trace has an all-keep intrinsic replay from the peer state.
> The replay preserves exact detailed rule tags, public rules, actors, and a
> complete trace assignment, and ends in a well-formed birth-erased-related
> state. A supplied related assigned two-step swap can replace one located
> adjacent window; the theorem constructs a new suffix from the related local
> endpoint and returns a complete trace whose final state remains related and
> whose detailed rules and actors are permutations of the original lists.

For the current calculus, the local simulator is constructible from:

- the proved birth-erased orchestration simulation; and
- an explicit `BirthErasedLifecycleAssignedSimulation` supplied by the caller.

For an orchestration-only source trace, the separate forward and backward
`*OrchestrationStepSimulation` constructors are constructible from the proved orchestration
simulation alone and replay an `AllOrchestrationTrace` without requiring the lifecycle premise.

For a mixed trace, `ForwardAssignedTraceEvidence` and
`BackwardAssignedTraceEvidence` instead require an exact matched lifecycle/orchestration step
for each source occurrence. Their replay constructors recursively build the complete shadow
trace and assignment, preserving WF, detailed rule tags, actors, and the final birth-erased
relation. The included leave→unload example is reflexive evidence for the existing concrete
transitions; it is evidence for that trace, not a derived lifecycle law for arbitrary related
states.

The module does not prove:

- lifecycle simulation from base `Dynamics`, `ReadEquivalent`, or
  `InertiaPolicy`;
- full Lemma 55 rule invariance for arbitrary dynamics;
- the existence of a non-exact related adjacent swap;
- relation-aware activation/O-Insert transposition;
- deletion of any occurrence;
- lifetime/no-redraw correctness;
- corrected Lemma 57 or Lemma 72;
- support or occurrence dependencies;
- a transformation sequence or executable normalization plan;
- termination or a decreasing normalization measure;
- a canonical trace;
- confluence; or
- Theorem 73.

## 15. Implementation order

Implement in this dependency order:

1. module header, imports, namespace, state abbreviation;
1. `DetailedRule`, `DetailedRule.global`, `detailedRule`, `detailedRules`;
1. detailed/global and append projection theorems;
1. forward and backward local match result structures;
1. coherent `toRetainedStep` bridges;
1. orchestration and lifecycle forward/backward matchers;
1. forward and bidirectional local simulation bundles and constructors;
1. keep-only rule/actor projection lemmas;
1. structural `replayTrace`;
1. `ForwardPaperTraceReplay` and `replayTrace`;
1. final relation, WF, list, and assignment projections;
1. `RelatedAssignedAdjacentSwap` and exact embedding;
1. `RelatedAdjacentRewrite`, reconstructed trace/assignment, and permutation
   theorems;
1. the public local-to-complete rewrite constructor;
1. positive orchestration replay evidence; and
1. the clock-sensitive impossibility theorems.

No declaration may rely on a later normalization module.

## 16. Tests and integration

Add `Cordis.GlobalPaperTraceSimulation` to:

- `Cordis.lean`;
- `Cordis/TestSuite.lean`;
- `Cordis/NegativeTests.lean`; and
- `Cordis/AxiomAudit.lean`.

The runtime suite must project at least:

- the positive orchestration replay's exact rule list;
- its actor list;
- a computable detailed-rule tag list or equivalent executable bridge; and
- a proof-carrying assignment transport checked by elaboration and the axiom
  audit when the assignment itself is noncomputable; the runtime projection
  remains the computable detailed-tag bridge above.

Negative tests must check that:

- coarse `lDivert` equality is not used as exact divert-branch equality;
- a relation proof does not elaborate where endpoint equality is required;
- a bare related endpoint does not synthesize a `RelatedAssignedAdjacentSwap`;
  and
- the clock-sensitive model cannot inhabit the forward local simulator.

The axiom audit must include all headline constructors, structural replay,
assignment transport, adjacent rewrite, permutation theorems, positive witness,
and countermodel declarations. Only the repository allow-list
`propext`, `Classical.choice`, and `Quot.sound` is acceptable.

## 17. Required verification

Run at minimum:

```text
lake env lean -DwarningAsError=true Cordis/GlobalPaperTraceSimulation.lean
lake --wfail build Cordis.GlobalPaperTraceSimulation
lake --wfail build
lake build
lake env lean Cordis/NegativeTests.lean
lake env lean Cordis/TestSuite.lean
uv run scripts/check_lean_hygiene.py --self-test
uv run scripts/check_lean_hygiene.py Cordis
uv run scripts/check_axiom_audit.py Cordis/AxiomAudit.lean
```

Also run:

- the repository forbidden-token scan;
- the 100-column scan;
- `git diff --check` or the equivalent `jj diff` whitespace check;
- documentation formatting and link checks after integration; and
- the runtime executable used by the existing test suite.

The implementation is complete only after a fresh independent read-only
semantic review checks the frozen module against this specification.
