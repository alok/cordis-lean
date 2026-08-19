# Paper-visible global relation: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: implemented by `Cordis.GlobalPaperRelation`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Equation 53,
Lemmas 55–57, Lemma 72, and Theorem 73.

Dependencies:

- `Cordis.GlobalRelations` for the existing stricter `RuleRelated`,
  `EffectRelated`, and key-indexed value setoids;
- `Cordis.GlobalRuleInvariance` for orchestration active-context facts;
- `Cordis.GlobalDeletion` for `RetainedStep`, `DeletionReplay`, finite
  vestigial families, ordered removal, and safe orchestration traces; and
- `Cordis.GlobalTraceRewrite` for exact step assignments; and
- `Cordis.GlobalProgress` for the concrete target-changed reloading state used
  by the lifecycle insufficiency model.

## 1. Goal

Implement `Cordis.GlobalPaperRelation`, a finite Lean candidate for the
paper-visible global observations after erasing only the allocator artifacts
introduced by the reference refinement:

- `GlobalState.nextBirth`; and
- `Fiber.birth`.

The module must do more than define a relation. It must:

1. prove full-domain birth-erased rule observation is a Setoid and a weakening
   of current `RuleRelated`;
1. prove outside-deleted rule observation and its conjunction with
   `EffectRelated` are Setoids;
1. kernel-prove that the existing opposite insertion-order endpoints become
   related while remaining unequal and not current-`RuleRelated`;
1. derive genuine bidirectional O-Insert/O-Retire/O-Remove simulation between
   independently well-formed full-domain related states;
1. return actual `GlobalDeletion.RetainedStep` values with assignment
   transport;
1. prove that, from a well-formed source carrying a finite `VestigialNames`
   certificate, removal satisfies the combined deletion relation; and
1. from that same certified source, construct a directional safe
   orchestration trace replay under the relation.

The module must also state an exact lifecycle assigned-simulation frontier and
kernel-separate at least one required lower law—such as inertia respect—from
the relation alone.

This remains a finite candidate, not identification with the paper's
unrestricted quotient or full Lemma 55/57/72 semantics.

## 2. Why the existing relation is deliberately too strong

Current `GlobalRelations.FiberControl` stores:

- component;
- parent;
- `birth`;
- retirement; and
- phase.

Current `RuleRelated` additionally requires exact `nextBirth` equality.

Those allocator fields are useful for the strengthened Lean
`WellFormed.birth_bounded` and `parent_older` invariant, but they are absent
from the paper state. Existing kernel examples already show the mismatch:

- two legal insertion orders assign opposite birth ranks to fixed names;
- the exact endpoint states differ; and
- current `RuleRelated` rejects them.

The new relation must erase only those allocator fields. It must not erase
component, parent, retirement, phase, committed providers, iterator codes,
undo stacks, or outcomes.

“Only” is relative to current `RuleRelated`: that relation already observes
active values only up to their configured value setoids and already omits
ambient state and nonactive private tables. The new layer does not restore or
further weaken those pre-existing choices.

## 3. Paper-visible fiber control

Define:

```lean
structure PaperFiberControl (catalog : Catalog sig) where
  component : sig.ComponentId
  parent : Option sig.Name
  retired : Bool
  phase : Phase (catalog.declaration component)
```

Define:

```lean
def paperFiberControl
    (fiber : Fiber catalog) : PaperFiberControl catalog

def paperControlAt
    (state : State catalog Ambient)
    (name : sig.Name) : Option (PaperFiberControl catalog)
```

Bridge the current control:

```lean
def eraseFiberControl
    (control : GlobalRelations.FiberControl catalog) :
    PaperFiberControl catalog

theorem paperControlAt_eq_map_controlAt :
  paperControlAt state name =
    (GlobalRelations.controlAt state name).map eraseFiberControl
```

There must be no birth projection from `PaperFiberControl`.

## 4. Full-domain birth-erased rule observation

Define:

```lean
noncomputable def BirthErasedRuleRelated
    (values : ValueSetoids sig)
    (left right : State catalog Ambient) : Prop :=
  ContextRelated values (activeContext left) (activeContext right) ∧
    ∀ name,
      paperControlAt left name = paperControlAt right name
```

This still observes the exact registry domain because absence is `none` and
presence is `some paperControl`.

Prove:

```lean
theorem birthErasedRuleRelated_refl ...
theorem birthErasedRuleRelated_symm ...
theorem birthErasedRuleRelated_trans ...

noncomputable def birthErasedRuleSetoid
    (values : ValueSetoids sig) : Setoid (State catalog Ambient)
```

No well-formedness, dynamics, inertia, or decidability premise belongs in the
Setoid laws.

## 5. Observation outside deleted names

Define:

```lean
noncomputable def BirthErasedRuleRelatedOutside
    (values : ValueSetoids sig)
    (deleted : sig.Name → Prop)
    (left right : State catalog Ambient) : Prop :=
  ContextRelated values (activeContext left) (activeContext right) ∧
    ∀ name,
      ¬deleted name →
      paperControlAt left name = paperControlAt right name
```

Package the equivalence:

```lean
noncomputable def birthErasedRuleOutsideSetoid
    (values : ValueSetoids sig)
    (deleted : sig.Name → Prop) : Setoid (State catalog Ambient)
```

This relation compares the complete active context, not a provider-filtered
context. That is intentionally stronger than a fully general outside-deleted
paper relation. It is appropriate for the intended deletion path because all
deleted source entries are vestigial—inactive and noninstalled—and the shadow
entries are absent.

Do not claim target, provider, reliance, or guard transport for arbitrary
members of this outside Setoid. If deleted entries may be active or installed,
active-value equality does not identify the provider name or installed
consumer.

## 6. Combined deletion endpoint observation

Define:

```lean
noncomputable def DeletionRelated
    (values : ValueSetoids sig)
    (deleted : sig.Name → Prop)
    (left right : State catalog Ambient) : Prop :=
  EffectRelated left right ∧
    BirthErasedRuleRelatedOutside values deleted left right
```

Package:

```lean
noncomputable def deletionSetoid
    (values : ValueSetoids sig)
    (deleted : sig.Name → Prop) : Setoid (State catalog Ambient)
```

This is the finite Lemma-72-shaped endpoint observation:

- effect observation globally; and
- rule/control observation outside deleted names;
- with allocator ranks erased.

It is an observation Setoid, not a theorem that steps are replayable.

Expose named projections:

```lean
theorem DeletionRelated.effect ... : EffectRelated left right
theorem DeletionRelated.outside ... :
  BirthErasedRuleRelatedOutside values deleted left right
```

## 7. Domain, weakening, and monotonicity theorems

Prove:

```lean
theorem paperControlAt_isSome :
  (paperControlAt state name).isSome =
    (state.registry name).isSome
```

```lean
theorem birthErased_registry_domain
    (related : BirthErasedRuleRelated values left right) :
  (left.registry name).isSome = (right.registry name).isSome

theorem birthErased_registry_none_iff ...

theorem outside_registry_domain
    (related : BirthErasedRuleRelatedOutside values deleted left right)
    (kept : ¬deleted name) :
  (left.registry name).isSome = (right.registry name).isSome

theorem outside_registry_none_iff ...
```

Bridge from the current stricter relation:

```lean
theorem birthErased_of_ruleRelated
    (related : RuleRelated values left right) :
  BirthErasedRuleRelated values left right

theorem outside_of_birthErased ...
theorem outside_of_ruleRelated ...
```

Provide the empty-deletion converse and deletion-set monotonicity:

```lean
theorem birthErased_of_outsideEmpty ...
theorem birthErased_of_deletionEmpty ...

theorem outside_mono
    (included : ∀ name, smaller name → larger name) ...

theorem deletion_mono
    (included : ∀ name, smaller name → larger name) ...
```

Do not prove or claim the converse from `BirthErasedRuleRelated` to current
`RuleRelated`.

## 8. Control transport without birth equality

Prove only the paper-control projections:

```lean
theorem paperFiberControl_component_eq ...
theorem paperFiberControl_parent_eq ...
theorem paperFiberControl_retired_eq ...
theorem paperFiberControl_installed_iff ...
theorem paperFiberControl_active_iff ...
```

Define:

```lean
structure PaperFiberMatch
    (values : ValueSetoids sig)
    (source peer : State catalog Ambient)
    (name : sig.Name)
    (sourceFiber : Fiber catalog) where
  peerFiber : Fiber catalog
  peer_present : peer.registry name = some peerFiber
  control_eq :
    paperFiberControl sourceFiber = paperFiberControl peerFiber
```

```lean
def matchPaperFiber
    (related : BirthErasedRuleRelated values source peer)
    (sourcePresent : source.registry name = some sourceFiber) :
  PaperFiberMatch values source peer name sourceFiber
```

No field or theorem may assert source and peer birth equality.

## 9. Orchestration successor-control lemmas

Prove pointwise paper-control equality after matching edits:

```lean
theorem paperControlAt_insert_related ...
theorem paperControlAt_retire_related ...
theorem paperControlAt_remove_related ...
```

O-Insert may use different source clocks and therefore create different fiber
births. The paper controls must still agree.

For active contexts, prove:

```lean
theorem contextRelated_after_orchestration
    (leftStep : OrchestrationStep left leftAfter)
    (rightStep : OrchestrationStep right rightAfter)
    (leftWf : WellFormed left)
    (rightWf : WellFormed right)
    (related : BirthErasedRuleRelated values left right) :
  ContextRelated values
    (activeContext leftAfter)
    (activeContext rightAfter)
```

Both well-formedness premises are mandatory. The relation erases the clock and
birth ranks used by `WellFormed.birth_bounded` and `parent_older`; it does not
transport well-formedness from one state to the other.

Include a concrete pair of birth-erased-related states where one is well formed
and the other is not, so an attempted one-sided theorem cannot be reintroduced.

## 10. Full-domain forward orchestration match

Define a result that carries the raw matched step and from which the existing
deletion replay payload is derived:

```lean
structure ForwardPaperOrchestrationMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {left right leftAfter : State catalog Ambient}
    (source : OrchestrationStep left leftAfter) where
  rightAfter : State catalog Ambient
  matched : OrchestrationStep right rightAfter
  same_kind : orchestrationKind matched = orchestrationKind source
  same_actor : orchestrationName matched = orchestrationName source
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related :
    BirthErasedRuleRelated values leftAfter rightAfter
```

Derive rather than store:

```lean
def ForwardPaperOrchestrationMatch.toRetainedStep
    (result : ForwardPaperOrchestrationMatch ... source) :
  RetainedStep
    (shadowBefore := right)
    (Step.orchestration source)
```

The derived replay must be the actual `.orchestration result.matched` step and
its shadow endpoint must therefore be definitionally `result.rightAfter`. Its
rule and actor equations come from kind/name equality, and its assignment
transport must construct `StepProgramAssignment.ofOrchestration result.matched`.

Construct:

```lean
noncomputable def matchOrchestrationForward
    (leftWf : WellFormed left)
    (rightWf : WellFormed right)
    (related : BirthErasedRuleRelated values left right)
    (source : OrchestrationStep left leftAfter) :
  ForwardPaperOrchestrationMatch values
    (dynamics := dynamics) (inertia := inertia)
    (right := right) source
```

Every branch must reconstruct the peer rule:

- Insert: freshness, parent presence, and provision freshness;
- Retire: peer fiber and presence;
- Remove: presence, retirement, noninstallation, and childlessness.

Successor well-formedness is derived independently on both sides.

## 11. Backward orchestration match and bundle

Define the exact left/right dual:

```lean
structure BackwardPaperOrchestrationMatch
    (values : ValueSetoids sig)
    {dynamics : Dynamics sig catalog Ambient}
    {inertia : InertiaPolicy dynamics}
    {left right rightAfter : State catalog Ambient}
    (source : OrchestrationStep right rightAfter) where
  leftAfter : State catalog Ambient
  matched : OrchestrationStep left leftAfter
  same_kind : orchestrationKind matched = orchestrationKind source
  same_actor : orchestrationName matched = orchestrationName source
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related :
    BirthErasedRuleRelated values leftAfter rightAfter

noncomputable def matchOrchestrationBackward
    (leftWf : WellFormed left)
    (rightWf : WellFormed right)
    (related : BirthErasedRuleRelated values left right)
    (source : OrchestrationStep right rightAfter) :
  BackwardPaperOrchestrationMatch values
    (dynamics := dynamics) (inertia := inertia)
    (left := left) source
```

The backward result must also expose a real `RetainedStep` from the supplied
right-source occurrence to the matched left step, derived by a
`BackwardPaperOrchestrationMatch.toRetainedStep` function rather than stored as
an unrelated existential field.

Package:

```lean
structure BirthErasedOrchestrationSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) where
  forward : ∀ {left right leftAfter},
    WellFormed left → WellFormed right →
    BirthErasedRuleRelated values left right →
    (source : OrchestrationStep left leftAfter) →
      ForwardPaperOrchestrationMatch values
        (dynamics := dynamics) (inertia := inertia)
        (right := right) source
  backward : ∀ {left right rightAfter},
    WellFormed left → WellFormed right →
    BirthErasedRuleRelated values left right →
    (source : OrchestrationStep right rightAfter) →
      BackwardPaperOrchestrationMatch values
        (dynamics := dynamics) (inertia := inertia)
        (left := left) source

noncomputable def birthErasedOrchestrationSimulation
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
  BirthErasedOrchestrationSimulation values dynamics inertia
```

No additional semantic assumption is needed for these three orchestration
constructors.

## 12. Literal allocator-order validation

Use the existing `LiteralPaperGap.normal` and `.swapped` endpoints.

Kernel-prove:

```lean
theorem BirthGap.birth_erased_related :
  BirthErasedRuleRelated LiteralPaperGap.exactValues
    LiteralPaperGap.normal LiteralPaperGap.swapped

theorem BirthGap.strict_rule_relation_fails :
  ¬RuleRelated LiteralPaperGap.exactValues
    LiteralPaperGap.normal LiteralPaperGap.swapped

theorem BirthGap.exact_states_differ :
  LiteralPaperGap.normal ≠ LiteralPaperGap.swapped
```

Expose the active-context and per-name paper-control equations used in the
positive proof.

Also instantiate the forward and backward orchestration matcher on one real
step at each of the two related states and exercise the returned parallel peer
`RetainedStep` assignment transports. Do not describe either matched step as a
transition from `normal` directly to `swapped`; each begins at the opposite
related source and reaches its own related successor.

## 13. Vestigial removal and finite deletion relation

For one entry, prove:

```lean
theorem vestigial_remove_outside ... :
  BirthErasedRuleRelatedOutside values
    (fun candidate => candidate = name)
    state (removeFiber state name)

theorem vestigial_remove_deletion_related ... :
  DeletionRelated values
    (fun candidate => candidate = name)
    state (removeFiber state name)
```

The source `WellFormed` plus actual vestigial O-Remove witness should derive
the removed state's well-formedness; do not require it as unrelated caller
data if the proof can construct it.

Prove global full-domain separation:

```lean
¬BirthErasedRuleRelated values state (removeFiber state name)
```

because the full relation still observes exact registry domain.

For a finite `VestigialNames state names` family, prove:

```lean
theorem removeNames_wellFormed ... :
  WellFormed (removeNames state names)

theorem vestigialNames_deletionRelated ... :
  DeletionRelated values (fun name => name ∈ names)
    state (removeNames state names)
```

Use deletion-set monotonicity while composing singleton removals.

## 14. Directed safe outside-deleted replay

The outside relation is a symmetric state Setoid, but it is not an operational
bisimulation.

For the specialized finite vestigial family, define:

```lean
structure ForwardDeletedOrchestrationReplay
    (values : ValueSetoids sig)
    (family : VestigialNames before names)
    (source : OrchestrationStep before after) where
  retained :
    RetainedStep
      (shadowBefore := removeNames before names)
      (Step.orchestration source)
  remove_after :
    removeNames after names = retained.shadowAfter
  before_related :
    DeletionRelated values (fun name => name ∈ names)
      before (removeNames before names)
  after_wellFormed : WellFormed after
  shadowAfter_wellFormed : WellFormed retained.shadowAfter
  after_related :
    DeletionRelated values (fun name => name ∈ names)
      after retained.shadowAfter
  remains : VestigialNames after names
```

Construct it from:

```lean
noncomputable def replaySafeVestigialOrchestration
    (beforeWf : WellFormed before)
    (family : VestigialNames before names)
    (source : OrchestrationStep before after)
    (safe : SafeForVestigialNames names source) :
  ForwardDeletedOrchestrationReplay values family source
```

The exact safety is:

- retained actor outside the deleted family; and
- retained insertion parent outside the deleted family.

No additional provision premise is needed in the forward direction because
removing entries relaxes provision freshness.

For a generic outside-related shadow that is not definitionally
`removeNames before names`, directional replay also requires every deleted name
to be absent in the shadow. The specialized finite-family constructor derives
that fact from ordered removal and `Nodup`; do not generalize it to arbitrary
outside-related states without a `DeletedAbsent` premise.

## 15. Full safe orchestration trace replay

Define:

```lean
structure ForwardDeletedTraceReplay
    (values : ValueSetoids sig)
    (family : VestigialNames before names)
    (source : Trace dynamics inertia before after) where
  shadow : Trace dynamics inertia
    (removeNames before names) (removeNames after names)
  certificate :
    DeletionReplay
      (DeletionRelated values (fun name => name ∈ names))
      (fun _ => False)
      source shadow
  sourceAfter_wellFormed : WellFormed after
  shadowAfter_wellFormed : WellFormed (removeNames after names)
  remains : VestigialNames after names
```

Construct:

```lean
noncomputable def replaySafeVestigialTrace
    (beforeWf : WellFormed before)
    (family : VestigialNames before names)
    (safe : SafeNamesOrchestrationTrace names dynamics inertia source) :
  ForwardDeletedTraceReplay values family source
```

Derive:

```lean
theorem ForwardDeletedTraceReplay.final_related ...

noncomputable def ForwardDeletedTraceReplay.transportAssignment ...
```

This theorem should build only `DeletionReplay.keep` nodes. It is a
relation-aware reformulation of the exact trace square, not a record-deletion
theorem.

## 16. Why outside-deleted bisimulation is false

Use `GlobalVestigial.Counterexample.state` and `withoutVestigial`, which satisfy
the combined deletion relation for the vestigial name.

Retain the forward parent obstruction:

- source O-Insert adopts the vestigial parent;
- deleted shadow cannot supply that parent.

Retain backward obstructions:

- deleted shadow redraws the absent name, while source freshness fails;
- deleted shadow inserts a provision conflicting with the source vestige; and
- deleted shadow removes a parent that is childless only after deletion.

Kernel-prove at least:

```lean
theorem OutsideGap.unsafe_parent_step_rejected :
  ¬SafeForVestigialNames [deletedName] adoptingInsert

theorem OutsideGap.no_backward_same_tag_redraw :
  ¬∃ after, ∃ step : OrchestrationStep sourceState after,
    orchestrationKind step = orchestrationKind redrawStep ∧
    orchestrationName step = orchestrationName redrawStep
```

Do not define a symmetric outside-deleted operational bundle.

## 17. Lifecycle assigned-simulation frontier

Full-domain birth-erased relation does not determine lifecycle behavior. Base
`Dynamics`, registration oracles, inertia, and recovery may inspect ambient,
allocator clock, births, inactive tables, or arbitrary external observations.

Define exact forward and backward result types:

```lean
structure ForwardAssignedLifecycleMatch
    (transition : Transition dynamics inertia left leftAfter) where
  rightAfter : State catalog Ambient
  matched : Transition dynamics inertia right rightAfter
  same_lifecycle_rule : matched.rule = transition.rule
  same_actor :
    (Step.lifecycle matched).actor =
      (Step.lifecycle transition).actor
  leftAfter_wellFormed : WellFormed leftAfter
  rightAfter_wellFormed : WellFormed rightAfter
  successors_related :
    BirthErasedRuleRelated values leftAfter rightAfter
  transportAssignment :
    StepProgramAssignment (Step.lifecycle transition) →
      StepProgramAssignment (Step.lifecycle matched)
```

Define the dual `BackwardAssignedLifecycleMatch`. Both must derive an actual
`RetainedStep` through named `ForwardAssignedLifecycleMatch.toRetainedStep` and
`BackwardAssignedLifecycleMatch.toRetainedStep` functions constructed from the
stored matched transition, exact lifecycle rule/actor facts, and assignment
transport. Do not store an independent unconstrained retained-step existential.

Package—but do not inhabit from the base relation—the bidirectional frontier:

```lean
structure BirthErasedLifecycleAssignedSimulation ... where
  forward : ∀ {left right leftAfter},
    WellFormed left → WellFormed right →
    BirthErasedRuleRelated values left right →
    (transition : Transition dynamics inertia left leftAfter) →
      ForwardAssignedLifecycleMatch values dynamics inertia
        (right := right) transition
  backward : ∀ {left right rightAfter},
    WellFormed left → WellFormed right →
    BirthErasedRuleRelated values left right →
    (transition : Transition dynamics inertia right rightAfter) →
      BackwardAssignedLifecycleMatch values dynamics inertia
        (left := left) transition
```

Preserve exact lifecycle-rule equality. Global `.lDivert` equality is too weak
because it conflates aborting and landing Divert.

## 18. Lifecycle inertia-law insufficiency

Reuse or adapt the existing ambient-sensitive inertia model to prove:

- the two sources are `BirthErasedRuleRelated`; but
- the inertia policy does not respect that relation.

Define the exact missing law before refuting it:

```lean
def InertiaRespectsBirthErased
    (values : ValueSetoids sig)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) : Prop :=
  ∀ owner code {left right},
    BirthErasedRuleRelated values left right →
    (inertia.canAbort owner code left ↔ inertia.canAbort owner code right)
```

If practical, also provide a clock-sensitive dynamics witness, since the new
relation intentionally erases `nextBirth`.

This proves one required premise of a lifecycle simulation is independent of
the relation.

Also construct the actual transition-level refutation. Reuse the well-formed,
retired reloading, target-changed state from
`GlobalProgress.RegistrationRejectionGap.changed`, clone it with only
`nextBirth` incremented, and define an inertia policy whose abortability tests
the original clock. Kernel-prove:

- both states are independently well formed;
- they are `BirthErasedRuleRelated`;
- the original source has an actual L-DivertAbort; and
- no lifecycle transition from the shifted source has the same exact
  `GlobalLifecycle.Rule.divertAbort` rule.

Conclude:

```lean
¬Nonempty
  (BirthErasedLifecycleAssignedSimulation
    exactValues dynamics clockInertia)
```

for that instance. The bundle is `Type`-valued, so use `Nonempty`; bare
negation of the type is ill formed. The proof must compare exact lifecycle
rules, not the global `.lDivert` projection that also includes DivertLand.

## 19. Explicit non-claims

This slice does not prove:

- equivalence with current `RuleRelated`;
- the converse from birth-erased to current rule relation;
- transport of well-formedness from one related state to the other;
- target/provider/reliance transport for arbitrary outside-related states;
- outside-deleted orchestration bisimulation;
- lifecycle matching from base `Dynamics`;
- fixed-program assignment transport for lifecycle rules without additional
  program/oracle/reach laws;
- registration-oracle, landing, inertia, recovery, or external-undo transport;
- relation-aware activation/O-Insert swapping;
- suffix replay containing lifecycle steps;
- backward Lemma 57 simulation across deleted names;
- no-redraw or lifetime correctness for bare deletion predicates;
- name equivariance or quotienting by renaming;
- general registration or episode deletion;
- Lemma 55, 56, 57, or 72;
- normalization, canonical form, confluence, or termination; or
- Theorem 73.

The exact positive claim is:

> Erasing Lean's allocator clock and per-fiber birth ranks yields a finite
> paper-visible rule observation under which all three well-formed orchestration
> rules admit real bidirectional peer steps and assignment-preserving retained
> replay. From a well-formed source carrying a finite `VestigialNames`
> certificate, safe foreign orchestration traces replay directionally to the
> erased shadow under the combined effect/outside-control deletion relation.

## 20. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalPaperRelation
lake env lean Cordis/GlobalPaperRelation.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalPaperRelation.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. add birth-gap, orchestration-match, and directed deletion-replay projections
   to `Cordis.TestSuite`;
1. add guarded attempts to recover current `RuleRelated`, one-sided
   well-formedness, or outside-deleted backward replay to
   `Cordis.NegativeTests` where they supplement kernel countermodels;
1. add selected Setoid, bridge, match, replay, and counterexample declarations
   to `Cordis.AxiomAudit`;
1. change this specification's status to implemented;
1. update `README.md`, `SPEC.md`, `docs/PAPER_MAP.md`,
   `docs/V0_2_SPEC.md`, `docs/TRUST_BOUNDARY.md`, and
   `docs/IMPLEMENTATION_GUIDE.md`;
1. run strict/default builds, runtime suite, demo, hygiene, documentation,
   link, and selected-axiom gates; and
1. repeat every gate from a clean `git archive` before pushing.
