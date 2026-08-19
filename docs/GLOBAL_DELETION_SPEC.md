# Corrected global deletion replay: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: planned

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Lemma 57,
Lemma 72, and the deletion phase of Theorem 73.

Dependencies:

- `Cordis.GlobalCalculus` and `Cordis.GlobalTraceFacts` for intrinsic exact
  steps, traces, records, episodes, and alignment;
- `Cordis.GlobalTraceRewrite` for exact program occurrences and recursive
  trace assignments;
- `Cordis.GlobalVestigial` for corrected one-name orchestration removal
  squares and their parent exception;
- `Cordis.GlobalSpatial` for episodes located inside one master trace; and
- `Cordis.GlobalRelations` for the existing effect-observation relation used
  by the bounded keep/drop example.

## 1. Goal

Implement `Cordis.GlobalDeletion`, a counterexample-first deletion substrate
and the strongest exact finite suffix theorem currently justified by the
kernel.

The module must deliver two distinct results:

1. a generic relation-indexed, constructor-by-constructor keep/drop replay of
   an intrinsic global trace, including derivation of the output
   `TraceProgramAssignment`; and
1. an exact theorem replaying an arbitrary finite suffix of safe foreign
   orchestration steps after removing a finite family of entries that are
   already vestigial.

It must also package the local parent-enablement, allocator-clock, and
name-reuse obstructions that prevent those results from being called paper
Lemma 72.

Do not implement deletion as `List.filter (Trace.records trace)`. A retained
step replayed after deletion normally has different dependent source and
endpoint indices from the source record. The output trace must be constructed
intrinsically from local replay evidence.

## 2. Exact source defect in Lemma 72

Paper Lemma 72 deletes:

- the owner steps inside one closing episode; and
- every step acting on a name drawn by a registration in that episode.

There is also an interval mismatch in the printed statement. Definition 53
places the opening L-Begin at step `b - 1`, while Lemma 72 says to delete owner
steps in `[b,u]`. Retaining that Begin while deleting the rest of the closing
episode does not restore the pre-episode control state. The corrected bounded
selection uses `BoundedEpisode.core`, which includes the opening step,
interior, and closing step: it corresponds to `[b - 1,u]`, not the literal
printed interval.

Its suffix invariant claims each drawn name remains vestigial while retained
steps replay. That claim fails for the raw orchestration rule:

```text
registration or insertion creates r;
later retained O-Insert creates x with parent r.
```

The second step is legal in the original state because `r` is present. After
deletion, its parent-presence premise is false. The paper's condition that the
activation did not register the orchestration actor does not address a
different registered parent.

The module must therefore make parent safety explicit before presenting any
positive replay theorem.

## 3. Parent closure surfaces

Define the occurrence-independent state predicates:

```lean
def NoSurvivingParentRefs
    (deleted : sig.Name → Prop)
    (state : State catalog Ambient) : Prop :=
  ∀ child fiber,
    state.registry child = some fiber →
    ¬deleted child →
    ∀ parent,
      fiber.parent = some parent →
      ¬deleted parent
```

```lean
def DescendantClosed
    (deleted : sig.Name → Prop)
    (state : State catalog Ambient) : Prop :=
  ∀ child fiber parent,
    state.registry child = some fiber →
    fiber.parent = some parent →
    deleted parent →
    deleted child
```

Prove:

```lean
theorem descendantClosed_iff_noSurvivingParentRefs :
  DescendantClosed deleted state ↔
    NoSurvivingParentRefs deleted state
```

For one retained orchestration occurrence, define the smaller operational
condition:

```lean
def AvoidsDeletedParents
    (deleted : sig.Name → Prop)
    (step : OrchestrationStep before after) : Prop :=
  ∀ name,
    deleted name →
    AvoidsVestigialParent name step
```

The exact suffix theorem should consume this occurrence-local condition. Do
not silently compute descendant closure and claim every other Lemma 72 premise
is preserved for the enlarged deletion set.

## 4. Full-trace parent and allocator counterexample

Construct an actual two-record intrinsic trace:

```text
source
  -- O-Insert(1, parent = 0) -->
registered
  -- O-Insert(2, parent = 1) -->
adoptionAfter.
```

Expose the exact projections:

```lean
trace.rules  = [.oInsert, .oInsert]
trace.actors = [.fiber 1, .fiber 2]
```

Prove `WellFormed` for `source`, `registered`, and `adoptionAfter` using the
actual two insertion steps. The negative result below must therefore be read as
deletion breaking a valid execution invariant, not as an artifact of an
already malformed source state.

Kernel-prove all of the following separately:

```lean
theorem no_surviving_same_template_insert :
  ¬∃ earlyAfter, ∃ early : OrchestrationStep source earlyAfter,
    SameOrchestrationTemplate early adoptingInsert
```

```lean
theorem final_parent_closure_fails :
  ¬NoSurvivingParentRefs (fun name => name = 1) adoptionAfter
```

```lean
theorem removed_final_not_wellFormed :
  ¬WellFormed (removeFiber adoptionAfter 1)
```

```lean
theorem removing_child_does_not_restore_clock :
  removeFiber registered 1 ≠ source
```

The first theorem refutes replay applicability; the next two refute naive
state deletion; the last isolates the independent `nextBirth` obstruction.

This compact trace need not satisfy every unrelated Lemma 72 premise. It is a
kernel counterexample to the local suffix invariant used in the paper proof.

## 5. Registration provenance for future episode deletion

The current `TraceProgramAssignment` classifies Begin, Iter, and Finish. A
landing L-Divert can also register a child, so the deletion layer needs a
separate exact landing surface.

Define:

```lean
def transitionRegisteredChild
    (step : Transition dynamics inertia before after) : Option sig.Name
```

It returns the actual `stepRegisteredChild` for Iter, Finish, and DivertLand,
and `none` for every other constructor.

Lift this to unified steps:

```lean
def landedRegisteredChild
    (step : Step dynamics inertia before after) : Option sig.Name
```

Define an intrinsic `LandingOccurrence step` with exactly three constructors:

- Iter;
- Finish; and
- DivertLand.

Each constructor must retain the exact fixed `Program`, source fiber and phase,
target or changed-target guard, actual `Landing`, and
`LandingProgramWitness`. It must not infer a program from a bare landing.
Each constructor's result index must be the exact corresponding unified
`Step.lifecycle (.iter ...)`, `.finish`, or `.divertLand` value built from those
same payloads; an unlinked program/landing plus a rule tag is insufficient.

## 6. Located episode and registration ledgers

Define an assignment decomposition aligned with one existing
`GlobalSpatial.LocatedEpisode`:

```lean
structure AssignedLocatedEpisode
    (located : LocatedEpisode dynamics inertia master) where
  beforeAssignment :
    TraceProgramAssignment dynamics inertia located.episode.beforeTrace
  openAssignment : StepProgramAssignment located.episode.openStep
  interiorAssignment :
    TraceProgramAssignment dynamics inertia located.episode.interior
  closeAssignment : StepProgramAssignment located.episode.closeStep
  afterAssignment :
    TraceProgramAssignment dynamics inertia located.episode.afterTrace
```

Derive rather than assume:

```lean
noncomputable def AssignedLocatedEpisode.masterAssignment :
  TraceProgramAssignment dynamics inertia master
```

using the located episode's exact master decomposition and assignment append.

One actual registered child is:

```lean
structure RegisteredChildInEpisode
    (located : LocatedEpisode dynamics inertia master)
    (child : sig.Name) where
  record : StepRecord dynamics inertia
  member :
    record ∈ Trace.records (GlobalSpatial.BoundedEpisode.core located.episode)
  owner : record.step.actedName = located.episode.name
  landing : LandingOccurrence record.step
  registered : landedRegisteredChild record.step = some child
```

Make the finite ledger exact in both directions:

```lean
structure RegistrationLedger
    (located : LocatedEpisode dynamics inertia master) where
  names : List sig.Name
  nodup : names.Nodup
  complete :
    ∀ child,
      child ∈ names ↔
        Nonempty (RegisteredChildInEpisode located child)
```

This first ledger is deliberately name-level. `Nodup` and `Nonempty` do not
distinguish two generations if one name is removed and redrawn inside the
episode. It may support the bounded no-redraw theorem below, but it must not be
advertised as a lifetime-correct deletion set.

The paper's crucial boundary premise must remain explicit:

```lean
structure VestigialRegistrationBoundary
    (ledger : RegistrationLedger located) where
  witness :
    ∀ child,
      child ∈ ledger.names →
      Vestigial located.episode.closeAfter child
```

Do not derive this merely from “the child has no episode.” Current arbitrary
non-root insertion and incomplete retirement provenance do not justify that
inference.

Keep the two trace segments structurally separate and define only local
authorization predicates:

```lean
def MayDropInCore
    (owner : sig.Name)
    (record : StepRecord dynamics inertia) : Prop :=
  record.step.actedName = owner

def MayDropInSuffix
    (deleted : List sig.Name)
    (record : StepRecord dynamics inertia) : Prop :=
  record.step.actedName ∈ deleted
```

`MayDropInCore` may be used only by a `DeletionReplay` whose exact source trace
is `BoundedEpisode.core located.episode`; it authorizes only that core's owner
steps. Child occurrences inside the core need explicit positional or lifetime
evidence and are deferred. `MayDropInSuffix` may be used only by a replay whose
exact source is `located.episode.afterTrace`. The intrinsic replay constructors
then identify positions. Do not authorize drops in a master trace by
existential `StepRecord` membership: an equal self-loop record outside the
episode core could otherwise be misclassified.

Both predicates remain bare-name policies. The suffix theorem must additionally
use the no-redraw boundary below; neither predicate distinguishes earlier or
later lifetimes on its own.

## 7. One retained occurrence

Define:

```lean
structure RetainedStep
    {sourceBefore sourceAfter shadowBefore : State catalog Ambient}
    (source : Step dynamics inertia sourceBefore sourceAfter) where
  shadowAfter : State catalog Ambient
  replay : Step dynamics inertia shadowBefore shadowAfter
  same_rule : replay.rule = source.rule
  same_actor : replay.actor = source.actor
  transportAssignment :
    StepProgramAssignment source →
      StepProgramAssignment replay
```

The assignment field is essential. Equal rules and actors do not construct a
fixed-program `ProgramOccurrence` at the shadow state.

## 8. Intrinsic keep/drop replay

Define the relation-indexed certificate:

```lean
inductive DeletionReplay
    (Related : State catalog Ambient → State catalog Ambient → Prop)
    (MayDrop : StepRecord dynamics inertia → Prop) :
    Trace dynamics inertia sourceBefore sourceAfter →
    Trace dynamics inertia shadowBefore shadowAfter →
    Type (u + 1) where

  | nil
      (related : Related source shadow) :
      DeletionReplay Related MayDrop (.nil source) (.nil shadow)

  | keep
      (related : Related sourceBefore shadowBefore)
      (retained : RetainedStep (shadowBefore := shadowBefore) sourceHead)
      (tail : DeletionReplay Related MayDrop sourceTail shadowTail) :
      DeletionReplay Related MayDrop
        (.cons sourceHead sourceTail)
        (.cons retained.replay shadowTail)

  | drop
      (related : Related sourceBefore shadowBefore)
      (mayDrop : MayDrop ⟨sourceBefore, sourceMiddle, sourceHead⟩)
      (tail : DeletionReplay Related MayDrop sourceTail shadowTrace) :
      DeletionReplay Related MayDrop
        (.cons sourceHead sourceTail)
        shadowTrace
```

The constructors must build the output trace. Do not accept one arbitrary
already-filtered trace plus a proposition saying it is correct.

At a drop, the shadow state does not advance. The recursive tail must therefore
establish the relation again between the source post-state and the unchanged
shadow source.

Provide the existential wrapper:

```lean
structure DeletionResult
    (Related : State catalog Ambient → State catalog Ambient → Prop)
    (MayDrop : StepRecord dynamics inertia → Prop)
    (source : Trace dynamics inertia sourceBefore sourceAfter)
    (shadowBefore : State catalog Ambient) where
  shadowAfter : State catalog Ambient
  shadow : Trace dynamics inertia shadowBefore shadowAfter
  certificate : DeletionReplay Related MayDrop source shadow
```

## 9. Derived replay theorems

Define an executable positional decision projection:

```lean
inductive ReplayDecision where
  | keep
  | drop
deriving DecidableEq, Repr

def DeletionReplay.decisions : List ReplayDecision

theorem DeletionReplay.decisions_length :
  replay.decisions.length = (Trace.records source).length
```

Prove structurally:

```lean
noncomputable def DeletionReplay.transportAssignment :
  TraceProgramAssignment dynamics inertia source →
    TraceProgramAssignment dynamics inertia shadow
```

```lean
theorem DeletionReplay.final_related :
  Related sourceAfter shadowAfter
```

```lean
theorem DeletionReplay.rules_sublist :
  shadow.rules.Sublist source.rules

theorem DeletionReplay.actors_sublist :
  shadow.actors.Sublist source.actors
```

Also expose:

- intrinsic alignment of the shadow trace;
- `shadow.records.length ≤ source.records.length`;
- the corresponding rule/actor length inequalities; and
- the decision projection and length equation above.

The output assignment must be derived from each retained step's local transport
and recursive deletion of dropped assignments. Do not store a preassembled
output assignment in the certificate.

## 10. Exact multi-vestigial orchestration replay

First strengthen the existing one-name API with two compositional helpers.

Removal of a different entry preserves vestigiality:

```lean
def Vestigial.remove_other
    (vestigial : Vestigial state kept)
    (different : kept ≠ removed) :
  Vestigial (removeFiber state removed) kept
```

The current forward square preserves the entire orchestration template:

```lean
theorem forwardOrchestration_sameTemplate
    (vestigial : Vestigial state name)
    (step : OrchestrationStep state after)
    (foreign : orchestrationName step ≠ name)
    (parentSafe : AvoidsVestigialParent name step) :
  SameOrchestrationTemplate
    (vestigial.forward_orchestration step foreign parentSafe).matched
    step
```

Also prove a constructor-level transport lemma showing that if an original
step avoids a second deleted parent, the matched step still avoids that parent.
Same kind and actor alone do not expose the inserted parent payload abstractly;
the proof must inspect the orchestration constructor or use exact replay
template equality.

Define a finite simultaneous family:

```lean
structure VestigialNames
    (state : State catalog Ambient)
    (names : List sig.Name) where
  nodup : names.Nodup
  witness :
    ∀ name,
      name ∈ names →
      Vestigial state name
```

Define ordered state erasure:

```lean
def removeNames
    (state : State catalog Ambient) :
    List sig.Name → State catalog Ambient
```

The recorded list order is part of this first certificate. Do not claim
permutation independence unless it is separately proved from
`remove_remove_commute`.

Define the exact occurrence safety condition:

```lean
def SafeForVestigialNames
    (names : List sig.Name)
    (step : OrchestrationStep before after) : Prop :=
  orchestrationName step ∉ names ∧
    AvoidsDeletedParents (fun name => name ∈ names) step
```

Prove the equivalent pointwise formulation used by the recursion. This keeps
the state-level parent-safety vocabulary connected to the executable finite
family API.

Construct one matched step:

```lean
structure ForwardNamesStepSquare
    (family : VestigialNames before names)
    (step : OrchestrationStep before after) where
  removedAfter : State catalog Ambient
  matched :
    OrchestrationStep (removeNames before names) removedAfter
  same_template : SameOrchestrationTemplate matched step
  remove_after : removeNames after names = removedAfter
  remains : VestigialNames after names
```

```lean
noncomputable def forwardNamesStep
    (family : VestigialNames before names)
    (step : OrchestrationStep before after)
    (safe : SafeForVestigialNames names step) :
  ForwardNamesStepSquare family step
```

## 11. Exact safe orchestration suffix

Define an intrinsic classifier containing only safe orchestration steps:

```lean
inductive SafeNamesOrchestrationTrace
    (names : List sig.Name)
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics) :
    Trace dynamics inertia before after → Type (u + 1)
```

Its `cons` constructor must store the exact raw `OrchestrationStep`, its
`SafeForVestigialNames` proof, and a recursively safe tail.

Define an intrinsic positional template relation:

```lean
inductive SameOrchestrationTraceTemplate :
    Trace dynamics inertia sourceBefore sourceAfter →
    Trace dynamics inertia shadowBefore shadowAfter →
    Type (u + 1) where
  | nil ...
  | cons
      (same : SameOrchestrationTemplate shadowHead sourceHead)
      (tail : SameOrchestrationTraceTemplate sourceTail shadowTail)
```

The exact indices may be packaged through the two raw orchestration heads, but
the relation must identify every retained position, not only the aggregate
rule and actor lists.

Define the exact output square:

```lean
structure ForwardNamesTraceSquare
    (family : VestigialNames before names)
    (trace : Trace dynamics inertia before after) where
  removedAfter : State catalog Ambient
  matched :
    Trace dynamics inertia (removeNames before names) removedAfter
  rules_eq : matched.rules = trace.rules
  actors_eq : matched.actors = trace.actors
  templates : SameOrchestrationTraceTemplate trace matched
  remove_after : removeNames after names = removedAfter
  remains : VestigialNames after names
  matchedAssignment : TraceProgramAssignment dynamics inertia matched
```

```lean
noncomputable def forwardNamesOrchestrationTrace
    (family : VestigialNames before names)
    (safe : SafeNamesOrchestrationTrace names dynamics inertia trace) :
  ForwardNamesTraceSquare family trace
```

The assignment and positional template certificate must be constructed during
the same recursion. This is the strongest exact multi-entry suffix theorem
currently supported by the base semantics.

## 12. Fiber lifetimes and no-redraw boundary

General episode deletion cannot identify a fiber only by name. O-Remove permits
the same name to be inserted again for an unrelated component.

Define at least the boundary vocabulary:

```lean
structure FiberLifetime (Name : Type u) where
  name : Name
  birth : Nat
```

```lean
def FiberLifetime.PresentAt
    (lifetime : FiberLifetime sig.Name)
    (state : State catalog Ambient) : Prop :=
  ∃ fiber,
    state.registry lifetime.name = some fiber ∧
    fiber.birth = lifetime.birth
```

This is only state-indexed vocabulary. A later theorem still needs insertion
provenance, uniqueness in the relevant trace, and a source/shadow lifetime
correspondence; opaque recovery does not currently imply global birth
monotonicity.

Define redraw semantically for every rule, rather than enumerating only
explicit insertion constructors:

```lean
def DrawsName
    (step : Step dynamics inertia before after)
    (name : sig.Name) : Prop :=
  before.registry name = none ∧
    ∃ fiber, after.registry name = some fiber
```

This detects O-Insert, successful registration landings, and any new entry
created by opaque unload recovery. An `Option sig.Name` projection is
insufficient because recovery may introduce more than one name.

Define:

```lean
def NoRedraw
    (names : List sig.Name)
    (trace : Trace dynamics inertia before after) : Prop :=
  ∀ record,
    record ∈ Trace.records trace →
    ∀ name,
      DrawsName record.step name →
      name ∉ names
```

For the future episode theorem, the intended bounded premise is specifically:

```lean
NoRedraw ledger.names located.episode.afterTrace
```

It applies only to the post-close suffix; applying it to the episode core would
forbid the very registrations recorded by the ledger. This bare-name condition
is intentionally stronger than a lifetime-correct policy and rejects all later
reuse of those names.

No current recovery or dynamics law derives this semantic no-redraw property;
it is explicit future authority.

Retain or extend the existing kernel witness that a removed vestigial name can
be redrawn. Package it as an actual trace and prove a named theorem of the
shape:

```lean
theorem redraw_trace_not_noRedraw :
  ¬NoRedraw [deletedName] redrawTrace
```

Do not claim current well-formedness implies `NoRedraw`.

The exact multi-vestigial theorem above does not need lifetime transport
because every retained step is foreign to every removed name. These
definitions state the larger boundary required by future episode deletion.

## 13. Positive record-deletion example

Construct a state containing:

- a provider at name `0`; and
- one retired, successful-inactive, empty-table, childless entry at name `1`.

The source trace is:

```text
[ O-Remove(1), O-Retire(0) ]
```

The shadow trace is:

```text
[ O-Retire(0) ]
```

Build an actual `DeletionReplay` under current `EffectRelated`:

- drop O-Remove(1), using `Vestigial.effectRelated_remove`;
- retain O-Retire(0) with an exact replay step and orchestration assignment;
  and
- finish under reflexive effect relation.

Also package that replay as a `DeletionResult` from the removed shadow source;
the wrapper must be exercised rather than left as dead public structure.

Kernel-prove:

- the shadow rule list is `[.oRetire]`;
- it is a sublist of `[.oRemove, .oRetire]`;
- actors form the corresponding sublist;
- final states are related;
- the shadow trace is intrinsically aligned; and
- any supplied source `TraceProgramAssignment` is transformed into an output
  assignment; and
- the executable decision projection is exactly `[.drop, .keep]` and its
  length is the source record count.

Expose a computable kept-rule/actor or keep/drop projection for the runtime
test. Do not place `#eval` in the library.

## 14. Positive finite multi-name suffix example

Instantiate `VestigialNames` with at least one real entry and replay one or
more safe foreign orchestration records. Prove:

- the exact removed endpoint equation;
- identical rule and actor lists;
- preservation of the vestigial family; and
- construction of the matched assignment ledger.

If practical, include two vestigial names to exercise iteration rather than
only the singleton base case. A singleton remains acceptable only if the
generic recursion itself is independently audited.

## 15. Why full Lemma 72 remains absent

The generic replay type can represent a future theorem; it does not derive the
required local matches.

Full closing-episode deletion still needs:

1. a Corollary-62-style local episode projection under explicit temporal
   recovery certificates;
1. complete registration and retirement provenance;
1. a `VestigialRegistrationBoundary` proof, not merely its type;
1. no-redraw or lifetime-indexed deletion;
1. parent safety or descendant closure at every retained insertion;
1. a `VestigialOrAbsent` suffix invariant if source-side O-Remove steps at
   deleted names are dropped, or an explicit ban on those removals;
1. exact lifecycle/read/oracle/inertia/recovery matching for every retained
   suffix occurrence;
1. a relation outside deleted lifetimes that erases or relates allocator
   birth ranks and `nextBirth`; and
1. a proved retained-step simulation for that new relation.

Current `EffectRelated` is too weak for rule replay because it forgets
lifecycle and registry controls. Current `RuleRelated` is too strong because
it observes both `nextBirth` and every fiber's birth. Current name equivariance
preserves those ranks and therefore cannot repair the mismatch.

The paper's final applicability argument also invokes printed Lemma 70. A
corrected derivation must either consume `SupportOrder`, `ActiveParentClosed`,
well-formedness, quiescence, no failure, and provision totality as in
`GlobalSupport.support_eq_active`, or bypass that argument by supplying an
actual `RetainedStep` replay certificate for every suffix occurrence. These
are different theorem architectures; the generic replay type supports the
second but does not derive the first.

Negative evidence must retain both allocator failures: removing a child does
not restore `nextBirth`, and the existing
`registration_insert_birth_order_differs` theorem shows that surviving fixed
names may receive exchanged birth ranks even when final clocks agree.

## 16. Why Theorem 73 remains absent

The printed orchestration-front canonical order is also false under arbitrary
non-root O-Insert. A corrected normalization order must retain at least:

```text
MustPrecede :=
  original order among orchestration inputs
  ∪ registration-before-child-use
  ∪ parent-creation-before-dependent-O-Insert
  ∪ exact-allocator-order from every registering activation to every O-Insert
      it would otherwise have to cross
  ∪ support-order episode dependencies.
```

The allocator edge is independent of parent enablement: even a root-parented
O-Insert cannot cross a registering activation under the current exact
birth-ranked semantics. A future alternative may replace that edge with a
`RelatedAdjacentSwap` only after defining and proving a birth-erased or
rank-renamed step simulation.

Future work needs an explicitly well-founded or acyclic `MustPrecede`
certificate; `SupportOrder` for one component of the union is insufficient.
A supplied finite `NormalizationPlan` must have every move discharged by an
`AssignedAdjacentSwap`, certified deletion replay, or the future relational
swap. It must then prove plan existence and termination of the finite
normalization algorithm before claiming canonical form. Separately, upgrading
confluence of already-quiescent traces to unique-normal-form existence needs
maximal lifecycle termination of the kind printed Theorem 66 claims; current
`GlobalProgress` proves neither obligation. Two normal forms additionally
require trace-level name action and uniqueness under the birth-erased outside
relation.

## 17. Circular APIs to reject

Do not accept any of the following as the theorem:

- an arbitrary already-filtered output trace with no positional keep/drop
  derivation;
- a preassembled output `TraceProgramAssignment`;
- same rule and actor as a substitute for a real replayed
  `ProgramOccurrence`;
- an arbitrary `∀ record, ∃ matched` law presented as though it came from base
  dynamics;
- `GlobalTemporal.Intervening.replay`, which composes total state maps but does
  not prove raw step applicability;
- exact endpoint equality after deleting a registration despite `nextBirth`;
- a birth-erased relation with no retained-step bisimulation; or
- name equivariance as a substitute for allocator-rank transport.

## 18. Explicit non-claims

This slice does not prove:

- paper Lemma 72;
- Theorem 73, canonical form, confluence, or unique normal forms;
- deletion of a general closed lifecycle episode;
- automatic registration/retirement provenance;
- that “no child episode” implies vestigiality;
- lifecycle, iterator, oracle, inertia, or recovery suffix simulation;
- no-redraw from well-formedness;
- correctness across reused bare names without lifetime evidence;
- exact endpoint equality after deleting registration;
- current `RuleRelated` after deletion;
- a birth-erased or rank-renamed outside relation;
- backward deletion bisimulation;
- arbitrary normalization or plan existence; or
- acyclicity of the future combined `MustPrecede` relation;
- termination of a future finite normalization algorithm; or
- quantitative progress, fairness, or maximal lifecycle termination.

The exact positive claim is:

> A relation-indexed intrinsic keep/drop certificate reconstructs a valid
> dependent replay trace and its fixed-program assignment ledger. For a finite
> family of entries already proved vestigial, every retained foreign
> orchestration suffix whose insertions avoid those parents has an exact
> same-rule, same-actor, same-template replay after removing the family.

## 19. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalDeletion
lake env lean Cordis/GlobalDeletion.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalDeletion.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. add the positive keep/drop and exact suffix projections to
   `Cordis.TestSuite`;
1. add guarded attempts to replay the parent-adopting insert or fabricate an
   output assignment to `Cordis.NegativeTests` where they add evidence beyond
   the kernel countermodels;
1. add selected counterexample, replay, assignment, multi-name, and positive
   declarations to `Cordis.AxiomAudit`;
1. change this specification's status to implemented;
1. update `README.md`, `SPEC.md`, `docs/PAPER_MAP.md`,
   `docs/V0_2_SPEC.md`, `docs/TRUST_BOUNDARY.md`, and
   `docs/IMPLEMENTATION_GUIDE.md`;
1. run strict/default builds, runtime suite, demo, hygiene, documentation,
   link, and selected-axiom gates; and
1. repeat every gate from a clean `git archive` before pushing.
