# Corrected global support: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: planned

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 67, Lemma
68, Definition 69, and Lemma 70.

Dependency: the state-local `PrecedesAt` relation from `Cordis.GlobalProgress`.

## 1. Goal

Implement `Cordis.GlobalSupport`, a counterexample-first corrected support
layer.

The module must kernel-refute the printed Lemma 68 premise before defining the
positive API:

- provider precedence may be well founded;
- the strengthened birth-ranked parent relation may be acyclic;
- the state may be reached from an empty registry by legal O-Inserts; yet
- the union of provider and parent edges may contain a cycle.

That cycle makes the Definition 67 recursive equations nonunique. The positive
support set must therefore require well-foundedness of the combined relation
directly, not derive it from separate acyclicity.

The module must also expose the independent Lemma 70 parent-provenance seam.
An active child with an inactive or retired parent is legal under current
static `WellFormed` and arbitrary non-root O-Insert. A corrected support/active
equality theorem therefore needs explicit active-parent closure unless a later
trace-provenance layer derives it.

## 2. Static support relations

Reuse `GlobalProgress.PrecedesAt` with provider-to-consumer orientation.

Define the parent edge:

```lean
def ParentEdge
    (state : State catalog Ambient)
    (parent child : sig.Name) : Prop :=
  ∃ childFiber,
    state.registry child = some childFiber ∧
      childFiber.parent = some parent
```

Define the combined relation:

```lean
def SupportEdge
    (state : State catalog Ambient)
    (lower upper : sig.Name) : Prop :=
  PrecedesAt state lower upper ∨ ParentEdge state lower upper
```

Both constructors point from a support prerequisite to the fiber depending on
it:

- provider to consumer;
- parent to child.

Do not reverse one half merely to obtain a convenient rank.

## 3. Reachable mixed-cycle counterexample

Use a finite two-name signature with one key and two components:

- root consumer `A`:
  - dependencies `{k}`;
  - provision empty;
- child provider `B`:
  - dependencies empty;
  - provision `{k}`;
  - parent `A`.

Starting from an empty registry, construct an exact `FromEmpty` trace:

```text
O-Insert A at root;
O-Insert B with parent A.
```

Kernel-prove:

```lean
theorem final_wellFormed : WellFormed final

theorem precedence_wellFounded :
  WellFounded (PrecedesAt final)

theorem parent_edge : ParentEdge final A B

theorem provider_edge : PrecedesAt final B A

theorem support_cycle :
  Relation.TransGen (SupportEdge final) A A

theorem supportEdge_not_wellFounded :
  ¬WellFounded (SupportEdge final)
```

This state satisfies the current strengthened parent birth order. The
counterexample pinpoints the paper proof's unsupported step: O-Insert permits an
orchestrator to place a provider below an arbitrary present consumer without
that provider being registered by the consumer's activation.

Also document the general graph error: the union of two acyclic relations need
not be acyclic. A larger alternating cycle need not reduce to one direct
descendant-provider edge without an additional common rank argument.

## 4. Definition 67 equations

Define:

```lean
def ParentSupported
    (candidate : sig.Name → Prop)
    (fiber : Fiber catalog) : Prop :=
  match fiber.parent with
  | none => True
  | some parent => candidate parent
```

```lean
def DependenciesSupported
    (state : State catalog Ambient)
    (candidate : sig.Name → Prop)
    (fiber : Fiber catalog) : Prop :=
  ∀ key,
    key ∈ (catalog.declaration fiber.component).dependencies.keys →
    ∃ provider providerFiber,
      state.registry provider = some providerFiber ∧
        candidate provider ∧
        key ∈ (catalog.declaration providerFiber.component).provision
```

```lean
def SupportClause
    (state : State catalog Ambient)
    (candidate : sig.Name → Prop)
    (name : sig.Name) : Prop :=
  ∃ fiber,
    state.registry name = some fiber ∧
      fiber.retired = false ∧
      ParentSupported candidate fiber ∧
      DependenciesSupported state candidate fiber
```

```lean
def SupportSolution
    (state : State catalog Ambient)
    (candidate : sig.Name → Prop) : Prop :=
  ∀ name, candidate name ↔ SupportClause state candidate name
```

Also define the explicit registry-domain predicate:

```lean
def PresentNames
    (state : State catalog Ambient)
    (name : sig.Name) : Prop :=
  ∃ fiber, state.registry name = some fiber
```

Package existence and extensional uniqueness explicitly:

```lean
def HasUniqueSupport
    (state : State catalog Ambient) : Prop :=
  ∃ supported : sig.Name → Prop,
    SupportSolution state supported ∧
      ∀ candidate,
        SupportSolution state candidate → candidate = supported
```

For the mixed-cycle state, prove both the empty predicate and
`PresentNames final` solve the equation and are distinct:

```lean
theorem empty_support_solution : ...
theorem present_support_solution : ...
theorem no_unique_support : ¬HasUniqueSupport final
```

For the two-name example it is fine to additionally prove
`PresentNames final = fun _ => True`; do not use literal `True` as the public
meaning of “full support” if the carrier later gains an unused name.

This separately refutes the uniqueness conclusion of Lemma 68.

## 5. Explicit combined-order authority

Define:

```lean
structure SupportOrder
    (state : State catalog Ambient) : Prop where
  wellFounded : WellFounded (SupportEdge state)
```

Do not add fields for separate precedence or parent acyclicity as substitutes.
They may be consequences or diagnostics, but the combined certificate is the
recursion authority.

## 6. Support by well-founded recursion

Define support using `SupportOrder.wellFounded.fix`:

```lean
noncomputable def supported
    (order : SupportOrder state) : sig.Name → Prop
```

The recursion body may need a local edge-indexed candidate such as:

```lean
fun lower => ∃ edge : SupportEdge state lower name, recursive lower edge
```

or an equivalent decidable `if edge then ... else False`. Prove a
`supportClause_congr` lemma and use it to identify that local candidate with the
public `supported order`. A raw recursive call without carrying the lower-edge
proof does not satisfy `WellFounded.fix`'s motive.

At name `n`, recursive hypotheses are available exactly for:

- `parent` through `ParentEdge state parent n`; and
- each selected provider through `PrecedesAt state provider n`.

Prove the unfolding equation:

```lean
theorem supported_iff
    (order : SupportOrder state) (name : sig.Name) :
    supported order name ↔
      SupportClause state (supported order) name
```

Then prove:

```lean
theorem supported_solution
    (order : SupportOrder state) :
    SupportSolution state (supported order)
```

```lean
theorem support_solution_unique
    (order : SupportOrder state)
    (candidate : sig.Name → Prop)
    (solution : SupportSolution state candidate) :
    candidate = supported order
```

Use well-founded induction, function extensionality, and proposition
extensionality. Do not use finite enumeration or a least-fixed-point library as
a replacement for the displayed recursive semantics.

Package:

```lean
theorem hasUniqueSupport
    (order : SupportOrder state) : HasUniqueSupport state
```

## 7. State-local Definition 69

Current fibers guarantee only:

```text
dom(table) subset component.provision.
```

Define the missing converse for active fibers:

```lean
def TotalOnProvisionAt
    (state : State catalog Ambient) : Prop :=
  ∀ name fiber,
    state.registry name = some fiber →
    fiber.Active →
    ∀ key,
      key ∈ (catalog.declaration fiber.component).provision →
      (fiber.table key).isSome = true
```

Prove the exact table-domain equivalence at active fibers from this law plus
`Fiber.table_within_provision`.

This is deliberately state-local. The paper's component-wide property—every
finishing activation installs every provision key—requires fixed component/
program/episode provenance and belongs in a later module.

## 8. No-failure and active-name predicates

Define:

```lean
def NoFailedFiber
    (state : State catalog Ambient) : Prop :=
  ∀ name fiber error,
    state.registry name = some fiber →
    fiber.phase ≠ .inactive (some error)
```

```lean
def ActiveNames
    (state : State catalog Ambient)
    (name : sig.Name) : Prop :=
  ∃ fiber,
    state.registry name = some fiber ∧ fiber.Active
```

Prove basic lookup/phase consequences needed by the quiescent theorem.

## 9. Parent-closure seam

Define the smallest static authority missing from the paper/current trace API:

```lean
def ActiveParentClosed
    (state : State catalog Ambient) : Prop :=
  ∀ child childFiber parent,
    state.registry child = some childFiber →
    childFiber.parent = some parent →
    childFiber.Active →
    ∃ parentFiber,
      state.registry parent = some parentFiber ∧ parentFiber.Active
```

This is not implied by `WellFormed`, `FromEmpty`, or `Quiescent`:

- external O-Insert may create a non-root child;
- the parent does not necessarily retain that child in an accumulator;
- retiring/unloading the parent need not retire an arbitrarily orchestrated
  child.

Add a finite `ActiveParentGap` with:

- retired successful-inactive root parent;
- active unretired child with empty dependencies;
- well-founded `SupportEdge`;
- `WellFormed`, `Quiescent`, `NoFailedFiber`, and
  `TotalOnProvisionAt`; but
- `¬ActiveParentClosed` and `supported order ≠ ActiveNames state`.

This is an independent Lemma 70 counterexample after the Lemma 68 order problem
has already been repaired explicitly.

## 10. Active names form the support solution

Under:

- `WellFormed state`;
- `Quiescent state`;
- `NoFailedFiber state`;
- `TotalOnProvisionAt state`; and
- `ActiveParentClosed state`;

prove:

```lean
theorem activeNames_solution :
  SupportSolution state (ActiveNames state)
```

Proof obligations:

### Active to support clause

- quiescence gives the exact positive target equal to the active committed
  view;
- target soundness gives `retired = false` and active providers for every
  dependency;
- table presence plus `table_within_provision` gives each provider's declared
  provision membership; and
- `ActiveParentClosed` supplies the parent clause.

### Support clause to active

- every candidate provider is active by the chosen candidate predicate;
- `TotalOnProvisionAt` turns its static provision membership into an actual
  table value;
- choose a committed provider view for all declared keys and build a positive
  `IsTargetView`;
- `targetView_eq_of_isTarget` gives a positive target;
- quiescence excludes reloading/unloading;
- `NoFailedFiber` excludes `.inactive (some error)`; and
- `.inactive none` would require target `none`, so only Active remains.

The choice of one provider per dependency may use standard `Classical.choice`.

## 11. Corrected quiescent support theorem

Prove:

```lean
theorem support_eq_active
    (order : SupportOrder state)
    (wf : WellFormed state)
    (quiet : Quiescent state)
    (noFailed : NoFailedFiber state)
    (total : TotalOnProvisionAt state)
    (parents : ActiveParentClosed state) :
    supported order = ActiveNames state
```

Derive it from:

- `activeNames_solution`; and
- `support_solution_unique order`.

This is the source-honest corrected local analogue of Lemma 70.

## 12. Printed-hypothesis counterexample at quiescence

Retain a separate finite active state with the mixed parent/provider cycle and
prove:

```lean
WellFormed activeState
WellFounded (PrecedesAt activeState)
Quiescent activeState
NoFailedFiber activeState
TotalOnProvisionAt activeState
```

while both the empty and present-name support predicates solve Definition 67.
Prove active names equal the present-name solution but support is nonunique.

Also prove `ActiveParentClosed activeState`. This isolates the failure to the
missing combined `SupportOrder`: the state then satisfies every corrected
Lemma-70 assumption except well-foundedness of `SupportEdge`.

This is a static finite witness for the printed Lemma 70 hypothesis shape. Do
not call it a `FromEmpty` lifecycle execution unless an explicit dynamics trace
that installs the provider table is constructed. The earlier inactive
counterexample already refutes Lemma 68 with an actual `FromEmpty` trace.

## 13. Future support provenance

Do not derive `SupportOrder` or `ActiveParentClosed` from current `FromEmpty`.
A later `GlobalSupportProvenance` layer needs at least one of:

- external O-Insert is root-only;
- every non-root insertion carries proof that it came from registration by its
  parent; or
- an explicit combined support rank respected by every insertion.

It must also retain:

- the registration child's matching retirement undo in the parent
  accumulator;
- execution of that retirement during recovery;
- new-name and retirement-write provenance across opaque recovery; and
- trace linkage from each child to the exact episode/program that registered
  it.

Current `RecoveryConfinement` deliberately permits new opaque names and current
trace facts do not prove retirement-write provenance.

## 14. Positive executable evidence

Compile at least:

- the reachable mixed-cycle counterexample;
- empty/present-name support-solution nonuniqueness;
- the active printed-hypothesis nonuniqueness model;
- the independent `ActiveParentGap` under a valid `SupportOrder`; and
- one acyclic root-only state whose explicit `SupportOrder` yields
  `support_eq_active`.

Add a computable finite projection such as:

```text
(precedence edge, parent edge, support-cycle flag)
```

or active/support Boolean membership. Bridge any noncomputable support result
to the executable projection with kernel theorems; do not place `#eval` in the
library.

## 15. Explicit non-claims

This slice does not prove:

- pinned Lemma 68 from precedence acyclicity;
- that separate provider and parent acyclicity imply union acyclicity;
- that every non-root parent pointer came from activation registration;
- that `FromEmpty` supplies new-entry or retirement provenance;
- component-wide Definition 69 from a state-local table property;
- Active/support equality without `ActiveParentClosed`;
- full Lemma 70 from the printed assumptions;
- trace-wide episode/program assignment;
- Lemma 72 deletion;
- Theorem 73 canonical form or confluence;
- a birth-erasing paper rule relation; or
- progress or termination.

The exact positive claim is:

> A state whose combined parent/provider support relation is explicitly well
> founded has one recursively defined support solution. At a well-formed,
> quiescent, nonfailed state that is total on active provisions and whose active
> children have active parents, that unique support predicate is exactly the
> set of active fiber names.

## 16. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalSupport
lake env lean Cordis/GlobalSupport.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalSupport.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. add finite support/cycle projections to `Cordis.TestSuite`;
1. add a guarded attempt to derive combined order from precedence-only evidence
   to `Cordis.NegativeTests`;
1. add selected counterexample, recursion, uniqueness, and active-equality
   declarations to `Cordis.AxiomAudit`;
1. change this specification's status to implemented;
1. update `README.md`, `SPEC.md`, `docs/PAPER_MAP.md`,
   `docs/V0_2_SPEC.md`, `docs/TRUST_BOUNDARY.md`, and
   `docs/IMPLEMENTATION_GUIDE.md`;
1. run strict/default builds, runtime suite, demo, hygiene, documentation,
   link, and selected-axiom gates; and
1. repeat every gate from a clean `git archive` before pushing.
