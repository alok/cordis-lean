# Global iterator transposition: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: next implementation slice after commit
`f44f6cb29ddbbb6dd5d1c08e60191f6bf2168aa2`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 60 and
Lemma 71.

## 1. Goal

Add the strongest transposition consequences justified by the current executable
global APIs without claiming an adjacent lifecycle-rule swap.

The slice must prove:

1. exact raw execution diamonds for two reachable codes in independent iterator
   programs;
1. exact and `EffectEquiv`-relational commutation squares for totalized global
   step maps whose closure membership and acted owner are certified;
1. exact commutation of distinct-name phase edits; and
1. an explicit stronger lifecycle-yield relation that retains syntactic
   `UndoCode` equality.

It must also give a kernel counterexample showing why ordinary semantic
`YieldAgrees` does not imply the stronger lifecycle relation when
`Dynamics.applyUndo` is noninjective.

The implementation module is `Cordis.GlobalTransposition`.

## 2. Why Definition 60 stops before lifecycle endpoints

`GlobalIteratorIndependence.Independent` compares the partial forward maps and
interpreted yielded inverses of reachable iterator executions. Its
`YieldAgrees.inverse` field says:

```lean
total (dynamics.applyUndo left.undo) =
  total (dynamics.applyUndo right.undo)
```

This is equality of interpreted functions, not equality of the stored codes.
L-Iter and L-Finish prepend the syntactic code itself to the phase accumulator.
Without injectivity or a canonical-code law for `Dynamics.applyUndo`, equal
inverse functions therefore do not imply equal lifecycle endpoints.

There is a second independent gap. `GlobalTemporal.Step.partialMap` intentionally
models the paper's state map before the lifecycle edit. An actual L-Iter or
L-Finish endpoint additionally calls `setPhase`. `Dynamics.runIterator` receives
the whole global state, and the current abstract `ReadEquivalent` contract does
not prove that changing a foreign fiber's phase is unobservable to another
iterator.

Consequently, Definition 60 already proves a raw execution diamond, but not a
paper Lemma 71 lifecycle transition diamond.

## 3. Raw forward diamond

For programs `left` and `right`, reachable codes, and successful executions from
one origin, define or prove a result with the following data:

```lean
structure ForwardDiamond ... where
  rightAfterLeft :
    IterationStep dynamics right.owner rightCode leftStep.after
  leftAfterRight :
    IterationStep dynamics left.owner leftCode rightStep.after
  right_executed :
    executeOne dynamics right.oracle rightCode leftStep.after =
      .ok rightAfterLeft
  left_executed :
    executeOne dynamics left.oracle leftCode rightStep.after =
      .ok leftAfterRight
  right_yield : YieldAgrees rightAfterLeft rightStep
  left_yield : YieldAgrees leftAfterRight leftStep
  endpoint_eq : rightAfterLeft.after = leftAfterRight.after
```

The theorem `independent_forward_diamond` consumes only:

- `Independent left right`;
- reachability of both codes; and
- the two successful executions at the common source.

Its proof must use all three parts of Definition 60 explicitly:

- `right_yield_stable` constructs the right execution after the left forward;
- `left_yield_stable` constructs the left execution after the right forward;
- `transformations_commute` proves equality of the two raw endpoints.

No totalization, lifecycle transition, global trace, or relation certificate is
allowed in this theorem.

## 4. Totalized program-step map squares

Package one global step with both kinds of evidence needed by the temporal
algebra:

```lean
structure TotalProgramStep
    (effect : GlobalTemporal.EffectEquiv dynamics)
    (program : GlobalIteratorIndependence.Program dynamics)
    (step : GlobalCalculus.Step dynamics inertia before after) where
  map : GlobalTemporal.TotalStepMap effect step
  generated : GlobalIteratorIndependence.StepMapMember program step
```

`generated.owner_eq` must remain part of the package. Identity and recovery maps
can belong extensionally to many closures, so map equality cannot recover the
step's program owner.

Prove two squares:

```lean
theorem TotalProgramStep.commute_exact ... :
  left.map.apply (right.map.apply state) =
    right.map.apply (left.map.apply state)

theorem TotalProgramStep.commute_effect ... :
  effect.setoid.r
    (left.map.apply (right.map.apply state))
    (right.map.apply (left.map.apply state))
```

The exact theorem consumes `Independent`. The relational theorem consumes
`ObservationalIndependent`. Both must derive the square from closure membership
and rewrite the partial executions with the supplied `TotalStepMap.total`
witnesses. Neither theorem may infer totality from an indexed source execution.

## 5. Exact lifecycle-yield agreement

Add a separate relation for the information stored by lifecycle phases:

```lean
structure LifecycleYieldAgrees (left right : IterationStep ...) : Prop where
  undo_eq : left.undo = right.undo
  continuation : left.next = right.next
  kind : sourceKind left = sourceKind right
```

Prove:

```lean
theorem LifecycleYieldAgrees.toYieldAgrees :
  LifecycleYieldAgrees left right → YieldAgrees left right
```

Do not replace the semantic Definition 60 relation globally. Exact code equality
is a stronger lifecycle/control requirement and should remain visibly separate.

## 6. Required noninjective-undo counterexample

Construct a finite executable dynamics with at least two distinct
`ExternalUndoCode` values whose interpretations are the same state function.
The same iterator code must successfully execute at two states and yield the two
different undo codes while retaining the same continuation and ordinary source
kind.

Kernel-check all of the following:

```lean
theorem semantic_yields_agree : YieldAgrees leftStep rightStep
theorem undo_codes_differ : leftStep.undo ≠ rightStep.undo
theorem lifecycle_yields_do_not_agree :
  ¬LifecycleYieldAgrees leftStep rightStep
```

This witnesses the exact reason a raw Definition 60 diamond cannot be silently
upgraded to equality of L-Iter/L-Finish phase accumulators.

## 7. Structural edit theorem

Prove that `GlobalLifecycle.setPhase` commutes exactly at distinct names:

```lean
theorem setPhase_commute ... (different : leftName ≠ rightName) :
  setPhase (setPhase state leftName leftFiber leftPhase)
      rightName rightFiber rightPhase =
    setPhase (setPhase state rightName rightFiber rightPhase)
      leftName leftFiber leftPhase
```

This is a structural ingredient for a later lifecycle theorem. It does not say
that either iterator remains defined or yields the same data after the foreign
edit.

## 8. Noncircular future boundary

Expose, but do not assume inhabited, a lower-level foreign-phase compatibility
contract stated only with:

- `Program` and `Reach`;
- `executeOne` under the program's fixed oracle;
- distinct owner/foreign names;
- the foreign fiber and its exact source lookup witness;
- `setPhase`;
- `LifecycleYieldAgrees`; and
- exact commutation of the raw successor with the foreign phase edit.

The contract must not mention a lifecycle `Transition`, a unified `Step`, a
swapped endpoint, or the theorem it is intended to support. It is the smallest
honest future premise for lifting the raw diamond through phase edits.

## 9. Explicit non-claims

This slice does not prove:

- that `Step.partialMap` totalizes off source;
- that `ProgramRespects` follows from `EffectEquiv`;
- that semantic inverse equality implies exact `UndoCode` equality;
- that an iterator ignores foreign phase/control edits;
- that lifecycle guards or targets survive a foreign activation;
- that every lifecycle landing belongs to one fixed program/oracle occurrence;
- paper Lemma 71's adjacent activation-step transposition;
- its activation/orchestration clause;
- mixed-trace reordering, Theorem 61, Corollary 62, or confluence; or
- Lemmas 68, 70, or 72.

In particular, the paper's activation/orchestration clause cannot be copied into
the current raw calculus: an activation can register a fresh child that a later
O-Insert uses as its parent even when the activation did not register the
O-Insert's own acted name.

## 10. Verification requirements

Before integration, the module must pass:

```bash
lake --wfail build Cordis.GlobalTransposition
lake env lean Cordis/GlobalTransposition.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalTransposition.lean
```

The implementation must contain no `sorry`, `admit`, project-defined axiom,
`unsafe`, `partial`, native-decision trust shortcut, or compiler implementation
override. Headline declarations and counterexamples must be added to
`Cordis.AxiomAudit`, and one executable plus one guarded negative fixture must be
added before the module enters the public umbrella.
