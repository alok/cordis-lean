# Foreign-phase frame: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: next implementation slice after `Cordis.GlobalTransposition`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 48's read
restriction and Lemma 71's activation-step exchange.

## 1. Goal

Implement `Cordis.GlobalForeignPhase`, the exact lower layer between the raw
Definition 60 diamond and any future lifecycle transition transposition.

The module must:

1. prove that full `GlobalIteratorIndependence.Independent` does not imply
   `GlobalTransposition.ForeignPhaseCompatibility`;
1. expose noncircular read/result/oracle frame laws;
1. derive `ForeignPhaseCompatibility` from those laws using
   `Dynamics.run_read_confined`;
1. construct one-sided phase-framed executions; and
1. combine two compatibility certificates with the existing raw diamond and
   `setPhase_commute` to obtain a framed raw endpoint diamond.

No declaration may mention a lifecycle `Transition` as a hypothesis or
conclusion, and no result may be called paper Lemma 71.

## 2. Why iterator independence is insufficient

Definition 60 closes the partial forward maps and yielded inverse
interpretations of iterator programs. A foreign lifecycle phase edit is not a
generator in either closure. Therefore closure commutation and yield stability
do not constrain what an iterator observes after that edit.

The existing `Dynamics.ReadEquivalent` relation is also caller-defined. The
base record proves only reflexivity and preservation of `runIterator` for pairs
already declared read-equivalent. It does not state that a distinct owner's
`setPhase` update is read-equivalent.

## 3. Required independence counterexample

Build a finite two-owner model with:

- `Name := Bool`;
- one unit iterator code;
- Boolean external undo codes;
- a registry containing fibers at both names;
- the observed program owned by `false` and the foreign program owned by
  `true`;
- identity raw successor maps whenever the selected owner is present; and
- an external undo interpreter that ignores its Boolean code and returns its
  input state.

The observed program's raw result must choose its Boolean undo code by inspecting
the phase of the foreign fiber:

```text
foreign inactive -> false
foreign active   -> true
```

The foreign program always yields `false`. Both continuations are `none`.

Choose:

```lean
dynamics.equivalence.r := Eq
dynamics.ReadEquivalent owner left right := left = right
```

Every successful forward generator is a partial identity and every inverse
generator is total identity. Prove generator commutation and generator yield
stability, then use `Independent.of_generators` to obtain the complete
cross-closure certificate:

```lean
theorem programs_independent :
  Independent observedProgram foreignProgram
```

Let `before` contain the foreign fiber in `.inactive none`, and let
`afterPhaseEdit` activate that same foreign fiber. Prove successful observed
program executions at both states. Their semantic yields agree because the two
undo interpretations are the same function, but their stored codes differ:

```lean
theorem semantic_yields_agree : YieldAgrees afterEditStep beforeStep
theorem undo_codes_differ : afterEditStep.undo ≠ beforeStep.undo
theorem lifecycle_yields_do_not_agree :
  ¬LifecycleYieldAgrees afterEditStep beforeStep
```

The decisive result is:

```lean
theorem independent_not_foreignPhaseCompatible :
  Independent observedProgram foreignProgram ∧
    ¬ForeignPhaseCompatibility observedProgram
```

The negative proof must use `ForeignPhaseCompatibility.execute_setPhase` and
the exact moved execution to contradict `lifecycle_yields_do_not_agree`.

Also prove that the concrete foreign phase edit is not
`dynamics.ReadEquivalent` for the observed owner. This locates the gap in the
current dynamics interface without pretending that every dynamics must fail it.

Add two focused necessity witnesses:

1. an ordinary-frame model where the foreign edit is `ReadEquivalent` and
   `run_read_confined` preserves the exact undo/continuation, but the moved raw
   successor is only related by a coarse dynamics equivalence and fails the
   exact `setPhase` frame equation; and
1. an oracle model where `runIterator` returns the same registration request on
   both read-equivalent states, but the fixed oracle accepts before the phase
   edit and rejects afterward or chooses another child.

These witnesses must separately prove that readability alone does not imply the
ordinary frame and that raw registration read stability does not imply stable
`executeOne` admission.

## 4. Foreign phase readability

First prove the reusable source fact:

```lean
theorem IterationStep.owner_present
    (step : IterationStep dynamics owner code state) :
    ∃ fiber, state.registry owner = some fiber
```

The ordinary branch uses `dynamics.ordinary_confined`; the registration branch
uses `RegistrationAdmission.owner_present`.

Define the first lower, program-scoped law:

```lean
structure ForeignPhaseReadable
    (program : Program dynamics) : Prop where
  read_equivalent :
    ∀ {state foreignName foreignFiber phase},
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      dynamics.ReadEquivalent program.owner state
        (setPhase state foreignName foreignFiber phase)
```

Together with `setPhase_lookup_other`, this supplies both owner lookups and the
read relation required by `Dynamics.run_read_confined`.

The resulting `RunRelated` witness already gives:

- exact ordinary external undo-code equality;
- exact ordinary continuation equality;
- related ordinary successors;
- exact registration component equality; and
- exact equality of registration continuation functions.

It does not give an exact successor frame or stable oracle admission.

## 5. Ordinary successor frame

Define an ordinary-only exact frame law below lifecycle transitions:

```lean
structure OrdinaryForeignPhaseFrame
    (program : Program dynamics) : Prop where
  after_eq :
    ∀ {code state foreignName foreignFiber phase
        original moved},
      Reach program code →
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      dynamics.runIterator program.owner code state =
        .ok (.ordinary original) →
      dynamics.runIterator program.owner code
          (setPhase state foreignName foreignFiber phase) =
        .ok (.ordinary moved) →
      dynamics.equivalence.r original.after moved.after →
      moved.after =
        setPhase original.after foreignName foreignFiber phase
```

Do not duplicate undo/continuation equality in this record. Those fields must be
obtained from `run_read_confined`, making the use of Definition 48 visible.

## 6. Registration oracle frame

Registration needs a separate program-specific law because `RunRelated` does not
choose a child or prove moved-state admission:

```lean
structure RegistrationOracleForeignPhaseFrame
    (program : Program dynamics) : Prop where
  certify :
    ∀ {code state foreignName foreignFiber phase
        originalRequest movedRequest originalAdmission},
      Reach program code →
      state.registry foreignName = some foreignFiber →
      foreignName ≠ program.owner →
      dynamics.runIterator program.owner code state =
        .ok (.register originalRequest) →
      dynamics.runIterator program.owner code
          (setPhase state foreignName foreignFiber phase) =
        .ok (.register movedRequest) →
      originalRequest.component = movedRequest.component →
      originalRequest.next = movedRequest.next →
      program.oracle.certify state originalRequest =
        .ok originalAdmission →
      ∃ movedAdmission,
        program.oracle.certify
            (setPhase state foreignName foreignFiber phase)
            movedRequest = .ok movedAdmission ∧
        movedAdmission.child = originalAdmission.child
```

Equal child selection plus equal request continuations must be used to recover
exact retirement undo and concrete continuation equality. Determinism of the
oracle at each state is not a substitute for this cross-state law.

Do not assume the registration successor frame. Prove a structural helper that
registration insertion at the oracle-selected fresh child commutes with a
pre-existing, distinct foreign `setPhase` update. Freshness and the foreign
lookup prove that the child and foreign name differ. Equality of request
component/continuation fields identifies the raw registration requests, and
same-child selection then yields the exact framed successor equation.

## 7. Derive foreign-phase compatibility

Prove:

```lean
theorem ForeignPhaseCompatibility.of_read_frames
    (readable : ForeignPhaseReadable program)
    (ordinary : OrdinaryForeignPhaseFrame program)
    (registration : RegistrationOracleForeignPhaseFrame program) :
    ForeignPhaseCompatibility program
```

The proof must:

1. derive the owner's source lookup from the successful `IterationStep.source`;
1. retain that lookup after the distinct foreign edit;
1. call `dynamics.run_read_confined`;
1. eliminate impossible error/branch mismatches;
1. use `OrdinaryForeignPhaseFrame.after_eq` in the ordinary case;
1. use `RegistrationOracleForeignPhaseFrame.certify` in the registration case;
1. derive registration insertion/phase commutation structurally from request
   equality, same-child selection, and freshness;
1. construct the exact moved `executeOne` result;
1. construct `LifecycleYieldAgrees`; and
1. return the exact raw-successor frame equation.

The theorem must not assume `ForeignPhaseCompatibility` or any transition-level
bisimulation in its premises.

## 8. Phase-framed executions

Package one use of compatibility:

```lean
structure PhaseFramedExecution
    (program : Program dynamics)
    (step : IterationStep dynamics program.owner code state)
    (foreignName : sig.Name)
    (foreignFiber : Fiber catalog)
    (foreignPhase : Phase (catalog.declaration foreignFiber.component)) where
  movedStep : IterationStep dynamics program.owner code
    (setPhase state foreignName foreignFiber foreignPhase)
  executed :
    executeOne dynamics program.oracle code
        (setPhase state foreignName foreignFiber foreignPhase) =
      .ok movedStep
  yield_agrees : LifecycleYieldAgrees movedStep step
  after_eq :
    movedStep.after =
      setPhase step.after foreignName foreignFiber foreignPhase
```

Add a noncomputable constructor from:

- `ForeignPhaseCompatibility program`;
- `Reach program code`;
- the exact foreign-fiber source lookup;
- distinct ownership; and
- the original successful execution.

## 9. Framed raw diamond

Build a theorem below lifecycle transitions that combines:

- `Independent left right`;
- both reachable/common-source successful iterator executions;
- `ForeignPhaseCompatibility left` and right;
- distinct owners;
- the left owner's post-left-raw fiber and lookup in `leftStep.after`;
- the right owner's post-right-raw fiber and lookup in `rightStep.after`; and
- arbitrary well-typed left and right phase payloads.

First use `independent_forward_diamond`. Then frame the right off-axis execution
across the supplied left edit and the left off-axis execution across the supplied
right edit. Apply the second phase update to each framed raw successor. Use the
raw endpoint equality, both exact frame equations, and `setPhase_commute` to prove
the two final framed raw states exactly equal.

The result may package:

```lean
structure PhaseFramedDiamond ... where
  raw : ForwardDiamond leftStep rightStep
  rightAfterLeftEdit : PhaseFramedExecution ...
  leftAfterRightEdit : PhaseFramedExecution ...
  right_present_before_final :
    rightAfterLeftEdit.movedStep.after.registry right.owner =
      some rightFiber
  left_present_before_final :
    leftAfterRightEdit.movedStep.after.registry left.owner =
      some leftFiber
  endpoint_eq :
    setPhase rightAfterLeftEdit.movedStep.after
        right.owner rightFiber rightPhase =
      setPhase leftAfterRightEdit.movedStep.after
        left.owner leftFiber leftPhase
```

The phase payloads are supplied. The theorem must not claim they are the phases
selected by an L-Iter or L-Finish rule.

Derive the two retained lookup fields rather than assuming them. Use
`GlobalTraceFacts.iteration_foreign_lookup` on each off-axis raw execution,
transport across `ForwardDiamond.endpoint_eq`, then preserve the remaining
foreign lookup through the framed `setPhase` edit with
`setPhase_lookup_other`. This records that the final point updates use the
actual post-raw fibers rather than arbitrary stale payloads.

## 10. Explicit non-claims

This slice does not prove:

- that `Independent` implies foreign-phase compatibility;
- that `Dynamics.ReadEquivalent` includes foreign control edits;
- that `EffectEquiv` implies `ProgramRespects` or any read-frame law;
- that a registration oracle chooses the same child across foreign edits without
  its explicit frame law;
- lifecycle target or guard stability;
- that supplied phase payloads correspond to lifecycle rule outputs;
- fixed program/oracle assignment for every live fiber episode;
- a lifecycle `Transition` diamond or either clause of paper Lemma 71;
- mixed-trace reordering, Theorem 61, Corollary 62, or confluence; or
- paper Definition 65/Theorem 66 progress.

`PhaseFramedDiamond` is an exact theorem about raw iterator execution plus
supplied point updates. It is not an activation-rule transposition theorem.

## 11. Verification requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalForeignPhase
lake env lean Cordis/GlobalForeignPhase.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalForeignPhase.lean
```

The module must contain no `sorry`, `admit`, custom axiom, `unsafe`, `partial`,
native-decision trust shortcut, or compiler implementation override. Add one
runtime observation of the counterexample, one guarded failure proving
independence cannot fabricate compatibility, and selected axiom entries before
adding the module to `Cordis.lean`.
