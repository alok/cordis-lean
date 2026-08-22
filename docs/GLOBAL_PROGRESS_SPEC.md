# Conditional global progress: bounded implementation specification

<!-- markdownlint-disable MD013 -->

Status: implemented by `Cordis.GlobalProgress`

Source basis: CORDIS paper revision
`948a07b369c62adb3b12e102458be5c18dfb69b9`, especially Definition 65 and
Theorem 66.

## 1. Goal

Implement `Cordis.GlobalProgress`, a counterexample-first correction of the
paper's global progress layer.

The module must establish three distinct facts:

1. a fixed program may be stuck when its configured registration oracle
   rejects, even though the raw lifecycle relation can silently choose another
   oracle;
1. the raw lifecycle relation itself may be genuinely deadlocked when the
   finite name carrier has no fresh registration name; and
1. a source-honest conditional no-deadlock theorem is derivable once the
   missing execution, recovery, precedence, and committed-provider authorities
   are supplied explicitly.

Do not claim the quantitative or maximal-termination conclusions of Theorem 66. They require trace/program occurrence assignment, a finite name universe
closed under registration, target-turn accounting, and a well-founded global
execution measure that the current repository does not yet provide.

## 2. Exact current mismatch

`GlobalLifecycle.Transition` has no registration-rejection rule.

- `executeOne` distinguishes:

  ```lean
  RunError.iterator error
  RunError.registration error
  ```

- L-Raise accepts only:

  ```lean
  dynamics.runIterator owner code state = .error error
  ```

- L-Iter, L-Finish, and landing L-Divert require an actual successful
  `Landing`.

Therefore a registration request rejected by the selected fixed oracle is
neither a landing nor an L-Raise error.

At the same time, raw `Landing` existentially stores its own oracle. An
unconfigured raw `Transition` may use a different permissive oracle for the
same state. The module must keep fixed-program and raw-relation progress claims
separate.

## 3. Fixed-program registration-rejection gap

Construct a well-formed state with:

- an owner in `.reloading code undos committed`;
- `targetView = some committed`;
- `runIterator = .ok (.register request)`;
- a fixed `Program` whose oracle rejects the request; and
- a non-aborting inertia policy.

Define the narrow configured activation predicate:

```lean
def FixedActivationApplicable
    (program : Program dynamics)
    (state : State catalog Ambient) : Prop :=
  Nonempty (ProgramActivation program state)
```

Kernel-prove:

```lean
theorem fixed_program_rejection_gap :
  WellFormed state ∧
    ¬Quiescent state ∧
    ¬FixedActivationApplicable program state
```

Then construct a different permissive oracle, admitted registration,
`Landing`, and raw L-Finish at the same state:

```lean
theorem raw_relation_can_change_oracle :
  ∃ after, Nonempty (Transition dynamics inertia state after)
```

This is an API underdetermination witness. It does not refute the existential
raw lifecycle relation, but it blocks a fixed-program theorem until lifecycle
occurrences retain program/oracle provenance.

Also exercise the target-changed reloading case:

- with rejecting execution and non-aborting inertia, no fixed-program landing,
  raw iterator error, or abort is available;
- with an always-abort policy, construct `Transition.divertAbort`.

This proves the paper proof's claim that it never needs aborting inertia relies
on an unstated landing-or-raw-error totality law.

## 4. Raw freshness-exhaustion deadlock

Give the stronger literal no-lifecycle-step counterexample with:

- `sig.Name := Bool`;
- both names already present;
- owner `false` reloading at a stable positive target;
- owner `true` active at its target;
- empty dependencies and provisions, hence empty provider precedence;
- an iterator returning a registration request with terminal continuation; and
- a non-aborting inertia policy.

For every possible oracle, an admitted registration would require a fresh
Boolean name. Prove:

```lean
theorem no_admission :
  RegistrationAdmission dynamics state false request → False

theorem no_lifecycle_transition :
  ¬∃ after, Nonempty (Transition dynamics inertia state after)

theorem raw_progress_fails :
  WellFormed state ∧
    ¬Quiescent state ∧
    ¬∃ after, Nonempty (Transition dynamics inertia state after)
```

Constructor-eliminate all eight lifecycle rules. The Iter/Finish/DivertLand
cases must fail because no arbitrary `Landing` can contain an admission, not
because one selected oracle rejects.

Also prove:

```lean
theorem no_freshSupply_bool : ¬Nonempty (FreshSupply Bool)
```

Finiteness and decidable equality do not imply inexhaustible freshness. Even a
`FreshSupply` would not by itself guarantee provision-disjoint admission or
oracle policy acceptance; successful admission is the exact missing semantic
authority.

## 5. Definition 65 provider precedence

Define the state-local relation with provider-to-consumer orientation:

```lean
def PrecedesAt
    (state : State catalog Ambient)
    (provider consumer : sig.Name) : Prop :=
  ∃ providerFiber consumerFiber key,
    state.registry provider = some providerFiber ∧
      state.registry consumer = some consumerFiber ∧
      key ∈ (catalog.declaration providerFiber.component).provision ∧
      key ∈ (catalog.declaration consumerFiber.component).dependencies.keys
```

The relation reads only registry domain and static component declarations. It
does not require fibers to be active.

Expose the finite executable order certificate:

```lean
structure FinitePrecedenceRank
    (state : State catalog Ambient) where
  names : List sig.Name
  nodup : names.Nodup
  covers :
    ∀ name fiber, state.registry name = some fiber → name ∈ names
  rank : sig.Name → Nat
  increases :
    PrecedesAt state provider consumer → rank provider < rank consumer
```

Prove:

- `FinitePrecedenceRank.wellFounded`;
- no positive `TransGen PrecedesAt name name`;
- every nonempty registry predicate represented inside `names` has a
  rank-maximal witness; and
- a strict precedence successor of that witness contradicts maximality.

Do not infer this certificate from `WellFormed`: Definition 65 acyclicity is an
explicit paper assumption, and the later combined support relation needs an
even stronger order.

## 6. Fixed-program registration totality

Name the narrow registration authority:

```lean
structure OracleTotal
    (program : Program dynamics) : Prop where
  admits :
    ∀ {code state request},
      Reach program code →
      dynamics.runIterator program.owner code state =
        .ok (.register request) →
      ∃ admission,
        program.oracle.certify state request = .ok admission
```

This contains no lifecycle transition or progress conclusion.

The direct progress-facing law is:

```lean
def LandingOrRaiseAt
    (program : Program dynamics)
    (code : sig.IteratorCode)
    (state : State catalog Ambient)
    (fiber : Fiber catalog) : Prop :=
  (∃ landing : Landing dynamics program.owner code state fiber,
      LandingProgramWitness program landing) ∨
    ∃ error,
      dynamics.runIterator program.owner code state = .error error
```

```lean
structure LandingOrRaiseTotal
    (program : Program dynamics) : Prop where
  ready :
    ∀ {code state fiber},
      Reach program code →
      state.registry program.owner = some fiber →
      LandingOrRaiseAt program code state fiber
```

Prove:

```lean
theorem OracleTotal.toLandingOrRaiseTotal
    (total : OracleTotal program) : LandingOrRaiseTotal program
```

The proof must case-split `runIterator`:

- raw error gives L-Raise readiness;
- ordinary success constructs the exact `IterationStep` and `Landing` from
  ordinary confinement;
- registration success uses `OracleTotal.admits` and constructs the exact
  registration step/landing.

Retain the fixed program's registration-error type and oracle. Do not replace
the program oracle with an existential one.

## 7. Recovery totality

Name the separate L-Unload authority:

```lean
structure RecoveryTotal
    (dynamics : Dynamics sig catalog Ambient) : Prop where
  admits :
    ∀ {state owner fiber undos committed outcome},
      WellFormed state →
      state.registry owner = some fiber →
      fiber.phase = .unloading undos committed outcome →
      ¬Relied state owner →
      Nonempty
        (RecoveryAdmission dynamics state owner fiber undos outcome)
```

This is noncircular. Current `RecoveryAdmission` and
`RecoveryConfinement` do not imply existence of such an admission.

The state-local theorem must consume only:

```lean
def RecoveryReadyAt
    (dynamics : Dynamics sig catalog Ambient)
    (state : State catalog Ambient) : Prop :=
  ∀ {owner fiber undos committed outcome},
    WellFormed state →
    state.registry owner = some fiber →
    fiber.phase = .unloading undos committed outcome →
    ¬Relied state owner →
    Nonempty
      (RecoveryAdmission dynamics state owner fiber undos outcome)
```

Prove `RecoveryTotal.readyAt`. Keep `RecoveryTotal` as a reusable convenience
contract, not mandatory global authority in `LocalProgressLaws`.

## 8. Committed-provider provision soundness

The paper's unloading-chain proof treats a relied provider as lower in
Definition 65 than its consumer. Current `Relied` stores a committed provider
name, but static `WellFormed` does not prove that the named provider's component
declares the selected key in its provision.

Define:

```lean
def CommittedProvisionSound
    (state : State catalog Ambient) : Prop :=
  ∀ consumerName consumer committed declared providerFiber,
    state.registry consumerName = some consumer →
    consumer.phase.committed? = some committed →
    state.registry (committed.provider declared) = some providerFiber →
    declared.key ∈
      (catalog.declaration providerFiber.component).provision
```

Prove:

```lean
theorem relied_precedes
    (wf : WellFormed state)
    (sound : CommittedProvisionSound state)
    (relied : Relied state provider) :
    ∃ consumer, PrecedesAt state provider consumer
```

This law is intended to be discharged later by trace/program provenance and the
full table-constancy content of Theorem 63. Do not infer it from a committed
name alone.

## 9. Assign ready programs to reloading occurrences

Represent the state-local configured program for one exact reloading fiber:

```lean
structure ReloadingReadyAt
    (dynamics : Dynamics sig catalog Ambient)
    (state : State catalog Ambient)
    (name : sig.Name)
    (fiber : Fiber catalog)
    (code : sig.IteratorCode) where
  program : Program dynamics
  owner_eq : program.owner = name
  root_aligned :
    program.root = (catalog.declaration fiber.component).entry
  reachable : Reach program code
  ready : LandingOrRaiseAt program code state fiber
```

The headline assumptions must provide this occurrence-specific witness for
every present reloading fiber and its stored code. A program-wide
`LandingOrRaiseTotal` is a convenience constructor for `ready`, not a mandatory
global theorem premise. The theorem may eliminate `owner_eq` before
constructing a raw lifecycle transition. `root_aligned` makes the phrase
“configured component program” honest even though the current local rule uses
only the reachable stored code.

This is deliberately state-local. A later termination theorem needs a stronger
trace/episode assignment proving one program remains fixed throughout the
episode.

## 10. Conditional local progress authority

Bundle only the missing semantic/static laws:

```lean
structure LocalProgressLaws
    (dynamics : Dynamics sig catalog Ambient)
    (state : State catalog Ambient) where
  precedence : FinitePrecedenceRank state
  committed_sound : CommittedProvisionSound state
  reloading_ready :
    ∀ {name fiber code undos committed},
      state.registry name = some fiber →
      fiber.phase = .reloading code undos committed →
      ReloadingReadyAt dynamics state name fiber code
  recovery : RecoveryReadyAt dynamics state
```

The structure contains no `Transition`, no no-deadlock conclusion, and no
termination measure.

## 11. Corrected state-local no-deadlock theorem

Define:

```lean
def LifecycleApplicable
    (dynamics : Dynamics sig catalog Ambient)
    (inertia : InertiaPolicy dynamics)
    (state : State catalog Ambient) : Prop :=
  ∃ after, Nonempty (Transition dynamics inertia state after)
```

Implement:

```lean
theorem lifecycle_progress
    (wf : WellFormed state)
    (laws : LocalProgressLaws dynamics state)
    (notQuiet : ¬Quiescent state) :
    LifecycleApplicable dynamics inertia state
```

Use proof by contradiction or select a nonquiet fiber. The phase matrix is:

| Nonquiet phase                    | Constructed rule             | Extra authority                  |
| --------------------------------- | ---------------------------- | -------------------------------- |
| `.inactive none`, positive target | L-Begin                      | none                             |
| `.active`, target differs         | L-Leave                      | none                             |
| `.reloading`, target agrees       | L-Iter, L-Finish, or L-Raise | occurrence `LandingOrRaiseAt`    |
| `.reloading`, target differs      | L-DivertLand or L-Raise      | occurrence `LandingOrRaiseAt`    |
| `.unloading`, not relied          | L-Unload                     | state-local `RecoveryReadyAt`    |
| `.unloading`, relied              | follow a committed consumer  | rank + `CommittedProvisionSound` |

For the final case, choose a maximal-rank unloading fiber among the finite
covered registry names. If it is relied upon:

1. obtain the installed consumer from `Relied`;
1. prove its target differs because the committed provider is unloading and
   therefore not active;
1. inactive is impossible from installedness;
1. active yields L-Leave;
1. reloading yields an assigned landing or L-Raise;
1. unloading plus `CommittedProvisionSound` yields a strict higher-rank
   consumer, contradicting maximality.

Therefore the maximal unloading fiber is unrelied, and `RecoveryReadyAt` yields
L-Unload.

Do not use the aborting L-Divert alternative. The theorem should cover
non-aborting inertia once every exact reloading occurrence supplies
`LandingOrRaiseAt`.

## 12. Positive and negative evidence

Required public evidence:

- fixed-program registration rejection with raw alternate-oracle distinction;
- target-changed rejection under non-aborting inertia and a positive
  always-abort transition;
- raw Boolean freshness-exhaustion deadlock;
- absence of `FreshSupply Bool`;
- a finite precedence-rank example and its acyclicity theorem;
- an `OracleTotal` example and derived `LandingOrRaiseTotal`;
- a finite state satisfying `LocalProgressLaws` where `lifecycle_progress`
  constructs an actual rule;
- if compact, an unloading/reliance chain example that exercises the
  maximal-rank branch rather than only Begin.

Runtime tests may inspect finite phase/rule tags and the freshness carrier. The
universal theorem and impossibility results remain kernel evidence.

## 13. Quantitative termination boundary

Do not implement or claim:

```text
S(n) <= (K + 4)(V(n) + 1)
```

until the repository has:

- a trace-wide fixed program/component assignment for every fiber;
- `Reach` evidence for every landing occurrence;
- one program/root/oracle reused through each episode;
- a finite universe of all names ever held, closed under registration;
- lifecycle-only trace evidence;
- target snapshots and target-turn counts;
- proof that each target turn is charged to a lower-precedence step or one
  retirement event;
- retirement-write and new-name provenance across recovery;
- a maximal or infinite execution type, or a globally decreasing transition
  measure.

`FiniteProgram` and `BoundedContinuation` are reusable but currently unconnected
to arbitrary lifecycle records. Existing `Trace` values are finite by
construction and cannot state that every maximal execution terminates.

## 13.5. Conditional quantitative certificate

`Cordis.GlobalProgressTermination` implements the narrow arithmetic bridge that
the preceding section says is safe to add without changing the paper claim. It
defines an explicit strict natural-valued potential over exact dependent
lifecycle edges. The generic telescoping theorem proves, for every finite trace,

```text
trace.length + potential(final) <= potential(initial)
```

and `KPlusFourCertificate.trace_length_le_k_plus_four` derives a `K + 4`
trace-length bound from an explicit initial bound. The same potential rules out
nonempty exact cycles. This is a supplied certificate layer, not a derivation
from `lifecycle_progress`; it still does not provide target-turn accounting,
trace-wide assignment, maximal/infinite execution semantics, fairness, support,
or confluence. The executable three-state witness checks the arithmetic without
claiming to model the paper's global name universe.

## 14. Explicit non-claims

This slice does not prove:

- paper Theorem 66 from its printed assumptions;
- that finite names imply fresh-name availability;
- that `FreshSupply` implies provision-compatible oracle admission;
- that raw `Transition` retains one fixed program or oracle;
- that base `Dynamics`, `WellFormed`, or `Reach` imply landing-or-raise
  totality;
- that `RecoveryAdmission` always exists;
- full Theorem 63 provider/provision soundness;
- the paper's `(K + 4)` bound from its printed assumptions (the separate
  `GlobalProgressTermination` certificate requires an explicit potential);
- target-turn finiteness;
- termination of maximal executions;
- scheduler fairness;
- support well-foundedness, Lemma 68, Lemma 70, Lemma 72, or confluence.

The exact positive claim is:

> A nonquiescent well-formed finite state has an applicable lifecycle rule when
> its provider precedence carries an explicit finite increasing rank, committed
> providers are statically sound, every reloading occurrence is assigned a
> fixed reachable program with an exact landing-or-raise witness, and every
> unrelied unloading occurrence admits recovery.

## 15. Verification and integration requirements

Before public integration, run:

```bash
lake --wfail build Cordis.GlobalProgress
lake env lean Cordis/GlobalProgress.lean
uv run scripts/check_lean_hygiene.py Cordis/GlobalProgress.lean
```

The module must remain free of `sorry`, `admit`, custom axioms, `unsafe`,
`partial`, native-decision trust shortcuts, compiler implementation overrides,
and library-level `#eval` commands.

Before claiming the slice complete:

1. import it through `Cordis.lean`;
1. import `Cordis.GlobalProgressTermination` through `Cordis.lean` and the test/audit modules;
1. add representative runtime projections to `Cordis.TestSuite`;
1. add a guarded fixed-program or fresh-admission rejection to
   `Cordis.NegativeTests`;
1. add selected counterexample, authority, and headline theorem declarations to
   `Cordis.AxiomAudit`;
1. change this specification's status to implemented;
1. update `README.md`, `SPEC.md`, `docs/PAPER_MAP.md`,
   `docs/V0_2_SPEC.md`, `docs/TRUST_BOUNDARY.md`, and
   `docs/IMPLEMENTATION_GUIDE.md`;
1. run strict/default builds, runtime suite, demo, hygiene, documentation,
   link, and selected-axiom gates; and
1. repeat every gate from a clean `git archive` before pushing.
