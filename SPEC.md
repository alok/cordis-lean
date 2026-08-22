# CORDIS Lean: delivered finite reference-kernel specification

<!-- markdownlint-disable MD013 -->

Status: delivered `v0.1.0` finite reference kernel for Linear issue ALOK-824

This file is the immutable claim ledger for the reviewed `0.1.0` milestone.
Active `0.2` development is specified separately in
[`docs/V0_2_SPEC.md`](docs/V0_2_SPEC.md): a generic phase-indexed runner,
exact-call policy denial, a non-counter dependent-output configuration, and a
canonical rich session whose model requests and structural protocol are proved
to be log projections are now implemented. Proof-producing validation now
admits or rejects typed rich events after kind-specific payload parsing; byte
parsing, durability, asynchronous scheduling, full paper metatheory, and
whole-Harness refinement remain open, so this historical acceptance matrix is
not silently redefined as a broader completion claim.

The active line also includes a rich interleaved LLM-stream validator, an
arbitrary-finite semantic permutation theorem for certified commuting pure
effects, bounded mechanizations through paper Definition 41, and supported
current-Harness stream and session JSON-AST refinements. Definition 34/Lemma 35
also expose a formal paired-inverse coherence gap instead of assuming it away.
Finite exact Theorem 20/Corollary 21 and the first birth-ranked global
registry/orchestration preservation slice are also implemented. Opaque iterator
codes now have external proof-carrying ordinary/registration semantics and a
fueled recovery runner. The quotient-versus-exact Theorem 42 representative
boundary is mechanized. The seven global lifecycle rule names now have exact
phase-indexed transitions and preservation traces with an explicit unload
recovery admission, and one unified exact-endpoint relation now projects to the
paper's ten rule names from an empty-registry origin. Arbitrary finite
outcome-selected computation trees now satisfy a corrected exact whole-run
interchange theorem. Bounded Lemma 54 foreign/episode facts are proved under a
named unload-confinement law, and a kernel countermodel shows bare recovery
admission is insufficient. Explicit off-source step maps and per-record
commutation certificates now yield parameterized finite interleaved recovery;
countermodels separate that algebra from canonical paper `≈`, off-source
totality, and RecoveryConfinement alone. The complete finite partial/Kleisli
transformation monoids now satisfy a Definition 19/Theorem 42 analogue, with
whole-run equality proved strictly weaker. The complete theorem now also descends
through the finite context relation: related partial representatives agree on
definedness and return related successors, because the existing operation laws
prove every adaptive forward and yielded-inverse generator respectful. Separate
finite rule/effect observation setoids make the paper's two incomparable global
relations explicit and bridge respectful undo interpretation into the temporal
algebra. Bidirectional well-formed orchestration rule invariance is now proved
without equating private tables; a kernel model shows ambient-sensitive inertia
still blocks full lifecycle Lemma 55. The assumption-free lifecycle observation
substrate now transports provider names, targets, committed resolution, reliance,
quiescence, phase patterns, and structural guards; newly active landing tables
remain an explicit Finish obligation. Under explicit noncircular landing,
run-error, inertia, and recovery-admission contracts, all eight lifecycle cases
and the unified ten-rule relation now satisfy a well-formed bidirectional
`RuleRelated` certificate; a kernel model proves the Finish table clause
necessary. This conditional result is not base-Dynamics Lemma 55. Vestigial removal is proved
effect-equivalent, and corrected bidirectional orchestration simulations make
four exact exceptions explicit. Well-formed countermodels show the pinned Lemma
57 raw clauses omit forward parent adoption and backward parent removal; the
latter is a third backward exception. Finite located episodes prove
dependency provision, explicit nested opening/closing order, persistent provider
resolution/no-unload, conditional table-value constancy, and a local reloading
target/divert/raise classification. Full Lemmas 55–57, maximal episodes and the
full T63/T64 recovery conclusions remain open, as do the paper's literal
total/quotient setting, task concurrency, and complete
preservation/progress/confluence results.

The pure scheduler boundary now also includes `Cordis.ParallelSchedule`:
arbitrary finite sequences of certified parallel windows and exclusive barriers
compose with exact endpoint/recovery equality, model-order reports, and global
task-ID uniqueness. This remains a reference-kernel schedule; wall-clock
overlap, worker IO, promise races, fairness, and deployed scheduler equivalence
remain outside the claim.

`Cordis.AsyncHarness` now adds a bounded fiber-state slice on top of that pure
schedule boundary. Indexed fibers carry pending/running/terminal phases, typed
start/complete/fail/cancel transitions, and finite traces whose completion order
is explicit. A drained successful-schedule certificate proves that any supplied
completion permutation reaches the canonical pure endpoint. The slice is still
an executable proof-carrying model, not live `IO`: task handles, wall-clock
fairness, cancellation delivery, cleanup, and deployed Harness refinement remain
outside the claim.

`Cordis.DeepSeekAsyncHarness` crosses one narrow part of that boundary with the
existing process adapter: two complete-body text-prefix jobs run in cooperative
`ContextAsync` children, and `ContextAsync.race` retains the first typed result
while requesting cancellation of the loser. A deterministic two-process fixture
exercises the race, and pure theorems map a winning response or typed error to a
terminal phase. The underlying line-oriented read is synchronous, so this does
not prove blocked-read interruption, wall-clock fairness, arbitrary cleanup, or
deployed Harness equivalence.
`Cordis.DeepSeekAsyncStreamHarness` lifts the same race over the complete-body streamed Harness
continuation. Each child can execute a tool-call round and a later text terminal under explicit
fuel, preserving the typed runner, final model, and round witnesses in the winning result. Its
fixture exercises two real processes; synchronous line reads, fairness, cleanup, and deployed
asynchronous equivalence remain external.
`Cordis.DeepSeekAsyncStreamCancellation` carries the typed pre-round cancellation policy into the
same race. The fixture cancels one child before round zero while the other remains a real streamed
continuation; the cancellation result preserves the unchanged runner/model endpoint, typed reason,
and empty completed-round prefix. It does not claim blocked-read interruption, fairness, cleanup,
or deployed cancellation equivalence.
`Cordis.DeepSeekAsyncStreamRetryCancellation` composes that cooperative race with retry-aware
streamed jobs. The dependent winner retains its indexed retry trace and final endpoint; a
cancellation-first child retains the pre-round decision and empty accepted prefix, while a
delayed-child fixture exercises the success-first branch with two accepted rounds. Blocked-read
interruption, fairness, cleanup, reconnect, and deployed retry/cancellation equivalence remain
external.

Name equivariance now has an executable structural core: lawful bijections act through all stored
payloads, dependent tables/views/undo stacks/phases, the finite registry, and global state; state
inversion, strengthened well-formedness, and all orchestration rules are equivariant. A kernel
countermodel refutes the old opaque action record. Full dynamics and lifecycle Lemma 56 still
requires explicit semantics. Under exact dynamics action, inertia action, and fixed catalog entry
codes, those semantics now derive registration/oracle/execute-one/Landing/recovery actions and
bidirectional equivariance for all lifecycle and unified rules over well-formed states. This is a
conditional fixed-catalog Lemma 56 analogue, not a base-Dynamics theorem.

The active line now also includes an oracle-specific finite partial/Kleisli analogue of paper
Definition 60. Reachable iterator codes are generated from successful continuation yields; their closures
contain the reachable partial forwards and actually yielded totalized inverses; and exact plus
`EffectEquiv`-observational independence retains inverse, continuation, and registration-component
stability. The observational descent additionally receives `ProgramRespects` for both programs'
reachable forward maps; only yielded inverse respect follows from `EffectEquiv.applyUndo_respects`.
Occurrence-indexed families and separate caller-supplied finite-reach/continuation-bound certificate
types expose the paper's finite assumptions rather than inferring them. A
provenance-and-membership theorem discharges `GlobalTemporal.PerStepCommutes` only after receiving
each foreign step's `TotalStepMap`; it does not derive totalization, owner inverse stability, trace
reordering, Theorem 61, or Corollary 62.

Given `Independent`, the bounded transposition layer derives an exact raw execution diamond and
exact commutation for two already totalized generated step maps. Given `ObservationalIndependent`,
the same packaged maps commute under its supplied `EffectEquiv`; that certificate retains separate
`ProgramRespects` obligations. The layer also requires syntactic `UndoCode` equality for
lifecycle-visible yields, proves distinct-name phase edits commute, and exposes a noncircular
foreign-phase compatibility contract without constructing an inhabitant. A finite noninjective
interpreter proves semantic inverse equality cannot recover stored code equality. These are
ingredients toward Lemma 71, not a lifecycle-step transposition or mixed-trace reorder theorem.

The foreign-phase layer now derives that compatibility contract from explicit read-equivalence,
ordinary exact-successor, and same-child registration-oracle frame laws. It uses the existing raw
diamond plus both compatibility certificates to prove exact equality after arbitrary supplied
distinct-name phase updates, retaining the actual post-raw fiber lookups. Full independence,
readability, and raw registration stability are each kernel-separated from the stronger premises
they do not imply. The result remains about framed raw executions; it does not construct lifecycle
rules or their guards and targets.

The landing transposition layer now reaches actual lifecycle syntax for exactly the four
L-Iter/L-Finish combinations. It adds exact cross-forward syntactic-yield stability beyond semantic
independence, fixes each landing to the program oracle, derives positive target preservation from
source well-formedness, and constructs both common-source orders with one exact final state.
Countermodels separately justify the extra yield, common-applicability, and oracle-provenance
premises.

The activation transposition layer wraps those landings together with program-root-aligned
L-Begin. It proves exact foreign lookup and positive-target framing, fixed-program endpoint and rule
determinism, and one exact diamond for all nine common-source Begin/Iter/Finish combinations. The
law surface is branch-minimal: Begin/Begin needs no iterator law, mixed pairs need only the landing
program's foreign-phase compatibility, and landing pairs retain exact
`ForwardLifecycleIndependent`. A paper-shaped wrapper accepts an actual normal-order second
activation and derives the swapped actual lifecycle transition at the same endpoint. This is a
partial, fixed-oracle, exact-representative Lemma 71(1) analogue; that activation-only module does
not itself rewrite a stored trace, assign episode programs, or prove the paper's literal
total/quotient theorem.

The activation/orchestration audit shows that the literal clause (2) premise is false. A
registration can create a distinct parent required by a later O-Insert without registering that
step's actor, and exact insertion orders swap the proof-only birth ranks. The corrected theorem
therefore excludes registering activation/O-Insert, requires child/actor inequality for
Retire/Remove, and asks an iterator-backed activation for one occurrence-specific exact execution
frame. It reconstructs the early legal orchestration step with the same kind, actor, and replay,
preserves the activation's positive target structurally, rebuilds the moved fixed-program
activation, and proves the exact normal final endpoint. This is a corrected bounded analogue, not
literal Lemma 71(2), a birth-erasing quotient, or arbitrary trace rewriting.

The exact trace-rewrite layer closes the local-to-intrinsic-trace bridge for those corrected
branches. `AdjacentOccurrence` retains an exact dependent before/window/after decomposition;
`ProgramOccurrence` identifies actual stored lifecycle steps with fixed root-aligned program and
oracle evidence; and both semantic adapters return assignments for their moved pair. Rewriting
therefore preserves the complete trace's exact outer indices, alignment, length invariants, and
final well-formedness while proving that rules and actors undergo one adjacent permutation. Exact
membership theorems locate the original selected records; they do not identify those dependent
records with the moved replacements. A
nonempty-prefix example rewrites `[O-Insert, L-Begin, O-Insert]` to
`[O-Insert, O-Insert, L-Begin]`. This does not derive branch laws for arbitrary records. A merely
birth-erased local endpoint still cannot attach to the retained exact suffix without a separate
bisimulation, so registering activation/O-Insert, automatic/canonical normalization, deletion, Lemma 72, and
confluence remain open.

The bounded deletion layer now gives trace filtering an intrinsic semantics. `DeletionReplay`
consumes source constructors in order, either replaying one actual dependent step with an explicit
assignment transport or dropping that exact occurrence while the shadow state stays fixed. It
derives the shadow rule/actor sublists, final relation, alignment, length bounds, and complete
`TraceProgramAssignment`. A separate theorem removes a finite list of entries already proved
vestigial and replays any safe foreign orchestration suffix exactly, retaining the full edit
template position by position. The executable example records `[drop, keep]` while filtering
`[O-Remove(1), O-Retire(0)]` to `[O-Retire(0)]`.

This is not the paper's closing-episode deletion theorem. A full intrinsic counterexample shows a
retained O-Insert can lose its parent; other kernel witnesses expose unrecovered `nextBirth`,
changed surviving birth ranks, and redraw of a removed bare name. The module supplies semantic
no-redraw and vestigial-or-absent vocabulary, but no lifecycle/oracle/recovery suffix simulation or
birth-erased outside relation. Lemma 72, Theorem 73, canonical form, confluence, and both
automatic/canonical normalization and maximal-lifecycle termination remain open. The separate
`GlobalPaperTraceNormalization` module composes a finite connected list of supplied
`RelatedAdjacentRewrite` certificates, retaining assignments and proving terminal relation plus
rule/actor permutations; it does not supply a rewrite strategy, canonical form, or confluence.

`GlobalPaperTraceNormalizer` is the terminating conditional layer above that certificate
composition. Its `Authority` explicitly supplies normal-form decidability, a source-indexed
rewrite witness, and a strictly decreasing natural measure. `normalize_some` therefore produces
a finite dependent rewrite chain, and the `Result` theorems preserve the endpoint relation and
rule/actor permutations. This is not an inferred rewrite strategy or a proof of canonical form,
global termination from CORDIS dynamics, Lemma 72, or confluence.

`GlobalPaperTraceConfluence` supplies the reusable conditional confluence kernel above this
surface. For any decreasing rewrite system with local joinability, its constructive Newman-style
theorem produces a global join, and any two irreducible normal-form endpoints are equal.
`AuthorityLinked` reconstructs the authority-selected path from `normalizeFuel`, while
`ConfluentAuthority` and `normalize_results_unique` apply the result to actual `TracePackage`
normalizer endpoints. The Boolean two-branch witness exercises the theorem, but CORDIS still does
not derive the required local joins, measure, or normal-form strategy; consequently this does not
close Theorem 73.

`GlobalPaperTraceScopedConfluence` adds the indexed version needed when a caller has a finite
reachable package family. Package identity, selected-link source/target equations, decreasing
fuel, and normal-form decisions are all fields of the type; its activation/orchestration fixture
therefore proves a nonempty real-link normalization result and endpoint uniqueness without
eliminating a reachability proposition into data. This is still conditional finite metatheory,
not a CORDIS-derived strategy or Theorem 73.

The paper-relation layer then erases the allocator artifacts that the reference refinement added
but the paper does not observe. Its full-domain relation compares active values plus exact
component/parent/retirement/phase control while omitting `nextBirth` and per-fiber birth; the
outside-deleted variant ignores selected slots, and `DeletionRelated` conjoins it with global
effect observation. All three are Setoids, and current stricter `RuleRelated` implies the new full
relation.

This is not definition-only infrastructure. Between independently well-formed full-domain related
states, O-Insert, O-Retire, and O-Remove have real peer steps in both directions, with related
successors and assignment-preserving `RetainedStep`s. From a well-formed source carrying a finite
`VestigialNames` certificate, erasure satisfies the combined deletion relation and safe foreign
orchestration traces replay directionally through an intrinsic all-keep `DeletionReplay`. The
opposite-allocation endpoints are related despite exact
state and current-rule-relation inequality. A clock-sensitive target-changed model has an actual
L-DivertAbort but no same-lifecycle-rule peer, refuting any unconditional assigned lifecycle
simulation. General lifecycle replay, relation-aware activation swaps, Lemma 72,
automatic/canonical normalization, and confluence remain open.

The progress layer proves that printed Theorem 66 also needs stronger executable premises. A
configured oracle may reject a registration that the raw relation can admit through another
oracle, while finite Boolean name exhaustion produces a well-formed nonquiescent state with no raw
lifecycle transition at all. The corrected theorem assumes a finite increasing provider-precedence
rank, statically sound committed providers, exact landing-or-raise readiness for every current
reloading occurrence, and recovery readiness for every current unrelied unloading occurrence. It
then proves state-local no-deadlock by choosing a maximal-rank unloading provider when necessary.
The quantitative step bound, target-turn finiteness, maximal-execution termination, and fairness
remain open trace/provenance work.

`Cordis.GlobalProgressRun` is the finite executable bridge for this conditional result. It accepts
an explicit `ProgressAuthority` and strict `StepPotential`, recursively chooses the certified
lifecycle edge, preserves `WellFormed` endpoints, and returns an intrinsic trace with either a
quiescent stop or a full-fuel certificate. Funding the run with its initial potential proves the
endpoint is quiescent. These authorities are supplied rather than derived, so this remains a
finite conditional runner and not the paper's unrestricted quantitative or maximal-termination
Theorem 66.

`Cordis.GlobalProgressAssignment` supplies the missing provenance layer without pretending to
derive it. Its `AssignedProgressAuthority` gives a `StepProgramAssignment` for each lifecycle
transition, and `assignTrace` recursively builds a dependent `TraceProgramAssignment` for every
finite runner trace. Endpoint well-formedness, stop certificates, and the initial-potential
quiescence theorem are preserved. The fixed program, root, oracle, and reachability evidence are
explicit authority fields; raw transitions do not imply them, so full Definition 60/66 provenance
and maximal-execution claims remain open.

`Cordis.GlobalPaperProgressReplay` composes that assigned finite runner with a caller-supplied
`ForwardAssignedStepSimulation`. `replayRun` replays the runner's exact intrinsic trace from a
birth-erased-related well-formed peer, retaining the source endpoint, length, stop certificate,
transported assignment, and exact rule/actor projections while proving the peer endpoint
well-formed and related. The simulator and lifecycle provenance remain explicit inputs; this is
not a derived lifecycle bisimulation, maximal execution, or unrestricted Theorem 66 bridge.

The support layer exposes another printed-proof gap. A reachable, well-formed two-insert registry
can have well-founded provider precedence and an acyclic parent relation while their union cycles,
making Definition 67 support nonunique. The corrected API therefore requires a well-founded
combined `SupportOrder`, defines support by edge-indexed recursion, and proves uniqueness. At a
well-formed quiescent nonfailed state, state-local provision totality and explicit active-parent
closure make active names a support solution; uniqueness yields `support_eq_active`. Separate
countermodels prove both new authorities necessary. Current `FromEmpty` does not derive non-root
registration provenance, matching retirement execution, or the combined order.

Repository: `cordis-lean`

Lean toolchain: `leanprover/lean4:v4.33.0`

## 1. Delivered result and claim boundary

CORDIS Lean is an executable, credential-free Lean kernel for finite
proof-carrying agent-harness executions. The delivered implementation combines:

- request-indexed APIs and tool contracts;
- committed capability views and reversible dependent-registry updates;
- exact and observational recovery for modeled state;
- a certified pure two-call reordering theorem;
- proof-carrying `Lean.Json` AST codecs for inputs and dependent results;
- indexed session, policy, stream, and lifecycle transitions;
- raw event validation that reconstructs intrinsic typed traces;
- a deterministic counter harness supporting finite steps and turns;
- exact-subject policy evidence, request-indexed encoded results, replay proofs,
  and one joint call-history certificate tying model state, leases, IDs,
  records, and log boundaries together; and
- executable adversarial tests plus an explicit headline-theorem axiom audit.

The central design claim remains:

> An API is a dependent type signature, not a stringly registry plus a runtime
> convention.

An operation selects its request type, and the request selects its response
type. A component view requires evidence that an operation was declared. A
typed transition determines its legal successor. A modeled reversible effect
returns a captured inverse and proof that applying it to the produced state
recovers the indexed predecessor.

The scope is intentionally finite and local. `v0.1.0` is not a line-by-line
formalization of the CORDIS paper, a full CORDIS implementation port, an
asynchronous or distributed scheduler, or a semantic-equivalence proof for the
DeepSeek TypeScript Harness. Names and event shapes inherited from those
sources do not imply complete behavioral compatibility.

## 2. Primary sources and pinned snapshots

The interpretation is pinned because all upstream projects are active:

| Source                                                              | Snapshot used                                                                                                                                 | Role in this project                                                                                      |
| ------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------- |
| [CORDIS paper](https://github.com/cordiverse/paper)                 | [`948a07b369c62adb3b12e102458be5c18dfb69b9`](https://github.com/cordiverse/paper/commit/948a07b369c62adb3b12e102458be5c18dfb69b9)             | Effect/coeffect interpretation, component lifecycle, recovery, and ordering obligations.                  |
| [CORDIS implementation](https://github.com/cordiverse/cordis)       | [`8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4`](https://github.com/cordiverse/cordis/commit/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4)            | Concrete context, fiber, registry, lifecycle, isolation, and interception reference.                      |
| [DeepSeek Harness](https://github.com/deepseek-ai/deepseek-harness) | [`47f943859bef60e4160492346772ded9b24f765a`](https://github.com/deepseek-ai/deepseek-harness/commit/47f943859bef60e4160492346772ded9b24f765a) | Turn/step/tool-call/result vocabulary, ordered result behavior, cancellation concepts, and adapter seams. |

The Harness vendor manifest more specifically pins its production CORDIS
dependency to CORDIS `v4.0.0-rc.7` and loader `v1.0.0-rc.5` at
[`56b3d4f725681cf4556c1a8695a709cc3b6eed74`](https://github.com/cordiverse/cordis/commit/56b3d4f725681cf4556c1a8695a709cc3b6eed74),
plus DeepSeek CORDIS plugins at
`abb0a307cb1d3b0947f455d590cf5ba922d4caa4`. The newer standalone CORDIS
snapshot is interpretive context only. Compatibility between these snapshots
is never inferred.

The paper snapshot is the 88-page draft titled _A Programming Paradigm for
Spatiotemporal Composability_, dated 2026-08-13. The implementation here
selects a finite subset of its ideas and marks the rest as future work.

## 3. Delivered semantics

### 3.1 Modeled reversible effects and finite reordering

`Cordis.Effect` represents a modeled reversible step as:

```lean
structure Applied (State : Type u) (before : State) where
  after : State
  undo : State -> State
  undo_after : undo after = before

def Effect (State : Type u) := (before : State) -> Applied State before
```

Sequential composition executes forward functions left to right and captured
inverses right to left. The implementation proves identity laws,
associativity, sequential recovery, accumulator recovery, and indexed
`UndoStack` recovery. The observational variant replaces equality with a
`Setoid` relation and requires each inverse to respect that relation.

`Cordis.EffectContext` now formalizes the paper's function-level effect-context tower through
Definitions 1–3, 6, and 8–12. Its proof-carrying `WitnessedEffect` returns the inverse selected
at the application state; `track`/`recover` prove the projection, twisted-composition, and
soundness laws; `effectComp` proves the state-indexed monoid laws; and `effectLift` proves the
next-level projection, exact lifted-inverse calculation, recovery preservation, and the precise
uniform-inverse criterion. The indexed `Theorems.Run` type proves finite reverse-order context
recovery and recovery-target preservation. This is a finite exact tower slice, not the paper's
later arbitrary interleaving or total/quotient independence theorem.

`Cordis.Batch` delivers the finite ordering result as a batch of exactly two
heterogeneous pure calls. Its certificate is stronger than forward
commutation:

1. both orders reach the same modeled successor;
1. both orders expose extensionally equal composed recovery functions; and
1. each call's result is stable when the other effect is evaluated first.

Given that evidence, model and swapped evaluation produce the same
proof-carrying `BatchOutcome`, retain results in declared model order, and
recover the same predecessor. This is a semantic reordering theorem, not task
creation, wall-clock overlap, `IO`, or async scheduling. The deterministic
counter harness still dispatches calls sequentially in model order.

### 3.2 Dependent APIs, registries, and lifecycle

The API universe is a dependent family:

```lean
structure Signature where
  Op : Type u
  Request : Op -> Type v
  Response : (op : Op) -> Request op -> Type w
```

`SomeCall` stores a decoded operation and matching request.
`AuthorizedCall` additionally carries membership in a `Needs` predicate, and
`Reply call` stores only the response type selected by that exact call.
`View.execute` preserves the dependency between call and reply.

A `View` is a committed resolution witness: resolving an operation requires a
proof that it is declared, returns a nominally identified provider, and proves
that provider is present in the indexed registry. `Cordis.Registry` supplies
typed set/install/withdraw operations, exact local inverses, recovery theorems,
and strong commutation of distinct-key updates.

`Cordis.Lifecycle` implements a finite synchronous state machine:

```text
inactive -> reloading -> active -> unloading -> inactive
```

Reload iterations extend an indexed undo stack while retaining one committed
view. Diversion can move partial activation to unloading. Unload requires a
`Withdrawable` guard and proves both exact modeled recovery and impossibility
when an installed consumer still relies on the provider. The lifecycle is a
generic finite model; it is not wired to hot-module acquisition, asynchronous
fiber draining, or a production plugin loader.

### 3.3 Tool contracts and the JSON AST boundary

`ToolSpec` makes `Input`, request-dependent `Output` and `Failure`,
preconditions, postconditions, capability requirements, and an emission class
part of the tool contract. A `ToolSpec.Invocation` carries the accepted
precondition and authority proofs. Only a `VerifiedTool` can construct a
`CertifiedOutcome` containing the result, successor state, and exact
postcondition proof.

Every wire value uses a proof-carrying codec:

```lean
structure Codec (alpha : Type u) where
  schema : Lean.Json
  encode : alpha -> Lean.Json
  decode : Lean.Json -> Except DecodeError alpha
  roundtrip : forall value, decode (encode value) = .ok value
```

The delivered primitive/composite codecs cover unit, Boolean, string, natural
number, product, and list values, with structured paths for nested decode
errors.

`ToolWire` provides operation-specific input codecs and request-dependent
output and failure codecs. The result codec uses these tagged representations:

```text
[false, encoded failure]
[true, encoded output]
```

It proves round-trip recovery for the exact
`Except (Failure input) (Output input)` and can encode the actual result inside
a `CertifiedOutcome`. `ToolWire.validate` fails closed on unknown names,
undeclared tools, malformed AST shapes, rejected contracts, and missing
capabilities before it constructs an `AuthorizedCall`.

All codec theorems begin with an already constructed `Lean.Json` AST. Byte
parsing, text encodings, rendering, transport, storage, and the behavior of an
external schema consumer are outside the theorem boundary.

The delivered counter catalog contains:

- `counter_read`, a pure read requiring the read capability; and
- `counter_increment`, an internally reversible increment requiring the write
  capability and a proof that the request limit is not crossed.

The counter wire supplies `Nat` output codecs and `String` failure codecs for
both operations.

### 3.4 Indexed session protocol and typed raw-trace reconstruction

The session state distinguishes:

```text
ready(nextTurn)
turn(turn, nextStep)
step(turn, step, pendingCallIds)
```

Typed `Event` constructors enforce exact turn/step numbers, fresh call IDs,
pending membership for results, an empty pending set at step close, and an open
turn at turn close. Typed traces compose only when adjacent state indices
match.

The runtime mirror validates `RuntimeEvent` values and reports structured
errors for wrong phase, turn/step mismatches, duplicate calls, orphan results,
and pending calls at step close. The dynamic boundary does more than compute a
runtime state:

- `validateEvent` reconstructs an intrinsic `Event` whose erasure is the exact
  raw event;
- `validateTrace` reconstructs an intrinsic typed `Trace` whose erasure is the
  exact raw list;
- `validateRuntimeTrace` starts from the index represented by a runtime state;
  and
- `ValidatedEvent.applies` and `ValidatedTrace.replays` prove that the
  reconstructed witness executes to its indexed endpoint.

Thus typed-trace erasure and raw-to-typed reconstruction are both delivered for
finite in-memory event lists.

`Cordis.Stream` separately models a bounded assistant text stream. Each typed
text chunk consumes one budget unit and appends exactly its fragment; only an
open state can finish. Consequently text after finish and double finish are
unrepresentable. Its raw validator returns `budgetExhausted` or
`alreadyFinished`, and its erasure/replay theorems reconstruct exact
left-to-right concatenation and the terminal result. Tool-call payload parsing,
network streaming, byte decoding, backpressure, and cancellation are outside
this subsystem.

### 3.5 Exact-subject policy and the deterministic harness

`LeasePool` maintains a duplicate-free list of available call IDs. Issuing a
live ID fails, successful consumption removes that ID, and a consumed lease
cannot be consumed again without reissue.

`SubjectPolicyState` retains the exact dependent subject through:

```text
proposed -> decided -> dispatched -> settled
```

Dispatch exists only from `allow` and consumes the lease associated with the
same call ID. A non-allow decision can settle only as a rejection. A completion
has type `Completed subject`, so the terminal value remains indexed by the
exact proposed subject. For one explicitly threaded `SubjectPolicyTrace`, the
phase strictly advances, dispatch occurs at most once, a completed trace
dispatches exactly once, and a denied trace dispatches zero times.

The counter `Harness` integrates that stronger policy type rather than merely
testing it in isolation. Each admitted `CallEvidence` retains:

- the exact `AuthorizedCall` returned by raw validation;
- the equality witnessing that validation result;
- lease issue and consumption evidence;
- the provider completion type indexed by that exact call;
- the equality witnessing provider execution; and
- an exact-subject policy trace ending in that completion.

Rejected admission retains the structured admission error and proof that raw
validation returned it. Rejections preserve the model and emit a matching tool
result event so the session protocol cannot be left with an orphaned pending
call. Successful provider completions retain the request-indexed tagged JSON
result; admission rejection and provider-level execution failure do not
fabricate an encoded provider result.

`RunnerState` contains both its current runtime protocol state and a proof that
replaying the complete append-only in-memory log from `ready 0` yields that
state. Its history field has the stronger joint type:

```lean
RecordChain initialModel nextCall records model leases (callBoundaries log)
```

It supports:

- one or more steps inside a turn;
- one or more turns inside a session;
- session-wide monotonically allocated call IDs; and
- sequential model-order dispatch and record commitment.

`RecordChain initial nextCall records final leases boundaries` is initialized
as `RecordChain initial 0 [] initial .empty []`. Its append constructor requires
each record's `before` model to equal the preceding model endpoint and each
record's `leasesBefore` to equal the preceding lease endpoint. The successor
indices are that record's `after` model and `leasesAfter` pool. The same
constructor requires `record.id.value = nextCall` and appends exactly
`[call record.id, result record.id]` to the boundary index.

Consequently:

- the record count equals `nextCall`;
- record IDs equal `List.range nextCall`;
- `LeasesThreaded .empty records leases` holds; and
- for every `RunnerState`,
  `callBoundaries log = recordBoundaries records`.

The public generic `RunnerState.emit` operation has been removed. The remaining
non-boundary emitter is private and requires
`RuntimeEvent.callBoundary? event = none`. Tool-call and tool-result events are
created only inside the private settlement transition. That transition first
validates both events, then returns one immutable `RunnerState` containing the
adjacent call/result pair, corresponding record, successor model, successor
lease pool, extended joint history, and replay proof. Failure returns an error
without exposing an intermediate runner state with only the call boundary.

This is atomicity of one pure `Except RunnerError RunnerState` transition. It
does not establish a filesystem or database transaction, crash-safe
persistence, multi-process exclusion, or external exactly-once execution.

The static `certifiedTwoCallTrace` exercises the intrinsic protocol API; its
erasure replay theorem reaches the exact terminal state. Separately,
`runMultiTurn` and the tests exercise raw multi-step/multi-turn logs and
reconstruct them as typed traces.

The credential-free demo starts at counter `2`, executes read, increment by `3`
under limit `10`, read, and an unknown call, then ends at counter `5` and
`ready 1`. It stores four ordered records and 12 replay-certified protocol
events. The first three records contain one policy dispatch and an encoded
result; the unknown call contains no dispatch and no encoded result. The demo
and multi-turn tests also check the exact boundary/record equality and consume
the empty-to-final lease-threading certificate.

## 4. Delivered module map

`Cordis.DeepSeekHarnessEventProcessOutcome` composes certificate-gated current-Harness event
text/byte restoration with complete-body rich outcomes and a fuel-bounded streamed conversation.
Prepared requests, process/round/tool endpoints, raw archive, restored-session equality, protocol
projection, and completion/exhaustion stops remain dependent evidence; caller source, provider
authenticity, blocked-read cancellation, persistence, and deployed equivalence remain external.

`Cordis.LoaderHMR` now supplies a bounded pure loader/HMR model: Definition 74 entry fields,
stable-ID keyed reconciliation, Algorithm 8 fixed-point accepted/declined classification with
unresolved-cycle fallback, Algorithm 9 stale dependency walks with declined boundaries, and
Algorithm 10 invalidate/import/dispose/install/commit with exact failure rollback. It does not
claim dynamic-import execution, filesystem watching, real fiber disposal, OS cache mutation, or
deployed plugin-loader equivalence.

| Module                                                     | Delivered responsibility                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| ---------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Cordis.Api`                                               | Dependent API signatures, provider identity, registries, needs, committed bindings/views, authorized calls, and call-indexed replies.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.Effect`                                            | Exact and observational effects, LIFO composition, identities, associativity, accumulators, and indexed undo stacks.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.EffectContext`                                     | Paper effect-context Definitions 1–3, 6, 8–12 and Theorems 4–5, 7, 10–16: tracking, recovery, composition, lifting, and finite indexed reverse-order recovery.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.Codec`                                             | `Lean.Json` AST codecs, schemas, nested decode errors, and round-trip proofs.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.Tool`                                              | Request-indexed tool contracts, invocations, certified outcomes, verified implementations, catalogs, emission classes, and decisions.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.ToolWire`                                          | Raw-call resolution/admission, dynamic input validation, request-dependent result codecs, and certified-result encoding.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.Registry`                                          | Dependent set/install/withdraw operations, witnessed recovery, distinct-key commutation, and satisfaction witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.Protocol`                                          | Indexed session events/traces, runtime validation, raw-to-typed reconstruction, replay, and well-formedness theorems.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.Policy`                                            | Duplicate-free lease pools, ID-only compatibility policy, exact-subject policy transitions/traces, and dispatch-count theorems.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.Batch`                                             | Strong independence certificates and order equivalence for exactly two heterogeneous pure calls.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.Stream`                                            | Bounded typed assistant text chunks, raw validation, deterministic assembly, and terminal reconstruction.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.Lifecycle`                                         | Finite synchronous component phases, committed views, undo stacks, diversion, and withdrawal guards.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.Examples.Counter`                                  | Verified counter read/increment contracts, implementations, registry, view, and postcondition theorem.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.Examples.CounterWire`                              | Counter JSON codecs, name resolution, admission proofs, capability decisions, and raw sample calls.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.Harness`                                           | Deterministic counter runner, exact-subject `CallEvidence`, encoded results, replay-certified finite turns/steps, private atomic settlement, and joint model/lease/ID/log-boundary `RecordChain`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.ParallelHarness`                                   | Bounded proof-carrying parallel windows, model-order commits, one exclusive barrier, and pure cancellation drains.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.ParallelSchedule`                                  | Arbitrary finite sequences of certified windows and exclusive barriers, with exact composed endpoint/recovery equality, model-order reports, and global task-ID uniqueness; this is a pure schedule certificate, not wall-clock concurrency.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.AsyncHarness`                                      | Indexed pending/running/terminal fibers, typed start/complete/fail/cancel transitions, completion-order traces, drained successful-schedule certificates, and concrete race/cancellation witnesses; pure bounded state-machine semantics only.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekAsyncHarness`                              | Cooperative `ContextAsync.race` over two process-backed complete-body text-prefix jobs, retaining the first typed result and a terminal-phase bridge; the fixture is executable, while blocked-read interruption, fairness, cleanup, and deployed async equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekHarnessEventProcessTimeout`                | Per-read timer race over the current-event process cursor: a real `Std.Async.Sleep` can kill a blocked child read, while the dependent result retains the accepted cursor prefix, line ledger, exit code, stderr, and timeout index; completion and timeout fixtures cover both branches. Local configured-child evidence only; arbitrary descendant cleanup, fairness, backpressure, authenticity, durability, and deployed asynchronous equivalence remain external.                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekHarnessEventProcessTimeoutRefinement`      | Proof-level attachment from the timed cursor to `SessionRefinement.ValidatedSequence`: existing per-entry refinement proofs are transported from the cursor's snoc trace to the validator's cons trace, retaining entries, final state, and exact protocol projection without reparsing. The wrapper is noncomputable proof packaging; the executable timeout runner remains the preceding module. No raw `decodeEvents` equivalence, byte framing, authenticity, persistence, or deployed refinement is claimed.                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekAsyncStreamHarness`                        | Cooperative race over two process-backed complete-body streamed Harness continuations; the winner retains typed tool executions, two round witnesses, final model, and runner endpoint. Synchronous reads, fairness, cleanup, and deployed async equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.DeepSeekAsyncStreamCancellation`                   | Policy-bearing cooperative race over streamed children; a real fixture cancels one child before dispatch and retains its typed pre-round stop, unchanged runner/model endpoint, and empty completed-round prefix. Blocked-read interruption, fairness, cleanup, and deployed cancellation equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekAsyncStreamRetryCancellation`              | Cooperative race over retry-aware streamed children; the winner retains its dependent indexed retry trace/final endpoint, while cancellation-first zero-round and delayed-child success-first two-round fixtures cover both terminal branches. Blocked-read interruption, fairness, cleanup, reconnect, and deployed retry/cancellation equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.GenericSessionHarness`                             | Reusable rich-session/request wrapper over any `GenericHarness.Config`, with exact Session-to-structural-log projection and generic call/lifecycle append transitions.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.Examples.DependentChoiceSession`                   | Non-counter dependent-choice fixture carrying one successful `Nat` branch and one policy-rejected `String` branch through the generic rich-session wrapper, with executable request/projection certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.TestSuite`                                         | Executable effect, batch, codec, stream, registry, lifecycle, protocol, policy, admission, encoded-result, replay, joint-history, and harness checks.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.NegativeTests`                                     | Guarded expected compiler errors for dependent reply mismatch, forbidden transitions, and forged joint-history indices.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.AxiomAudit`                                        | Explicit `#print axioms` checks for headline theorems.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.Version`                                           | Delivered version string.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekApi`                                       | Typed OpenAI-compatible DeepSeek request/response boundary with dependent JSON certificates, an explicit `ChatRequest.stream` flag (`buildRequest` defaults false and `buildStreamingRequest` proves true), and explicit transport/status/API errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekApiErrorEnvelope`                          | Typed validation of non-success OpenAI-compatible `{error: ...}` response bodies, retaining exact parsed JSON, `ApiErrorBody`, and the decode equation; retry and authenticity remain caller/runtime obligations.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekRequestMode`                               | Type-indexed complete/streaming request plans whose `stream` flag is tied to the mode by an equality certificate; the terminal execution wrapper accepts only a complete plan.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekCurlTransport`                             | Process-backed `Transport` adapter that passes request bodies on stdin, URL/headers as direct executable arguments, and parses a typed status trailer; includes a deterministic `sh` fixture.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.DeepSeekStream`                                    | Strict in-memory DeepSeek SSE framing and typed delta decoding with retained raw-frame certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekStreamFailure`                             | Source-honest complete-body terminal-failure certificate for `content_filter` and `insufficient_system_resource`: retains the leading frames, terminal raw frame, singleton choice/reason, and optional usage without fabricating a normal rich/session finish.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekTerminalOutcome`                           | Complete-body sum that classifies provider terminal failures or one of the successful text, one-tool, mixed, and finite multi-call rich languages, retaining the chosen dependent certificate and typed rejection.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekStreamIncremental`                         | Pure proof-carrying SSE prefix state: complete lines are accepted one at a time with exact accumulated-body/frame certificates, terminal `[DONE]` is demanded by `finish`, and a finite line policy can stop before the next line. Live IO/backpressure/cancellation remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekStreamByteFraming`                         | Pure arbitrary-byte SSE ingress: LF-delimited chunks retain an exact canonical reconstruction, complete lines decode as UTF-8 before entering the typed prefix state, incomplete final lines and invalid UTF-8 are typed errors, and `finish` bridges to strict SSE validation. Process-level reads, backpressure, blocked-read interruption, cancellation, reconnect, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekCurlByteFraming`                           | Process-backed byte-chunk ingress: bounded stdout reads retain raw chunks and the private status/body parse equation, then feed the observed body chunks unchanged through `DeepSeekStreamByteFraming` with typed status, UTF-8, framing, process, and read-limit errors. Network, credentials, executable trust, blocked-read interruption, backpressure, cancellation, reconnect, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekStreamHarnessByte`                         | Byte-backed complete-body streamed Harness continuation: bounded stdout chunks retain the dependent byte/framing/status witness while the decoded body enters the existing rich/tool/session runner; the one-round and fuel-bounded loop fixtures exercise tool execution, certified result append, and text-terminal completion. Byte-level cancellation, blocked-read interruption, backpressure, reconnect, and deployed Harness semantics remain external.                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekCurlBytePrefix`                            | Process-backed byte-prefix ingress: bounded stdout reads retain raw chunks and pending fragments, complete body lines advance the typed prefix state, and the private status trailer is separated before strict completion validation. The stop policy is checked before each subsequent read; blocked-read interruption, backpressure, cancellation, reconnect, and deployed Harness semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekStreamHarnessBytePrefix`                   | Process-byte prefix to Harness continuation: completed prefix certificates feed the existing rich/tool/session runner, while prefix fuel stops remain explicit Harness stops. Deterministic one-round and two-round fixtures retain raw/framing/status evidence beside tool execution and runner endpoints; blocked-read interruption, backpressure, reconnect, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekCurlBytePrefixTimeout`                     | Timer-driven process-byte prefix ingress: a real `Std.Async.Sleep` races each blocking stdout-byte read, and a configured-child timeout retains the typed prefix state, raw chunks, pending fragment, stderr, exit observation, and timeout line. Blocked, delayed-prefix, and fast-completion fixtures are executable; arbitrary descendant cleanup, fairness, backpressure, authenticity, durability, reconnects, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekStreamHarnessBytePrefixTimeout`            | Timed byte-prefix to Harness continuation: completed prefixes reuse the existing dependent finish/tool/session path and a fuel-bounded multi-round trace carries exact runner endpoints, while timeout, fuel, and cancellation stops become explicit nonterminal prefix errors. The executable adapter retains the timed prefix witness beside the runner boundary; in-flight provider behavior, reconnects, and deployed asynchronous equivalence remain external.                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekHarnessPersistenceStreamBytePrefixTimeout` | Composes memory-backed validated restore with the timed byte-prefix process adapter: the fuel fixture checks `8 -> 10`, one accepted round, and explicit exhaustion, while the terminal companion checks `8 -> 11`, two rounds, completion, and model `0`, with exact restored-session equalities. Durable media, crash recovery, blocked-read interruption, provider/process authenticity, cleanup, external effects, and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekHarnessEventIgnorableProjection`           | Archive-side projection for the current envelope's explicit `ignorable: true` marker: positional keep/drop decisions drop only opaque ignorable rows, retain supported wire certificates and source positions, and reject required opaque rows.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekHarnessEventIgnorableNormalization`        | Supported-subset continuation of that projection: retained rows are renumbered contiguously, supported `sourceEventSeqs`/`surfaceOp` references are remapped through the physical-to-local map, and the normalized JSON is passed to `SessionRefinement.validateJsonLog`. Duplicate physical sequences, missing references, malformed rewrites, required opaque rows, and semantic failures reject; opaque payload semantics and deployed Harness equivalence remain obligations.                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekHarnessEventSimulation`                    | Occurrence-indexed source-to-local replay for the normalized supported subset: a typed `DecisionLedger` records every keep/drop decision, `ReplayStep` carries each exact pre-state `RefinedEvent`, and `SourceReplay` proves protocol erasure plus final session-projection equality. Opaque semantics, provider behavior, bytes, persistence, cancellation delivery, and complete deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekHarnessEventArchiveReplay`                 | Archive-aware dependent replay for that supported subset: `ArchiveReplay` combines the indexed `SourceReplay` with the inductive keep/drop ledger, retains exact archive/kept raw rows, and exposes dropped opaque rows and positions. The fixture checks nine physical rows, eight supported transitions, and one explicit opaque no-op; required opaque rows still fail closed.                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekHarnessEventIgnorableRunner`               | Attaches a normalized validated endpoint to `ConversationRunner`, preserves exact session/step certificates, and rebuilds a typed `ChatRequest` through `buildRequestCertificate`; the tool fixture exercises the normalized user/assistant/tool path. Opaque semantics, provider authenticity, persistence, transport, and deployed Harness equivalence remain obligations.                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekHarnessEventIgnorableTransport`            | Carries the normalized runner through the existing process-backed complete-response conversation trace, retaining final runner/model/stop evidence in `RestoredTransportRun`; the deterministic fixture exercises one no-tool completion. Injected transport, credentials, provider authenticity, persistence, and deployed Harness equivalence remain obligations.                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekCurlStream`                                | Complete-body process-backed SSE validation with typed process/status/stream errors and a deterministic `sh` fixture; incremental reader semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekCurlOutcome`                               | Process-backed complete-body dispatch into the typed provider-failure/text/tool/mixed/multi outcome sum, with process, HTTP-status, and semantic errors kept distinct.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekOutcomeSession`                            | Typed terminal-outcome dispatch: provider failures preserve an unchanged runner, while successful text/tool/mixed/multi outcomes finish and append through the proof-carrying session runner; source-event evidence and failure-message policy remain caller obligations.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekOutcomeConversation`                       | Process-backed terminal-outcome handoff into `ConversationRunner`: provider failures preserve the conversation, while successful rich assistants append with model/tool-count proofs and route completed `FunctionCall` values through the existing dependent executor, including certified tool-result appends; retry, persistence, cancellation, and provider-ID policy remain caller-controlled.                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekOutcomeTransportLoop`                      | Generic-`Transport` complete-body rich-outcome continuation: type-indexed streaming requests, terminal validation, dependent tool execution, updated-runner continuation, and distinct provider-failure/completion/fuel stops; incremental IO, retry, cancellation, credential trust, and deployed equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekCurlSession`                               | Complete-body process-backed terminal SSE composition into accepted rich/session values, retaining the wire certificate and runner append invariants; live/deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekCurlIncremental`                           | Line-oriented process-backed SSE delivery to a callback under an explicit read budget, followed by reconstructed-body strict validation and typed process/status/stream/callback/limit errors; byte-level semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekCurlPrefix`                                | Process-backed proof-carrying prefix execution: each complete body line advances `PrefixState` before the next read, fuel/cancellation stops kill and wait for the child, and terminal success retains raw output, status, normalized frames, and strict `[DONE]` validation. Blocked-read cancellation and deployment semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekCurlPrefixSession`                         | Completed process prefix projection into accepted text/tool/mixed/multi stream semantics and append-only runner proofs; fuel and cancellation remain typed stops, while blocked-read interruption, external execution, and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.HarnessPersistenceIO`                              | Executable UTF-8 JSONL byte/text adapter over memory and filesystem backends, retaining exact read/parse/persistence certificates and permitting append-only rows only after the current document validates; fsync, torn-tail repair, locking, and stable-media durability remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.HarnessPersistenceBytes`                           | Pure `ByteArray` UTF-8/JSONL adapter retaining source bytes, decoded text, parsed rows, packed-row expansion, and the final Session/Protocol projection; executable fixtures cover accepted, malformed, empty, and invalid-UTF-8 bytes.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekRichStream`                                | Source-honest text-only SSE projection into `RichStream.ValidatedTrace`, with wire/projection/rich certificates and fail-closed semantic errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekRichToolStream`                            | Restricted one-tool SSE projection into rich tool-call blocks, preserving raw arguments and retaining wire/projection/rich certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.DeepSeekRichMixedStream`                           | Composed one-choice text/reasoning/one-tool SSE projection with first-seen block indices, stateful tool metadata, exact rich-trace certificates, and same-frame mixed-kind rejection.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekRichMultiStream`                           | One-choice text/reasoning/multi-tool SSE projection with provider-indexed call state, first-seen local blocks, exact per-call argument assembly, terminal closure, and typed rejection paths.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.DeepSeekSessionBridge`                             | Terminal rich-view extraction and proof-carrying session append with caller-supplied numeric call IDs and source-event evidence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekSessionRunner`                             | Pure composition of accepted text/one-tool/mixed/multi-call responses into an append-only runner with exact sequence, message-order, and tool-call-count invariants.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekApiSession`                                | Fail-closed projection of decoded non-streaming DeepSeek responses into the append-only runner with singleton-choice, finish, payload, and local ID/count certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekHarness`                                   | Typed model-round bridge from the session surface to a request plan, process/API response acceptance, generic dependent tool admission/policy/provider execution, and retained typed replies; `appendRoundToolResults` encodes dependent outcomes back into the canonical session with exact local-ID, source-sequence, message-order, and protocol certificates; `ConversationRunner` and `executeConversationRound` carry that certified session into a subsequent request, while `runConversation` repeats the round under explicit fuel and returns either a no-tool-call completion certificate or explicit exhaustion; the test suite covers both outcomes.                                                                                                                                                   |
| `Cordis.DeepSeekGenericBridge`                             | Explicitly composes bounded provider function-call/schema admission with a named generic catalog binding and dependent `Config.validate`, retaining both certificates and the existentially selected local call/request type; provider-schema semantic equivalence and execution remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekSchemaExecution`                           | A separate schema-aware execution adapter consumes that combined certificate, applies generic policy, and invokes only the committed dependent `View`; admission, policy, and provider failures remain typed, while the raw compatibility path is unchanged.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekSchemaHarness`                             | Carries a successful schema-aware execution into the existing `DeepSeekHarness.ExecutedTool`, exact session append surface, and `ConversationRunner` without re-executing it; provider certificates remain nested, and message/next-sequence/protocol-projection theorems are reused.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekSchemaRound`                               | Bounded complete-body response round for exactly one accepted assistant function call: preserves the response/tool-call witness, dispatches through schema-aware execution, appends to the existing runner, and rejects zero/multiple calls with typed errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekSchemaMultiRound`                          | Bounded complete-body response round for a nonempty homogeneous list under one explicit provider/generic binding: sequential dependent execution, exact list-length evidence, typed later-call failures, and certified multi-result runner endpoint. Heterogeneous schema registries and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekSchemaRegistry`                            | Bounded heterogeneous registry: each dependent entry carries its own provider schema and generic binding; name lookup, sequential mixed-operation execution, exact runner accounting, and typed unknown-name rejection are proved/exercised locally. Live transport, provider obedience, call-ID authenticity, persistence, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekSchemaConversation`                        | Connects registry-derived tool declarations to a typed complete-body transport plan and validated response, retaining the exact plan/response certificates, heterogeneous execution batch, and runner endpoint for one round.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.DeepSeekSchemaConversationLoop`                    | Adds a caller-fueled loop over those transport-backed heterogeneous rounds, with a dependent round history, explicit terminal no-tool witness, model/runner endpoint, and distinct fuel-exhaustion stop. Retries, cancellation, persistence, external effects, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekSchemaTransportRetryCancellation`          | Composes the heterogeneous schema registry with the single-decoder retry boundary and pre-round cancellation: the successful validated response feeds terminal admission or dependent weather/clock execution without reparsing, each tool-round tail is indexed by its exact runner/model endpoint, and completion/cancellation/exhaustion remain distinct. In-flight IO interruption, provider backoff/idempotency, persistence, external effects, and deployed retry/cancellation equivalence remain external.                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekSchemaProcessRetryCancellation`            | Instantiates that same dependent retry/cancellation result with the existing `IO.Process`/`sh` adapter: a deterministic fixture emits 503, heterogeneous weather/clock calls, and a terminal no-tool body over successive attempts, preserving retry history and exact endpoints. Network, credentials, shell trust, provider obedience, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekSchemaStreamConversation`                  | Adds a complete-body SSE/rich-stream/session continuation over the same heterogeneous registry: the typed request proves `stream: true`, the terminal streamed body is validated before dependent dispatch, and a fuel-bounded run distinguishes a certified text terminal from exhaustion. Incremental delivery and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.DeepSeekSchemaStreamPrefixConversation`            | Adds the line-oriented process-prefix version: exact accepted prefixes survive line-budget exhaustion or line cancellation, and only a completed `[DONE]` body reaches heterogeneous schema dispatch. Byte framing, blocked-read interruption, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekSchemaStreamErrors`                        | Adds the opt-in heterogeneous provider-failure continuation: each failed registry entry retains schema/admission/policy/error/model evidence, becomes an `isError` result through the existing runner, and a streamed terminal response can follow with `.include`; retries, cancellation, persistence, and deployed error semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekHarnessErrors`                             | Explicit opt-in error-result continuation: `ErrorToolResultPolicy.reject` remains fail-closed by default, while `.include` admits a proof-carrying `ProviderFailedTool`, preserves its parsed/admission/policy/provider-error evidence and model stability, and appends it as a model-visible `isError` tool result before a subsequent typed request.                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekHarnessRetry`                              | Explicit bounded complete-body retry: `RetryPolicy` retries only opted-in transport/transient-HTTP failures, `RetryHistory` retains prior `ClientError`s with a retry bound, `executeWithRetry` reuses one exact `RequestPlan`, and `executeConversationRoundRetry` carries that history into the typed continuation result.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekHarnessCancellation`                       | Boundary-safe pre-round cancellation: `CancellationPolicy` is checked before each complete request round, and `CancellableRunResult` retains the exact completed prefix, runner/model endpoint, and proof-carrying cancellation decision; fuel exhaustion and completion remain distinct stops. In-flight IO interruption is outside.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekHarnessLiveProbe`                          | Credential-safe environment parsing plus a complete-mode prepared request and bounded conversation probe through curl or an injected transport; missing/empty credentials are typed and never logged, while credential validity and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekHarnessLocalHttp`                          | A one-shot loopback HTTP server validates the actual curl method, route, authorization, model, and `stream: false` body before returning two typed responses; the dependent result retains port/request/server evidence beside the final runner endpoint. Remote reachability, TLS, provider authenticity, and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekHarnessLocalSse`                           | A one-shot loopback HTTP server validates a typed `stream: true` request, emits the real SSE body in line chunks through curl, and retains the incremental line/body/wire certificate before appending the finished text response to the dependent runner. Byte framing, backpressure, blocked-read cancellation, reconnects, provider authenticity, and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekHarnessTransportRetryCancellation`         | Composes the indexed injected-transport retry trace with a pre-round cancellation policy: cancellation retains the exact retry-aware prefix, unchanged runner/model endpoint, and round/reason decision, while a non-cancelled fixture retains the 503 retry history and terminal two-round endpoint. In-flight IO interruption, provider backoff/idempotency, persistence, external effects, and deployed retry/cancellation equivalence remain external.                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.DeepSeekStreamHarness`                             | Complete-body process-backed rich tool-stream continuation into the generic `ConversationRunner`: terminal streamed calls receive local numeric IDs, pass through the same dependent admission/policy/provider execution path, and append certified typed tool results. Streamed rounds use `buildStreamingRequestPlan`, whose source/body certificate proves `stream: true`; an executable fixture rejects the non-streaming serialization. Both the one-call entry point and `executeConversationMultiStreamRound` are exercised by deterministic process fixtures, including a two-call terminal stream; `runConversationMultiStream` reuses those certificates under explicit fuel and stops on a text-only terminal response or typed exhaustion. Incremental delivery and deployed semantics remain external. |
| `Cordis.DeepSeekStreamHarnessByte`                         | Byte-backed complete-body streamed Harness continuation: bounded stdout chunks retain the dependent byte/framing/status witness while the decoded body enters the existing rich/tool/session runner; one-round and fuel-bounded fixtures exercise dependent tool execution, certified result append, and text-terminal completion. Byte-level cancellation, blocked-read interruption, backpressure, reconnect, and deployed Harness semantics remain external.                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekStreamHarnessCancellation`                 | Boundary-safe pre-round cancellation over `runConversationMultiStream`: the policy is checked before each complete streamed request, and the result retains the exact streamed witness prefix, unchanged runner/model endpoint, and typed cancellation decision; in-flight process interruption remains external.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekStreamHarnessPrefix`                       | Line-oriented process-prefix continuation for a multi-call streamed round: every complete line is parsed before the next read; completion reuses the typed stream/tool/session continuation, while fuel exhaustion or line cancellation returns the exact prefix and typed stop evidence. Blocked-read interruption and deployed stream semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekStreamHarnessErrors`                       | Complete-body streamed provider-failure continuation and fuel-bounded loop: a failed streamed tool call retains typed parsed/admission/policy/provider evidence, preserves the model, and appends an `isError` tool result; a later streamed terminal can continue only with `RequestSource.errorToolResults := .include`. Incremental recovery, retries, persistence, and deployed error semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekStreamHarnessRetry`                        | Checked complete-body streamed retry: an explicit policy retries process and transient-HTTP `SessionClientError`s, retains the exact ordered failure history with a bound, and carries that history into the existing streamed assistant/tool continuation; stream framing, semantic response, and tool failures remain terminal. Backoff, idempotency, cancellation, persistence, and deployed retry equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekStreamHarnessRetryConversation`            | Process-backed retry-aware streamed conversation: indexed fuel-bounded traces retain each complete streamed body, retry history, dependent assistant/tool endpoint, and exact runner/model continuation; completion, exhaustion, and bounded transient-HTTP failure remain distinct. Backoff, idempotency, blocked-read cancellation, persistence, reconnects, and deployed retry equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekStreamHarnessRetryCancellation`            | Boundary-safe pre-round cancellation over the indexed retry-aware streamed conversation: cancellation retains the exact accepted retry-aware trace prefix, unchanged runner/model endpoint, round/reason decision, and per-round retry history; completed and fuel-exhausted stops remain distinct. It does not interrupt in-flight process/HTTP/stream/tool IO or claim cleanup, reconnect, or deployed Harness cancellation equivalence.                                                                                                                                                                                                                                                                                                                                                                          |

The public library umbrella is `Cordis.lean`. `Main.lean` is the
`cordis_demo` entry point, and `Tests.lean` is the `cordis_tests` entry point.
`Cordis.TestSuite`, `Cordis.NegativeTests`, and `Cordis.AxiomAudit`
intentionally remain separate from the umbrella's runtime behavior. The static
rejection module is nevertheless a default Lake library target, so `lake build`
must elaborate it.

## 5. Finite acceptance matrix

| Acceptance item                                                        | Delivered evidence                                                                                                                            | Scope qualification                                                                                                  |
| ---------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| Identity, sequential recovery, associativity, and accumulator recovery | `Effect.identity_seq`, `seq_identity`, `seq_recovers`, `seq_assoc`, `UndoAccumulator.push_recovers`, `UndoStack.recover_after`                | Pure modeled state.                                                                                                  |
| Observational recovery                                                 | `Observational.Effect.seq_recovers` and related laws                                                                                          | Up to the supplied `Setoid`.                                                                                         |
| Certified two-call reorder                                             | `Effect.IndependentAt`, `CertifiedTwoBatch.execute_order_irrelevant`, `execute_outputs_in_model_order`, `execute_recovers`                    | Exactly two pure calls; no async scheduler.                                                                          |
| Finite multi-segment scheduler                                         | `ParallelSchedule.Plan.execute`, `execute_after_eq_canonical`, `execute_undo_eq_canonical`, `execute_reports_ids_nodup`                       | Arbitrary finite pure windows/barriers with model-order reports and exact recovery; no wall-clock or IO concurrency. |
| Dependent call/reply correspondence                                    | `AuthorizedCall`, `Reply call`, `View.execute`                                                                                                | Static dependent API after admission.                                                                                |
| Declared capability and present provider                               | `View.resolve`, `View.provider_present`, `Registry.Satisfies`                                                                                 | Constructive view evidence; no process isolation.                                                                    |
| Reversible registry mutation and distinct-key commutation              | `Registry.setEffect_recovers`, `setEffect_commute`                                                                                            | Distinct typed operation keys.                                                                                       |
| JSON AST codec round-trip and nested errors                            | `Codec.decode_encode`, primitive/product/list codecs                                                                                          | AST only; no byte parser or external schema enforcement.                                                             |
| Fail-closed dynamic tool admission                                     | `ToolWire.validate`, `validate_declared`                                                                                                      | Name, declaration, AST shape, contract, and capability checks.                                                       |
| Request-indexed encoded results                                        | `ToolWire.resultCodec`, `decode_encoded_result`, `encodeCertifiedResult`, `decode_encoded_certified_result`                                   | Tagged success/failure AST values; no transport.                                                                     |
| Typed protocol structural invariants                                   | Indexed `Event`, `Event.preservesWellFormed`, `Event.noOrphanResult`                                                                          | Finite turn/step/pending-call machine.                                                                               |
| Raw event replay and intrinsic trace reconstruction                    | `validateEvent`, `validateTrace`, `validateRuntimeTrace`, `ValidatedTrace.replays`, `replayRaw_eraseTrace`                                    | Finite in-memory raw lists.                                                                                          |
| Bounded assistant stream reconstruction                                | Indexed `Stream.Chunk`/`Trace`, `noChunkAfterFinished`, `replay_completeTrace`                                                                | Text fragments only.                                                                                                 |
| Policy before dispatch and subject preservation                        | `SubjectPolicyTransition`, `SubjectPolicyTrace.dispatchCount_le_one`, `dispatchCount_to_completed`, `denied_dispatchCount_eq_zero`            | One explicitly threaded pure trace, not global exactly-once.                                                         |
| Exact-subject policy integrated into execution                         | `Harness.CallEvidence.admitted` stores validation, execution, lease, subject-indexed completion, and policy trace                             | Counter-specific deterministic harness.                                                                              |
| Encoded result retained by the harness                                 | `CallEvidence.encodedResult`, `CallRecord.encodedResult`; integration tests decode read and increment results                                 | Only after successful provider execution.                                                                            |
| Finite multi-step and multi-turn execution                             | `RunnerState.runStep`, `runSteps`, `runTurn`, `runTurns`, `runMultiTurn`                                                                      | Sequential call dispatch.                                                                                            |
| Runtime state/log agreement                                            | `RunnerState.replayProof`, `Harness.replayRaw_append`                                                                                         | In-memory state and list, not durable storage.                                                                       |
| Joint model, lease, and ID history                                     | `RecordChain initial nextCall records final leases boundaries`, `length_eq_nextCall`, `ids_eq_range`, `leases_threaded`                       | Starts at the initial model and empty lease pool; records remain in sequential model-commit order.                   |
| Exact log-boundary/record agreement                                    | `RecordChain.boundaries_eq_records`, `RunnerState.callBoundaries_eq_records`                                                                  | `callBoundaries log = recordBoundaries records` for finite in-memory lists; not a persistence theorem.               |
| Atomic call/result and record settlement                               | Private settlement transition extends protocol, log, record, model, leases, history, and replay proof together; public generic `emit` removed | Atomic only as one pure immutable `Except` result, not a durable transaction or global exactly-once guarantee.       |
| Partial lifecycle recovery and withdrawal guard                        | `Lifecycle.Transition.unload_recovers`, `unload_rejects_relied`, `active_successor_keeps_view`                                                | Finite synchronous generic lifecycle.                                                                                |
| End-to-end local reference execution                                   | `Harness.demo` and `Cordis.TestSuite.run`                                                                                                     | Certified counter tools only; no live API.                                                                           |
| Static rejection of selected malformed constructions                   | `Cordis.NegativeTests` guarded expected compiler errors                                                                                       | Concrete API attacks; not a universal metatheorem or complete adversarial search.                                    |

The original target language used words such as “parallel scheduling” and
“complete harness.” For `v0.1.0`, those claims are narrowed to the rows above:
the batch result is a certified pure two-call evaluation-order equivalence, and
the complete execution is complete only for the delivered finite local counter
scenario.

## 6. Reproducibility gates

The delivered checkout has five verified commands:

```bash
lake build
lake lean Cordis/NegativeTests.lean
lake exe cordis_tests
lake exe cordis_demo
lake lean Cordis/AxiomAudit.lean
```

Expected behavior:

- `lake build` builds the public library, the `CordisStaticTests` rejection
  target, and the `cordis_demo` and `cordis_tests` default executables.
- `Cordis/NegativeTests.lean` compiles only when the listed malformed
  constructions continue to produce their guarded expected errors. It is not
  imported into the native test executable.
- `cordis_tests` exits successfully and prints
  `CORDIS adversarial and integration tests passed`.
- `cordis_demo` reports final counter `5`, protocol `ready 1`, 12 replayed
  events, three successful encoded results with one policy dispatch each, and
  one unknown-tool rejection with zero dispatches and no encoded result.
- `Cordis/AxiomAudit.lean` prints the dependencies of the headline theorems.
  Its selected guarantees include boundary/record agreement and lease
  threading at both the `RecordChain` and `RunnerState` levels.
  The current audit reports only Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound` where dependencies occur; several
  theorems are axiom-free.

The pinned GitHub Actions workflow also runs `lake --wfail build`, verifies the
resolved Lean version, executes the self-testing lexical source checker, and
parses the axiom report. Repository hygiene additionally requires no actual
`sorry`, `admit`, project-defined `axiom` or bodyless `constant`, `unsafe`,
`partial`, external runtime override, credential, or committed local absolute
path. These automation checks are validation gates, not additional kernel
theorems.

## 7. Trust boundary

The following facts are proved for the delivered Lean values:

- accepted modeled effects recover their indexed predecessor;
- strong two-call certificates make the two finite evaluation orders equal;
- dependent calls and replies cannot be mismatched in typed code;
- committed views require declared-operation evidence and retain provider
  identity/presence evidence;
- generated codec values decode to their original typed values;
- raw tool calls fail closed before becoming authorized dependent calls;
- request-dependent success and failure results round-trip through their tagged
  AST codec;
- typed protocol, policy, stream, and lifecycle transitions exclude their
  stated illegal edges;
- accepted raw event lists reconstruct typed traces and replay to their indexed
  endpoints;
- a runner's stored protocol state equals replay of its complete event list;
- admitted counter calls retain policy and provider evidence for the exact same
  dependent subject;
- records thread model and lease endpoints from the initial model and empty
  pool, with monotone session-wide IDs;
- the log's call/result projection equals the ordered call/result pairs derived
  from the records;
- a successful pure settlement adds the call, result, record, model endpoint,
  lease endpoint, history witness, and replay witness together; and
- the deterministic counter providers satisfy their declared postconditions.

The following remain external facts or validation boundaries:

- `IO`, HTTP, filesystems, subprocesses, clocks, signals, native plugins,
  schedulers, persistence, and model providers may behave differently from the
  modeled state;
- parsing bytes into `Lean.Json`, rendering ASTs, character encoding, transport,
  and storage are outside the codec proofs;
- JSON schemas are metadata and cannot force a language model or service to
  conform;
- a certificate for an external action is only as strong as the observations
  used to construct it;
- irreversible emissions outside the modeled state cannot be undone;
- capability views do not provide host- or process-level isolation;
- a pure lease value can be duplicated, so policy theorems do not establish
  global exactly-once execution or atomicity across workers;
- pure runner settlement does not provide durable transactionality, crash
  recovery, or atomic coordination with external effects; and
- fairness, cancellation delivery, process termination, and remote availability
  are not theorems of this kernel.

There is no credential-loading path or live model API in `v0.1.0`. No API key
is needed for any acceptance command, and no key may be stored in the
repository. `DeepSeekCurlTransport` and `DeepSeekCurlStream` are process-backed
adapters, not proofs of network reachability, credential validity, executable
trust, deployment, or incremental stream semantics.

## 8. Explicit future work

The following are intentionally not part of the delivered finite acceptance
claim:

1. **Full asynchronous execution.** `Cordis.AsyncHarness` now supplies a bounded
   pure fiber state machine with typed start/complete/fail/cancel transitions,
   completion-order traces, and drained finite-schedule certificates. The
   remaining work is live task/fiber spawning, cancellation delivery,
   completion races, wall-clock fairness, cleanup, adapter-level failure
   handling, and integration with the deployed Harness.
1. **N-call concurrency.** `Cordis.ParallelSchedule` and `Cordis.AsyncHarness`
   cover arbitrary finite _pure_ segment schedules and indexed fiber traces.
   They do not provide the actual async/fiber adapter: dependency graphs,
   worker races, cancellation delivery, fairness, cleanup, or deployed
   scheduler equivalence remain open.
1. **External adapters.** `Cordis.DeepSeekApi` supplies the checked
   request/response codec and an explicit transport seam for a small,
   non-streaming OpenAI-compatible DeepSeek subset. `Cordis.DeepSeekCurlTransport`
   supplies a process-backed executable adapter and deterministic `sh` fixture;
   network policy, credential injection, process trust, real tool processes,
   persistence, and explicit per-adapter deployment declarations remain
   external. `Cordis.DeepSeekStream` covers
   strict in-memory SSE text/UTF-8 framing. `Cordis.DeepSeekRichStream` covers
   one-choice assistant text, `Cordis.DeepSeekRichToolStream` separately covers
   one indexed function call, and `Cordis.DeepSeekRichMixedStream` composes one
   choice that interleaves text, reasoning, and one indexed function call across
   frames while rejecting same-frame mixed kinds.
   `Cordis.DeepSeekRichMultiStream` extends the same source-honest boundary to
   any finite list of indexed function calls, retaining per-call IDs/names and
   raw argument fragments while assigning contiguous local block indices.
   `Cordis.DeepSeekSessionBridge` is the final local seam for a certified
   terminal rich view: it appends an assistant payload only with explicit
   numeric call-ID assignment and source-event proofs supplied by the caller.
   `Cordis.DeepSeekSessionRunner` composes those accepted responses sequentially
   and proves contiguous session sequence plus local tool-call-count invariants,
   including the multi-call response path, but does not model transport,
   cancellation, persistence, or external tools.
   `Cordis.DeepSeekApiSession` applies the same guards to the decoded non-streaming
   response path; it rejects extra choices and unsupported or empty terminal payloads
   before the local append.
   `Cordis.DeepSeekCurlStream` composes a complete process response with the
   strict SSE validator, preserving process/status/stream error distinctions;
   it does not implement a live reader, backpressure, cancellation, reconnect,
   or provider-complete assembler.
   `Cordis.DeepSeekCurlSession` composes a terminal text fixture through the
   rich projection and append-only runner, retaining both wire and runner
   certificates; source-event evidence, local ID allocation, and deployed
   session semantics remain explicit caller/runtime boundaries.
   `Cordis.DeepSeekStreamHarness` extends that complete-body boundary to a
   terminal rich tool stream: it assigns local IDs, executes admitted streamed
   calls through the generic dependent provider path, and appends certified tool
   results into the reusable conversation runner. The one-call and typed
   `executeConversationMultiStreamRound` paths are exercised by deterministic
   process fixtures, including a two-call terminal stream. Its
   `runConversationMultiStream` loop composes those rounds under explicit fuel,
   stopping on a text-only terminal response or typed exhaustion. It remains a
   complete-body adapter and does not claim incremental delivery, cancellation,
   backpressure, reconnects, provider-complete assembly, or deployed equivalence.
   `Cordis.DeepSeekStreamHarnessPrefix` connects the proof-carrying line prefix to that
   multi-call continuation: a completed prefix appends certified tool results, while a line
   policy or read budget returns the exact parsed prefix instead of a generic client error.
   It remains line-oriented and does not claim byte framing, blocked-read interruption,
   backpressure, reconnects, provider-complete assembly, or deployed equivalence.
   `Cordis.DeepSeekAsyncHarness` adds an executable cooperative race over two such process-backed
   text-prefix jobs. It retains the first typed result and requests cancellation of the loser, but
   does not claim that a synchronous line read is interruptible, nor fairness, cleanup, or deployed
   asynchronous Harness semantics.
   `Cordis.DeepSeekAsyncStreamHarness` lifts the same cooperative race over the streamed dependent
   tool/session continuation. The winner retains typed tool executions, runner, final model, and
   round witnesses under explicit fuel; synchronous reads, fairness, cleanup, and deployed
   asynchronous semantics remain external.
   `Cordis.DeepSeekCurlIncremental` then exposes each complete body line through
   an IO callback under an explicit read budget before consuming the private
   status trailer and validating the reconstructed body; it remains a
   line-oriented complete-response adapter, not a byte-level/backpressure/
   cancellation or deployed-stream theorem.
1. **Production streaming.** Extend the bounded text model with transport,
   backpressure, cancellation, tool-call payload assembly, provider-complete
   parser state, and a live HTTP reader; the current `DeepSeekStream` module is
   only the strict in-memory `data:` / `[DONE]` boundary. The rich projections
   cover text-only, one-tool, one-choice mixed text/reasoning/one-tool, and
   one-choice multi-call subsets, but still reject extra choices, unsupported
   provider finishes, replay metadata, and deployed assembler behavior rather
   than claiming the production stream protocol.
1. **Production policy guarantees.** Add durable lease storage, atomic
   consumption, multi-process exclusion, retries, and crash recovery before
   claiming global exactly-once behavior.
1. **Full CORDIS implementation coverage.** Model dynamic loader acquisition,
   real fiber lifetimes, interception, isolation, hot replacement, and the
   broader lifecycle implementation.
1. **Full paper mechanization.** Port and prove the remaining CORDIS calculus,
   iterator, arbitrary-removal, scheduling, and composability results rather
   than inferring them from similarly named finite structures.
1. **DeepSeek Harness equivalence.** Define an explicit relation to the pinned
   TypeScript state, plugin, cancellation, persistence, and error semantics and
   prove it. No such full equivalence theorem exists in `v0.1.0`.

Future adapters must preserve the distinction between checked boundary data,
Lean-proved kernel facts, and trusted external observations. Extending the
repository does not automatically extend any theorem beyond its stated model.
