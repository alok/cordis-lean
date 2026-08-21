# Trust boundary

<!-- markdownlint-disable MD013 MD029 -->

> **Current-development addendum.** The `0.2` work described in
> [`V0_2_SPEC.md`](V0_2_SPEC.md) moves catalog coherence, runner phase,
> exact-call policy rejection, rich surface placement, log sequence continuity,
> proof-producing validation after typed payload parsing, request
> reconstruction, and rich-to-structural protocol equality into Lean types. It
> adds partial TypeScript boundaries: supported current-Harness stream-chunk
> JSON-AST values decode into the intrinsic rich-stream validator, and a
> stateful turn/step/tool session subset jointly refines into local Session and
> Protocol witnesses. It does not
> add byte-level parsing, durable storage, transport, real model/tool I/O,
> asynchronous fibers, global exactly-once execution, full paper metatheory, or
> whole-Harness behavioral equivalence. The reviewed `0.1.0` boundary below
> remains historical evidence rather than a claim about those absent layers.

The active line also proves local reactive coeffect behavior for paper
Definitions 22–26, direct finite isolation/interception models for Definitions
27–31, finite unfoldings for Definition 32, and the finite-context relation and
reactive invariance of Definition 33. Key-local equivalences, operation laws,
metadata monoids, and runtime correspondence remain supplied obligations;
Definition 34/Lemma 35's fixed-generator relation and Definitions 36–37 with
the finite Lemma 38 core are now explicit. A formal counterexample shows that
same-word tests do not derive the stronger paired-inverse law; Definitions
17–19 and full total Definition 39 are now explicit, as are finite exact Theorem
20/Corollary 21, a finite partial distinct-key Theorem 40, and a Definition 41
interpreter. Arbitrary finite branch trees now satisfy a corrected exact/observational whole-run
interchange theorem, and their complete finite partial/Kleisli transformation closures satisfy
cross-monoid commutation and yield stability. The paper's literal total/quotient setting remains
open. `Schedule` executes sequentially, and
`RichStream` excludes transport, images, tool-result blocks, and pruning. These
types do not extend the theorem boundary to corresponding external systems
automatically.

The global layer now includes exact phase-indexed lifecycle edges and finite preservation traces.
An executed landing must be reconstructed by `executeOne`, and unload alone consumes a named
`RecoveryAdmission`. A second module combines orchestration and lifecycle into one ten-name,
exact-endpoint relation with an empty-registry-origin trace. It is still not Theorem 59:
arbitrary-interleaving recovery remains supplied evidence and most global lemmas are unproved.
The first trace audit makes that gap executable: bare unload admission can preserve well-formed
endpoints while changing a foreign table, so existing-fiber Lemma 54 facts require a separate
`RecoveryConfinement` certificate.

CORDIS Lean proves properties of typed, pure Lean values. It does not by itself prove that a
model response, JSON parser, TypeScript Harness process, operating-system resource, or remote
service behaves like those values. This document marks the exact perimeter.

This is also the boundary emphasized by the paper's [§6.1 system-boundary
discussion][paper-pdf]: a recovery argument covers only effects represented inside the chosen
context and backed by valid inverses.

The detailed paper-to-declaration ledger is in [`PAPER_MAP.md`](PAPER_MAP.md).

## Boundary at a glance

The intended tool path crosses several different assurance levels:

```text
model bytes
  -- trusted parser/encoding --> Lean.Json
  -- checked ToolWire.decode/admission + supplied proofs --> AuthorizedCall
  -- indexed View.execute --> request-indexed Reply
  -- proved pure VerifiedTool contract --> abstract successor Model
  -- proved request-indexed AST encoding --> Lean.Json
  -- trusted renderer/transport --> external bytes and effects
```

Only the middle, in-memory Lean segment is inside the theorem boundary. A production adapter
must justify every arrow into or out of it.

The supported stream-refinement path is separate:

```text
provider JSON bytes
  -- trusted UTF-8/JSON parser --> Lean.Json
  -- checked RuntimeRefinement decoder --> SupportedChunk list
  -- proof-producing RichStream.validateTrace --> intrinsic ValidatedTrace
  -- proved erasure/replay --> exact local runtime endpoint
```

The first arrow remains trusted. Unsupported upstream fields and variants are rejected, not
translated. Success proves the local endpoint for that supported subset; it does not prove that
the TypeScript assembler accepts exactly the same language.

The local protocol has both typed erasure and witness-reconstructing validation:

```text
typed Trace -- erase --> RuntimeEvent list -- replayRaw --> erased endpoint
             \_________________ proved _________________/

local RuntimeEvent list -- validateTrace --> ValidationError
                         |
                         +--> ValidatedTrace
                              { finish, intrinsic Trace, erase_eq }
                                      |
                                      +-- ValidatedTrace.replays --> erased endpoint
```

Successful `validateEvent` and `validateTrace` calls therefore do reconstruct intrinsic
witnesses for the exact local six-event vocabulary. This is not a translation from the complete
DeepSeek Harness event union, and no theorem relates either Lean representation to a persisted
Harness session.

## What is proved

“Proved” means that Lean checks the proposition shown in the declaration. It does not extend
to a larger real-world interpretation without a refinement proof.

### Reversible state

- `Applied.undo_after` proves `undo after = before` for the exact state at which one effect was
  applied.
- `Effect.seq_recovers` and the monoid laws prove the local sequential effect algebra.
- `UndoStack.recover_after` proves exact LIFO recovery from the indexed terminal state.
- The observational effect variant proves the corresponding local recovery modulo a supplied
  `Setoid`, provided each inverse respects that relation.
- `Registry.setAt_restore` and `setEffect_recovers` prove exact recovery of a pure dependent
  provider map.
- `Registry.setEffect_commute` proves equality of two fixed, distinct-key registry-update
  sequences, including their composed recovery functions.
- `Effect.IndependentAt.seq_applied_eq` proves equality of both orders when supplied with a
  same-successor and pointwise same-recovery certificate at one predecessor.
- `CertifiedTwoBatch.execute_order_irrelevant` proves that either of two certified pure
  evaluation orders yields the same proof-carrying effect and model-ordered result pair;
  `execute_recovers` proves either outcome recovers that predecessor.
- `ParallelHarness.ParallelWindow` generalizes this to a finite proof-carrying window: the
  scheduled task list carries explicit ID/mode/effect/result-permutation certificates, and
  `WindowOutcome.execute` proves the scheduled endpoint agrees with canonical model order.
- `ParallelHarness.Plan` adds one intrinsically exclusive pure barrier after that window, while
  `ParallelHarness.drain.drainOutcome` emits ordered synthetic cancellation reports with an
  unchanged model. These are scheduler certificates, not concurrent execution.
- `DurableSettlement.Log` is an intrinsically indexed append-only frame log with a
  collision-free list transcript; `CrashPrefix` proves exact recovery of a retained prefix and
  typed resume after that prefix. This is a pure torn-prefix certificate, not a filesystem or
  cryptographic durability proof.

These results do not prove that an inverse recovers an arbitrary state, that arbitrary effects
are independent, or that external side effects are reversible. The evaluators perform no `IO`,
launch no tasks, and prove no wall-clock concurrency, promise cancellation, fairness, or
safe-parallel-execution property. The scheduler layer requires its effect, ID, and result
permutation certificates from the caller.

### Reactive, isolated, and observational contexts

- `Coeffect.Context` is a finite dependent map. `Present`/`Absent` make local preconditions
  explicit, while witnessed set/remove operations prove exact concrete recovery.
- `CoeffectAt` requires the integrator to supply each key's equivalence, typed operations,
  executable domain, and preservation laws. Lean checks those laws once supplied; it does not
  derive that they describe a live provider.
- `UnifiedContext.IsolatedContext` proves typed realm resolution and retains an injective
  embedding of logical keys into their own realms. This is a data-model property, not a sandbox
  or tenant-confinement theorem.
- `UnifiedContext.InterceptionContext` proves the declared/context metadata merge order and
  recovery for a supplied key-indexed monoid and provider table. The meaning of right bias and
  the behavior of real middleware remain external.
- `UnifiedContext.Approximation` exposes exact finite unfoldings of Definition 32. It is not a
  fixed point: the paper equation contains the recursive context negatively in `Gamma -> Gamma`,
  so this project does not pretend it is an ordinary strictly positive Lean inductive.
- `Coeffect.Observational.Related` is exactly same presence domain plus key-wise related values.
  The supplied `contextSetoid`, satisfaction invariance, and notification invariance are proved
  for finite contexts.
- `OperationalEquivalence` executes finite heterogeneous words of forward operations and
  concrete seeded inverses, including undefined domains and typed outcomes. Its relation is the
  largest equivalence respected by those fixed generators.
- `PairedGap.pairedInverseCoherent_fails` proves that same-word tests need not relate two
  different inverses yielded at related seeds. `PairedInverseCoherent` is therefore an explicit
  additional premise for the stronger `CoeffectAt` reconstruction, not a hidden theorem.
- `Observational.Quotient.Admissible.seq` and `Program.recovers` prove finite
  quotient-respecting composition/recovery. `Coeffect.Quotient.lift_results_related` connects
  the key-local laws to related whole contexts.
- `Transformation.Closure` includes identity, every effect forward/yielded-inverse generator,
  and composition. Generator commutation and inverse stability promote to the full monoids, and
  full Definition 19 implies the existing adjacent Batch/Schedule certificate.
- `Removal.RemovalTrace` retains the target-present and target-omitted application states and
  later inverse equalities through a finite suffix. `inverse_permutation_recovers` proves every
  permutation of the exact originally yielded inverses recovers the initial state. This is
  finite exact Theorem 20/Corollary 21, not observational or external-effect recovery.
- `ExactOperationIndependent` adds outcome stability to full total Definition 39.
  `distinctKeys_finiteIndependent` covers arbitrary finite partial operation words at distinct
  dependent keys, including inverse and outcome stability, and `Computation.run` implements
  Definition 41 with exact recovery.
- `MediatedIndependence.RealizedPath` retains actual outcome-selected branches.
  A universal-relation cell model proves exact representatives need the extra
  `ExactRepresentativeCoherence` law. `MediatedTheorem` then proves all-branch finite whole-run
  interchange and conditional yielded-inverse stability after correcting the partial-domain API.
  `PartialTransformation` then closes the partial forward/yielded-inverse Kleisli monoids under
  identity/composition and proves full cross-closure commutation plus success-conditional yield
  stability. A countermodel proves the whole-run certificate is strictly weaker.
  `ObservationalPartialTransformation` proves the current `CoeffectAt` laws make every adaptive
  generator relation-respecting and then descends that full closure theorem to related
  representatives with exact partial-domain agreement. Its separate `RespectGap` demonstrates
  why exact commutation is not enough for arbitrary maps.

### Current stream JSON refinement

- `SafeNat` proves accepted numeric indices/counts are canonical nonnegative JSON integers in
  JavaScript's exact range.
- `decodeChunk` and `decodeChunks` operate on `Lean.Json`, preserve provider IDs and raw argument
  strings, and return path-aware errors.
- `ValidatedJsonTrace` retains the exact decoded supported chunks and an intrinsic
  `RichStream.ValidatedTrace`; `replay_eq` proves the erased trace reaches its indexed endpoint.
- Missing optional upstream usage counts become zero only in the named `WireUsage.toLocal`
  normalization.
- Opaque replay state, image/tool-result blocks, and upstream error/abort `LlmFailure` payloads
  are rejected because the local types are not equivalent.

This is soundness of one fail-closed supported subset. It is not completeness for the current
TypeScript `BlockAssembler`, JSON-text parser correctness, transport correctness, or a claim
that provider bytes match the audited AST shapes.

`SessionRefinement` is a second, stateful supported subset. It retains decoded upstream sequence
and time values, normalizes one-based upstream steps to zero-based local steps, derives
`turn/end.nextStep` only from the already validated prefix, and assigns provider string call IDs
to fresh numeric IDs with proof-carrying uniqueness state. Each admitted event carries both a
`Session.ValidatedAppend` and a `Protocol.ValidatedEvent`; the cumulative theorem equates the
complete rich-session structural projection with intrinsic trace erasure. Messages, chunks,
headers, replacements, extensions, opaque tool metadata, and non-equivalent turn reasons are
rejected. No completeness, persistence, or whole-session behavioral equivalence follows.

### Dependent calls and tool contracts

- `Signature.Response op request` prevents attaching another operation's or request's response
  type to a well-typed call.
- `Binding.present` and `View.provider_present` prove that the committed provider is present in
  the particular pure registry value indexing the view.
- `AuthorizedCall.declared` carries the proof that the selected operation belongs to the
  supplied `Needs` predicate.
- `ToolSpec.Invocation` carries the declared precondition and modeled capability evidence.
- `CertifiedOutcome.postcondition` carries the declared postcondition for the exact invocation,
  result, and abstract successor state.
- `ToolCatalog.signature` preserves those dependencies when adapting a verified tool to the
  generic API.
- A successful `ToolWire.validate` returns an `AuthorizedCall` whose exact operation, decoded
  input, precondition, and required-capability evidence survived the checked boundary.
- `ToolWire.decode_encoded_result` and `decode_encoded_certified_result` prove one-way
  `Lean.Json` AST round trips for the selected request's failure/output type.
- `Decision.tighten` has proved deny-absorbing, allow-identity, commutative, associative, and
  idempotent laws.

These are anti-confusion and contract-carrying results. They do not prove that the declared
precondition, capabilities, postcondition, or abstract `Model` faithfully describe the outside
world.

### Exact-subject policy traces

- `SubjectPolicyState` retains the same exact subject through proposal, decision, dispatch, and
  subject-indexed settlement.
- `SubjectPolicyTransition.denied_cannot_dispatch` proves there is no dispatch constructor from
  a denied state, while `dispatched_lease_absent` proves dispatch consumed that subject's exact
  call-ID lease in the returned pool.
- `SubjectPolicyTrace.dispatchCount_le_one` and `cannot_dispatch_twice` prove at-most-once
  dispatch along one explicitly threaded trace.
- `dispatchCount_to_completed` proves that a trace from proposal to a completed result crosses
  dispatch exactly once, and `denied_dispatchCount_eq_zero` proves that a trace starting denied
  has no dispatch edge.

These are path properties of a pure indexed value. Lean values, including pre-consumption lease
pools and policy states, can be duplicated. The theorems do not provide global exactly-once
execution, atomic mutation, mutual exclusion between workers, persistence, or retry safety.

### Session protocol

- Typed `Event` constructors make the six encoded phase transitions intrinsic.
- `Event.preservesWellFormed` and `Trace.preservesWellFormed` preserve duplicate-free pending
  identifiers for typed transitions.
- `Event.noOrphanResult` proves that a typed result names a call pending in its predecessor.
- `applyRaw_eraseEvent` and `replayRaw_eraseTrace` prove that erasing a typed execution is
  accepted by the Lean runtime validator at its statically known endpoint.
- `validateEvent` and `validateTrace` reconstruct intrinsic witnesses tied by `erase_eq` to the
  exact raw event or list they accepted.
- `ValidatedEvent.applies` and `ValidatedTrace.replays` prove those reconstructed witnesses are
  accepted by `applyRaw`/`replayRaw` at their intrinsic endpoints.
- `Trace.erase_append` proves that typed trace composition erases to list append.

These are properties of `Cordis.RuntimeEvent`, not of the complete, merge-extensible Harness
event union or its persistence backend.

### Local lifecycle

- The `Transition` indices permit only the encoded local phase edges.
- `State.inactive` retains a modeled current state; the `unload` constructor's endpoint is
  exactly `.inactive origin outcome`.
- Each `iterate` transition extends the indexed undo stack with one witnessed `Effect`.
- `Transition.unload_recovers` proves exact recovery of the activation origin for the local
  stack carried by an `unload` constructor.
- `Transition.unload_rejects_relied` proves that the supplied withdrawal guard contradicts
  supplied evidence of an installed, relying consumer in the supplied consumer list.
- `Transition.active_successor_keeps_view` proves that leaving `active` retains exactly the same
  committed view and undo stack in `unloading`.

These are local constructor facts. They are not the paper's multi-fiber preservation, recovery,
ordering, resolution-coherence, progress, or confluence theorems.

### JSON AST codecs

- Every `Codec` carries `decode (encode value) = .ok value`.
- The unit, Boolean, string, natural-number, product, and list codecs discharge that theorem.
- Nested product and list errors preserve array-index paths.

The theorem begins and ends with `Lean.Json`. It is neither a parser theorem nor a JSON Schema
theorem.

### Bounded text streams

- Typed `Stream.Chunk` values consume one explicit text-chunk budget unit and cannot start from
  a finished state.
- `Stream.replayRaw_eraseTrace` proves the local raw mirror accepts every erased typed stream at
  its indexed endpoint.
- `Stream.replay_completeTrace` proves that the deterministic finite text trace finishes with
  the exact left-to-right concatenation of its source strings.
- The executable validator rejects budget exhaustion, text after finish, and double finish.

This is a `String`-level model with only text and finish messages. It is not the pinned
Harness's richer [block/reasoning/tool-call/usage stream protocol][harness-llm-stream] and does
not cover byte decoding, token indexes, network transport, provider exceptions, cancellation,
or persistence.

### Deterministic local Harness records

- Every `Harness.RunnerState` carries `replayProof`, showing that its log over the local
  six-variant event vocabulary replays from `.ready 0` to its stored local protocol state.
- `Harness.CallEvidence` retains either the exact failed admission equation or the exact
  admitted dependent call, provider completion, execution equation, lease issue, and
  exact-subject policy trace for that call.
- For admitted provider successes, `CallEvidence.encodedResult` uses the operation and request
  retained by the dependent call; the `ToolWire` codec theorem proves the resulting AST decodes
  to that exact result.
- `Harness.CallBoundary` and `callBoundaries` project the in-memory runtime log to its ordered
  call/result IDs, while `recordBoundaries` produces one exact adjacent call/result pair for
  every audit record.
- The six-index `Harness.RecordChain` jointly threads the initial model, next numeric call ID,
  records, final model, final lease pool, and boundary projection. Each appended record starts
  at the preceding modeled successor and lease pool and contributes its next ID and exact
  call/result pair.
- `RecordChain.length_eq_nextCall`, `RecordChain.ids_eq_range`,
  `RecordChain.boundaries_eq_records`, and `RecordChain.leases_threaded` prove the corresponding
  record count, ordered ID range, boundary equality, and lease continuity from
  `LeasePool.empty` to the indexed final pool.
- `RunnerState.history` specializes that chain to `RunnerState.leases` and
  `callBoundaries RunnerState.log`. The public `RunnerState.callBoundaries_eq_records` and
  `RunnerState.leases_threaded` theorems expose those two correspondences directly.
- `RunnerState.dispatch` explicitly constructs an allow/dispatch/settle policy trace for each
  admitted call. Rejected admissions still receive a matching local result event but have no
  admitted subject and no dispatch trace.
- Structural turn/step events use the private `emitNonBoundary` helper, which requires proof
  that an event is not a call boundary. The private settlement helper returns the call event,
  result event, appended record, successor model and lease pool, and extended certificates in
  one new `RunnerState`; it exposes no intermediate state containing only a call.

These facts are one joint invariant of the pure local state: replay fixes the protocol endpoint,
while `history` fixes the model/ID/record/lease chain and the log's call/result projection.
Settlement is atomic only in the sense that one pure Lean result contains all those updates.
It is not an external transaction and does not make tool side effects, storage, or retries
atomic.

The reusable `GenericHarness.Runner` is catalog-generic, while the executable
`Cordis.Harness` wrapper and demo remain pure, deterministic, sequential,
counter-specific, and credential-free. Neither is the TypeScript Harness, and
neither proves asynchronous scheduling, real tool `IO`, approval flow,
cancellation, persistence, or crash behavior.

## What is checked but not proved

Executable rejection is valuable, but it is not a refinement theorem.

| Boundary                                     | Check performed                                                                                                                                                                                                                                                                                                                        | Missing theorem or guarantee                                                                                                                                                                                                                                                                                                     |
| -------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Codec.decode`                               | Rejects JSON AST constructors or lengths outside each decoder's accepted shape.                                                                                                                                                                                                                                                        | No proof that accepted values are exactly the values denoted by `schema`, and no completeness result for arbitrary JSON.                                                                                                                                                                                                         |
| `ToolWire.validate`                          | Resolves a name, checks declaration, decodes the selected input, and requires `certifyAdmission` evidence before returning a dependent call.                                                                                                                                                                                           | The supplied resolver, codecs, propositions, capability source, and admission procedure are not proved equivalent to a deployed registry or authenticated policy.                                                                                                                                                                |
| `Protocol.validateEvent` / `validateTrace`   | Checks the six local event variants and returns exact intrinsic witnesses for successful inputs.                                                                                                                                                                                                                                       | No translation or equivalence to the full Harness event union; no theorem equates every successful erased `replayRaw` call with witness reconstruction.                                                                                                                                                                          |
| `Stream.applyRaw`                            | Checks one text/finish protocol, explicit chunk budget, and terminal-state discipline.                                                                                                                                                                                                                                                 | No witness reconstruction for arbitrary accepted raw streams and no equivalence to Harness `StreamChunk` assembly or persistence.                                                                                                                                                                                                |
| `RuntimeRefinement.validateJsonTrace`        | Decodes a supported current-Harness stream JSON-AST subset, then returns an exact intrinsic `RichStream.ValidatedTrace` or a separated decode/semantic error.                                                                                                                                                                          | No byte parser, full stream-union coverage, tolerant-assembler completeness, transport, storage, or whole-runtime equivalence.                                                                                                                                                                                                   |
| `SessionRefinement.validateJsonLog`          | Stateful supported-subset decoding returns exact rich append and intrinsic protocol witnesses, fresh local call-ID evidence, and a cumulative projection theorem.                                                                                                                                                                      | No complete event union, replacement translation, persisted JSONL parser, timestamp truth, crash recovery, or whole-session equivalence.                                                                                                                                                                                         |
| `UnifiedContext` constructors                | Enforce dependent realm/provider types, derived-parent indices, finite unfolding depth, and witnessed local recovery.                                                                                                                                                                                                                  | No imperative alias identity, recursive fixed point, tenant sandbox, middleware execution, or runtime refinement.                                                                                                                                                                                                                |
| `Coeffect.Observational.Related`             | Makes presence/absence mismatches unconstructible and packages supplied key relations as a finite-context `Setoid`.                                                                                                                                                                                                                    | The key relations are supplied; operational tests can replace them only under the separately documented laws.                                                                                                                                                                                                                    |
| `OperationalEquivalence` / `QuotientEffect`  | Checks finite partial test words and certifies finite quotient-respecting effect programs; the paired-inverse counterexample is kernel-checked.                                                                                                                                                                                        | Universal test equivalence is not decidable here; the stronger paired law needs a premise, and this layer alone does not prove mediated independence.                                                                                                                                                                            |
| `Transformation` / `OperationIndependence`   | Constructs exact generated monoids, promotes full inverse/outcome stability, checks finite distinct-key words, and interprets outcome-mediated computations.                                                                                                                                                                           | Partial words are finite syntax, not abstract Kleisli monoids; the next row's whole-run closure does not supply the full computation transformation monoid.                                                                                                                                                                      |
| `Removal`                                    | Builds indexed original/omitted finite traces with exact later inverse equalities and checks arbitrary permutations of the retained inverse list.                                                                                                                                                                                      | Exact pure effects only; no observational quotient, infinite family, asynchronous runtime, or real external recovery.                                                                                                                                                                                                            |
| `MediatedIndependence`                       | Reifies selected branches, states quotient closure, bridges it to exact closure under representative coherence, and checks a finite exact-representative counterexample.                                                                                                                                                               | Its old individual-domain `PairwiseOverlapComplete` is false for partial computation versus unit; the next row supplies the corrected bounded theorem.                                                                                                                                                                           |
| `MediatedTheorem`                            | Corrects composite partial domains and constructively swaps arbitrary finite outcome-selected trees with exact after/undo and conditional inverse stability, then derives the observational form.                                                                                                                                      | Finite whole-run analogue only; old `PairwiseOverlapComplete` is false for partial unit, and the next row proves the stronger partial monoid result.                                                                                                                                                                             |
| `PartialTransformation`                      | Builds the complete partial forward/actual-yielded-inverse Kleisli closures and proves all cross transformations commute plus success-conditional domain/inverse stability.                                                                                                                                                            | Full finite exact partial D17/D19/T42 analogue; not the paper's literal total/quotient, external, asynchronous, or infinite setting.                                                                                                                                                                                             |
| `ObservationalPartialTransformation`         | Proves adaptive computation generators respect the finite context relation and descends exact closure independence to domain-sensitive related partial maps; checks a generic respect counterexample.                                                                                                                                  | Finite observational partial/Kleisli analogue under exact `PairwiseOverlap`; not quotient-only operation independence or the paper's unrestricted total setting.                                                                                                                                                                 |
| `GlobalRegistry`                             | Checks code-only component/fiber/global data, unique providers/targets, birth-ranked acyclicity, and preservation by insert/retire/remove orchestration.                                                                                                                                                                               | Uses a strengthened parent invariant and noncomputable derived views; no code interpreter, read confinement, lifecycle rules, or full Theorem 59.                                                                                                                                                                                |
| `GlobalDynamics`                             | Interprets opaque codes externally and reconstructs ordinary/registration steps, recovery, confinement/read/WF evidence, and fueled traces with explicit exhaustion.                                                                                                                                                                   | Most laws are integrator obligations; phase updates and unload policy are handled only by the next bounded layer.                                                                                                                                                                                                                |
| `GlobalLifecycle`                            | Checks exact target/phase guards, executed landings, inertia, unload recovery, all-edge WF preservation, and finite lifecycle traces.                                                                                                                                                                                                  | Orchestration remains separate; general `RecoveryAdmission` is supplied, oracle rejection has no lifecycle edge, and full Definition 53/Theorem 59 are unclaimed.                                                                                                                                                                |
| `GlobalCalculus`                             | Unifies orchestration/lifecycle endpoints under ten rule names, retains acted-on names, separates state maps from edits, proves installation-boundary semantics, and packages empty-origin traces.                                                                                                                                     | Finite sequential Definition 53 model; general recovery is admitted, oracle rejection remains absent, and full Theorem 59 is unclaimed.                                                                                                                                                                                          |
| `GlobalTraceFacts`                           | Proves non-unload foreign exactness, conditional unload table/control/static continuity, aligned name-specific episodes, and a kernel bare-admission countermodel.                                                                                                                                                                     | Bounded existing-fiber Lemma 54 fragments; new-entry/retire-write provenance and remaining global metatheory are unproved.                                                                                                                                                                                                       |
| `GlobalTemporal`                             | Reifies fallible off-source step maps and proves per-step commutation composes to finite relation-indexed recovery with explicit inverse/reorder/unload certificates.                                                                                                                                                                  | Parameterized T61/Cor62 algebra only; the next row supplies a D60-to-per-step bridge, while canonical `≈`, totality, continuation stability, and arbitrary trace reordering remain absent.                                                                                                                                       |
| `GlobalIteratorIndependence`                 | Generates oracle-specific reachable partial forwards and actually yielded totalized inverses, promotes exact generator laws through the closures, descends to `EffectEquiv` only with supplied forward-map respect, exposes occurrence-indexed family independence, and derives `PerStepCommutes` from explicit provenance/membership. | Partial/Kleisli Definition 60 analogue only. The oracle is fixed; finite reach/bounds are separate certificate types; `ProgramRespects` is supplied while only inverse respect follows from `EffectEquiv`; effect observation is not rule `≃`; totalization, owner inversion, reordering, T61, and Corollary 62 are not derived. |
| `GlobalTransposition`                        | Given `Independent`, constructs raw off-axis executions/common endpoint and exact commutation for two supplied totalized closure-member pre-edit maps; given `ObservationalIndependent`, proves the effect-relational square while retaining separate `ProgramRespects`; also separates exact lifecycle codes and phase edits.         | Bounded ingredients toward Lemma 71 only. `GlobalTransposition` itself constructs no phase-frame inhabitant; semantic inverse equality is weaker than stored-code equality; no guard/target preservation, edited endpoint square, or lifecycle transition swap is proved.                                                        |
| `GlobalForeignPhase`                         | From explicit readability, ordinary exact-successor, and same-child oracle laws, derives exact strong-yield compatibility; combines two such certificates with independence into a framed raw diamond retaining the actual post-raw fibers; kernel-separates all three premises.                                                       | Lower contracts, distinct owners, reach/execution, post-raw fiber lookups, and typed phases are supplied. No `Transition`/`Step`, guard/target preservation, lifecycle phase provenance, Lemma 71 exchange, or mixed-trace reorder theorem.                                                                                      |
| `GlobalLandingTransposition`                 | Adds exact cross-forward yield syntax and fixed-program landing provenance, derives foreign positive-target preservation from WF, reframes off-axis landings, and constructs actual L-Iter/L-Finish transitions in both orders with one exact final state; includes positive and necessity models.                                     | Landing-only four-pair theorem. Requires WF, distinct owners, exact cross-forward stability, both phase compatibilities, and common-source program-aligned activations. No Begin pair, trace-step identity, episode assignment, or full Lemma 71.                                                                                |
| `GlobalActivationTransposition`              | Adds root-aligned Begin, exact foreign lookup/positive-target framing, fixed-program endpoint/rule determinism, all nine common-source Begin/Iter/Finish diamonds, and an actual-second-step swapped transition; includes branch and necessity witnesses.                                                                              | Partial fixed-oracle Lemma 71(1) analogue. Requires WF, distinct owners, common applicability, explicit provenance, and branch-relevant frame/exact-yield laws. No orchestration clause (2), arbitrary stored-trace rewrite, episode assignment, literal total/quotient Lemma 71, or confluence.                                 |
| `GlobalActivationOrchestrationTransposition` | Kernel-refutes the literal clause-(2) child condition, classifies registration, derives legal early orchestration/positive targets, and proves an occurrence-framed exact exchange with the same template and endpoint; includes birth/frame gaps and structural/ordinary/registering examples.                                        | Corrected partial fixed-oracle Lemma 71(2) analogue. Registering×Insert is excluded, frames are supplied, and the parent countermodel is compact structural evidence. No birth-erasing quotient, arbitrary stored-trace rewrite, literal paper clause, Lemma 72, or confluence.                                                  |
| `GlobalTraceRewrite`                         | Locates exact dependent two-step windows, identifies actual fixed-program activation/orchestration occurrences, splices the corrected transposition through retained context, and reconstructs the occurrence-indexed assignment ledger; rules and actors are adjacent permutations.                                                   | Exact stored-trace consequence of the bounded corrected Lemma 71 analogues. It does not derive occurrence laws, admit registering×Insert, weaken endpoints to a birth-erased relation, simulate arbitrary suffixes, normalize traces, delete vestiges, or prove Lemma 72/confluence.                                             |
| `GlobalDeletion`                             | Builds intrinsic relation-indexed keep/drop replay and output assignments; exactly replays safe foreign orchestration suffixes after finite already-vestigial families; kernel-checks parent, redraw, clock, and surviving-birth obstructions.                                                                                         | Bounded deletion substrate below Lemma 72. It does not delete a general lifecycle episode, derive provenance or no-redraw, simulate lifecycle suffixes, define a birth-erased relation, normalize traces, or prove Lemma 72/Theorem 73/confluence.                                                                               |
| `GlobalPaperRelation`                        | Erases allocator clock/birth from current rule observation, proves full/outside/deletion Setoids and strict bridges, reconstructs orchestration bidirectionally between two WF full-domain states, and from a WF source with `VestigialNames` gives directional safe deleted-shadow replay.                                            | Finite structural paper-relation slice. No one-sided WF transport, outside bisimulation, lifecycle simulation, name quotient, relation-aware activation swap, general episode deletion, Lemma 72, normalization, or confluence.                                                                                                  |
| `GlobalProgress`                             | Separates fixed-program oracle rejection from raw oracle-existential applicability, kernel-refutes raw progress under finite-name exhaustion, and proves state-local no-deadlock from explicit finite precedence, current execution/recovery readiness, and committed-provider soundness.                                              | Corrected conditional no-deadlock fragment of Theorem 66. Printed assumptions omit admission/freshness totality. No quantitative bound, target-turn finiteness, maximal termination, fairness, trace program assignment, support, deletion, or confluence.                                                                       |
| `GlobalSupport`                              | Kernel-refutes combined support order from separate acyclicity, defines the unique support predicate by edge-indexed well-founded recursion, and proves corrected support-equals-active under state-local provision totality, no failure, and active-parent closure; includes independent necessity models.                            | Corrected local Definitions 67/69 and Lemmas 68/70 analogues. Combined order and parent closure are supplied rather than trace-derived; totality is state-local. No component-wide provenance, deletion, canonical form, or confluence.                                                                                          |
| `GlobalRelations`                            | Defines key-indexed rule observation and ambient/table effect observation as setoids, bridges respectful undo to the temporal interface, and separates the candidates by executable models.                                                                                                                                            | Finite Equation 53/Lemmas 55–57 candidates only; rule bisimulation, name-action laws, and the full global lemmas remain unproved.                                                                                                                                                                                                |
| `GlobalRuleInvariance`                       | Matches every well-formed insert/retire/remove step bidirectionally across rule-related states with exact peer endpoints and related well-formed successors, without equating tables.                                                                                                                                                  | Orchestration-only L55 fragment; ambient-sensitive inertia is a checked lifecycle obstruction and further dynamics/recovery laws are absent.                                                                                                                                                                                     |
| `GlobalRuleObservations`                     | Transports provider identity, dependent targets, committed resolution, reliance, phases, quiescence, and all structural lifecycle guards across well-formed rule-related states.                                                                                                                                                       | Assumption-free L55 observation substrate; it executes no lifecycle step and leaves landing/error/inertia/oracle/recovery contracts explicit.                                                                                                                                                                                    |
| `GlobalLifecycleBisimulation`                | Under noncircular landing, run-error, inertia, and recovery-admission contracts, matches all lifecycle/unified rules bidirectionally with exact valid related endpoints.                                                                                                                                                               | Conditional well-formed L55 analogue; external contracts are supplied, raw no-WF bisimulation is uninhabited, and Finish requires related yielded tables.                                                                                                                                                                        |
| `GlobalNameAction`                           | Defines executable bijections over all stored payloads, canonical dependent state action, identity/composition/inverse, WF equivalence, and exact bidirectional orchestration equivariance.                                                                                                                                            | Structural/orchestration L56 fragment; catalog entry, dynamics, oracle, recovery, inertia, and lifecycle action laws remain separate.                                                                                                                                                                                            |
| `GlobalNameLifecycle`                        | From exact dynamics/inertia/catalog-entry action laws, derives registration, oracle, execution, landing, recovery, lifecycle, inverse, and unified name actions with exact endpoints.                                                                                                                                                  | Conditional well-formed fixed-catalog L56 analogue; primitive semantic laws are supplied and arbitrary base Dynamics is not automatically equivariant.                                                                                                                                                                           |
| `GlobalVestigial`                            | Proves vestigial removal effect-equivalent and gives exact bidirectional orchestration removal squares under all kernel-necessary exceptions, with well-formed countermodels.                                                                                                                                                          | Corrected L57 orchestration fragment only; pinned clauses omit parent adoption/removal, and iterator/lifecycle/oracle/inertia/recovery insensitivity is unproved.                                                                                                                                                                |
| `GlobalSpatial`                              | Proves dependency provision, explicit nested episode order, committed resolution/no-unload propagation, conditional table constancy, and local reloading-step classification.                                                                                                                                                          | Finite T63/T64 fragments only; nesting/maximality, same-owner confinement, initial intervals, eventual close, and recovery conclusions remain premises or absent.                                                                                                                                                                |
| `CertifiedTwoBatch`                          | Requires same-successor, pointwise same-recovery, and result-stability certificate fields before either order is permitted.                                                                                                                                                                                                            | The certificate is supplied, exactly two pure calls are modeled, and no actual concurrency or external-effect safety follows.                                                                                                                                                                                                    |
| `ParallelHarness`                            | Requires finite task IDs/modes, effect commutation, and result-permutation certificates; proves model-order commit, one exclusive barrier, and a no-effect cancellation drain.                                                                                                                                                         | The bounded proof-carrying scheduler slice is pure and finite; no promise races, cleanup, fairness, persistence, or TypeScript equivalence follows.                                                                                                                                                                              |
| `DurableSettlement`                          | Requires an indexed pure effect specification; proves frame/entry length and projection, exact newest-first recovery, supplied crash-prefix decomposition, and typed resume.                                                                                                                                                           | The transcript digest is a collision-free Lean list, and the crash cut is supplied as a proof. No bytes-on-disk, fsync, cryptographic authentication, process coordination, or external exactly-once behavior follows.                                                                                                           |
| `Registry.setAt`                             | Uses dependent equality transport so a value cannot be installed at a differently typed key.                                                                                                                                                                                                                                           | No runtime aliasing, notification, or mutable-store semantics are modeled.                                                                                                                                                                                                                                                       |
| `View.resolve`                               | Requires `needs op` before a binding can be requested.                                                                                                                                                                                                                                                                                 | Construction of the view and completeness of its registry snapshot remain obligations.                                                                                                                                                                                                                                           |
| `ToolSpec.Invocation`                        | Requires proof fields before dispatch through the dependent API.                                                                                                                                                                                                                                                                       | The origin and adequacy of the propositions are not certified by the structure itself.                                                                                                                                                                                                                                           |
| `EmissionClass`                              | Records a classification.                                                                                                                                                                                                                                                                                                              | No behavior is enforced from the label.                                                                                                                                                                                                                                                                                          |
| `Lifecycle.Withdrawable`                     | Quantifies over a supplied finite list of supplied consumer records.                                                                                                                                                                                                                                                                   | The list is not proved to enumerate a live registry, and its Boolean `installed` fields are not linked to lifecycle states.                                                                                                                                                                                                      |
| `Harness.RunnerState`                        | Sequential reference functions construct `replayProof` and a six-index `RecordChain` tying model history, IDs, records, final leases, and `callBoundaries log`; public theorems expose boundary/record equality and lease threading.                                                                                                   | The boundary projection erases coordinates and has no full Harness translation; there is no refinement to TypeScript Harness, real I/O, parallel scheduling, durable storage, or crash recovery.                                                                                                                                 |

When an adapter such as `ToolWire` is used, textual resolution, decoding, and admission can
fail closed before an `AuthorizedCall` is constructed. The adapter still supplies its resolver,
codecs, decidability procedures, and proof-producing `certifyAdmission` implementation. Its
existence does not prove correspondence to a deployed Harness registry.

## Trusted base and assumptions

### Lean foundations and build

The proof claims trust the Lean 4 kernel, elaborator output presented to the kernel, compiler,
and imported Lean/Std definitions. The mapped modules introduce no custom `axiom` declaration,
but “Proved” should not be read as constructively axiom-free: standard Lean developments may
depend on principles such as proposition extensionality, quotient soundness, and classical
choice. A `#print axioms` report states dependencies of a selected declaration; it does not
validate an external runtime.

The source also has to be in the build and public-import surface actually shipped. A theorem in
an unimported module remains a valid Lean theorem, but it is not evidence that a particular demo,
binary, test target, or TypeScript adapter used it.

At the documented HEAD, `Cordis.lean` imports the mapped proof, adapter, example, and local
Harness modules; `Tests.lean` runs `Cordis.TestSuite.run`; and the separate default
`CordisStaticTests` target elaborates guarded expected failures in `Cordis/NegativeTests.lean`.
Those facts establish the current Lean build surface and finite executable/static checks, not
deployment or upstream interoperability. `Cordis/AxiomAudit.lean` runs `#print axioms` for 882
selected declarations; its report is scoped to that list and does not validate the compiler,
runtime, or external systems. The pinned CI workflow additionally applies a lexical source policy
and allow-list parser, both of which remain trusted automation rather than kernel theorems.

### JSON, text, and transport

The following remain trusted or outside scope:

- parsing bytes or text into `Lean.Json`;
- rendering `Lean.Json` back to text;
- UTF encoding, framing, network transport, storage, and replay;
- correspondence between `Codec.schema` and a particular JSON Schema dialect or validator;
- the model following a schema merely because it was shown one; and
- equality between a Harness raw argument string and a Lean AST after parse/render cycles.

`Codec.schema` is metadata. No field states that `encode value` satisfies it or that every AST
satisfying it decodes.

### Abstract state versus the world

`Effect State`, `ToolSpec Model Capability`, and the registry operate over types chosen by the
integrator. Their proofs cover only facts represented in those types.

`CertifiedTwoBatch` additionally assumes a proof that two modeled effects have equal successors,
pointwise-equal composed recovery functions, and stable pure results. That certificate does not
authorize parallel execution of files, processes, databases, HTTP calls, or any other real
effects.

For a file write, process launch, database transaction, HTTP request, email, or credential use,
the integrator must separately establish that:

1. the abstract `before` accurately represents the relevant external state;
2. execution changes the world as the abstract successor claims;
3. the captured inverse or compensation is executable and has the proved abstract meaning;
4. failures, retries, cancellation, and concurrent observers are represented; and
5. irreversible emissions are either forbidden by policy or intentionally accepted.

`EmissionClass.externalIdempotent`, `.compensatable`, and `.irreversible` are labels, not proofs
of those properties. `Applied.undo_after` cannot make an email unsent or an unmodeled network
observer forget a request.

### Capabilities and provider identity

`Authorized` quantifies over the caller-supplied `granted : Capability -> Prop`. A malicious or
mistaken integrator can choose `fun _ => True` and prove authorization trivially. A production
capability source must be tied to authenticated identity, scope, expiry, revocation, and the
actual operation performed.

`ProviderId` is ordinary data. Uniqueness, freshness, ownership, version compatibility, and
correspondence to a live implementation are not proved. `Binding.present` proves membership in
one pure `Registry` value, not continued liveness in a mutable process.

### Tool implementation and policy runtime

`VerifiedTool.execute` is a pure proof-producing function. A real I/O bridge is trusted until it
has a refinement proof that its observations and effects construct the claimed
`CertifiedOutcome` honestly.

The pinned Harness performs much more dynamically:

- `ToolDefinition.execute` is asynchronous and cancellation is cooperative; the source states
  that the registry cannot hard-kill same-process code ([tool contract][harness-tools]).
- Registry visibility includes scoped shadowing and restrictions; concurrency defaults to
  exclusive unless a classifier returns exactly `true`
  ([runtime view][harness-tools-view]).
- Pre-dispatch policy, approval, monotonic guards, around-dispatch wrappers, post-policy,
  output validation, and final materialization form an asynchronous pipeline
  ([execution pipeline][harness-tools-execute]).
- Dispatches may overlap while results commit in model order, with explicit abort and drain
  behavior ([tool scheduler][harness-tool-scheduler]).

The Lean `Decision` algebra proves none of those implementation facts, and the pinned
TypeScript source is evidence, not an imported or verified artifact.

The exact-subject policy lifecycle improves the local statement: an admitted subject remains
the same indexed value through settlement, and one threaded trace dispatches at most once. It
does not make `LeasePool` linear. Copying the same pure pre-consumption pool or state can create
two separately valid traces, so a production runner still needs atomic storage, idempotency,
mutual exclusion, and restart semantics.

The repository's local `Cordis.Harness` constructs one such allow/dispatch/settle trace for every
admitted counter call and retains its dependent completion. Its joint history also threads the
local record leases and equates record pairs with the in-memory log's boundary projection. This
is evidence about that pure Lean function only, not about the pinned TypeScript policy runtime
or an external exactly-once mechanism.

### Runtime registry and lifecycle

The paper's §5 implementation and the pinned CORDIS source dynamically resolve providers,
notify dependents, commit views, and await teardown. See the standalone
[`Fiber`][cordis-fiber] and [`ReflectService`][cordis-reflect], and the Harness
[vendor manifest][harness-vendor] for its locally hardened copy.

The new `GlobalRegistry` module moves a structural subset inward without interpreting code:

- state stores opaque component/iterator/undo codes, never a function over the enclosing
  `GlobalState`, so the negative recursive occurrence is not hidden;
- finite typed tables are confined to declared provision lists;
- active providers/values and committed targets are unique under strengthened well-formedness;
- parents are both present and strictly older, yielding a proved acyclic parent relation;
- explicit-freshness insert, unconditional retire, and retired/inactive/childless remove preserve
  the strengthened invariant over orchestration traces.

The birth-order field is stronger than paper Definition 58(1), because parent presence alone
permits cycles. `activeContext` and `targetView` use noncomputable unique choice over proof-finite
data; they are specifications, not extracted runtime algorithms. The combined ten-rule trace and
full preservation theorem remain outside this structural module.

`GlobalDynamics` then interprets those codes externally rather than putting functions back into
stored state. Its `Dynamics` contract makes ordinary recovery, undo/run respect, write
confinement, an owner-indexed read-equivalence law, well-formedness preservation, and retirement
respect explicit obligations. Registration admission separately supplies child freshness,
parent/provision legality, and observational vestigial recovery. `executeOne` reconstructs an
intrinsic certified step; the fueled runner retains continuation codes on exhaustion and carries
newest-first accumulated recovery plus trace-level well-formedness. Ambient mutation is
intentionally permitted, matching Definitions 45/48, and must be reversed by the supplied undo.
The older optional name-equivariance assumption is under-specified; `GlobalNameAction` replaces
its structural portion, while dynamics/lifecycle action laws remain separate.

`GlobalLifecycle` consumes those certified steps in exact phase-indexed transitions. Landing
constructors retain an oracle and the equation showing `executeOne` returned their step; the
registration-error type remains distinct from iterator errors. Abort permission is explicit,
L-Unload alone interprets accumulated recovery, and every lifecycle edge preserves strengthened
well-formedness. The general unload proof deliberately consumes `RecoveryAdmission`, because
arbitrary-interleaving temporal recovery is not yet derived. Orchestration is still a separate
relation, and an oracle-rejected registration request has no modeled lifecycle edge.

`GlobalCalculus` wraps both source relations without weakening their endpoints. Every step retains
the acted-on name from Definition 53, both diversion alternatives project to L-Divert, and the
Equation 51 state map is kept separate from insert/retire/remove or phase edits. The combined trace
preserves well-formedness from an explicitly empty registry, and constructor analysis proves the
actual installed predicate changes only at L-Begin and L-Unload. This is bounded sequential
preservation; it does not discharge the recovery admission or the remaining global metatheory.

`GlobalTraceFacts` makes the next condition explicit. `RecoveryConfinement` preserves every
pre-existing foreign table and control record and the actor's static fields during accumulated
recovery. All non-unload rules prove these facts without an extra premise. A finite countermodel
shows a bare `RecoveryAdmission` can instead change a foreign table while both endpoints remain
well formed. Under the stronger law, aligned per-name episodes propagate installation and
committed views and identify their opening/closing rules exactly. The law does not forbid opaque
recovery from adding a brand-new name and does not prove that each retirement came from
`UndoCode.retire`.

`GlobalTemporal` keeps the temporal assumptions separate. It re-executes an exact iterator
code/oracle pair to obtain a partial off-source state map, so totality must be certified rather
than inferred. A caller supplies an effect-relevant `Setoid` distinct from the arbitrary
`Dynamics.equivalence`, proves each step map total/respectful/edit-invisible, supplies per-step
recovery commutation, the owner's off-source inverse law, and the mixed-trace reorder relation.
Those certificates compose to finite interleaved and terminal unload recovery. Countermodels show
that an exact landing may fail off-source, a universal dynamics relation is vacuous for table
recovery, and `RecoveryConfinement` alone does not imply temporal exactness.

`GlobalIteratorIndependence` moves only the iterator-family certificate inward. A raw registration
request does not determine the chosen child, and that child controls both the continuation and
retirement inverse, so the registration oracle is deliberately part of each `Program`. `Reach`,
`YieldedAccumulator`, and `StepMapMember` retain successful-yield provenance, acted-owner equality,
and exact closure membership. `ProgramRespects` separately requires every reachable partial
forward to respect the selected effect relation; only yielded inverse respect is inherited from
`EffectEquiv.applyUndo_respects`. The observational bridge then turns an owner/foreign
`ObservationalIndependent` certificate into `GlobalTemporal.PerStepCommutes`, but only for a trace
whose steps already carry `TotalStepMap` witnesses. It neither equates effect observation with rule observation nor
supplies the remaining totality, inversion, or reordering premises of Theorem 61.

`GlobalTransposition` moves only the raw and pre-edit map squares inward. `Independent` constructs
both successful off-axis iterator executions, preserves their semantic yields, identifies their
raw successors, and gives exact commutation for two `TotalProgramStep`s. Each packaged step retains
supplied totality and acted-owner closure provenance. `ObservationalIndependent` gives the
`EffectEquiv` square; that certificate still includes separately supplied `ProgramRespects`.
Because lifecycle phases store codes, `LifecycleYieldAgrees` strengthens semantic inverse equality
with exact `UndoCode` equality; a finite identity-interpreter model proves that strengthening cannot
be inferred. Raw distinct-name phase updates commute, but this module constructs no
`ForeignPhaseCompatibility` inhabitant. That future contract requires fixed-oracle execution and
exact strong-yield stability across the foreign edit. No actual lifecycle endpoint is swapped.

`GlobalForeignPhase` gives that assumption-only contract a compositional constructor without
raising the proof level. `ForeignPhaseReadable` is what lets `run_read_confined` compare the two raw
runs. Its ordinary branch still needs an exact successor frame beyond the dynamics relation; its
registration branch still needs the fixed oracle to accept the moved request with the same child.
`of_read_frames` uses those three laws, deriving registration successor framing from request
equality, child freshness, and insertion/phase commutation. `phase_framed_diamond` combines two
derived or supplied compatibility certificates with the raw independent diamond and structural
phase commutation, retaining both actual post-raw owner lookups. Three finite models prove that
independence, readability, and raw request stability each omit one necessary fact. The supplied
phase payloads are arbitrary typed point updates, not claimed lifecycle-rule outputs.

`GlobalLandingTransposition` performs the first actual lifecycle lift, but only for common-source
L-Iter/L-Finish pairs. `ForwardLifecycleIndependent` adds the exact cross-forward `UndoCode`
stability that semantic Definition 60 independence lacks. `LandingProgramWitness` pins each bare
landing's stored step to the fixed program oracle. Exact foreign lookup preservation and source
well-formedness derive preservation of an already-valid target view; neither full target equality
nor `none`-target preservation is claimed. The theorem composes exact common-to-off-axis and
off-axis-to-phase-framed yields, reframes each moved landing from the common landing's fiber/control
template, and returns both real lifecycle orders with one shared exact final state. Separate models
kernel-check the cross-forward syntax gap, the common-applicability premise, and fixed-oracle
landing provenance.

`GlobalActivationTransposition` adds program-root-aligned Begin without broadening the landing
premises. A branch-indexed law record requires no iterator law for Begin/Begin, only the landing
program's foreign-phase compatibility for a mixed pair, and both compatibility certificates plus
`ForwardLifecycleIndependent` for a landing pair. Exact lookup and a non-active source actor derive
positive-target preservation. Fixed-program execution makes the endpoint and rule deterministic,
so `transpose_program_activations` can reconcile its constructed normal-order second activation
with any supplied actual second activation and derive the swapped lifecycle transition. This is a
partial fixed-oracle exact-representative analogue of Lemma 71(1), not clause (2), arbitrary trace
rewriting, episode assignment, or the paper theorem verbatim.

`GlobalActivationOrchestrationTransposition` shows why the remaining literal paper clause cannot
simply be copied. Registration may enable a distinct O-Insert parent, and opposite legal insertions
produce different exact birth assignments. The corrected API classifies the registered child,
excludes registering activation/O-Insert, and asks a landing for one occurrence-specific moved
fixed-oracle execution/yield/raw replay square. From the supplied normal orchestration occurrence it
derives the legal early step, positive target, moved activation, exact same-template evidence, and
normal final endpoint. Separate birth-clock and retirement-sensitive-oracle models prove neither
nonregistration nor registration safety derives the semantic frame. This is not literal Lemma
71(2), a birth-erasing relation, or a trace-rewrite theorem.

`GlobalProgress` exposes two further executable authorities omitted by printed Theorem 66.
Configured-program rejection can block a fixed landing even while the raw relation chooses another
oracle, and an exhausted Boolean carrier blocks every possible registration admission and every raw
lifecycle rule. The positive theorem therefore receives a finite provider-precedence rank,
committed-provider provision soundness, exact landing-or-raise readiness at each current reloading
fiber, and recovery readiness at each current unrelied unloading fiber. A maximal-rank unloading
argument proves state-local no-deadlock without aborting inertia. The module does not prove the
quantitative bound, target-turn finiteness, maximal termination, or fairness.

`GlobalSupport` records the next paper-level correction. A reachable two-insert state has
well-founded provider precedence and acyclic parent pointers but a cyclic union, so Definition 67
has distinct empty and present-name solutions. `SupportOrder` therefore supplies combined
well-foundedness directly, and `supported` uses edge-indexed recursion to obtain the unique
solution. `support_eq_active` additionally requires state-local provision totality, failure
exclusion, and active-parent closure. An independent model with a retired parent and active child
proves that parent closure is not implied by current well-formedness/quiescence. No trace provenance
or component-wide totality is inferred.

`GlobalTraceRewrite` closes the exact local-to-stored-trace bridge without broadening the
semantics. An `AdjacentOccurrence` owns an exact dependent before/window/after decomposition, and
the replacement pair has the same source and endpoint by type. `ProgramOccurrence` identifies the
actual stored lifecycle step with one fixed root-aligned program/oracle activation;
`TraceProgramAssignment` is supplied occurrence-indexed evidence rather than inferred from a bare
transition. Both corrected semantic adapters return assignments for their moved steps, so the
complete rewritten ledger is reconstructed. The retained example has a nonempty O-Insert prefix
and proves the exact projection `[O-Insert, O-Insert, L-Begin]` with actors `[0, 1, 0]`.

The exact endpoint requirement is intentional. A birth-erased local endpoint cannot be attached to
an existing suffix whose source is the old exact state; that future relation needs a separate
suffix-simulation or bisimulation theorem. No such theorem, arbitrary normalization, deletion, or
confluence result is claimed here.

`GlobalDeletion` makes the next boundary constructive without claiming the paper theorem.
`DeletionReplay` consumes source occurrences positionally and constructs the shadow trace through
local keep/drop evidence; same rule/actor is supplemented by a real assignment transport for each
retained occurrence. The output relation, rule/actor sublists, alignment, lengths, decisions, and
assignment are derived. Separately, a finite family already proved vestigial admits an exact
same-template replay of every safe foreign orchestration suffix after ordered removal.

The counterexamples are part of the trusted claim boundary: deleting a parent can make a
well-formed trace unreplayable and its final state malformed; removing the newly inserted entry
does not restore the allocation clock; changing insertion order changes surviving birth ranks; and
a removed name may be redrawn. The module defines semantic no-redraw and vestigial-or-absent
vocabulary. It proves no general lifecycle episode projection, lifecycle/oracle/recovery suffix
matching, birth-erased
outside relation, Lemma 72, normalization, or confluence.

`GlobalPaperRelation` supplies that missing finite outside relation without overstating it.
Relative to current `RuleRelated`, it erases only `nextBirth` and `Fiber.birth`; all control
already observed by the strict relation remains. Opposite insertion endpoints become related,
while exact equality and current rule relation still fail. With independent well-formedness on
both sources, the module reconstructs actual peer O-Insert/O-Retire/O-Remove steps in both
directions and derives assignment-preserving retained replay. Finite vestigial removal satisfies
combined effect/outside control, and safe orchestration traces replay directionally from a
well-formed source carrying a `VestigialNames` certificate to the erased shadow.

The outside relation is only a symmetric observation Setoid, not an operational bisimulation.
Existing parent, redraw, provision, and parent-removal countermodels block the reverse theorem.
Lifecycle behavior remains external: a clock-sensitive related pair has an actual L-DivertAbort on
one side and no same-lifecycle-rule peer on the other, proving no nonempty assigned lifecycle
simulation bundle exists for that instance.

`GlobalRelations` then makes the two observation interfaces concrete without identifying them.
`RuleRelated` observes the derived coeffect context through supplied key-indexed setoids and keeps
the registry domain, fiber control, and local birth clock exactly. `EffectRelated` instead keeps
ambient state and every normalized table lookup exactly while forgetting lifecycle control and
identifying an absent fiber with a vestigial empty table. Both are proved equivalence relations.
`EffectUndoRespect` is still a supplied semantic law before this effect relation can instantiate
the temporal recovery interface, and `RuleBisimulation` names—rather than proves—the missing rule
simulation obligation. Kernel examples establish both incomparability directions and separate the
arbitrary dynamics relation from the effect candidate.

`GlobalRuleInvariance` proves the complete bidirectional result for the three orchestration
constructors over well-formed sources. `FiberMatch` retains registry presence and exact control
equality while deliberately allowing unequal tables. Active-value equivalences show that inactive
insertion, retirement, and removal of a noninstalled fiber leave each side's active context exact;
the predecessor context relation then supplies observational successor values. Matched steps keep
kind, acted name, exact dependent endpoint, endpoint well-formedness, and `RuleRelated`. A
heterogeneous example uses unequal parity-related naturals and length-related strings. Full
lifecycle Lemma 55 remains false for the current interface: a well-formed ambient-only state change
is invisible to `RuleRelated` but can flip `InertiaPolicy.canAbort`.

`GlobalRuleObservations` isolates everything the relation itself can prove for lifecycle rules.
Same-name active-provider identity yields transported dependent target views; exact controls yield
committed resolution, reliance, non-reliance, and phase-pattern equivalences. Together these give
quiescence and bidirectional availability of begin, reloading-target, leave, divert, and unload
structural guards. Matched active tables are only pointwise related. A reloading owner's table is
not observed, so a future Finish landing contract must separately relate the newly active tables.
Concrete models show `RuleRelated` neither implies `EffectRelated` nor ambient equality, and
`EffectRelated` can forget registry data required by rules.

`GlobalLifecycleBisimulation` makes the remaining semantic authority explicit. `LandingTransport`
supplies a real peer landing, equal undo and continuation codes, related landing endpoints, and a
related-table witness only when the landing finishes. `RunErrorTransport` preserves the exact raw
error; inertia respect preserves abortability; `RecoveryAdmissionTransport` supplies a peer unload
admission with related final endpoints. No contract mentions a transition or step, so the theorem
is not circular. Those laws yield exact matches for all eight lifecycle constructors and combine
with orchestration into a well-formed ten-rule certificate. A kernel model starts from related
reloading states whose private tables have different parity and proves that activating them breaks
`RuleRelated`, so the Finish table clause cannot be dropped.

`GlobalNameAction` supplies a real structural nominal action. Because the project is Std-only, it
defines a minimal executable equivalence with forward/inverse proofs, then bundles one name
permutation with bijections on ambient data, each dependent value type, errors, iterator codes,
and external undo codes. The derived action renames parent pointers, committed providers, and
retirement undo names; reindexes the finite registry; and maps every phase/table payload. Exact
identity, composition, inverse, lookup, state recovery, strengthened well-formedness, edit
commutation, and orchestration-step equivariance are proved. A nonidentity Boolean example
exercises the full structure. The old assumption admits a constant noninjective name map under an
owner-insensitive dynamics, so its lone run equation cannot imply Lemma 56.

`GlobalNameLifecycle` keeps the external seam smaller than the delivered theorem. The primitive
record contains exact acted `runIterator` output—including errors and name-dependent registration
continuations—external-undo commutation, dynamics-equivalence invariance, inertia invariance, and
fixed catalog entries. Registration admissions, a conjugated oracle, proof-carrying iteration,
`executeOne`, Landing, accumulated recovery, target views, reliance, all lifecycle transitions,
inverse actions, and unified steps are derived. The theorem is restricted to well-formed sources
because target selection uses uniqueness. A nonidentity L-Raise renames owner and stored error;
counterexamples show why fixed entries and error-aware run action matter.

`GlobalVestigial` proves that the paper's exact vestigial witness—retired, successful inactive,
empty table, and no children—is `EffectRelated` to deleting its entry. For orchestration, the
theorem surface is corrected rather than copied. Forward simulation excludes insertion whose
parent is the vestigial name. Backward simulation excludes drawing that name, provision overlap,
and O-Remove of the vestigial fiber's own parent. Exact removal-square equations preserve rule
kind, acted name, and vestigiality. A well-formed three-name model proves all four exceptions are
real. The backward parent-removal example pinpoints a directional error in the pinned paper proof:
“no fiber has parent `n`” does not imply that `n` has no parent `m`.

`GlobalSpatial` consumes the exact trace facts without upgrading them to maximal episodes. A
well-formed L-Begin target satisfies every declared dependency. Two episodes obtain strict
provider/consumer boundary order only from `NestedEpisodes`, whose fields explicitly exhibit both
episodes inside one master-trace decomposition. Within a consumer's boundary-free interior,
sufficient confinement preserves its committed provider resolution, makes that provider `Relied`,
and rules out the provider's L-Unload. Table-value constancy needs `TraceTableConfinement` for each
record; foreign-actor confinement proves it only when the trace never acts on that provider. The
local reloading theorem classifies a single next lifecycle rule and deliberately says nothing
about eventual close or accumulated recovery.

The older finite `Cordis.Lifecycle` model separately assumes:

- inactive states retain the modeled recovered value, and `unload` returns specifically to the
  activation origin;
- the `Consumer` list is a complete and current snapshot;
- `installed : Bool` tells the truth;
- each `CommittedView.resolve` value denotes the intended provider;
- each pushed `Effect` models the complete state change;
- no relevant foreign transition occurs unless represented in the indexed model; and
- executing `UndoStack.recover` is the intended real recovery operation.

It does not model notification races, promises, cleanup exceptions, re-entrant disposal,
fairness, dynamic consumer insertion, a changing consumer snapshot, or global orchestration.
Retaining the recovered inactive model closes the local endpoint ambiguity; it does not supply
the paper's multi-fiber registry or interleaving theorem.

### Session log and durability

The pinned Harness's `Session.append` checks lossless JSON and surface structure, snapshots and
freezes the event, appends it, then notifies observers
([append implementation][harness-session-append]). Its turn/step/call relational checks live in
an optional companion that must be loaded
([session invariant][harness-session-invariant]). Persistence and per-request checkpoints are
separate services.

Consequently:

- a Lean `RuntimeEvent` is not a Harness `SessionEvent`;
- `validateTrace` reconstructs an intrinsic witness only for Lean's six local event variants;
- `ValidatedTrace.replays` and `replayRaw_eraseTrace` are not storage or crash-recovery
  theorems;
- `RunnerState.callBoundaries_eq_records` covers only the call/result-ID projection of one
  in-memory local log; it is not a persistence, payload, or external-effect theorem;
- the separate rich `Session.ValidLog` does prove in-memory sequence continuity, surface
  provenance, and reconstruction, but not timestamps, observer containment, flushes, or durable
  writes;
- `DurableSettlement` adds a separate typed crash-prefix/resume model, but its `CrashPrefix` is
  a supplied certificate over an intrinsically valid log rather than an arbitrary persisted-file
  parser or repair algorithm;
- Lean's step numbering and pending-call rules differ from the pinned companion; and
- the optional companion being present in source does not prove it is loaded in a deployment.

### CORDIS and Harness source pins

This project does not compile, import, or verify the TypeScript repositories. The pinned source
links make the comparison reproducible, but source inspection is still a **checked/reference**
activity, not a Lean proof.

The Harness vendor manifest pins upstream CORDIS
`56b3d4f725681cf4556c1a8695a709cc3b6eed74` and records local modifications. The separate
standalone architecture pin is `8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4`. No compatibility
claim is inferred between them.

## Claims this project must not make

Without additional proofs or tests, do not state that:

- CORDIS Lean formalizes the entire paper;
- `setEffect_commute` or `CertifiedTwoBatch.execute_order_irrelevant` proves paper Definition
  19, Theorem 20, Corollary 21, or real parallel scheduling; `ParallelHarness` is only the
  bounded pure certificate slice documented above;
- `unload_recovers` proves paper Theorem 61 or Corollary 62 for interleaved fibers;
- the lifecycle guard proves paper Theorem 63, deadlock freedom, or termination;
- retaining the inactive recovered model or one committed view on one edge proves the complete
  Theorem 64;
- `validateTrace` accepts or types arbitrary full Harness logs, or that `ValidatedTrace.replays`
  makes those logs durable and valid;
- exact-subject `dispatchCount_le_one` provides global exactly-once execution across duplicated
  states, workers, retries, or crashes;
- the pure two-call batch executes tools concurrently or makes external effects safe to reorder;
- pure `RunnerState` call/result/record settlement is a durable transaction, makes external tool
  I/O atomic, or provides process-wide exactly-once execution;
- the local `Cordis.Harness` verifies or is behaviorally equivalent to DeepSeek Harness;
- `Approximation` constructs Definition 32's recursive fixed point, fixed-generator tests imply
  paired-inverse coherence, or the finite exact/observational partial-Kleisli theorems are the
  paper's literal total/quotient Theorem 42;
- finite exact `Removal` proves observational, asynchronous, infinite, or external-effect
  recovery;
- `GlobalDynamics` verifies a real code interpreter rather than requiring its recovery,
  confinement, read-agreement, equivariance, and WF laws as fields; `GlobalLifecycle` discharges
  arbitrary-interleaving recovery without its named admission; `GlobalCalculus` proves full
  Theorem 59, progress/confluence, or runtime completeness; `GlobalTraceFacts` proves fresh-name
  or retirement-write provenance for opaque undo codes; `GlobalTemporal` derives canonical paper
  `≈`, off-source totality, or arbitrary T61/Cor62 from current step evidence;
  `GlobalIteratorIndependence` identifies its `EffectEquiv` variant with the paper's displayed rule
  relation `≃`, removes the oracle from registration-dependent programs, constructs `TotalStepMap`,
  owner inverse stability, or a mixed-trace reorder certificate, or upgrades its finite
  partial/Kleisli Definition 60 analogue into Theorem 61 or Corollary 62;
  `GlobalTransposition` upgrades a raw iterator diamond or totalized pre-edit map square into
  lifecycle Lemma 71 without exact stored-code, fixed program/oracle, foreign-control, guard, and
  edited-endpoint evidence, or proves Lemmas 68, 70, or 72;
  `GlobalForeignPhase` derives readability, ordinary exact framing, or same-child oracle stability
  from base `Dynamics` or `Independent`, treats caller-supplied phases as lifecycle outputs, or
  upgrades its framed raw endpoint into a `Transition`, either Lemma 71 clause, or trace reordering;
  `GlobalLandingTransposition` derives exact cross-forward stored-code stability from semantic
  independence, reassigns a bare landing to an arbitrary fixed program, drops source WF or
  common-source applicability, covers any Begin pair, or identifies its moved step with an
  arbitrary existing trace step;
  `GlobalActivationTransposition` drops root/reach/oracle provenance, branch-relevant frame or
  exact-yield laws, distinct owners, source WF, or common-source applicability, rewrites an
  arbitrary stored trace, or upgrades its bounded partial fixed-oracle theorem to the paper's
  literal total/quotient Lemma 71;
  `GlobalActivationOrchestrationTransposition` derives its occurrence frame from registration
  safety, base dynamics, independence, or WF, admits registering activation/O-Insert into exact
  equality, erases birth rank through current `RuleRelated`, repairs the literal parent premise
  without the stronger safety condition, or rewrites arbitrary stored traces;
  `GlobalTraceRewrite` infers fixed-program/oracle assignments for bare transitions, derives swap
  laws for arbitrary records, uses relation-only endpoints as exact casts, simulates retained
  suffixes, admits registering activation/O-Insert, or proves arbitrary normalization, deletion,
  Lemma 72, or confluence;
  `GlobalDeletion` obtains a filtered trace by list operations, derives local keep/replay evidence
  from rule tags, treats name-level ledgers as fiber lifetimes, derives no-redraw or vestigiality
  from well-formedness, ignores parent closure or allocator history, simulates lifecycle suffixes,
  or proves Lemma 72, Theorem 73, normalization, confluence, or termination;
  `GlobalPaperRelation` transports well-formedness from one related state, upgrades birth-erased
  observation to current `RuleRelated`, provides outside-deleted or lifecycle bisimulation,
  derives fixed-program lifecycle assignments from tags, supplies name quotienting, performs
  relation-aware activation swaps, or proves general deletion, normalization, confluence, or
  termination;
  `GlobalProgress` derives fresh-name/admission totality from finite names, treats raw existential
  oracle choice as fixed-program provenance, derives recovery or occurrence readiness from WF, or
  upgrades state-local no-deadlock to the quantitative/maximal-termination clauses of Theorem 66;
  `GlobalSupport` derives combined support well-foundedness from separate provider/parent
  acyclicity, treats arbitrary non-root O-Insert as activation registration, upgrades state-local
  provision totality to a component-wide law, drops active-parent closure, or claims printed Lemmas
  68/70, deletion, or confluence;
  `GlobalRelations` proves full Lemma 55 rule bisimulation, full lifecycle name equivariance, or
  vestigial rule simulation merely by defining candidate setoids; or strengthened birth order is
  literally paper Definition 58;
- `GlobalRuleInvariance` extends its well-formed orchestration certificate to lifecycle rules
  without iterator/read, oracle/landing, recovery-admission, and inertia-respect laws;
- `GlobalRuleObservations` turns structural guard transport into transition bisimulation or
  reconstructs newly active landing tables from source rule observation;
- `GlobalLifecycleBisimulation` derives its four external compatibility records from base
  `Dynamics`, or upgrades its conditional well-formed certificate to the raw no-WF API;
- `GlobalNameAction` proves dynamics, registration-oracle, recovery, inertia, or lifecycle
  equivariance merely from carrier bijections and the separate catalog-entry fixed-point law;
- `GlobalNameLifecycle` derives its primitive dynamics/inertia/catalog-entry laws from arbitrary
  base `Dynamics`, acts component/catalog identities, or removes its well-formed-source boundary;
- `GlobalVestigial` proves the literal unqualified Lemma 57 clauses or extends its corrected
  orchestration squares to iterator, lifecycle, oracle, inertia, or accumulated recovery behavior;
- `GlobalSpatial` derives maximal episode containment, same-owner table immutability, eventual
  closing, or full Theorem 63/64 recovery merely from its explicit nested/confinement witnesses;
- `RuntimeRefinement` accepts the full Harness stream union, is complete for the tolerant
  TypeScript assembler, verifies provider streaming, or proves chunk storage;
- `SessionRefinement` accepts the complete Harness event union, preserves every source field in
  the local event, validates persistence, or proves whole-session behavioral equivalence;
- a `Codec` schema is verified, parser-safe, or wire-compatible with Harness;
- a `VerifiedTool` verifies arbitrary real I/O;
- an emission label provides compensation, idempotence, or sandboxing;
- a Lean capability proposition authenticates a user or confines a process; or
- the lexical source scan or finite static rejection fixtures are a complete trust or
  adversarial audit; or
- similarly named Lean and TypeScript types are behaviorally equivalent.

## Moving a boundary inward

A future change may upgrade a trusted or checked edge only by adding evidence appropriate to
that edge. Examples include:

1. prove decoder soundness/completeness against a formal schema semantics, then verify the
   chosen parser/renderer or constrain the adapter to a certified one;
2. if `replayRaw` and `validateTrace` remain separate public acceptance APIs, prove their exact
   success/error relationship for the local event subset;
3. define an explicit translation from pinned Harness events to Lean events and prove or
   property-test its stated refinement, including every documented divergence;
4. formalize the paper's global fiber registry, operation-level independence and interleaving
   semantics, recursive iterator semantics, and global transition relation before claiming
   Theorems 59, 61–64, 66, or 73;
5. connect capability evidence to an authenticated policy source and OS-enforced sandbox;
6. prove each real backend refines its `ToolSpec`, including failure, cancellation, and external
   emission semantics;
7. bind call leases to an atomic durable store before claiming process-wide exactly-once
   behavior;
8. add crash, persistence, cancellation, streaming, and concurrency tests at the real
   TypeScript/Lean adapter boundary.

Until then, the conservative reading is the correct one: Lean certifies the pure kernel facts,
the validators check a bounded dynamic surface, and adapters plus the external world remain
trusted.

[paper-pdf]: https://raw.githubusercontent.com/cordiverse/paper/948a07b369c62adb3b12e102458be5c18dfb69b9/paper.pdf
[cordis-fiber]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/fiber.ts#L78-L485
[cordis-reflect]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/reflect.ts#L61-L227
[harness-vendor]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/vendor/README.md#L9-L49
[harness-tools]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L211-L269
[harness-tools-view]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L1031-L1284
[harness-tools-execute]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L1328-L1530
[harness-llm-stream]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/llm/llm/src/types.ts#L283-L303
[harness-tool-scheduler]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/agent-loop/src/tool-calls.ts
[harness-session-append]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/index.ts#L564-L655
[harness-session-invariant]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/invariant.ts#L1-L250
