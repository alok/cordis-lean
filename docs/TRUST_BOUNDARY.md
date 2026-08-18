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
interpreter. Full branch-indexed Theorem 42 remains open. `Schedule` executes sequentially, and
`RichStream` excludes transport, images, tool-result blocks, and pruning. These
types do not extend the theorem boundary to corresponding external systems
automatically.

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

These results do not prove that an inverse recovers an arbitrary state, that arbitrary effects
are independent, or that external side effects are reversible. The two-call evaluator performs
no `IO`, launches no tasks, and proves no concurrency or safe-parallel-execution property.

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
  Definition 41 with exact recovery. `MediatedClosure` records the still-unproved
  branch-indexed obligation for full Theorem 42.

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

| Boundary                                    | Check performed                                                                                                                                                                                                                      | Missing theorem or guarantee                                                                                                                                                                     |
| ------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `Codec.decode`                              | Rejects JSON AST constructors or lengths outside each decoder's accepted shape.                                                                                                                                                      | No proof that accepted values are exactly the values denoted by `schema`, and no completeness result for arbitrary JSON.                                                                         |
| `ToolWire.validate`                         | Resolves a name, checks declaration, decodes the selected input, and requires `certifyAdmission` evidence before returning a dependent call.                                                                                         | The supplied resolver, codecs, propositions, capability source, and admission procedure are not proved equivalent to a deployed registry or authenticated policy.                                |
| `Protocol.validateEvent` / `validateTrace`  | Checks the six local event variants and returns exact intrinsic witnesses for successful inputs.                                                                                                                                     | No translation or equivalence to the full Harness event union; no theorem equates every successful erased `replayRaw` call with witness reconstruction.                                          |
| `Stream.applyRaw`                           | Checks one text/finish protocol, explicit chunk budget, and terminal-state discipline.                                                                                                                                               | No witness reconstruction for arbitrary accepted raw streams and no equivalence to Harness `StreamChunk` assembly or persistence.                                                                |
| `RuntimeRefinement.validateJsonTrace`       | Decodes a supported current-Harness stream JSON-AST subset, then returns an exact intrinsic `RichStream.ValidatedTrace` or a separated decode/semantic error.                                                                        | No byte parser, full stream-union coverage, tolerant-assembler completeness, transport, storage, or whole-runtime equivalence.                                                                   |
| `SessionRefinement.validateJsonLog`         | Stateful supported-subset decoding returns exact rich append and intrinsic protocol witnesses, fresh local call-ID evidence, and a cumulative projection theorem.                                                                    | No complete event union, replacement translation, persisted JSONL parser, timestamp truth, crash recovery, or whole-session equivalence.                                                         |
| `UnifiedContext` constructors               | Enforce dependent realm/provider types, derived-parent indices, finite unfolding depth, and witnessed local recovery.                                                                                                                | No imperative alias identity, recursive fixed point, tenant sandbox, middleware execution, or runtime refinement.                                                                                |
| `Coeffect.Observational.Related`            | Makes presence/absence mismatches unconstructible and packages supplied key relations as a finite-context `Setoid`.                                                                                                                  | The key relations are supplied; operational tests can replace them only under the separately documented laws.                                                                                    |
| `OperationalEquivalence` / `QuotientEffect` | Checks finite partial test words and certifies finite quotient-respecting effect programs; the paired-inverse counterexample is kernel-checked.                                                                                      | Universal test equivalence is not decidable here; the stronger paired law needs a premise, and this layer alone does not prove mediated independence.                                            |
| `Transformation` / `OperationIndependence`  | Constructs exact generated monoids, promotes full inverse/outcome stability, checks finite distinct-key words, and interprets outcome-mediated computations.                                                                         | Partial words are finite syntax, not abstract Kleisli monoids; the branch-closure derivation for full Theorem 42 remains absent.                                                                 |
| `Removal`                                   | Builds indexed original/omitted finite traces with exact later inverse equalities and checks arbitrary permutations of the retained inverse list.                                                                                    | Exact pure effects only; no observational quotient, infinite family, asynchronous runtime, or real external recovery.                                                                            |
| `GlobalRegistry`                            | Checks code-only component/fiber/global data, unique providers/targets, birth-ranked acyclicity, and preservation by insert/retire/remove orchestration.                                                                             | Uses a strengthened parent invariant and noncomputable derived views; no code interpreter, read confinement, lifecycle rules, or full Theorem 59.                                                |
| `CertifiedTwoBatch`                         | Requires same-successor, pointwise same-recovery, and result-stability certificate fields before either order is permitted.                                                                                                          | The certificate is supplied, exactly two pure calls are modeled, and no actual concurrency or external-effect safety follows.                                                                    |
| `Registry.setAt`                            | Uses dependent equality transport so a value cannot be installed at a differently typed key.                                                                                                                                         | No runtime aliasing, notification, or mutable-store semantics are modeled.                                                                                                                       |
| `View.resolve`                              | Requires `needs op` before a binding can be requested.                                                                                                                                                                               | Construction of the view and completeness of its registry snapshot remain obligations.                                                                                                           |
| `ToolSpec.Invocation`                       | Requires proof fields before dispatch through the dependent API.                                                                                                                                                                     | The origin and adequacy of the propositions are not certified by the structure itself.                                                                                                           |
| `EmissionClass`                             | Records a classification.                                                                                                                                                                                                            | No behavior is enforced from the label.                                                                                                                                                          |
| `Lifecycle.Withdrawable`                    | Quantifies over a supplied finite list of supplied consumer records.                                                                                                                                                                 | The list is not proved to enumerate a live registry, and its Boolean `installed` fields are not linked to lifecycle states.                                                                      |
| `Harness.RunnerState`                       | Sequential reference functions construct `replayProof` and a six-index `RecordChain` tying model history, IDs, records, final leases, and `callBoundaries log`; public theorems expose boundary/record equality and lease threading. | The boundary projection erases coordinates and has no full Harness translation; there is no refinement to TypeScript Harness, real I/O, parallel scheduling, durable storage, or crash recovery. |

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
deployment or upstream interoperability. `Cordis/AxiomAudit.lean` runs `#print axioms` for 260
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
data; they are specifications, not extracted runtime algorithms. Registration callbacks, read
confinement, iterator/undo interpretation, lifecycle transitions, and the full ten-rule
preservation theorem remain outside.

The local Lean lifecycle instead assumes:

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
  19, Theorem 20, Corollary 21, or safe parallel scheduling;
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
  paired-inverse coherence, or the bounded operation layer proves full Theorem 42;
- finite exact `Removal` proves observational, asynchronous, infinite, or external-effect
  recovery;
- `GlobalRegistry` interprets its opaque codes, proves Definition 48 read confinement, implements
  lifecycle rules, or establishes full Theorem 59; or that its strengthened birth-order invariant
  is literally identical to paper Definition 58;
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
