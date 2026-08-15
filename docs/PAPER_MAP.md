# CORDIS paper and upstream map

This document maps the Lean kernel to the pinned CORDIS paper and to the runtime
systems that motivated it. It is a claim ledger, not a claim that the Lean code is a
line-by-line mechanization or a drop-in implementation of either JavaScript system.

## Claim vocabulary

The labels below have deliberately narrow meanings.

| Label | Meaning |
| --- | --- |
| **Proved** | A proposition or proof field is checked by Lean's kernel. The claim is only the displayed Lean type. |
| **Checked** | A constructor, index, or executable validator rejects some bad values. No refinement theorem to an upstream runtime follows. |
| **Trusted** | Correctness depends on data or behavior supplied outside the proved Lean term. |
| **Not implemented** | The cited paper or runtime claim has no theorem in the mapped modules. |

“Corresponds to,” “models,” and “is a narrow analogue of” do not mean “proves the
paper theorem.” In particular, a theorem about one local transition is not identified
with a paper theorem quantified over an interleaved, multi-fiber execution.

## Pinned evidence set

All external links below include a full commit hash.

| Source | Pin | Evidence used here |
| --- | --- | --- |
| CORDIS paper | [`948a07b369c62adb3b12e102458be5c18dfb69b9`][paper-tree] | The 88-page draft [*A Programming Paradigm for Spatiotemporal Composability*][paper-pdf] |
| Standalone CORDIS | [`8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4`][cordis-tree] | `Context`, `Fiber`, registry, resolution, isolation, interception, and lifecycle source |
| DeepSeek Harness | [`47f943859bef60e4160492346772ded9b24f765a`][harness-tree] | Tool runtime, ordered tool scheduler, session log, and optional session invariant companion |

The Harness snapshot source-vendors its production framework. Its
[vendor manifest][harness-vendor] pins:

- `@deepseek-ai/cordis` `4.0.0-rc.7` and the loader `1.0.0-rc.5` to CORDIS
  [`56b3d4f725681cf4556c1a8695a709cc3b6eed74`][harness-cordis-pin]; and
- the include, group, timer, HMR, and console-logger plugins to DeepSeek's CORDIS fork
  [`abb0a307cb1d3b0947f455d590cf5ba922d4caa4`][harness-plugins-pin].

The same manifest records local modifications to the vendored sources. Therefore the
actual Harness behavior is the code under `vendor/` at the Harness pin, not an inferred
combination of either CORDIS commit with the Harness code. The newer standalone CORDIS
pin is architectural evidence only; compatibility between the three CORDIS snapshots is
not assumed.

This ledger describes declarations in their defining modules. In this checkout, the public
umbrella `Cordis.lean` imports only `Cordis.Version`, and `Tests.lean` is only a version smoke
test. The entries below therefore make no claim that the seven modules are re-exported by the
umbrella or exercised by that executable test.

## Declaration map

### `Cordis.Effect`

Local source: [`Cordis/Effect.lean`](../Cordis/Effect.lean).

| Lean declaration | Status and exact Lean guarantee | Paper correspondence | Boundary |
| --- | --- | --- | --- |
| `Applied`, `Effect` | **Proved by construction:** each application stores `undo_after : undo after = before`. | §3.1.2, Definition 8, witnessed effect functions. | This is a state-indexed, one-sided inverse. It says nothing about `undo` away from the particular `after`. |
| `Effect.seq`, `seq_recovers` | **Proved:** two witnessed effects compose and the second inverse runs before the first. | Definition 9 and Theorem 11(1). | Lean's `seq first second` runs `first` then `second`; it corresponds to the paper's `second ⋄ first` order convention. |
| `identity_seq`, `seq_identity`, `seq_assoc` | **Proved:** the Lean operation has extensional unit and associativity laws. | The monoid part of Theorem 10(1). | Theorem 10(2), the homomorphism from transformation pairs, is not formalized. |
| `UndoAccumulator.push`, `UndoStack.push`, `UndoStack.recover_after` | **Proved:** an indexed LIFO sequence recovers its exact initial state from its indexed terminal state. | The reverse-order recovery conclusion of Theorem 16. | This does not include the paper's nested effect context, soundness invariant, or arbitrary interleaving. |
| `Observational.Applied`, `Observational.Effect.seq`, `seq_recovers` | **Proved:** every inverse respects a supplied `Setoid`, and composition recovers modulo it. | Definitions 36–37 and the composition/recovery portion of Lemma 38. | The supplied `Setoid` is arbitrary. The coeffect-derived relation of Definition 33 and the full Lemma 38 are not constructed. |

The standalone CORDIS runtime accepts disposer callbacks, promises, and iterators and
collects their disposers; the pinned source is in [`fiber.ts`][cordis-fiber]. The Harness
vendor adds documented re-entrant-disposal and lifecycle hardening in its
[`vendor/cordis/src/fiber.ts`][harness-vendor-fiber]. Those runtimes trust plugin authors
to return correct inverses. Lean instead makes recovery evidence part of `Applied`, but
does not model JavaScript promises, cleanup failures, or re-entrant disposal.

`Effect.seq` equality is not paper independence. The paper explicitly distinguishes
commutativity of a composite from Definition 19's requirements on every forward map,
every yielded inverse, and inverse-yield stability.

### `Cordis.Api`

Local source: [`Cordis/Api.lean`](../Cordis/Api.lean).

| Lean declaration | Status and exact Lean guarantee | Paper correspondence | Boundary |
| --- | --- | --- | --- |
| `Signature` | **Checked intrinsically:** an operation chooses its request type and the response type for that exact request. | Definition 24's typed operation argument/outcome families; §5.1.4's proposed compile-time mediation. | Request-indexed responses are a Lean strengthening, not a numbered theorem in the paper. |
| `Provider`, `Registry` | **Checked intrinsically:** a key can store only a provider for that key; a handle returns only the indexed response type. | §3.2.1, Definition 22's dependent partial function. | `Except String` is a pure model. It does not establish behavior of an external implementation. |
| `Needs` | **Checked as a proposition:** capability membership is `sig.Op -> Prop`. | §3.2.2, Definition 25's coeffect specification. | No finite-set representation or decidability is supplied here. |
| `Binding`, `View`, `provider_present` | **Proved:** resolving a declared operation returns a provider with equality evidence that it is present in the specific registry value. | Definition 44's committed view, Definition 46's provider-valued target view, and §5.1.4 context access. | It does not compute a dynamic target, notify dependents, or prove an episode-level coherence theorem. |
| `SomeCall`, `AuthorizedCall`, `Reply`, `View.execute` | **Checked intrinsically:** a response remains indexed by the resolved operation and exact request; authorization is carried as `needs op`. | Harness-facing strengthening of typed coeffect access. | Name lookup, decoding, and authority decisions occur outside this module. |
| `Component` | **Checked:** a component receives only a restricted `View`. | Part of Definition 43's dependency-facing component interface. | It omits Definition 43's declared provision and witnessed effect function, so it is not the paper's full component tuple. |

The standalone runtime enforces declarations dynamically through its proxy resolver in
[`reflect.ts`][cordis-reflect]: the resolver follows committed fiber stores and rejects
inactive or undeclared access. Lean moves the declared-operation check into the type of
`View.resolve`. No theorem proves that a JavaScript proxy access and a Lean `View.call`
select the same provider.

The pinned standalone `Context` derives isolation and interception scopes through inherited
tables in [`context.ts`][cordis-context]. The mapped Lean API has no corresponding realm or
metadata transformation.

### `Cordis.Registry`

Local source: [`Cordis/Registry.lean`](../Cordis/Registry.lean).

| Lean declaration | Status and exact Lean guarantee | Paper correspondence | Boundary |
| --- | --- | --- | --- |
| `setAt`, `install`, `withdraw`, `setAt_same`, `setAt_other` | **Proved/checked:** a dependent update changes only the selected key and retains its indexed provider type. | Definitions 22–23, dependent table update and restriction. | Paper `set` requires absence and its inverse removes the new key. Lean permits replacement and records the overwritten `Option`, so the operations are not definitionally the same. |
| `setAt_restore`, `setEffect`, `setEffect_recovers` | **Proved:** restoring the captured prior binding exactly recovers the whole registry. | Definition 23 viewed as a witnessed effect and Definition 8's recovery witness. | The proof is about a pure functional registry, not mutable runtime aliases or external resources. |
| `setAt_commute`, `setEffect_commute` | **Proved:** fixed updates at distinct keys commute; equality of `Effect.seq` includes both successor and composed recovery function. | A concrete distinct-key commutation instance related to Theorem 40. | It does not define transformation monoids, prove yielded-inverse stability for arbitrary operations, account for outcomes, or establish Theorem 40 in full. |
| `Satisfies`, `satisfiesNone`, `satisfiesOne` | **Proved by construction:** satisfaction is a resolver yielding a present provider for each declared operation. | Definition 25's satisfaction predicate and Definition 46's provider resolution. | There is no activating/deactivating/neutral notification classifier from Definition 26. |

CORDIS's concrete provider registration, notification, and withdrawal live in
[`reflect.ts`][cordis-reflect]. A disposer deletes the public binding, notifies and awaits
affected fibers, then removes self-access. Lean's registry contains no notification or wait;
it proves only pure table facts.

### `Cordis.Tool`

Local source: [`Cordis/Tool.lean`](../Cordis/Tool.lean).

| Lean declaration | Status and exact Lean guarantee | Paper/upstream correspondence | Boundary |
| --- | --- | --- | --- |
| `ToolSpec` | **Checked as a type:** input-dependent output/failure, precondition, postcondition, required capabilities, and an emission label are declared together. | Paper §1.2.2 motivates agent harnesses; Definition 24 supplies typed operations. Harness `ToolDefinition` has JSON schemas and an async body in [`tools/src/index.ts`][harness-tools]. | This contract shape is project-specific; the paper has no `ToolSpec` theorem. |
| `ToolSpec.Invocation` | **Proved by construction:** a value exists only with `precondition` and `authorized` proofs. | A static strengthening of Harness pre-dispatch policy and capability filtering. | The propositions and granted-capability predicate are supplied by the caller. |
| `CertifiedOutcome`, `VerifiedTool` | **Proved by construction:** a pure implementation must return a result, successor model, and the declared postcondition proof. | A proof-carrying counterpart to Harness's validated canonical tool outcome. | No external I/O backend is verified. A bridge that constructs the outcome remains trusted unless separately proved. |
| `ToolCatalog.signature`, `ToolCatalog.provider` | **Checked intrinsically:** a heterogeneous tool catalog becomes a dependent API without losing the request/result dependency. | Harness tool registry and schema projection. | No theorem relates Lean tool names or schemas to a deployed Harness registry. |
| `Decision.tighten` and its algebraic theorems | **Proved:** deny is absorbing, allow is the identity, and combination is commutative, associative, and idempotent. | Harness `PreToolDecision = allow | deny | ask` and its monotonic guards in [`tools/src/index.ts`][harness-tools-policy]. | Harness policy is an ordered async waterfall with reasons and approval routing. `tighten` is a small pure policy algebra, not a model of that whole pipeline. |
| `EmissionClass` | **Checked only as data:** one of five labels is attached to a tool. | Paper §6.1's system-boundary discussion. | Nothing in this module enforces idempotence, compensation, reversibility, or an OS sandbox from the label. |

The pinned Harness tool runtime additionally has scoped shadowing and restrictions,
fail-closed concurrency classification, cooperative cancellation, output-schema validation,
and pre/around/post execution stages. See its [registry view and scheduler-facing
classification][harness-tools-view] and [execution pipeline][harness-tools-execute]. None
of those runtime behaviors follows from `ToolSpec` or `Decision.tighten`.

### `Cordis.Protocol`

Local source: [`Cordis/Protocol.lean`](../Cordis/Protocol.lean).

| Lean declaration | Status and exact Lean guarantee | Upstream correspondence | Boundary |
| --- | --- | --- | --- |
| `SessionState`, `Event`, `Trace` | **Checked intrinsically:** adjacent states must match; tool calls require a fresh identifier; results require pending membership; a step can end only with no pending calls. | Harness turn, step, call, and result event vocabulary in [`session/src/types.ts`][harness-session-types]. | This is a deliberately smaller and stricter protocol, not the full merge-extensible Harness event map. |
| `SessionState.WellFormed`, `Event.preservesWellFormed`, `Trace.preservesWellFormed` | **Proved:** pending identifiers remain duplicate-free over typed events and traces. | Related to the optional Harness session invariant companion. | Harness uses a `Set` and does not reject a repeated `tool/call` identifier at insertion. |
| `Event.noOrphanResult` | **Proved:** a typed result event carries predecessor-membership evidence. | Harness normally requires a same-step pending call before a result. | Harness has explicit exceptions for repair-generated not-started results and surface replacements. |
| `applyRaw`, `replayRaw` | **Checked executable boundary:** the six runtime events are validated for phase, number, duplicate, orphan, and pending-call errors. | Harness optional relational validator in [`session/src/invariant.ts`][harness-session-invariant]. | Successful replay returns only `RuntimeState`, not an existential typed `Event` or `Trace`; validator soundness/completeness is not proved. |
| `applyRaw_eraseEvent`, `replayRaw_eraseTrace` | **Proved:** erasing a typed event/trace and replaying it is accepted at the erased endpoint. | A one-way refinement check from Lean's typed protocol to its own runtime validator. | The converse and equivalence to Harness logs are not proved. |
| `Trace.erase_append` | **Proved:** typed trace composition erases to list concatenation. | Append-only log composition. | It says nothing about persistence, sequence numbers, timestamps, surface metadata, or crash durability. |

#### Exact differences from the pinned Harness protocol

| Topic | Lean protocol | Pinned Harness |
| --- | --- | --- |
| Initial numbers | A caller chooses `.ready n`; `turnStart n` starts step counter `0`. | A fresh invariant trace expects turn `1` and step `1` ([initialization][harness-session-invariant]). |
| Duplicate call ID | Rejected and impossible in typed `Event.toolCall`. | `pendingCalls.add(callId)` does not reject an existing ID. |
| Step end with pending calls | Rejected by `pendingCallsRemain`; typed `stepEnd` requires `[]`. | The invariant companion clears `pendingCalls` at `step/end`. |
| Orphan result | Always rejected by the six-event validator. | Normally rejected, with exceptions for a synthetic repair result and non-append surface replacement. |
| Other events | No other event can occur in a typed trace. | User, assistant, request, seed, todo, and plugin-merged events share the log. |
| Always-on checks | `applyRaw` performs the listed relational checks whenever called. | `Session.append` always checks lossless JSON and surface rules, but relational turn/step checks require loading the optional invariant companion. |

Harness `Session.append` snapshots and freezes JSON before appending, assigns sequence and
time fields, validates surface operations, and publishes observers; see
[`session/src/index.ts`][harness-session-append]. Those checks are outside the Lean protocol.

Harness dispatch may overlap calls but commits results and result contexts in model order,
uses exclusive barriers, drains started calls on abort, and emits synthetic pairs for skipped
calls. That behavior is in [`agent-loop/src/tool-calls.ts`][harness-tool-scheduler].
`Cordis.Protocol` proves no concurrency, ordering, cancellation, or exactly-once durability
property for that scheduler.

### `Cordis.Lifecycle`

Local source: [`Cordis/Lifecycle.lean`](../Cordis/Lifecycle.lean).

| Lean declaration | Status and exact Lean guarantee | Paper correspondence | Boundary |
| --- | --- | --- | --- |
| `State` | **Checked intrinsically:** reloading, active, and unloading states carry an origin, current model, indexed undo stack, and committed view; reloading also carries an abstract iterator. | §4.3, Definition 49; §5.1.3. | The paper gives the iterator recursive witnessed semantics, and its global context also carries retirement, fiber tables, dependency/provision sets, and an error calculus. Lean abstracts or omits those parts. |
| `CommittedView`, `Consumer`, `Withdrawable` | **Checked/propositional:** the guard quantifies over the supplied consumer list and rejects an installed consumer whose supplied view resolves to the provider. | Definitions 44 and 50 and the `L-Unload` guard. | Completeness and freshness of the consumer snapshot, truth of `installed : Bool`, and provider existence are assumptions of the input data. |
| `Transition.begin`, `iterate`, `finish`, `divert`, `leave`, `unload` | **Checked intrinsically:** only the encoded phase changes can be constructed; iteration pushes an `Effect`; unloading requires a `Withdrawable` proof. | The local shape of the §4.3 lifecycle rules. | `begin` does not require target satisfaction, `iterate` is synchronous and accepts an arbitrary next iterator, and the trace fixes one consumer snapshot. It is not the paper calculus. |
| `Transition.unload_recovers` | **Proved:** for an `unload` constructor, the indexed stack recovers that activation's exact `origin`. | A local, non-interleaved analogue of Theorem 61 and Corollary 62. | Paper recovery quantifies over pairwise-independent interleaved steps and preserves foreign effects up to observational equivalence. None of those hypotheses or conclusions appears here. |
| `Transition.unload_rejects_relied` | **Proved:** given membership, installed, and reliance evidence in the supplied list, an unload transition yields `False`. | Definition 50 and the premise of `L-Unload`; it supports the intuition of Theorem 63. | Theorem 63's episode nesting, provision availability, and stable binding values are not proved. |
| `Transition.active_successor_keeps_view` | **Proved:** the only active successor is unloading with exactly the same committed view and undo stack. | A narrow structural fragment of Definition 44 and Theorem 64. | Theorem 64 covers one committed resolution throughout every iteration and its finish/divert dichotomy. This theorem covers only the `active -> unloading` edge. |
| lifecycle `Trace`, `Trace.append` | **Checked intrinsically:** adjacent lifecycle endpoints match. | §4.4 indexed step sequences. | It has no global registry, orchestration, fairness, progress, or confluence theorem. |

The standalone CORDIS implementation commits a provider snapshot during reload and reads
through that snapshot in its proxy resolver; see [`fiber.ts`][cordis-fiber] and
[`reflect.ts`][cordis-reflect]. Its provider removal notifies and waits for affected fibers
before deleting the provider's self-view. The Harness-vendored fiber contains additional
lifecycle hardening documented in the [vendor manifest][harness-vendor]. The Lean
lifecycle does not prove equivalence to either asynchronous implementation.

### `Cordis.Codec`

Local source: [`Cordis/Codec.lean`](../Cordis/Codec.lean).

| Lean declaration | Status and exact Lean guarantee | Upstream correspondence | Boundary |
| --- | --- | --- | --- |
| `DecodeError`, `PathSegment`, `JsonKind` | **Checked data:** decoding failures identify a type/length error and an AST path. | Harness receives raw tool arguments and validates schemas at runtime. | The error vocabulary does not model all JSON Schema failures or Harness error payloads. |
| `Codec`, `decode_encode` | **Proved by field:** `decode (encode value) = .ok value` at the in-memory `Lean.Json` AST boundary. | A proof-carrying replacement for a subset of Harness's schema/validation convention. | There is no numbered CORDIS paper theorem about JSON codecs. The theorem is one-way and does not prove schema soundness, completeness, parser correctness, or wire compatibility. |
| `unit`, `bool`, `string`, `nat`, `prod`, `list` | **Proved:** every constructed codec discharges the same AST round trip, including recursive products/lists. | Common tool-wire data shapes. | `nat` accepts the exact canonical nonnegative exponent-zero AST form used by its encoder. Object, optional, sum, arbitrary number, and named-field codecs are absent. |
| `schema` field | **Trusted descriptive metadata.** | Harness exposes parameter/output JSON Schema to model and runtime. | No Lean proposition connects `schema` to `encode` or `decode`, and an external producer is not proved to follow it. |

Harness model calls carry the raw argument string unchanged in the session event and parse it
later for dispatch. Its tool registry snapshots lossless JSON, validates input/output schemas,
and materializes failures. `Codec` begins after parsing, at `Lean.Json`; it is neither a parser
nor a proof about Harness's TypeScript schema engine.

## Paper claims not implemented by the mapped modules

The following are intentionally not presented as completed formalization work.

1. **Effect-context tower:** Definitions 1–3 and 6 and Theorems 4–5 and 7 (`track`,
   `recover`, twisted composition, the monoid homomorphism, and the soundness invariant)
   are not represented directly. Definition 12 and Theorems 13–15, which lift an effect into
   the next effect-context level, are also absent.
2. **Full effect independence:** Definition 17, Lemma 18, Definition 19, Theorem 20, and
   Corollary 21 are absent. `setEffect_commute` proves one fixed distinct-key equation, not
   arbitrary removal or arbitrary-order recovery.
3. **Reactive coeffect semantics:** Definition 24's operation/outcome semantics,
   Definition 26's notification classifier, Definition 27's realizations, Definitions 28–31's
   isolation/interception contexts, and Definition 32's recursive unified context are absent.
4. **Operational observational equivalence:** Definition 33's coeffect projection,
   Definition 34 and Lemma 35's test indistinguishability, and the full operation
   independence results of Definitions 39–41 and Theorems 40–42 are not proved.
5. **Full component calculus:** Definitions 43–53 are not mechanized as one global state and
   step relation. In particular, there is no fresh-name fiber registry, parent tree,
   retirement/orchestration calculus, confinement proof, recursive witnessed iterator,
   asynchrony rule, or failure rule.
6. **Preservation metatheory:** Lemmas 54–57, Definition 58's four-clause well-formed
   registry, and Theorem 59 are absent.
7. **Temporal composability:** Definition 60's iterator independence, Theorem 61's
   interleaved recovery exactness, and Corollary 62's terminal recovery are absent. The local
   `unload_recovers` theorem is not a substitute.
8. **Spatial composability:** Theorem 63's dependency episode ordering and Theorem 64's
   complete resolution-coherence statement are absent. The lifecycle guard and view-retention
   theorem establish only local constructor facts.
9. **Progress:** Definition 65's precedence relation and Theorem 66's no-deadlock and bounded
   termination result are absent.
10. **Confluence:** Definitions 67 and 69, Lemmas 68 and 70–72, and Theorem 73's canonical
    form and confluence result are absent.
11. **Loader and HMR:** Definition 74, declarative configuration-tree reconciliation, and
    §5.2 hot-module replacement are not modeled by these modules.
12. **System-boundary enforcement:** §6 discusses resource boundaries, service
    multiplexing, access control, sandboxing, language independence, and dependency
    granularity. The mapped modules do not prove OS isolation, credential confinement,
    network/filesystem policy, or correctness of irreversible external effects.

## Harness claims not established by this map

Even where adjacent local adapter or example modules execute a deterministic path, the seven
modules mapped above do not establish:

- source or binary compatibility with the pinned TypeScript packages;
- equivalence of Lean JSON schemas/decoders to Harness JSON Schema validation;
- scoped registration, shadowing, restrictions, approval routing, or the complete tool
  execution pipeline;
- bounded parallel dispatch, exclusive barriers, model-ordered commits, cancellation drains,
  or synthetic abort results;
- the complete merge-extensible session vocabulary, surface replacement rules, persistence,
  checkpoint durability, or crash recovery; or
- correctness of real tool I/O, host callbacks, JavaScript promises, an OS sandbox, or a
  network/storage backend.

These are adapter, runtime, and systems claims. They require separate refinement theorems or
integration tests; they cannot be inferred from similarly named Lean declarations.

[paper-tree]: https://github.com/cordiverse/paper/tree/948a07b369c62adb3b12e102458be5c18dfb69b9
[paper-pdf]: https://github.com/cordiverse/paper/blob/948a07b369c62adb3b12e102458be5c18dfb69b9/paper.pdf
[cordis-tree]: https://github.com/cordiverse/cordis/tree/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4
[cordis-context]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/context.ts#L21-L77
[cordis-fiber]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/fiber.ts#L78-L485
[cordis-reflect]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/reflect.ts#L61-L227
[harness-tree]: https://github.com/deepseek-ai/deepseek-harness/tree/47f943859bef60e4160492346772ded9b24f765a
[harness-vendor]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/vendor/README.md#L9-L49
[harness-cordis-pin]: https://github.com/cordiverse/cordis/tree/56b3d4f725681cf4556c1a8695a709cc3b6eed74
[harness-plugins-pin]: https://github.com/deepseek-harness/cordis/tree/abb0a307cb1d3b0947f455d590cf5ba922d4caa4
[harness-vendor-fiber]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/vendor/cordis/src/fiber.ts#L64-L689
[harness-tools]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L211-L269
[harness-tools-policy]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L582-L600
[harness-tools-view]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L1031-L1284
[harness-tools-execute]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L1328-L1530
[harness-session-types]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/types.ts#L230-L297
[harness-session-invariant]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/invariant.ts#L1-L250
[harness-session-append]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/index.ts#L564-L655
[harness-tool-scheduler]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/agent-loop/src/tool-calls.ts#L1-L289
