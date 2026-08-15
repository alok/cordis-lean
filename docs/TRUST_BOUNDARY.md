# Trust boundary

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
  -- checked Codec.decode --> typed input
  -- checked admission + supplied proofs --> AuthorizedCall
  -- indexed View.execute --> request-indexed Reply
  -- proved pure VerifiedTool contract --> abstract successor Model
  -- trusted renderer/transport --> external bytes and effects
```

Only the middle, in-memory Lean segment is inside the theorem boundary. A production adapter
must justify every arrow into or out of it.

The protocol has a separate one-way result:

```text
typed Trace -- erase --> RuntimeEvent list -- replayRaw --> erased endpoint
             \_________________ proved _________________/

arbitrary RuntimeEvent list -- applyRaw/replayRaw --> RuntimeState or ValidationError
                              \________ checked ________/
```

There is no theorem that every accepted raw list reconstructs an existential typed `Trace`, and
there is no theorem relating either Lean list to a persisted DeepSeek Harness session.

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

These results do not prove that an inverse recovers an arbitrary state, that arbitrary effects
are independent, or that external side effects are reversible.

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
- `Decision.tighten` has proved deny-absorbing, allow-identity, commutative, associative, and
  idempotent laws.

These are anti-confusion and contract-carrying results. They do not prove that the declared
precondition, capabilities, postcondition, or abstract `Model` faithfully describe the outside
world.

### Session protocol

- Typed `Event` constructors make the six encoded phase transitions intrinsic.
- `Event.preservesWellFormed` and `Trace.preservesWellFormed` preserve duplicate-free pending
  identifiers for typed transitions.
- `Event.noOrphanResult` proves that a typed result names a call pending in its predecessor.
- `applyRaw_eraseEvent` and `replayRaw_eraseTrace` prove that erasing a typed execution is
  accepted by the Lean runtime validator at its statically known endpoint.
- `Trace.erase_append` proves that typed trace composition erases to list append.

These are properties of `Cordis.RuntimeEvent`, not of the complete, merge-extensible Harness
event union or its persistence backend.

### Local lifecycle

- The `Transition` indices permit only the encoded local phase edges.
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

## What is checked but not proved

Executable rejection is valuable, but it is not a refinement theorem.

| Boundary | Check performed | Missing theorem or guarantee |
| --- | --- | --- |
| `Codec.decode` | Rejects JSON AST constructors or lengths outside each decoder's accepted shape. | No proof that accepted values are exactly the values denoted by `schema`, and no completeness result for arbitrary JSON. |
| `Protocol.applyRaw` | Checks phase, turn/step numbers, duplicate calls, orphan results, and pending calls for six event variants. | No soundness theorem producing a typed event, no completeness theorem for arbitrary accepted logs, and no Harness equivalence. |
| `Registry.setAt` | Uses dependent equality transport so a value cannot be installed at a differently typed key. | No runtime aliasing, notification, or mutable-store semantics are modeled. |
| `View.resolve` | Requires `needs op` before a binding can be requested. | Construction of the view and completeness of its registry snapshot remain obligations. |
| `ToolSpec.Invocation` | Requires proof fields before dispatch through the dependent API. | The origin and adequacy of the propositions are not certified by the structure itself. |
| `EmissionClass` | Records a classification. | No behavior is enforced from the label. |
| `Lifecycle.Withdrawable` | Quantifies over a supplied finite list of supplied consumer records. | The list is not proved to enumerate a live registry, and its Boolean `installed` fields are not linked to lifecycle states. |

When an adapter such as `ToolWire` is used, textual resolution, decoding, and admission can
fail closed before an `AuthorizedCall` is constructed. The adapter still supplies its resolver,
codecs, decidability procedures, and proof-producing `admit` implementation. Its existence does
not prove correspondence to a deployed Harness registry.

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

### Runtime registry and lifecycle

The paper's §5 implementation and the pinned CORDIS source dynamically resolve providers,
notify dependents, commit views, and await teardown. See the standalone
[`Fiber`][cordis-fiber] and [`ReflectService`][cordis-reflect], and the Harness
[vendor manifest][harness-vendor] for its locally hardened copy.

The local Lean lifecycle instead assumes:

- the `Consumer` list is a complete and current snapshot;
- `installed : Bool` tells the truth;
- each `CommittedView.resolve` value denotes the intended provider;
- each pushed `Effect` models the complete state change;
- no relevant foreign transition occurs unless represented in the indexed model; and
- executing `UndoStack.recover` is the intended real recovery operation.

It does not model notification races, promises, cleanup exceptions, re-entrant disposal,
fairness, dynamic consumer insertion, or a changing consumer snapshot.

### Session log and durability

The pinned Harness's `Session.append` checks lossless JSON and surface structure, snapshots and
freezes the event, appends it, then notifies observers
([append implementation][harness-session-append]). Its turn/step/call relational checks live in
an optional companion that must be loaded
([session invariant][harness-session-invariant]). Persistence and per-request checkpoints are
separate services.

Consequently:

- a Lean `RuntimeEvent` is not a Harness `SessionEvent`;
- `replayRaw_eraseTrace` is not a storage or crash-recovery theorem;
- it does not prove sequence numbers, timestamps, surface source references, observer
  containment, flushes, or durable writes;
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
- `setEffect_commute` proves paper Definition 19, Theorem 20, Corollary 21, or safe parallel
  scheduling;
- `unload_recovers` proves paper Theorem 61 or Corollary 62 for interleaved fibers;
- the lifecycle guard proves paper Theorem 63, deadlock freedom, or termination;
- retaining one field on one edge proves the complete Theorem 64;
- `replayRaw_eraseTrace` proves that arbitrary accepted logs are typed, or that Harness logs are
  durable and valid;
- a `Codec` schema is verified, parser-safe, or wire-compatible with Harness;
- a `VerifiedTool` verifies arbitrary real I/O;
- an emission label provides compensation, idempotence, or sandboxing;
- a Lean capability proposition authenticates a user or confines a process; or
- similarly named Lean and TypeScript types are behaviorally equivalent.

## Moving a boundary inward

A future change may upgrade a trusted or checked edge only by adding evidence appropriate to
that edge. Examples include:

1. prove decoder soundness/completeness against a formal schema semantics, then verify the
   chosen parser/renderer or constrain the adapter to a certified one;
2. make raw protocol validation return a dependent witness and prove both soundness and
   completeness for the accepted event subset;
3. define an explicit translation from pinned Harness events to Lean events and prove or
   property-test its stated refinement, including every documented divergence;
4. formalize the paper's global fiber registry, independence certificates, iterator semantics,
   and transition relation before claiming Theorems 59, 61–64, 66, or 73;
5. connect capability evidence to an authenticated policy source and OS-enforced sandbox;
6. prove each real backend refines its `ToolSpec`, including failure, cancellation, and external
   emission semantics; and
7. add crash, persistence, cancellation, and concurrency tests at the real TypeScript/Lean
   adapter boundary.

Until then, the conservative reading is the correct one: Lean certifies the pure kernel facts,
the validators check a bounded dynamic surface, and adapters plus the external world remain
trusted.

[paper-pdf]: https://github.com/cordiverse/paper/blob/948a07b369c62adb3b12e102458be5c18dfb69b9/paper.pdf
[cordis-fiber]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/fiber.ts#L78-L485
[cordis-reflect]: https://github.com/cordiverse/cordis/blob/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4/packages/core/src/reflect.ts#L61-L227
[harness-vendor]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/vendor/README.md#L9-L49
[harness-tools]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L211-L269
[harness-tools-view]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L1031-L1284
[harness-tools-execute]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/tools/src/index.ts#L1328-L1530
[harness-tool-scheduler]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/agent-loop/src/tool-calls.ts#L1-L289
[harness-session-append]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/index.ts#L564-L655
[harness-session-invariant]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/packages/core/session/src/invariant.ts#L1-L250
