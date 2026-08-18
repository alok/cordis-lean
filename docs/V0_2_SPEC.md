# CORDIS Lean 0.2: Log-reconstructible generic harness

<!-- markdownlint-disable MD013 MD029 -->

## Status

This specification defines the active implementation slice after the finite `0.1.0` counter
kernel. The generic phase-indexed runner, exact-call allow/reject policy paths, structured
non-counter example, intrinsic rich session/surface kernel, model-request reconstruction, and
the counter wrapper's rich-to-structural log equality are implemented. `SessionValidation`
proof-produces append/replacement and finite-suffix certificates from parsed-but-untrusted typed
events. Byte/payload parsing and the later production/refinement layers listed below remain open;
this file is therefore an in-progress contract, not a completed `0.2.0` release claim.

The slice closes two concrete gaps in the original objective:

1. the runner becomes generic over a dependent tool catalog instead of importing the counter
   example; and
2. the harness gains a proof-carrying append-only session log from which the model-visible
   surface and each request are reconstructed.

The counter remains as one executable instantiation and regression fixture.

Current machine-checked evidence includes:

- `Cordis.GenericHarness.Config`, `Runner cfg phase`, `DispatchResult`, and the generic
  model/lease/ID/log `RecordChain`;
- zero-dispatch admission/policy rejection, exactly-one-dispatch completion, terminal lease
  absence, and lease restoration theorems;
- `Cordis.Examples.DependentChoice`, where `Bool` definitionally selects `Nat` or `String` and
  policy rejects the exact string-producing call before dispatch;
- `Cordis.Session.EventIntent`, `SurfaceTransition`, `ValidLog`, `ModelRequest`, certified
  replacement examples, and rich-to-structural `ProtocolCertificate`;
- `Cordis.SessionValidation.RangeWitness`, `ValidatedAppend`, `ValidatedSuffix`, and
  `ValidatedLog`, including exact structured rejection examples;
- `Cordis.RichStream`, including block-kind-indexed deltas, interleaved first-seen ordering,
  exact block ends, usage/terminal discipline, error/abort terminals, and aligned replay data;
- `Cordis.Schedule.runEffects_eq_of_perm`, promoting the exactly-two batch result to arbitrary
  finite semantic orders under a real pairwise commuting-family certificate;
- `Cordis.Coeffect`, mechanizing paper Definitions 22–26 for dependent finite contexts, concrete
  reversible bindings, typed local operations, finite satisfaction, and exact notifications;
- `Harness.RunnerState.protocolProjection_eq_log` and `protocolProjection_replays`, tying the
  actual counter demo's canonical rich log to the generic runner; and
- executable, static-rejection, hygiene, strict-build, and selected-axiom gates covering those
  declarations.

## Authoritative source boundary

The design is grounded in these source revisions:

| Source            | Revision                                   | Role                                                                                                                     |
| ----------------- | ------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------ |
| CORDIS paper      | `948a07b369c62adb3b12e102458be5c18dfb69b9` | Revertible effects, reactive coeffects, unified context, dynamic composition, and composability claims.                  |
| Standalone Cordis | `8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4` | Concrete service, registry, effect, lifecycle, and event mechanisms.                                                     |
| DeepSeek Harness  | `99f6f02fecdb7dff40c3fbc9470f5907c29f74ca` | Current session-event vocabulary, model-surface reconstruction, request headers, tool pipeline, and turn/step lifecycle. |

The DeepSeek Harness revision is intentionally newer than the `0.1.0` pin. At this revision,
the Harness describes an append-only `SessionEvent` log as the single source of truth, derives
LLM message history from its ordered surface, requires surface metadata only on
message-producing events, records full request-header snapshots, and validates surface
replacement coverage at append time.

No theorem in this repository may claim behavioral equivalence to these TypeScript sources
without an explicit relation and proof.

## Design rules

### The API is the proof boundary

An API declaration selects all of the following in its type:

- the operation;
- the operation-specific request type;
- the response and failure types selected by that request;
- the required capabilities;
- the precondition and postcondition;
- the event payload selected by an event kind;
- whether an event may carry surface metadata;
- the legal predecessor and successor of a session-log append;
- the exact message history and request header supplied to a model adapter; and
- the exact dependent call subject threaded through policy, execution, result encoding, and
  audit settlement.

Runtime validation may construct these values from untrusted data. It may not weaken their
types after validation.

### The log is canonical

The model-visible message list is never an independently mutable field. It is a projection of
the validated ordered surface, which is itself reconstructed from the append-only event log.

The current request header is likewise a fold selecting the latest full `request/header`
snapshot. A model request must carry equalities tying both its history and header to these log
projections.

### Unknown data fails closed

Raw surface operations are rejected unless all structural obligations can be reconstructed:

- sequence numbers are contiguous;
- every source sequence refers to a unique earlier event;
- append and replacement markers are legal only for surface events;
- log-only events carry no surface marker;
- replacement endpoints are current surface nodes in left-to-right order;
- the replaced range is nonempty and contiguous in the current surface; and
- source sequences cover every shadowed surface node.

### Proof layers remain distinct

The implementation distinguishes:

- propositions proved by Lean;
- executable validation of untrusted finite values;
- trusted external observations and adapters; and
- absent production behavior.

Passing a validator does not prove that a remote model, filesystem, process, or persistence
backend faithfully implements the modeled contract.

## Session-log kernel

### Event schema

`Cordis.Session` will define a schema whose event kind selects its payload and visibility.
The core vocabulary includes at least:

- `turn/start` and `turn/end`;
- `step/start` and `step/end`;
- `user/message`;
- `request/header`;
- `assistant/chunk`;
- `assistant/message`;
- `tool/call`;
- `tool/result`; and
- an extension constructor parameterized by an application-supplied event family.

The visibility family classifies `user/message`, `assistant/message`, and `tool/result` as
surface events. All other core events are log-only. Extension kinds select their visibility
through the extension schema.

The append API uses a dependent intent family:

```lean
EventIntent schema kind
```

It reduces to a certified `SurfaceIntent` only when `kind` is surface-producing and to a
log-only token otherwise. Supplying a replacement marker to `turn/start`, `assistant/chunk`,
or another log-only event must therefore be a type error, not a runtime convention.

### Logged events

Each committed event carries its sequence number. The proof-carrying log enforces that the
next event's sequence equals the current log length. A valid log therefore proves:

```text
event sequence numbers = [0, 1, ..., log.length - 1]
```

Timestamps and byte-level JSON serialization remain outside this pure kernel.

### Surface operations

A surface node contains the sequence number and model-facing message selected by its event.
Two operations are supported:

- `append`: add the new node at the tail; and
- `replace`: replace one nonempty contiguous range of current nodes with the new node.

The intrinsic replacement constructor carries a decomposition of the predecessor surface into
prefix, shadowed range, and suffix. This is the canonical proof object. A raw replacement uses
start/end sequence numbers and must be validated into that decomposition.

The replacement certificate additionally proves that the event's unique earlier
`sourceEventSeqs` cover every shadowed node. Extra earlier source events may be cited when the
producer has additional provenance, but missing shadowed nodes are forbidden.

### History and header reconstruction

`deriveMessages` maps the final ordered surface to model messages. Log-only events never enter
this list. A replacement removes the shadowed messages and inserts the replacement at exactly
that position.

`foldRequestHeader` selects the latest full header snapshot. A header includes the modeled call
configuration, optional system prompt, and assembled tool schemas. Route capacity metadata,
transport options, credentials, and provider availability are not part of this theorem.

`ModelRequest session` carries:

- `messages` and a proof `messages = session.deriveMessages`;
- `header` and a proof `some header = session.foldRequestHeader`; and
- the session log length at which the request was reconstructed.

Construction fails before the first request-header event. Once constructed, a request cannot
substitute an independently assembled message history or stale header.

### Required theorems

The session slice is incomplete until Lean checks all of the following:

1. `ValidLog.length_eq_nextSeq`: the stored next sequence equals the event-list length.
2. `ValidLog.seqs_eq_range`: event sequence numbers are exactly `List.range nextSeq`.
3. `ValidLog.surface_references_earlier`: every current surface node names an earlier committed
   event.
4. `ValidLog.surface_nodup`: the current surface contains no duplicate sequence number.
5. `SurfaceTransition.replace_shadowed`: a replacement removes exactly its certified contiguous
   range.
6. `SurfaceTransition.replace_covers`: every removed surface node appears in the replacement's
   source-event set.
7. `ValidLog.messages_eq_surface`: derived model messages are exactly the current surface's
   message projection.
8. `ModelRequest.reconstructible`: every model request carries the exact log-derived history and
   latest header.
9. `ValidatedAppend.applies`: every successfully reconstructed raw append is accepted by the
   intrinsic transition and reaches the same surface/header endpoint.
10. `ValidatedLog.replays`: every successfully validated raw finite log reconstructs an
    intrinsic proof-carrying log with the same events and projections.

The exact declaration names may change during implementation, but the propositions may not be
dropped or replaced with weaker executable assertions.

## Generic dependent runner

### Configuration

`Cordis.GenericHarness.Config` is parameterized by `Model` and `Capability` and owns:

- a `ToolCatalog Model Capability`;
- a `ToolWire` for that exact catalog;
- the component's `Needs` predicate and decidability witness;
- the granted-capability predicate and decidability witness;
- a provider registry and committed `View` for the same signature and needs;
- an exact-call policy decision function; and
- a rejection explanation for every non-allow decision.

The registry, view, wire, needs, and catalog indices must agree by construction. A caller cannot
pair a wire for one catalog with a provider view for another.

### Policy behavior

The policy function receives the successfully admitted dependent call. `allow` may issue and
consume the call-ID lease and execute the provider. `ask` and `deny` fail closed in the pure
runner, settle a subject-indexed rejection trace, and do not invoke the provider.

A future approval adapter may refine `ask` to a new final decision, but `0.2` does not trust an
ambient callback to silently upgrade authority.

### Records and state

`CallEvidence config` retains one of:

- fail-closed admission rejection;
- admitted but policy-rejected exact call, with a no-dispatch policy trace; or
- admitted, allowed, exactly-once-in-trace dispatch, provider completion, certified outcome,
  request-indexed encoding, and final policy trace.

`CallRecord config` existentially packages the request-specific evidence while retaining its
raw call, ID, model endpoints, and lease endpoints.

`RecordChain config` generalizes the current joint invariant without weakening it. It must still
prove:

- record IDs are exactly `0 .. nextCall - 1` in order;
- each record starts at the predecessor's model and lease endpoints;
- the final state is the last record's successor;
- the log's ordered call/result boundaries equal the records' boundaries; and
- policy-rejected and admission-rejected records have zero dispatch edges.

The counter runner becomes a configuration value and thin instantiation. Core generic modules
must not import `Cordis.Examples.Counter` or `CounterWire`.

### Session integration

The generic runner's canonical log is the rich `Cordis.Session` log. Structural protocol replay
and call/result-boundary projections are derived from it rather than maintained as an unrelated
second event list.

For every model step, the runner must record at least:

1. turn and step boundaries;
2. entered user messages;
3. the full request header used for that request;
4. raw assistant chunks and the assembled assistant message;
5. each tool call before execution;
6. each corresponding model-facing tool result; and
7. closing step and turn events with no pending tool calls.

The model adapter interface receives `ModelRequest state.session`, so any scripted, fake, or
future external adapter consumes the same proof-carrying request contract.

## Executable and static tests

The slice requires all existing gates plus the following new coverage:

- a valid append-only session whose derived history contains user, assistant, and tool-result
  messages in surface order;
- log-only events demonstrably absent from derived history;
- a valid compaction-style replacement that shadows a contiguous surface range and changes the
  derived history exactly once;
- runtime rejection of a missing replacement endpoint, reversed range, duplicate source,
  forward source, and incomplete shadow coverage;
- compile-time rejection of surface metadata on a log-only event;
- compile-time rejection of a request with a fabricated message history or stale header;
- one generic counter configuration reproducing the `0.1.0` final model and dependent encoded
  results;
- one policy-denied admitted call proving the provider was not dispatched;
- a second non-counter catalog instantiation proving the runner is genuinely generic; and
- negative construction tests for mismatched catalog/wire/view indices and forged joint
  session/record history.

Headline theorems must be added to `Cordis/AxiomAudit.lean`. The full project must remain free of
`sorry`, `admit`, project-defined axioms, `unsafe`, `partial`, external implementation overrides,
and compiler-trust escape hatches.

## Verification gates

Before a commit is described as complete, run:

```bash
lake --wfail build
lake build
lake lean Cordis/NegativeTests.lean
lake exe cordis_tests
lake exe cordis_demo
lake lean Cordis/AxiomAudit.lean
python3 scripts/check_lean_hygiene.py --self-test .
```

Then rerun the Lean gates from a clean `git archive HEAD` materialization. A local `.olean` or
Jujutsu working-copy artifact is not release evidence.

## Non-claims

This slice does not by itself prove:

- behavioral equivalence with the complete TypeScript DeepSeek Harness;
- byte-level JSON parsing, rendering, or storage compatibility;
- durable persistence, flush barriers, crash repair, resume, or fork correctness;
- task/fiber scheduling, fairness, cancellation delivery, or wall-clock concurrency;
- arbitrary-N CORDIS composability or the paper's full dynamic calculus;
- native plugin isolation, process confinement, filesystem safety, or remote-service behavior;
- global exactly-once execution across workers; or
- that a model follows supplied schemas or chooses an appropriate tool.

Those remain later proof/refinement layers. The new work is valuable because it makes the pure
kernel's session and request boundary materially closer to the current Harness architecture
while retaining an exact, auditable theorem boundary.
