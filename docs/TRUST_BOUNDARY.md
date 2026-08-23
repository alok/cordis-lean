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
cross-monoid commutation and yield stability. `TotalQuotientIndependence` adds a finite
totalized/quotient specialization only when success at every context is an explicit certificate;
the paper's literal unrestricted total/quotient setting remains
open. `DomainTotalQuotientIndependence` adds a separate domain-certified refinement: partial
computations remain partial outside a named invariant domain, while totality, preservation, and
quotient transport are proof-carrying inside it. `Schedule` executes sequentially, and
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

`Cordis.DeepSeekHarnessExtensions` adds a generic request-side adapter over the session
`ExtensionSchema` for complete and streaming modes, plus a schema-preserving assistant append.
Its executable fixture keeps a custom log-only event in the append-only log while projecting only
the certified surface message into the request and append result. The schema-indexed runner
retains its sequence/tool-count invariants when a validated terminal rich response is appended
through the existing process/stream fixture. `SessionExtensionRefinement` supplies the bounded
typed-ingress counterpart: the caller's `ExtensionCodec` constructs the dependent kind/payload
sum, while the generic envelope checks the declared tag, safe sequence/time fields, rejected
metadata, and exact session-sequence freshness. Its `ExtensionReplay`/`ValidatedExtensionLog`
certificate consumes the supplied raw list in order, links each dependent event to the exact
intermediate session, and proves the final sequence and typed-event count. The heartbeat/banner
fixture exercises both visibility paths and exact rejection witnesses. This remains a codec
boundary, not arbitrary JSON or deployed provider decoding; provider compatibility, transport,
persistence, and deployed Harness equivalence remain external.

`Cordis.SessionExtensionArchive` is the adjacent persistence-facing composition: it joins the
lossless `SessionEventArchive` with the dependent replay only when every archived record is a
required extension. Known core tags and ignorable records reject, while success retains exact raw
order and the typed final session. This is still an in-memory certificate, not durable storage or
deployed archive equivalence.

`Cordis.DeepSeekHarnessExtensionArchive` attaches that required-extension certificate to the
schema-indexed `ExtensionRunner`. Its `restoreRunner` derives the tool-call count and stores exact
runner/session equality; `RequestCertificate` rebuilds the request from that same endpoint. The
attachment is schema-owned and in memory: mixed current-Harness replay, provider compatibility,
transport, durable storage, and deployed Harness equivalence remain external.

`Cordis.DeepSeekHarnessExtensionRequest` tightens the request edge by requiring
`DeepSeekToolSchema.CertifiedRequestSource` before rebuilding a request from that runner. The
result retains the validated tool-list/name proof and exact builder equation, while duplicate
tool names fail closed. Provider obedience, credentials, transport, and deployed equivalence are
not inferred.

`Cordis.DeepSeekHarnessExtensionPersistence` carries that extension-only certificate through the
logical JSONL header, canonical text, UTF-8 bytes, and `DurableIO.Backend` read/replace/append
surfaces. It retains the exact header/raw suffix and links the restored indexed runner/request
back to the persisted endpoint. Known core and ignorable rows reject; mixed replay, packed-row
persistence, fsync/crash guarantees, and deployed persistence equivalence remain external.

`Cordis.DeepSeekHarnessMixedPersistence` is intentionally weaker than a unified mixed-session
decoder. Its schedule-indexed certificate retains the complete archive and proves the core and
dependent-extension projection certificates separately. The source partition is real and
executable; extension surface edits, global sequence renumbering, combined-schema replay, and
provider/transport/deployed persistence claims remain outside.

`Cordis.DeepSeekHarnessSchemaLift` proves the neighboring schema-index transport for the core:
every validated `Session.noExtensions` event and `ValidLog` transition is lifted into an
arbitrary `ExtensionSchema`, with exact sequence, surface, header, and protocol-projection
equations. The custom-schema example is executable. It does not decode custom extension rows,
merge extension surface edits into the core protocol, or establish provider/transport/deployed
persistence equivalence.

`Cordis.DeepSeekHarnessMixedReplay` adds a bounded global replay certificate above that lift.
Each source row is tagged as core or extension; core rows are refined by the existing stateful
core validator, while extension rows are accepted only when they are custom log-only events.
The shadow core receives a phantom log-only clock row, and the resulting proof carries exact
sequence growth, surface/header invariance, and target-versus-shadow protocol equality. Surface
extension rows, extension encodings of core kinds, malformed rows, and stale sequence numbers
fail closed. This does not prove arbitrary custom surface interleaving, provider compatibility,
transport, persistence, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessTransportContract` is a local, injected-transport composition certificate.
It checks successful HTTP status, validates the response body once, applies `acceptValidated` to
the retained dependent decoder certificate, and links the accepted response to the exact runner
append endpoint. The successful tool-call and 503 fixtures are executable. This is not evidence
of live network reachability, credential validity, provider obedience, TLS/retry behavior,
persistence, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessTransportToolRound` keeps that same dependent transport certificate while
executing its typed tool calls. It does not parse or admit the response a second time; the result
packages the final model, executions, and exact session-runner sequence/tool-count endpoint. The
fixture is process-backed but local, so external tool effects, provider obedience, retries,
persistence, and deployed Harness equivalence remain outside the claim.

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
- `ParallelSchedule.Plan` folds an arbitrary finite sequence of certified windows and barriers,
  retaining exact canonical endpoint/recovery equality, model-order reports, and globally unique
  task IDs. It is still a pure schedule certificate, not wall-clock concurrency.
- `AsyncHarness` adds indexed pending/running/terminal fibers with typed start, complete, fail,
  and cancel transitions. Successful finite traces expose completion order, while a drained
  schedule certificate proves the canonical pure endpoint for a certified permutation. This is
  a bounded state-machine model, not live task handles, wall-clock fairness, promise cancellation
  delivery, cleanup, or a TypeScript/deployed Harness refinement.
- `DurableSettlement.Log` is an intrinsically indexed append-only frame log with a
  collision-free list transcript; `CrashPrefix` proves exact recovery of a retained prefix and
  typed resume after that prefix. This is a pure torn-prefix certificate, not a filesystem or
  cryptographic durability proof.
- `DurableCodec` is the JSON-AST boundary before `DurableSettlement`: it decodes numeric raw
  frames, checks entry-code recovery, sequence/previous/successor/digest continuity, and only
  then constructs a typed `Log`. Malformed JSON, a torn `null` frame, unknown entries, and
  non-contiguous frames fail closed. This still says nothing about bytes, storage, or fsync.
- `DurableBytes` is a separate pure binary boundary over finite `List UInt8` values. Its unary
  length framing and numeric `RawFrame` codec prove exact counted-prefix decoding and expose an
  unconsumed suffix before delegating to `DurableCodec.scanPrefix`; the format is not a JSON
  renderer and is not connected to a filesystem or flush barrier.
- `DurableIO` is the first executable stateful adapter beyond those pure boundaries. It performs
  host `IO` reads/writes/flush calls through `MemoryStore` and `FileBackend`, but the typed
  `AppendPlan`/`RecoveryCertificate` contract separates semantic recovery from that host
  acknowledgement. No stable-media, fsync, crash-atomicity, authentication, or worker-coordination
  theorem is implied.

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
  are rejected by this successful-trace decoder because the local types are not equivalent.

`RuntimeFailureRefinement.validateFailureTrace` is the adjacent normalized failure certificate. It
requires the final JSON chunk to be an in-band `error` or `aborted` finish, retains the exact
ordinary prefix and all typed `LlmFailure` fields, and rejects any chunk after the failure. It is
deliberately not a `RichStream.ValidatedTrace`: upstream failure/abort paths may leave blocks open,
so the certificate proves no local finish, retry/cancellation decision, provider authenticity, or
normal rich/session projection.

`RuntimeOutcomeRefinement.validateOutcome` is the small union dispatcher over those two languages.
It retains the successful rich-stream certificate or the normalized failure certificate without
erasing either branch; if both validators reject, it preserves both structured errors. It does not
choose retry/cancellation policy, reconstruct open blocks, append a session message, or claim
provider/runtime equivalence.
`RuntimeOutcomeSession.validateAndDispatch` is the adjacent pure runner bridge: text/bytes first
retain their decoded source and outcome certificate, then success appends a finished assistant
view while normalized failure returns the exact failure certificate and leaves the runner
unchanged. It does not fabricate failure messages or session events.

`TextRefinement` adds the preceding text boundary for supported append-only fixtures and
normalized failure terminals:
`parseJsonLines` parses newline-delimited text with zero-based line errors, `parseJsonLinesBytes`
rejects invalid UTF-8, and the `validate*Bytes` functions retain the decoded source and the
existing dependent stream/session/failure certificates. The failure path retains an in-band
`error`/`aborted` terminal and does not claim a successful rich trace. Lean's JSON parser and
canonical compact printer
remain library boundaries; no external logger schema, timestamp, transport, or persistence claim
is introduced.

`HarnessPersistenceRefinement` adds a separate logical JSONL storage boundary for the pinned
Harness backend. It requires the `type: "session"` header, decodes the supported header metadata,
retains verbatim event rows, and validates/expands `text-chunks`, `reasoning-chunks`, and
`tool-call-chunks` using safe sequence/time reconstruction before invoking `SessionRefinement`.
Unknown non-packed rows remain delegated to the event decoder, while malformed packed rows,
foreign versions, retired header fields, and foreign header tags fail closed. This is a
JSON-AST/logical-format theorem only: UTF-8 bytes, Zstandard, filesystem paths, byte offsets,
torn-tail repair, indexing, and crash durability are not modeled.

`HarnessPersistenceArchive` is the lossless storage companion for rows that the semantic subset
does not expand. It validates the same typed session header, retains each packed row's exact AST
and one of the three packed tags, and delegates ordinary envelope rows to `SessionArchive`.
Supported certificates and required/ignorable opaque records therefore survive JSONL inspection
without being silently dropped. Malformed ordinary envelopes carry their full storage index;
packed rows remain raw and have no replay semantics here.

`HarnessPersistenceIO` is the executable byte/text adapter above that logical boundary. Its
`ReadCertificate` retains the exact bytes, decoded text, parsed rows, logical persistence result,
and session projection; replacement writes can be revalidated, and `appendValidatedRow` refuses
to append to an invalid existing document. Memory and temporary filesystem fixtures exercise both
backend shapes. Host write/flush acknowledgement remains separate from semantic validity: fsync,
stable media, locking, torn-tail repair, and crash durability are not inferred.

`DeepSeekHarnessPersistenceIO` composes this read certificate with the logical DeepSeek restore
seam. A successful memory or temporary-file read retains the equality tying the decoded archive
to the restored `ConversationRunner` and to its request certificate; invalid UTF-8 remains a
structured text error. This still does not turn backend acknowledgement into fsync, stable-media,
locking, authenticity, or crash-recovery evidence.

`DeepSeekHarnessPersistenceFileLocalSseRetryConversation` then feeds that temporary-file-origin
runner into two real loopback retry rounds. Its dependent result retains the `ReadCertificate`,
archive/session equality, one typed 503 per round, distinct rebuilt request bodies, and the
executable `8 -> 10` endpoint. The file is scoped to `withTempFile`; fsync, stable media, crash
recovery, provider authenticity, external effects, and deployed Harness equivalence remain
outside. `RequestProvenance` also proves that the first plan rebuilds from the validated archive
session, the second from the first appended session, and both serialized bodies match their typed
request sources.

`DeepSeekHarnessPersistenceTransportRound` carries that exact restored runner through a complete
typed request and injected transport. Its `PersistedRound` retains the single response decoder,
`acceptValidated` equality, archive/session equality, typed tool executions, and final
assistant-plus-tool-result runner; `plan_build_archive` reconnects request construction to the
validated archive endpoint. The memory fixture is executable local evidence only. It does not
prove live network reachability, credentials, provider obedience, durable writes, retries,
cancellation, external effects, or deployed Harness equivalence.

`DeepSeekHarnessTransportConversation` composes the same round certificate into a fuel-bounded
`TransportTrace`. The dependent cons constructor forces the next round to start at the exact
previous runner/model endpoint; `TransportStop.completed` carries the final no-tool proof, while
`fuelExhausted` retains the certified prefix. The two-response fixture exercises both stops, but
the model still has no live-provider, retry/cancellation, durability, external-effect, or
deployed-Harness equivalence claim.

`DeepSeekHarnessTransportRetry` keeps retry within the same typed transport boundary. One
complete request plan is reused across bounded attempts; retryable transport/transient-HTTP
failures remain in `RetryHistory`, the successful body is validated once, and the dependent
response is passed to `acceptValidated` and typed tool execution. The 503-to-200 fixture checks
the retry history, attempt bound, and exact assistant/tool endpoint. Backoff, idempotency,
cancellation, persistence, external effects, live-provider behavior, and deployed Harness
equivalence remain outside this immediate injected-transport certificate.

`DeepSeekHarnessTransportRetryConversation` composes those retried rounds into an indexed,
fuel-bounded trace. Each head retains its `RetryHistory`, while the dependent tail starts at the
previous round's exact final runner and model; the executable fixture covers a retried tool round
followed by a no-tool terminal response. Completion and fuel exhaustion are distinct local
certificates. Provider backoff, idempotency, cancellation, persistence, external effects,
live-provider behavior, and deployed Harness equivalence remain external.

`DeepSeekHarnessEndToEnd` composes that retry trace with the byte-backed persistence read. Its
`PersistedRetryRun` retains the validated archive runner in the dependent trace index, the final
runner/model, every retry-aware head, and the typed completion stop. The executable fixture
projects archive `nextSeq = 8`, final `nextSeq = 11`, two rounds, one transient failure, and model
`0`. This is an in-memory/injected-transport certificate only; it does not establish fsync, live
provider reachability, backoff/idempotency, cancellation, external effects, or deployed Harness
equivalence.

`DeepSeekHarnessPersistenceProcessOutcome` attaches the same byte-restored runner to the actual
`IO.Process` outcome adapter. `PersistedProcessRound` retains the streaming request plan, complete
process body, rich outcome, typed execution, and exact endpoint; the deterministic shell fixture
projects archive `nextSeq = 8`, endpoint `nextSeq = 10`, and body length `523`. This is a local
process boundary only: process/credential trust, incremental delivery, blocked-read cancellation,
durability, external effects, and deployed Harness equivalence remain outside.

`DeepSeekHarnessPersistenceStreamRetry` extends that process boundary to a dependent two-round
continuation from the restored runner. Its shell fixture emits the two-call counter stream, runs
the typed tool executions, and emits terminal text after the first tool result is serialized into
the next request; the executable projection checks `8 -> 12`, two rounds, two first-round calls,
one attempt, model `0`, and typed completion. This proves a deterministic local process trace only:
provider/process authenticity, durable recovery, backoff/idempotency, blocked-read cancellation,
external effects, and deployed Harness equivalence remain external.

`DeepSeekHarnessPersistenceStreamRetryCancellation` adds a pre-round cancellation decision to
that same persisted process trace. It retains the first accepted tool round and decides before
round one, projecting `8 -> 11`, one round, two first-round calls, timeout reason, model `0`, and
the exact cancellation boundary. This proves no later request is selected after the decision; it
does not interrupt a blocked read or establish process cleanup, durability, external-effect, or
deployed cancellation equivalence.

`DeepSeekHarnessPersistenceFileStreamRetryCancellation` executes the same dependent cancellation
path after `DurableIO.FileBackend` writes and reads the archive in a temporary file. The returned
certificate still proves exact restored-session equality and the `8 -> 11` cancellation prefix,
and its executable summary records the temporary-file route. `withTempFile` removes the file on
return; fsync, stable media, crash recovery, in-flight interruption, process cleanup, external
effects, and deployed Harness equivalence remain outside.

`DeepSeekHarnessEventFileStreamRetryCancellation` applies that executable file route to the
supported current-Harness event JSONL surface. It writes and reads the event bytes, checks exact
source/read equality before restoring the event archive/session, and then feeds the restored
runner to the process-backed streamed cancellation trace. The result retains the byte witness,
archive/session equality, `8 -> 11` prefix, one round, two first-round calls, timeout reason, and
model `0`. It also retains a dependent streaming request plan rebuilt from the restored session,
with exact plan-build and serialized-body equations. This is request reconstruction evidence, not
an assertion that the process adapter exposes or authenticates its internally consumed request.
`withTempFile` cleanup is scoped; fsync, stable media, crash recovery, blocked-read interruption,
process cleanup, provider authenticity, external effects, and deployed Harness equivalence remain
outside.

`DeepSeekHarnessEventFileLocalSseRetryConversation` carries that current-event file endpoint into
the real two-round loopback HTTP/SSE retry conversation. Both accepted rounds remain indexed by
their predecessor runner; the first request is tied to the validated event archive session and
the second to the first accepted session, with exact serialized-body equations and `8 -> 10`
growth. This is local process/server evidence, not durable-file recovery, provider or credential
authenticity, blocked-read interruption, arbitrary cleanup, external effects, or deployed Harness
equivalence.

`DeepSeekHarnessEventFileProcessSchema` carries the same temporary-file current-event endpoint
into the heterogeneous weather/clock schema process. The dependent result retains source/read
bytes, archive/session equality, the registry-derived streaming plan, complete body, schema step,
and the executable `8 -> 11` endpoint. This is local process evidence, not provider obedience,
credential authenticity, durable storage, byte framing, cancellation, external effects, or
deployed Harness equivalence.

`DeepSeekHarnessEventFileLocalSseSchema` carries that restored event-session endpoint into two real
loopback HTTP/SSE byte-prefix rounds. The scoped heterogeneous registry, valid request counts,
complete byte evidence, distinct rebuilt bodies, dependent two-tool execution, and terminal `8 -> 12`
endpoint are retained together. The deterministic fixture model, local server, scoped approval,
temporary-file lifetime, provider obedience, credentials, durable storage, blocked-read cancellation,
external effects, and deployed Harness equivalence remain outside this certificate.

`DeepSeekHarnessEventFileLocalSseSchemaErrors` carries the same restored endpoint through the typed
failure path. Both scoped weather/clock providers fail with certified messages; their `isError` tool
results are appended before a terminal text round, with two validated requests, two attempts, and
the exact `8 -> 12` endpoint retained. This is still only local fixture evidence: provider obedience,
credential authenticity, durable storage, blocked-read cancellation, external effects, and deployed
Harness equivalence remain outside.

`DeepSeekHarnessPersistenceStreamBytePrefixTimeout` is the bounded persistence-plus-byte-prefix
composition. A memory archive restores the exact runner session; the fuel fixture accepts one
streamed tool round and returns a typed nonterminal stop at `nextSeq = 10` from archive `nextSeq = 8`, while its companion switches to terminal text after the first tool result and completes at
`nextSeq = 11` after two rounds. Both retain model `0` and restored-session equality. This is a
local fixture only: stable media, crash recovery, blocked-read interruption, cleanup,
provider/process authenticity, external effects, and deployed Harness equivalence remain separate
obligations.

`DeepSeekHarnessTransportRetryCancellation` composes that trace with a caller-controlled
pre-round cancellation policy. Its cancellation fixture proves that no request is issued before
round zero and retains the unchanged endpoint and typed reason; its success fixture retains the
503 retry history and the final no-tool endpoint. In-flight process/HTTP interruption, provider
backoff/idempotency, persistence, external effects, and deployed Harness equivalence remain
outside.

`DeepSeekStreamHarnessRetryConversation` is the process-backed streamed analogue. Its indexed
trace retains each complete SSE body, ordered retry history, dependent assistant/tool endpoint,
and exact runner/model tail; fixtures cover tool-to-text completion and an exhausted transient-HTTP
policy. Backoff, idempotency, blocked-read cancellation, persistence, reconnects, external effects,
and deployed Harness retry equivalence remain external.

`DeepSeekStreamHarnessRetryCancellation` composes that trace with a pre-round cancellation policy.
The cancellation constructor retains the exact accepted retry-aware prefix, unchanged runner/model
endpoint, round/reason decision, and retry history inside each retained head. It does not interrupt
in-flight process/HTTP/stream/tool IO or establish cleanup, reconnect, or deployed cancellation
equivalence.

`HarnessPersistenceBytes` is the pure immutable-`ByteArray` companion. Its dependent certificate
retains the original bytes, decoded UTF-8 text, parsed JSONL rows, packed-row expansion, and the
composed Session/Protocol projection. Runtime fixtures cover accepted, malformed, empty, and
invalid-UTF-8 bytes; this remains a parser/refinement witness, not deployed rendering,
compression, filesystem, or crash-durability evidence.

This is soundness of one fail-closed supported subset. It is not completeness for the current
TypeScript `BlockAssembler`, JSON-text parser correctness, transport correctness, or a claim
that provider bytes match the audited AST shapes.

`SessionRefinement` is a second, stateful supported subset. It retains decoded upstream sequence
and time values, accepts selected `request/header` snapshots, route context, whole-list todo
snapshots, empty seed markers, and text/reasoning index-zero `assistant/chunk` records, normalizes
one-based upstream steps to zero-based local steps, derives
`turn/end.nextStep` only from the already validated prefix, and assigns provider string call IDs
to fresh numeric IDs with proof-carrying uniqueness state, reusing those IDs in later call/result
events. Text `user/message` blocks and complete assistant `tool-call` blocks additionally retain
source IDs, provider/model metadata, usage, and provenance references in `State.wireSurface`,
while projecting assistant text plus typed tool calls into the smaller local `Session.Message`
vocabulary. All six pinned turn-end reason tags are decoded into the wire witness: `aborted` maps
to local cancellation, while structured `blocked`, `error`, and `interrupted` facts map to the
local failed-string case without discarding the source payload. Each admitted event carries both a
`Session.ValidatedAppend` and, for runtime events, a `Protocol.ValidatedEvent`; the cumulative
theorem equates the complete rich-session structural projection with intrinsic trace erasure.
Unsupported header/chunk shapes, unsupported replacement shapes, extensions, opaque tool metadata,
replay state, and multimodal blocks,
and unsupported turn-end tags are rejected. No completeness, persistence, or whole-session
behavioral equivalence follows.

`SessionOpaqueMetadata` is the intentionally smaller metadata bridge above that boundary. For a
supported session with provider/tool-owned `tool/result.data.error` and `tool/result.data.meta`,
it sanitizes exactly those two fields before validation, retains their exact source JSON in order,
and proves the existing sanitized Session/Protocol projection. The surface codec can emit the same
quarantined values as raw JSON, and its sanitization theorem recovers the existing tool-result
decoder. It assigns no meaning to either
field and does not claim provider/tool schema equivalence, replay, or complete event coverage.

`SessionArchive` is the lossless envelope companion to that semantic subset. It validates the
current `type`/`seq`/`time`/`data` envelope and its conditional `ignorable`, `sourceEventSeqs`,
and `surfaceOp` fields, retains the original JSON AST, and classifies decoder failures as required
or explicitly ignorable opaque records. A successful `SessionRefinement` decode is retained as a
typed certificate; opaque records are not assigned extension payload semantics or replay behavior.

`DeepSeekHarnessEventArchive` is a certificate-gated attachment, not an opaque-event coercion. Its
`SupportedEventLog` requires an exact `ArchivedLog`, an exact `ValidatedJsonLog`, and a proof that
every retained event is non-opaque. Only then can `RestoredRunner` expose a `ConversationRunner`
whose session equals the validated endpoint; the supported tool-message fixture also rebuilds a
typed request. Known opaque payloads and extensions fail closed, so no event is silently dropped
to make restoration succeed.

`DeepSeekHarnessEventIgnorableProjection` is intentionally weaker and more precise. It keeps the
lossless archive, assigns each physical row a positional keep/drop decision, drops only opaque rows
with the explicit `ignorable: true` marker, and retains supported wire certificates and source
positions. Required opaque rows return a typed error. `DeepSeekHarnessEventIgnorableNormalization`
continues the supported subset: it renumbers retained rows contiguously, remaps supported
`sourceEventSeqs`/`surfaceOp` references through the physical-to-local map, and validates the
rewritten JSON into a local session. Duplicate physical sequences, missing references, malformed
rewrites, and semantic failures return typed errors; opaque payload semantics and deployed Harness
equivalence remain external. `DeepSeekHarnessEventSimulation` consumes the normalized occurrences
with an occurrence-indexed `SourceReplay`: a typed `DecisionLedger` records every keep/drop
decision and each retained `ReplayStep` carries the exact pre-state refinement. The finite replay
proves source positions, local sequence renumbering, protocol erasure, and final
session-projection equality. Provider behavior, bytes, persistence, cancellation delivery, and
complete deployed-Harness equivalence remain external. `DeepSeekHarnessEventIgnorableRunner` attaches the normalized final
session to `ConversationRunner` and rebuilds a typed `ChatRequest` with exact endpoint certificates;
provider authenticity, transport, persistence, and deployed equivalence remain external.
`DeepSeekHarnessEventArchiveReplay` then packages the normalized source replay and the physical
archive ledger in one `ArchiveReplay`: all archive rows are retained by an exact raw projection,
while dropped rows are explicitly opaque/ignorable no-ops and retained rows carry indexed state
transitions. The fixture checks eight supported transitions plus one dropped row at physical
position `2`; this remains a finite supported-subset bridge rather than opaque-payload or deployed
Harness equivalence.
`DeepSeekHarnessEventIgnorableTransport` carries that same dependent runner through the existing
process-backed complete-response conversation trace, retaining final runner/model/stop evidence
and the original normalized-session certificates. It remains injected transport evidence, not a
credential, provider-authenticity, durable-persistence, external-effect, or deployed-equivalence
theorem.

`DeepSeekHarnessEventText` is the corresponding UTF-8/JSONL ingress. `restoreTextRunner` retains
the parsed source and both archive/semantic certificates, while `restoreBytesRunner` first retains
the exact `ByteArray`/UTF-8 equality and then reuses the text path. Invalid encoding and opaque or
extension events remain structured failures; this does not prove logger framing, transport,
persistence, or deployed Harness equivalence.
`DeepSeekHarnessEventPrefix` is the IO-free incremental target below that ingress. Its dependent
`Cursor.push` appends one decoded/refined event to the current session state and snoc trace, and
its fuel-bounded `run` can return an explicit cooperative stop with the unread JSON suffix. It
does not claim JSONL framing, blocked-read interruption, crash durability, or deployed equivalence.
`DeepSeekHarnessEventProcessPrefix` is the line-oriented executable reader below that target. It
feeds complete stdout lines into `Cursor.push`, retaining observed lines, endpoint, exit status, and
typed completion/fuel/cancellation stops, with a proof that consumed equals the dependent
cursor-entry count. Fuel/policy stops kill and wait for the child; malformed lines and nonzero exits
remain typed failures. It does not claim byte framing, blocked-read interruption,
executable/provider authenticity, crash durability, or deployed Harness equivalence.

`DeepSeekHarnessEventProcessTimeout` adds a per-read timer race below that line-oriented
adapter. `Std.Async.Sleep` competes with the blocking `stdout.getLine`; a timer win kills and
waits for the configured child, and `TimedProcessPrefixResult` retains the exact accepted cursor
prefix, line ledger, exit code, stderr, and timeout index. Executable completion and blocked-read
fixtures cover both branches. This is local configured-child interruption evidence, not arbitrary
descendant cleanup, fairness, backpressure, provider/executable authenticity, crash durability,
or deployed asynchronous Harness equivalence.

`DeepSeekHarnessEventProcessTimeoutRefinement` is a proof-level composition above that executable
boundary. It transports the cursor's existing per-entry `RefinedEvent` proofs into an intrinsic
`SessionRefinement.ValidatedSequence`, retaining the exact entry ledger, final state, and protocol
projection without reparsing. The snoc-to-cons conversion is noncomputable proof packaging; it
does not produce a standard raw `decodeEvents` certificate or claim JSONL framing, persistence,
provider authenticity, or deployed Harness refinement.

`DeepSeekHarnessEventProcessOutcome` is the next local composition seam: it carries a restored
event runner through a caller-supplied streaming request source and the complete process-backed
rich-outcome adapter. The result retains the restored-session/raw-archive certificates and the
prepared request, response, dependent-tool, endpoint, and protocol-projection certificates. It
does not turn the event log into authenticated provider configuration or prove deployed runtime
equivalence.

`DeepSeekHarnessEventProcessSchema` is the corresponding registry-aware seam. It attaches the
restored event session to the exact heterogeneous `stream: true` plan, complete process body,
schema-dispatched step, and dependent runner endpoint; text and byte entry points share the same
dependent certificate shape. The local fixture checks the restored eight-row session and the
`8 -> 11` two-tool endpoint, while provider obedience, credentials, byte framing, persistence,
cancellation, external effects, and deployed equivalence remain explicit obligations.
Its `executeRestoredStreamConversation` and byte twin also launch the existing fuel-bounded
complete-body streamed conversation from the restored endpoint, retaining the prepared request,
round history, final runner/model, and completion-or-exhaustion stop. The source remains
caller-supplied and blocked-read cancellation, persistence, and deployed semantics remain
external.

`DeepSeekHarnessPayloadText` composes the same text/byte restore with
`SessionPayloadArchive.PayloadLog`. Its dependent indices force the payload ledger and runner to
describe the same parsed lines, while raw message blocks, usage, tool-result `error`/`meta`, and
unknown block tags remain uninterpreted JSON rather than being assigned provider semantics.

`DeepSeekHarnessPayloadPersistence` carries that ledger through the logical persisted JSONL
archive, pure `ByteArray` validation, and executable memory/temporary-file reads. The restored
value retains the header/storage certificate, expanded event list, semantic runner endpoint, and
raw payload log at one dependent index. Storage and payload errors remain distinct; backend
acknowledgement is not durability, and no crash-recovery or deployed-Harness equivalence is
claimed.

The byte-backed counterpart is intentionally separate: `DeepSeekHarnessPersistenceIO` starts from
`HarnessPersistenceIO.ReadCertificate`, while `DeepSeekHarnessEventArchive` starts from the full
current-event archive plus the stateful event validator. Neither path assigns semantics to an
opaque payload or claims complete deployed Harness equivalence.

`DeepSeekHarnessMetadataArchive` is the explicit exception for a tool-result metadata event. Its
`AttachedLog` aligns the raw `SessionEventArchive` with the sanitized `RetainedLog`, so one known
opaque event remains in the raw ledger while the runner/request uses only the sanitized session.
This is still quarantine, not provider/tool interpretation or opaque replay.

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

`Cordis.GenericSessionHarness` is the reusable rich-session counterpart: it
retains the request header, user/assistant surface, tool calls, tool results,
and lifecycle events for any `GenericHarness.Config`, while proving that the
rich log erases to the generic runner log. `RunnerState.prepareRequestStep`
provides an indexed request-ready handoff whose `Session.mkRequest` is present,
and `attachCompletedDispatch_modelRequest` preserves that certificate across
an accepted call/result append. `Examples.DependentChoiceSession` exercises
this boundary with a non-counter dependent catalog. This is still a finite
in-memory bridge; it does not establish transport, persistence, external
execution, or TypeScript/deployed Harness equivalence.

`Cordis.DeepSeekSessionRequest` connects this handoff to the DeepSeek request vocabulary without
introducing a second snapshot: `SourceAgreement` explicitly equates the source model, system
prompt, and encoded tool schemas to the indexed `Session.ModelRequest`, and `PreparedRequest`
retains the successful `buildChatRequestFor` equation before constructing a raw `RequestPlan` or a
mode-indexed complete/streaming `TypedRequestPlan` whose `stream` flag is carried by the type.
`executeComplete` can run a complete plan through an injected transport and retain the API's
dependent response certificate; `executeStreamingSse` runs a streaming plan through the existing
local SSE process adapter and retains its validated wire frames. Optional DeepSeek controls are
caller policy. `executeCompleteAndAppend` composes the injected complete response with the
schema-indexed `ExtensionRunner`: fail-closed acceptance retains the dependent body, appends the
assistant to the same session, preserves the latest request header, advances sequence/tool-count
invariants, allocates local numeric IDs, and proves `Session.mkRequest` remains present. The module
does not prove parser-backed schema validity, provider obedience, credentials, remote transport
success, or deployed equivalence.

`Cordis.DeepSeekSessionRequestBytes` is the raw-byte continuation of this indexed seam.
`buildCompleteBytePlan` preserves the canonical UTF-8 request body, and
`executeCompleteBytesAndAppend` runs an injected byte transport, retaining raw response bytes,
decoded text, typed acceptance, and the exact schema-indexed runner endpoint. Invalid UTF-8,
HTTP, transport, and semantic response failures remain typed; live networking, credentials,
provider behavior, persistence, and deployed equivalence remain outside.

`Cordis.DeepSeekSessionRequestStreaming` closes the corresponding indexed streaming seam with a
caller-supplied certified finisher. `executeStreamingAndAppend` retains the mode-indexed
streaming plan, strict process/SSE frames, selected finished rich response, and exact
schema-indexed append endpoint; the text/tool/mixed/multi-call wrappers select existing
finishers. Unsupported, malformed/incomplete bodies, blocked-read interruption, live networking,
credentials, provider behavior, persistence, and deployed equivalence remain outside.

## What is checked but not proved

`Cordis.EffectContext` proves the exact function-level effect-context tower through the finite
lift in Theorems 4–5, 7, and 10–16. The `WitnessedEffect` inverse is selected at the application
state and its one-sided law is explicit in the type; the indexed `Run` proves finite reverse-order
raw-context recovery and recovery-target preservation. The module does not prove arbitrary
interleaving, transformation-monoid independence, quotient equivalence, or correspondence to
the deployed TypeScript Harness.

`Cordis.DeepSeekScopedRegistry` is a pure local routing certificate: nearest-first scopes select
dependent entries, restrictions fail closed at the matching scope, and an approval ticket is
retained before the generic provider view executes. Its fixtures cover automatic/review routes
plus restricted, unknown, and approval-rejected calls. Scope construction, authenticated approval,
asynchronous policy waterfalls, persistence, external effects, and deployed Harness equivalence
remain outside.

`Cordis.DeepSeekScopedStreamToolRound` is the checked composition immediately above that routing
certificate. It validates the complete accepted stream body, resolves every assembled call in
nearest-first scope order, retains the approval and dependent reply inside an indexed
`ScopedExecutionTrace`, and appends the assistant plus tool-result messages with exact local
sequence evidence. Its dual-call fixture reaches the expected model/session endpoint, while
terminal shadowing and denied explicit approval are typed failures. This does not establish
scope-construction or approval authentication, live/external tool effects, persistence,
cancellation, or deployed Harness equivalence.

`Cordis.DeepSeekProcessScopedStreamToolRound` is the process-backed companion to that scoped
composition. It retains the local process/status and strict SSE certificates before reusing
scoped approval, model-indexed dependent execution, and exact assistant/tool-result append. The
dual-call fixture validates three accepted frames and the final session endpoint. This is
deterministic complete-body process evidence only: network/authentication, process trust,
incremental delivery, cancellation, persistence, external effects, and deployed Harness
equivalence remain outside.

`Cordis.DeepSeekProcessScopedConversation` lifts this process-backed scoped round across a finite
dependent conversation. Its `Nat → ProcessConfig` family selects the body for each round; every
accepted round retains its process/status, scoped execution, model successor, and exact session
append. A no-call body yields a typed terminal, while exhausted fuel yields a distinct stop. The
local fixture checks a two-round four-message completion and a one-round exhausted prefix. This
does not establish retries, cancellation, persistence, external effects, live provider behavior,
or deployed Harness equivalence.

`Cordis.DeepSeekProcessScopedRequestConversation` adds the missing request-provenance index to
that loop. Each round rebuilds a typed streaming request from the current session and stores the
successful process/SSE/scoped result under the same exact `HttpRequest`. The fixture checks that
the two request bodies differ after the session grows and that completion and fuel exhaustion
remain distinct typed stops; live network/provider behavior, credentials, retries, cancellation,
persistence, external effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekProcessScopedRequestBytePrefixConversation` carries that exact request index into
arbitrary-byte process ingress. A completed witness keeps raw chunks, pending framing, status,
strict SSE completion, scoped approval, dependent execution, and session append together; the
fixture checks two completed rounds with distinct request bodies and a multi-chunk response, while
a one-read run retains a typed prefix-fuel stop. This remains bounded local-process evidence:
network/authentication, executable trust, blocked-read cancellation, backpressure, reconnects,
retries, persistence, external effects, and deployed Harness equivalence are not claimed.
`Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation` adds the real local HTTP boundary:
one bounded loopback server selects distinct dual-tool and terminal SSE bodies by request count,
real curl supplies arbitrary stdout byte chunks, and the resulting scoped conversation retains
the exact request/body/session evolution plus server request-validity and clean-exit evidence.

Executable rejection is valuable, but it is not a refinement theorem.

| Boundary                                                                                                                                                                                                  | Check performed                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             | Missing theorem or guarantee                                                                                                                                                                                                                                                                                                                           |
| --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `Codec.decode`                                                                                                                                                                                            | Rejects JSON AST constructors or lengths outside each decoder's accepted shape.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             | No proof that accepted values are exactly the values denoted by `schema`, and no completeness result for arbitrary JSON.                                                                                                                                                                                                                               |
| `ToolWire.validate`                                                                                                                                                                                       | Resolves a name, checks declaration, decodes the selected input, and requires `certifyAdmission` evidence before returning a dependent call.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | The supplied resolver, codecs, propositions, capability source, and admission procedure are not proved equivalent to a deployed registry or authenticated policy.                                                                                                                                                                                      |
| `Protocol.validateEvent` / `validateTrace`                                                                                                                                                                | Checks the six local event variants and returns exact intrinsic witnesses for successful inputs.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | No translation or equivalence to the full Harness event union; no theorem equates every successful erased `replayRaw` call with witness reconstruction.                                                                                                                                                                                                |
| `Stream.applyRaw`                                                                                                                                                                                         | Checks one text/finish protocol, explicit chunk budget, and terminal-state discipline.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | No witness reconstruction for arbitrary accepted raw streams and no equivalence to Harness `StreamChunk` assembly or persistence.                                                                                                                                                                                                                      |
| `RuntimeRefinement.validateJsonTrace`                                                                                                                                                                     | Decodes a supported current-Harness stream JSON-AST subset, then returns an exact intrinsic `RichStream.ValidatedTrace` or a separated decode/semantic error.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | No byte parser, full stream-union coverage, tolerant-assembler completeness, transport, storage, or whole-runtime equivalence.                                                                                                                                                                                                                         |
| `LoaderHMR.reconcile`, `classify`, `detectStale`, `transactionalReload`                                                                                                                                   | Models Definition 74 entries, stable-ID keyed configuration actions, Algorithm 8 fixed-point accepted/declined classification with unresolved-cycle fallback, Algorithm 9 declined-boundary stale walks, and Algorithm 10's staged reload with exact failure rollback.                                                                                                                                                                                                                                                                                                                                                                                                                                      | No dynamic-import evaluator, filesystem watcher, real fiber/cache mutation, external disposal, or deployed loader/HMR equivalence.                                                                                                                                                                                                                     |
| `RuntimeFailureRefinement.validateFailureTrace`                                                                                                                                                           | **Checked/proved:** decodes a terminal normalized `error`/`aborted` finish, retaining the exact ordinary prefix and typed `LlmFailure`; successful finishes, malformed fields, and post-failure chunks fail closed.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         | No open-block reconstruction, normal rich/session projection, retry/cancellation policy, provider authenticity, byte parser, or whole-runtime equivalence.                                                                                                                                                                                             |
| `RuntimeOutcomeRefinement.validateOutcome`                                                                                                                                                                | **Checked/proved:** dispatches the supported successful and normalized failure languages into one dependent outcome and retains both structured errors when neither accepts.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | No retry/cancellation choice, open-block reconstruction, session-message append, provider authenticity, or whole-runtime equivalence.                                                                                                                                                                                                                  |
| `RuntimeOutcomeSession.validateAndDispatch`                                                                                                                                                               | **Checked/proved:** validated JSON, canonical text, and UTF-8 byte fixtures append successful assistant views through the existing pure runner; normalized failure returns its exact certificate with the runner unchanged and source text retained.                                                                                                                                                                                                                                                                                                                                                                                                                                                        | No fabricated failure message, retry/cancellation policy, source-event synthesis, persistence, provider authenticity, or whole-runtime equivalence.                                                                                                                                                                                                    |
| `SessionRefinement.validateJsonLog`                                                                                                                                                                       | Stateful supported-subset decoding returns exact rich append/replacement witnesses, selected request-header, route-context, todo, seed, and text/reasoning assistant-chunk log records, text/reasoning/image/complete-assistant-tool-call surface metadata in `State.wireSurface`, runtime protocol witnesses when applicable, fresh local call-ID evidence reused by call/result events, and a cumulative projection theorem.                                                                                                                                                                                                                                                                              | No complete event union, unsupported header/chunk shapes, unknown todo statuses, nonempty seed payloads, unsupported/malformed replacement shapes, persisted JSONL parser, timestamp truth, crash recovery, or whole-session equivalence. Reasoning and image surface blocks are wire-visible but omitted from the smaller local text/tool projection. |
| `SessionRefinement.SurfaceCodec.encodeWireEvent`, `decode_encode`, `decodeWireEventsText_of_encoded`, `decodeWireEventsBytes_of_encoded`, `decode_sanitized_toolResultEventWithMetadata`                  | **Checked/proved/exercised:** reverse codec covers text-only user, text/reasoning/tagged-raw-image/complete-tool-call assistant, singleton-text tool events, and a metadata-aware raw tool-result emitter; AST/text/bytes retain safe integers, usage, provenance, ranges, IDs, raw tool-call arguments, `isError`, and quarantined `error`/`meta`, with assistant/user/tool/image/metadata and invalid-UTF-8 fixtures.                                                                                                                                                                                                                                                                                     | Narrow source-shaped local serialization boundary layered over `SessionRefinement`; tagged image objects and tool metadata are retained as opaque raw JSON until sanitization.                                                                                                                                                                         | Image schema semantics, provider metadata semantics, unsupported surface operations, full event-union codec, deployed logger equivalence, provider obedience, or persistence theorem are not claimed.                                      |
| `SessionOpaqueMetadata.validateLogRetainingMetadata`                                                                                                                                                      | Sanitizes only `tool/result.data.error` and `tool/result.data.meta`, retains their exact source JSON in order, and composes the existing dependent Session/Protocol validation with an unchanged sanitized projection.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | No provider/tool metadata semantics or schema equivalence, opaque replay/resume behavior, complete event-union coverage, persistence, or whole-session equivalence.                                                                                                                                                                                    |
| `SessionArchive.archive`, `ArchivedLog.raw_eq`                                                                                                                                                            | **Checked/proved:** every envelope-valid current-Harness record is retained in input order; supported records carry the existing typed decoder certificate, while unknown/unsupported records remain explicitly `opaqueRequired` or `opaqueIgnorable`; the raw JSON AST is preserved exactly.                                                                                                                                                                                                                                                                                                                                                                                                               | No extension payload semantics, opaque replay/resume behavior, complete event-union semantic validation, byte parser, timestamp truth, persistence, crash recovery, or whole-session equivalence.                                                                                                                                                      |
| `SessionPayloadArchive.archivePayload`, `PayloadLog.raw_exact`, `PayloadLog.length_exact`                                                                                                                 | **Checked/proved:** object-shaped known payloads retain exact message/chunk source objects and content-array order; all five current content-block tags plus unknown extensions are classified, assistant usage and tool-result `error`/`meta` stay raw, and malformed known shapes remain attached to their retained event AST.                                                                                                                                                                                                                                                                                                                                                                            | No provider/tool schema validation, opaque replay/resume semantics, local Session projection, persistence, crash recovery, or whole-session equivalence.                                                                                                                                                                                               |
| `TextRefinement.validate*Bytes`                                                                                                                                                                           | Parses UTF-8 JSONL into exact AST lines and composes the supported stream/session/failure validators, retaining the source text and dependent certificates. The failure branch retains a normalized `error`/`aborted` terminal.                                                                                                                                                                                                                                                                                                                                                                                                                                                                             | No deployed JSONL schema/logger framing, timestamp truth, transport, persistence, open-block recovery, or full Harness event/session equivalence.                                                                                                                                                                                                      |
| `HarnessPersistenceRefinement.validatePersistedJson`, `ValidatedPersistedJson.projection_exact`                                                                                                           | **Checked/proved:** the pinned logical JSONL header/storage split is retained; verbatim rows and exact packed text/reasoning/tool-call rows expand into event ASTs with safe sequence/time reconstruction, then compose with stateful session validation and its projection certificate.                                                                                                                                                                                                                                                                                                                                                                                                                    | Harness JSONL `format.ts`/`chunk-rows.ts` at `99f6f02`.                                                                                                                                                                                                                                                                                                | JSON AST only: no UTF-8/file framing, Zstandard, path sanitization, offsets, torn-tail repair, indexing, crash durability, or complete session-event coverage.                                                                             |
| `HarnessPersistenceIO.readValidated`, `replaceRows`, `appendValidatedRow`, `ReadCertificate`                                                                                                              | **Checked/exercised:** memory and filesystem backends read UTF-8 bytes into exact text/row/persistence/session certificates; replacement is revalidated and validated appends preserve the same logical proof boundary.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | Executable adapter above the logical JSONL refinement.                                                                                                                                                                                                                                                                                                 | Host acknowledgement is not fsync or stable-media evidence; no locking, torn-tail repair, crash durability, canonical deployed rendering, or complete storage-union compatibility is claimed.                                              |
| `HarnessPersistenceBytes.validatePersistedBytes`, `ValidatedPersistedBytes.projection_exact`                                                                                                              | **Checked/proved:** a pure `ByteArray` witness retains source bytes, decoded text, parsed rows, packed-row expansion, and the final Session/Protocol projection; executable fixtures cover accepted and fail-closed byte cases.                                                                                                                                                                                                                                                                                                                                                                                                                                                                             | Byte-level composition of the pinned Harness JSONL persistence subset.                                                                                                                                                                                                                                                                                 | Lean UTF-8/JSON parsing is a library boundary; no deployed renderer, compression, filesystem, torn-tail repair, crash durability, or complete storage-union compatibility is claimed.                                                      |
| `DeepSeekApi.buildRequest`, `validateResponse`, `execute`                                                                                                                                                 | Constructs a typed non-streaming OpenAI-compatible chat request, decodes a successful response into a dependent parse/decode certificate, and keeps transport, HTTP status, and API errors distinct.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | The fixture transport is deterministic `IO`; no live HTTP delivery, credential validity, provider-complete schema, streaming, or local `ToolSpec` validation is proved.                                                                                                                                                                                |
| `DeepSeekApiBytes.ByteRequestPlan`, `ValidatedResponseBytes`, `validateResponseBytes`, `execute`                                                                                                          | **Checked/proved/exercised:** retains exact UTF-8 request bytes, decodes successful byte responses into text plus the existing typed parse/decode certificate, and preserves invalid UTF-8 and non-2xx bodies as distinct byte-level errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                | Explicit raw-byte adapter above the typed DeepSeek API boundary.                                                                                                                                                                                                                                                                                       | The byte transport is injected and canonical UTF-8/JSON behavior is the local oracle; no network reachability, credential validity, provider obedience, byte-level deployed compatibility, or Harness equivalence is proved.               |
| `DeepSeekToolSchema.ValidatedParameters`, `validateParameters`, `ValidatedArguments`, `validateArguments`, `validateToolDefinition`, `validateRequestSource`, `CertifiedRequestSource.buildRequestPlan`   | **Checked/proved/exercised:** a bounded object-parameter vocabulary validates primitive property types, optional descriptions, required-name uniqueness/presence, optional `additionalProperties`, nonempty names, and duplicate tool names while retaining exact source JSON and indexing a certified request builder by the original tool list. A second argument certificate parses an object, proves duplicate-free fields and required names, checks primitive value kinds, and rejects unknown fields under `additionalProperties: false`.                                                                                                                                                            | This is a deliberately bounded request-side schema certificate. Nested schemas, unions, constraints, complete JSON-Schema semantics, provider validation, model obedience, and deployed Harness equivalence remain external.                                                                                                                           |
| `DeepSeekToolAdmission.CertifiedFunctionCall`, `validateFunctionCall`                                                                                                                                     | **Checked/proved/exercised:** a raw provider function call is accepted only when its name equals a certified declaration, and the result carries the parsed `ValidatedArguments` proof.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | A pre-execution bridge from provider wire data to the bounded schema certificate.                                                                                                                                                                                                                                                                      | No call-ID authenticity, provider obedience, generic capability lookup/execution, or deployed Harness equivalence is proved.                                                                                                               |
| `DeepSeekGenericBridge.SchemaToolBinding`, `validateAndAdmit`                                                                                                                                             | **Checked/proved/exercised:** an explicit provider/generic name binding composes the provider certificate with generic dependent admission and returns the selected local call/request type existentially together with both validation certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                       | A pre-execution bridge from bounded provider schema to the generic harness contract.                                                                                                                                                                                                                                                                   | No schema semantic equivalence, call-ID authenticity, provider execution, external effects, or deployed Harness equivalence is proved.                                                                                                     |
| `DeepSeekSchemaExecution.executeCertifiedCall`                                                                                                                                                            | **Checked/proved/exercised:** the schema-aware path applies generic policy and invokes the committed dependent `View` only after combined admission succeeds, retaining typed provider/schema, policy, reply, and execution certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                   | A pure schema-aware dispatch adapter over the generic contract.                                                                                                                                                                                                                                                                                        | No provider obedience, call-ID authenticity, live external effects, raw-path equivalence, or deployed Harness equivalence is proved.                                                                                                       |
| `DeepSeekSchemaHarness.SchemaExecutedTool`, `executeCertifiedFunctionCall`, `appendCertifiedToolResult`, `appendCertifiedToolResultToRunner`                                                              | **Checked/proved/exercised:** the provider certificate remains nested while the successful schema-aware execution is reified as the existing `DeepSeekHarness.ExecutedTool`; exact tool-result message, next-sequence, protocol-projection, and `ConversationRunner` append theorems are reused.                                                                                                                                                                                                                                                                                                                                                                                                            | Post-execution transport into the local session/runner surface.                                                                                                                                                                                                                                                                                        | No re-execution, provider obedience, call-ID authenticity, live external effects, persistence, or deployed Harness equivalence is proved.                                                                                                  |
| `DeepSeekSchemaRound.AcceptedSingleToolCall`, `acceptSingleToolCall`, `executeSchemaRound`                                                                                                                | **Checked/proved/exercised:** an accepted API response is constrained to exactly one function call, preserving the response/tool-call witness; schema-aware execution then reaches the existing runner with exact endpoint evidence, while zero/multiple calls fail structurally.                                                                                                                                                                                                                                                                                                                                                                                                                           | Bounded complete-body one-tool response round.                                                                                                                                                                                                                                                                                                         | No multi-tool dispatch, live transport, provider obedience, call-ID authenticity, persistence, or deployed Harness equivalence is proved.                                                                                                  |
| `DeepSeekSchemaMultiRound.AcceptedToolCalls`, `executeSchemaCalls`, `executeSchemaMultiRound`                                                                                                             | **Checked/proved/exercised:** a nonempty response call list is retained exactly; recursive execution carries one schema/generic binding through the evolving model, records a typed failure index, proves execution-list length, and appends every certified result to the existing runner.                                                                                                                                                                                                                                                                                                                                                                                                                 | Bounded homogeneous complete-body multi-call response round.                                                                                                                                                                                                                                                                                           | Heterogeneous registries, live transport, provider obedience, call-ID authenticity, persistence, and deployed Harness equivalence are not proved.                                                                                          |
| `DeepSeekSchemaRegistry.SchemaToolRegistry`, `resolveSchemaTool`, `executeSchemaRegistryCalls`, `executeSchemaRegistryRound`                                                                              | **Checked/proved/exercised:** a finite name-unique registry stores entry-specific schema/generic bindings; dependent lookup retains the selected entry and exact name equality; mixed-operation calls thread certified model successors, preserve execution-list length, append all results, and reject an unknown later name with its index.                                                                                                                                                                                                                                                                                                                                                               | Bounded heterogeneous schema-registry/runner composition.                                                                                                                                                                                                                                                                                              | No provider-complete discovery, live transport, provider obedience, call-ID authenticity, persistence, or deployed Harness equivalence is proved.                                                                                          |
| `DeepSeekSchemaConversation.executeSchemaRegistryConversationRound`                                                                                                                                       | **Checked/proved/exercised:** registry-derived tool declarations are tied to a typed complete-body request plan; the explicit transport returns a validated response, and one accepted heterogeneous round retains the plan, response, accepted calls, dependent execution batch, and runner endpoint.                                                                                                                                                                                                                                                                                                                                                                                                      | Heterogeneous registry attached to the typed DeepSeek transport seam.                                                                                                                                                                                                                                                                                  | No remote credential/provider-obedience, call-ID authenticity, persistence, retry, cancellation, external-effect, or deployed Harness equivalence is proved.                                                                               |
| `DeepSeekSchemaConversationBytes.executeSchemaRegistryConversationRound`                                                                                                                                  | **Checked/proved/exercised:** a typed complete plan becomes exact UTF-8 request bytes; a successful byte response retains source bytes, decoded text, and parse/decode certificates before one heterogeneous registry round is admitted, preserving accepted calls, dependent batch, and runner endpoint.                                                                                                                                                                                                                                                                                                                                                                                                   | Raw-byte heterogeneous schema conversation boundary.                                                                                                                                                                                                                                                                                                   | Injected transport and canonical UTF-8/JSON behavior only; no remote reachability, credential/provider obedience, byte-level deployed compatibility, persistence, retry, cancellation, external effects, or Harness equivalence is proved. |
| `DeepSeekSchemaConversationLoop.executeSchemaRegistryConversationStep`, `runSchemaConversation`                                                                                                           | **Checked/proved/exercised:** a validated no-tool response is retained as a terminal witness; certified tool rounds advance the dependent model and runner under explicit fuel; the existential round history and fuel-exhaustion stop are distinct.                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Caller-fueled transport-backed heterogeneous conversation loop.                                                                                                                                                                                                                                                                                        | Complete-body and caller-fueled only; no retries, in-flight cancellation, persistence, external effects, provider obedience, or deployed Harness equivalence is proved.                                                                    |
| `DeepSeekSchemaTransportRetryCancellation.executeSchemaRetryStep`, `SchemaRetryTrace`, `SchemaRetryStop`, `run`                                                                                           | **Checked/proved/exercised:** bounded retry reuses one request plan; the successful validated response feeds terminal admission or heterogeneous registry execution without a second decode; pre-round cancellation retains the unchanged endpoint; tool-round tails are dependent and completion/cancellation/exhaustion are distinct.                                                                                                                                                                                                                                                                                                                                                                     | Heterogeneous schema registry plus injected retry and caller-controlled pre-round cancellation.                                                                                                                                                                                                                                                        | No in-flight process/HTTP interruption, provider backoff/idempotency, persistence, external effects, credential/network trust, provider obedience, or deployed Harness equivalence is proved.                                              |
| `DeepSeekSchemaProcessRetryCancellation.processRetryTransport`, `Example.cancellationRun`, `Example.successRun`                                                                                           | **Checked/exercised:** the dependent retry/cancellation result crosses the existing `IO.Process`/`sh` adapter; successive fixture invocations retain a 503 retry, heterogeneous weather/clock execution, and terminal no-tool completion, while cancellation before round zero retains the unchanged endpoint.                                                                                                                                                                                                                                                                                                                                                                                              | Process-backed local evidence below the injected transport seam.                                                                                                                                                                                                                                                                                       | No network reachability, credential validity, provider obedience, shell/process trust, in-flight interruption, backoff/idempotency, persistence, external effects, or deployed Harness equivalence is proved.                              |
| `DeepSeekRequestMode.TypedRequestPlan`, `buildTypedCompleteRequest`, `buildTypedStreamingRequest`, `executeComplete`                                                                                      | **Checked:** complete/streaming request plans carry an equality certificate for the serialized `stream` flag; terminal execution consumes only the complete plan, and complete Harness round paths use that typed builder internally.                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Prevents mode confusion at the Lean API boundary.                                                                                                                                                                                                                                                                                                      | This is a request-shape certificate, not proof of live transport, provider behavior, or deployed Harness equivalence; the raw `RequestPlan` compatibility surface remains available.                                                       |
| `DeepSeekCurlTransport.runProcess`, `processTransport`, `curlTransport`                                                                                                                                   | **Checked/exercised:** invokes a configured executable with the request body on stdin, URL/headers as direct argv values, parses an explicit status trailer, and maps spawn/exit/malformed-output failures into the transport seam; the deterministic `sh` fixture reaches the typed DeepSeek decoder.                                                                                                                                                                                                                                                                                                                                                                                                      | Process-backed adapter evidence only. No network reachability, credential validity, executable trust, shell/curl semantics, timeout guarantee, provider-complete schema, streaming, or deployment equivalence is proved.                                                                                                                               |
| `DeepSeekCurlStream.executeSse`, `curlProcess`, `fixtureResponse`                                                                                                                                         | **Checked/exercised:** composes the complete-body process boundary with strict SSE validation, preserving typed process, HTTP-status, and stream errors before exposing frames; the deterministic `sh` fixture returns the example SSE body.                                                                                                                                                                                                                                                                                                                                                                                                                                                                | No incremental reader, buffering/backpressure, cancellation, reconnect, network, credential, executable-trust, or provider-complete assembler claim is made.                                                                                                                                                                                           |
| `DeepSeekCurlOutcome.executeOutcome`, `ProcessedOutcome`, `OutcomeClientError`                                                                                                                            | **Checked/exercised:** runs the deterministic process/status boundary into the unified provider-failure/text/tool/mixed/multi outcome validator, preserving the selected dependent witness and distinct process/status/semantic errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | Complete-body process-to-outcome bridge only. No incremental delivery, retry, cancellation, network/credential trust, session append, or deployed provider-equivalence claim is made.                                                                                                                                                                  |
| `DeepSeekOutcomeSession.dispatchOutcome`, `executeAndDispatchOutcome`                                                                                                                                     | **Checked/proved/exercised:** a validated provider failure returns with the same runner, while a successful rich outcome is finished and appended through the proof-carrying runner; deterministic process fixtures cover failure, text, tool, mixed, and multi branches.                                                                                                                                                                                                                                                                                                                                                                                                                                   | Typed local policy boundary between terminal outcomes and session state.                                                                                                                                                                                                                                                                               | Source-event evidence is caller-supplied; failure-to-message policy, persistence, retry, cancellation, external tools, and whole-session equivalence remain outside.                                                                       |
| `DeepSeekOutcomeConversation.dispatchOutcome`, `executeAndDispatchOutcome`, `executeOutcomeWithTools`, `executeAndRunOutcome`                                                                             | **Checked/proved/exercised:** a process-backed provider failure preserves `ConversationRunner`; successful rich terminal views append with model/tool-count certificates, project calls to `FunctionCall`, route them through the existing dependent executor, and append certified tool results. Deterministic failure/text/counter-tool fixtures cover the handoff and execution branches.                                                                                                                                                                                                                                                                                                                | Typed terminal-outcome handoff plus dependent tool execution into the conversation runner.                                                                                                                                                                                                                                                             | Provider-ID authentication, failure/retry policy, persistence, cancellation, external process trust, and whole-session/deployed equivalence remain outside.                                                                                |
| `DeepSeekOutcomeTransportLoop.executeOutcomeTransportRound`, `runOutcomeTransport`, `Example.run`                                                                                                         | **Checked/proved/exercised:** a generic `Transport` round builds a type-indexed `stream: true` request, keeps transport/status/terminal/execution failures separate, preserves provider failures without mutating the runner, and executes a deterministic tool round followed by a text completion with the updated runner.                                                                                                                                                                                                                                                                                                                                                                                | Generic transport-backed complete-body rich-outcome continuation.                                                                                                                                                                                                                                                                                      | Incremental reads, backpressure, reconnects, retry, cancellation, credentials, external tool trust, and deployed Harness equivalence remain outside.                                                                                       |
| `DeepSeekCurlSession.executeText`, `executeAndAppendText`, `ProcessedResponse`                                                                                                                            | **Checked/exercised:** retains the process-backed wire certificate, projects a terminal text response through the rich/session bridge, and appends it to the pure runner while preserving sequence/tool-count proofs; a terminal text `sh` fixture exercises the complete path.                                                                                                                                                                                                                                                                                                                                                                                                                             | No incremental reader, cancellation, source-event authenticity, provider-ID authenticity, persistence, external execution, or whole-session equivalence is proved.                                                                                                                                                                                     |
| `DeepSeekHarnessProcess.PreparedRequest`, `prepareRequest`, `executePreparedText`, `executeSourceText`, `ProcessRound`                                                                                    | **Checked/proved/exercised:** keeps the typed Harness source, exact request plan, and successful build equation tied to the runner session before process launch; the response and exact append endpoint remain indexed, with request and process failures distinct.                                                                                                                                                                                                                                                                                                                                                                                                                                        | Complete-body request-provenance bridge only. No credential/provider authenticity, incremental transport, persistence, external tool execution, cancellation, or deployed Harness equivalence is proved.                                                                                                                                               |
| `DeepSeekHarnessProcessOutcome.PreparedStreamingRequest`, `prepareStreamingRequest`, `executePreparedOutcome`, `executeSourceOutcome`, `ProcessOutcomeRound`                                              | **Checked/proved/exercised:** keeps the typed source and exact `stream: true` plan tied to a complete-body provider-failure or rich terminal outcome; dependent tool execution and the final `ConversationRunner` endpoint remain indexed by the same body, with request, process/status/stream, and execution failures distinct.                                                                                                                                                                                                                                                                                                                                                                           | Rich process-backed request-provenance bridge only.                                                                                                                                                                                                                                                                                                    | No provider/credential authenticity, incremental delivery, cancellation, persistence, external tool trust, or deployed Harness equivalence is proved.                                                                                      |
| `DeepSeekHarnessLiveProbe.parseApiKey`, `readApiKey`, `PreparedRequest`, `runWithKey`, `runFromEnvironment`, `Example.run`                                                                                | **Checked/proved/exercised:** classifies missing and empty environment credentials without logging; retains a complete-mode request plan and exact build equation; and runs the bounded conversation path through either the existing curl adapter or an injected two-response fixture.                                                                                                                                                                                                                                                                                                                                                                                                                     | Explicit credential/runtime handoff above the typed local Harness.                                                                                                                                                                                                                                                                                     | No credential validity, network reachability, provider obedience, process trust, backoff/idempotency, secret persistence, or deployed Harness equivalence is proved.                                                                       |
| `DeepSeekHarnessLiveStreamProbe.PreparedRequest`, `prepareRequest`, `runWithKey`, `runFromEnvironment`, `Example.run`, `Example.fixtureSummary`                                                           | **Checked/proved/exercised:** classifies the environment credential without logging; proves a `stream: true` request; feeds configured curl stdout byte chunks through the dependent byte-prefix conversation runner; and retains the raw-prefix, streamed-round, model/session endpoint, and explicit fuel-exhaustion evidence.                                                                                                                                                                                                                                                                                                                                                                            | Credential-safe live streaming handoff above the typed byte-prefix Harness seam.                                                                                                                                                                                                                                                                       | No credential validity, remote reachability, provider obedience, process trust, blocked-read cancellation, backpressure, retries, persistence, or deployed Harness equivalence is proved.                                                  |
| `DeepSeekHarnessLocalHttp.runWithKey`, `runCompleteAppendWithKey`, `LocalProbeResult`, `CompleteAppendProbeResult`, `Example.run`, `Example.summarize`                                                    | **Checked/proved/exercised:** starts a one-shot loopback HTTP server, sends the actual complete request through curl, validates method/route/authorization/model/`stream: false`, and retains port/request/validity counts, server exit evidence, the prepared request, and either the final conversation endpoint or the dependent accepted-response append endpoint in the indexed runner.                                                                                                                                                                                                                                                                                                                | Local process/HTTP runtime witness for the typed Harness and request-to-append boundaries.                                                                                                                                                                                                                                                             | No remote reachability, TLS, credential validity, provider obedience, executable trust, retry/idempotency, arbitrary cleanup, or deployed Harness equivalence is proved.                                                                   |
| `DeepSeekSchemaLocalHttp.runWithKey`, `LocalSchemaHttpResult`, `Example.run`, `Example.summarize`                                                                                                         | **Checked/proved/exercised:** starts a one-shot loopback HTTP server, validates a heterogeneous two-tool complete request at method/route/authorization/model/mode boundaries, sends the weather/clock tool response followed by a terminal response through real curl, and retains the prepared plan, dependent tool/terminal witnesses, request counts, server exit, final model, and runner endpoint.                                                                                                                                                                                                                                                                                                    | Local heterogeneous schema process/HTTP witness.                                                                                                                                                                                                                                                                                                       | No remote reachability, TLS, credential/provider authenticity, executable trust, retry/cancellation, persistence, external effects, or deployed Harness equivalence is proved.                                                             |
| `DeepSeekHarnessLocalSse.runWithKey`, `PreparedStreamingRequest`, `LocalSseResult`, `Example.run`, `Example.summarize`                                                                                    | **Checked/proved/exercised:** starts a one-shot loopback HTTP server, validates a typed `stream: true` request, emits the SSE response in complete line chunks, sends it through the real curl process and incremental reader, then retains the delivered lines, reconstructed body, strict wire certificate, finished text projection, and appended runner endpoint.                                                                                                                                                                                                                                                                                                                                       | Local line-oriented streaming runtime witness for the typed Harness boundary.                                                                                                                                                                                                                                                                          | No byte framing, backpressure, blocked-read cancellation, reconnect, remote/TLS reachability, credential/provider authenticity, executable trust, or deployed Harness equivalence is proved.                                               |
| `DeepSeekHarnessLocalSseRetry.runWithRetry`, `LocalSseRetryResult`, `Example.run`, `Example.summarize`                                                                                                    | **Checked/proved/exercised:** starts a two-request loopback HTTP server, validates both typed streaming requests, returns one transient HTTP 503 before the real curl/incremental-reader SSE success, and retains the typed failure history, reused plan, accepted body/wire certificate, and single appended runner endpoint.                                                                                                                                                                                                                                                                                                                                                                              | Local bounded retry/reconnect runtime witness for the typed Harness boundary.                                                                                                                                                                                                                                                                          | No provider backoff, tool idempotency, arbitrary retry policy, blocked-read cancellation, byte-level backpressure, credential/TLS authenticity, or deployed retry equivalence is proved.                                                   |
| `DeepSeekHarnessLocalSseRetryConversation.runTwoRounds`, `RetryConversationResult`, `RetryConversationResult.session_advance_twice`, `Example.run`, `Example.summarize`                                   | **Checked/proved/exercised:** repeats the real two-attempt loopback retry over two dependent conversation rounds; each round retains one typed transient HTTP 503 and one accepted append, while the second request is rebuilt from the first round's exact session endpoint and request body.                                                                                                                                                                                                                                                                                                                                                                                                              | Local request/session-indexed retry conversation evidence only.                                                                                                                                                                                                                                                                                        | No provider backoff, idempotency, arbitrary retry policy, cancellation, persistence, external effects, credential/TLS authenticity, or deployed retry/conversation equivalence is proved.                                                  |
| `DeepSeekHarnessLocalSseTimeout.runWithTimeout`, `TimedPrefix`, `Completed`, `Example.timeoutRun`, `Example.fastRun`                                                                                      | **Checked/proved/exercised:** starts a loopback HTTP server that flushes two valid SSE lines and then delays; a real asynchronous timer races the blocking curl stdout read, kills/waits the configured child, and retains the exact dependent prefix. A zero-delay sibling completes through strict wire validation and one runner append.                                                                                                                                                                                                                                                                                                                                                                 | Local configured-process in-flight timeout witness for the typed Harness boundary.                                                                                                                                                                                                                                                                     | No arbitrary descendant cleanup, fairness, backpressure, credential/TLS authenticity, provider-complete assembly, reconnect semantics, or deployed cancellation equivalence is proved.                                                     |
| `DeepSeekHarnessLocalSseMultiTool.runWithKey`, `PreparedMultiToolRequest`, `LocalSseMultiToolResult`, `Example.run`, `Example.summarize`                                                                  | **Checked/proved/exercised:** starts a one-shot loopback HTTP server, validates the typed `stream: true` request, emits the existing two-call SSE body through real curl, then invokes `executeConversationMultiStreamRound`; both local IDs, dependent executions, certified tool-result messages, request counts, and final runner endpoint remain retained.                                                                                                                                                                                                                                                                                                                                              | Local rich multi-tool HTTP/SSE runtime witness.                                                                                                                                                                                                                                                                                                        | No provider-complete assembly, byte/backpressure semantics, blocked-read cancellation, reconnect policy, credential/TLS authenticity, arbitrary process cleanup, or deployed Harness equivalence is proved.                                |
| `DeepSeekHarnessLocalSseMultiToolPrefix.runWithPolicy`, `PreparedMultiToolPrefixRequest`, `LocalSseMultiToolPrefixResult`, `Example.completeRun`, `Example.cancelledRun`, `Example.exhaustedRun`          | **Checked/proved/exercised:** starts a broken-pipe-safe loopback HTTP server, validates `stream: true`, feeds each complete curl line through the typed prefix state, and either reaches the dependent two-tool runner or retains a cancellation/fuel prefix before dispatch. Request counts, validity, server exit, prepared plan, parsed frames, and terminal tool execution remain inspectable.                                                                                                                                                                                                                                                                                                          | Local line-prefix multi-tool HTTP/SSE witness.                                                                                                                                                                                                                                                                                                         | No byte framing, backpressure, fairness, blocked-read interruption, reconnect policy, provider-complete assembly, credential/TLS authenticity, arbitrary process cleanup, or deployed Harness equivalence is proved.                       |
| `DeepSeekHarnessLocalSseMultiToolBytePrefix.runWithReads`, `LocalSseMultiToolBytePrefixResult`, `Example.completeRun`, `Example.exhaustedRun`                                                             | **Checked/proved/exercised:** starts a broken-pipe-safe loopback HTTP server, validates `stream: true`, sends the response through real curl, consumes bounded stdout byte chunks, and either retains the completed raw/framed byte witness beside both dependent executions or retains a one-read raw prefix before dispatch. Request counts, validity, server exit, prepared plan, and typed byte-prefix error remain inspectable.                                                                                                                                                                                                                                                                        | Local byte-prefix multi-tool HTTP/SSE witness.                                                                                                                                                                                                                                                                                                         | No byte-level backpressure, blocked-read interruption, reconnect policy, provider-complete assembly, credential/TLS authenticity, arbitrary process cleanup, or deployed Harness equivalence is proved.                                    |
| `DeepSeekHarnessLocalSseProviderAssemblyTool.runWithKey`, `PreparedRequest`, `LocalProviderAssemblyResult`, `Example.run`, `Example.summary`                                                              | **Checked/proved/exercised:** starts a one-shot loopback HTTP server, validates the typed `stream: true` request, emits the incremental provider tool body through real curl, and retains provider assembly, dependent execution, certified session append, request counts, and server evidence.                                                                                                                                                                                                                                                                                                                                                                                                            | Local provider-complete assembly HTTP/SSE witness.                                                                                                                                                                                                                                                                                                     | No provider obedience, byte/backpressure semantics, blocked-read cancellation, reconnects, credential/TLS authenticity, arbitrary cleanup, or deployed Harness equivalence is proved.                                                      |
| `DeepSeekHarnessLocalSseBytePrefixProviderAssemblyTool.runWithKey`, `PreparedRequest`, `LocalByteProviderAssemblyResult`, `Example.run`, `Example.summary`                                                | **Checked/proved/exercised:** validates the same typed streaming request at a one-shot loopback server, consumes the response through real curl one-byte chunks, and retains exact byte-prefix, provider assembly, dependent execution, request-count, and server-exit evidence.                                                                                                                                                                                                                                                                                                                                                                                                                            | Local byte-framed provider-complete assembly HTTP/SSE witness.                                                                                                                                                                                                                                                                                         | No provider obedience, byte backpressure, timeout fairness, reconnects, credential/TLS authenticity, arbitrary cleanup, or deployed Harness equivalence is proved.                                                                         |
| `DeepSeekStreamHarness.executeConversationStreamRound`, `executeConversationMultiStreamRound`, `runConversationMultiStream`, `ConversationRunner.appendFinished`                                          | **Checked/exercised at the complete-body stream/harness boundary:** streamed rounds use `buildStreamingRequestPlan`, and its source/body certificate proves the serialized request carries `stream: true`; an executable process fixture rejects the non-streaming body. Terminal rich tool streams retain their wire/session certificates, assign local numeric IDs, route each streamed call through dependent admission/policy/provider execution, and append certified typed results to the reusable conversation runner; deterministic process fixtures exercise both one-call and two-call terminal streams, then the fuel-bounded loop stops on the text-only terminal response or typed exhaustion. | No incremental delivery, cancellation, backpressure, reconnect, provider-complete assembly, credential/network/process-trust, or deployed Harness equivalence is proved.                                                                                                                                                                               |
| `DeepSeekStreamHarnessByte.executeConversationByteStreamRound`, `executeConversationMultiByteStreamRound`, `runConversationMultiByteStream`                                                               | **Checked/exercised:** bounded stdout `ByteArray` chunks retain raw/status/body/framing equations before the decoded body enters the existing rich/tool/session continuation; the round and fuel-bounded fixtures retain the byte witness, execute dependent tools, append certified results, and reach a text terminal.                                                                                                                                                                                                                                                                                                                                                                                    | Byte-level cancellation, blocked-read interruption, backpressure, reconnect, provider-complete assembly, credential/network/process-trust, and deployed Harness equivalence remain external.                                                                                                                                                           |
| `DeepSeekCurlIncremental.executeSseIncremental`, `readBodyLines`, `IncrementalResponse`                                                                                                                   | **Checked/exercised:** spawns a piped process, delivers each complete response-body line to a callback under an explicit read budget, consumes the private status trailer, and returns the reconstructed body with strict SSE validation.                                                                                                                                                                                                                                                                                                                                                                                                                                                                   | Line-oriented complete-response evidence only. No byte-level framing, backpressure, cancellation, reconnect, network/credential/process-trust, or provider-complete assembler theorem is made.                                                                                                                                                         |
| `DeepSeekCurlPrefix.executeSsePrefix`, `PrefixResponse`, `cleanup`                                                                                                                                        | **Checked/exercised:** advances the proof-carrying prefix state before each next process read; fuel/cancellation returns the raw prefix and normalized frames after synchronously killing/waiting the child, while terminal success retains status and strict `[DONE]` validation.                                                                                                                                                                                                                                                                                                                                                                                                                          | Typed process line-stop evidence with separate raw and normalized state.                                                                                                                                                                                                                                                                               | No byte framing, blocked-read cancellation, backpressure, reconnect, network/credential/process-trust, provider-complete assembler, or deployed stream-equivalence theorem is made.                                                        |
| `DeepSeekCurlPrefixSession.executeText`, `executeAndAppendText`, `ProcessedPrefix`                                                                                                                        | **Checked/exercised:** completed prefixes flow through the accepted terminal semantic validators and append-only runner, preserving wire/prefix/session certificates and exact sequence/tool-count proofs; fuel/cancellation remain typed stop outcomes.                                                                                                                                                                                                                                                                                                                                                                                                                                                    | Terminal semantic/session bridge above the process prefix boundary.                                                                                                                                                                                                                                                                                    | No blocked-read interruption, byte framing, backpressure, reconnect, external tool execution, provider-complete assembler, or deployed stream-equivalence theorem is made.                                                                 |
| `DeepSeekAsyncHarness.ProcessJob`, `RaceResult`, `executeRace`                                                                                                                                            | **Checked/exercised:** two complete-body text-prefix jobs run in cooperative `ContextAsync` children; `ContextAsync.race` retains the first typed result and requests loser cancellation, while pure facts classify waiting versus terminal success/failure.                                                                                                                                                                                                                                                                                                                                                                                                                                                | Executable async observation adjacent to the line-oriented process/session adapter.                                                                                                                                                                                                                                                                    | The synchronous line read is not interruptible by the cooperative request; no wall-clock fairness, arbitrary cleanup, network/credential/process trust, or deployed Harness async equivalence is made.                                     |
| `DeepSeekAsyncStreamHarness.StreamProcessJob`, `RaceResult`, `executeRace`                                                                                                                                | **Checked/exercised:** two complete-body streamed Harness continuations run in cooperative `ContextAsync` children; the first typed result retains dependent tool executions, two round witnesses, final model, and runner endpoint.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Executable async observation over the streamed tool/session continuation.                                                                                                                                                                                                                                                                              | Synchronous line reads remain non-interruptible; no wall-clock fairness, arbitrary cleanup, network/credential/process trust, or deployed Harness async equivalence is made.                                                               |
| `DeepSeekAsyncStreamCancellation.ProcessJob`, `ProcessJobResult`, `RaceResult`, `executeRace`                                                                                                             | **Checked/exercised:** policy-bearing children run the existing streamed cancellation loop; the fixture cancels one child before round zero and retains its typed reason, unchanged runner/model endpoint, empty completed prefix, and terminal phase.                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Executable pre-round cancellation observation over the streamed race.                                                                                                                                                                                                                                                                                  | The policy does not interrupt blocked reads; no fairness, arbitrary cleanup, network/credential/process trust, or deployed async cancellation equivalence is made.                                                                         |
| `DeepSeekStream.parseSse`, `validateSse`, `validateSseBytes`                                                                                                                                              | Parses a strict in-memory `data:` / `[DONE]` SSE subset into typed delta frames, retaining raw payload and parse/decode certificates while separating UTF-8, framing, JSON, decode, and terminal errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | No live HTTP reader, buffering/backpressure, cancellation, assembler, provider-complete stream schema, or transport delivery is proved.                                                                                                                                                                                                                |
| `DeepSeekStreamFailure.projectFrames`, `validateFailureStream`, `ValidatedFailureStream`                                                                                                                  | **Checked/proved:** a complete strict SSE body ending in `content_filter` or `insufficient_system_resource` retains the typed prefix, terminal raw `DataFrame`, singleton choice/reason, and optional usage certificate; ordinary finishes fail closed.                                                                                                                                                                                                                                                                                                                                                                                                                                                     | Provider terminal-failure wire subset only. No normal rich/session projection, wire `error`/`aborted` envelope, retry, cancellation, live delivery, or deployed provider-equivalence claim is made.                                                                                                                                                    |
| `DeepSeekTerminalOutcome.validateTerminalOutcome`, `TerminalOutcome`                                                                                                                                      | **Checked/proved/exercised:** fixed-order complete-body validation selects a provider failure or one of the text, one-tool, mixed, and finite multi-call rich certificates, preserving the selected dependent witness and typed rejection.                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Unified terminal-outcome classification over existing source-local validators. No new wire language, session message, retry, cancellation, live delivery, or deployed provider-equivalence claim is made.                                                                                                                                              |
| `DeepSeekStreamIncremental.PrefixState`, `pushLine`, `finish`, `consumeLines`, `consumeBody`                                                                                                              | **Checked/proved/exercised pure prefix path:** each accepted complete line retains the exact accumulated body, parsed frames, line count, and prefix equation; `finish` invokes the complete-body validator and requires `[DONE]`; `LinePolicy` can stop before consuming another line while retaining the prefix.                                                                                                                                                                                                                                                                                                                                                                                          | A typed prefix/state boundary immediately below the strict in-memory parser.                                                                                                                                                                                                                                                                           | No live HTTP reader, byte framing, buffering/backpressure, process cancellation, reconnect, provider-complete assembler, or deployed stream equivalence is proved.                                                                         |
| `DeepSeekRichStream.projectFrames`, `validateTextStream`                                                                                                                                                  | Projects a validated strict wire stream into an exact `RichStream.ValidatedTrace` for one assistant text choice, retaining wire/projection/rich certificates and typed semantic rejection errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           | The accepted language is one local text-only normalization; reasoning/tool/extra-choice and unsupported-finish cases are rejected. No live transport, deployed assembler, or provider-complete stream equivalence is proved.                                                                                                                           |
| `DeepSeekRichToolStream.projectFrames`, `validateToolStream`                                                                                                                                              | Projects a validated strict wire stream into an exact rich tool-call trace for at most one indexed function call, retaining raw arguments and wire/projection/rich certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | Multiple calls, missing IDs/names, reasoning, mixed deltas, live transport, tool execution, and provider-complete assembler behavior remain outside the accepted language.                                                                                                                                                                             |
| `DeepSeekRichMixedStream.projectFrames`, `projectChunks`, `validateMixedStream`                                                                                                                           | Projects one choice that interleaves text, reasoning, and one indexed function call across frames into an exact rich trace, retaining first-seen indices, stateful tool metadata, block ends, usage, terminal finish, and wire/projection/rich certificates; same-frame mixed kinds fail closed.                                                                                                                                                                                                                                                                                                                                                                                                            | Multiple choices/calls, unsupported provider finishes, replay metadata, live transport, tool execution, and provider-complete assembler behavior remain outside the accepted language.                                                                                                                                                                 |
| `DeepSeekRichMultiStream.projectFrames`, `projectChunks`, `validateMultiStream`                                                                                                                           | Projects one choice with any finite list of indexed function calls into an exact rich trace, retaining first-seen contiguous local indices, independent per-call IDs/names/raw arguments, exact block ends, usage, terminal finish, and wire/projection/rich certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                  | Same-frame cross-kind fields, multiple choices, unsupported provider finishes, replay metadata, live transport, tool execution, and provider-complete assembler behavior remain outside the accepted language.                                                                                                                                         |
| `DeepSeekProviderAssembler.push`, `assemble`, `validate`, `Certificate`                                                                                                                                   | **Checked/proved/exercised source-shaped assembler:** folds canonical post-decoder chunks with first-seen order, open-block text/reasoning/tool-call fallback, first-close-wins, latest tool metadata, last usage/finish/replay metadata, max-token tool pruning, and typed unknown-block rejection; successful validation retains the exact folded state and assembly equation.                                                                                                                                                                                                                                                                                                                            | Text/reasoning/tool-call post-decoder semantics only. Wire decoding, image/tool-result schemas, opaque replay JSON, live transport, and deployed TypeScript equivalence remain external.                                                                                                                                                               |
| `DeepSeekAssemblerToolRound.toFunctionCalls`, `executeAssembledTools`, `appendAssistant`, `appendToolResults`                                                                                             | **Checked/proved dependent continuation:** converts a successful assembly to local function calls, executes the existing model-indexed counter tool, and appends exact assistant/tool-result messages to the canonical session surface.                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | Post-assembly local dependent execution/session seam. Provider-ID authenticity, external effects, transport, persistence, and deployed Harness equivalence remain external.                                                                                                                                                                            |
| `DeepSeekProviderStreamAssembly.validateBody`, `mapRawChunks`, `ValidatedProviderAssembly`                                                                                                                | **Checked/proved wire-to-assembler composition:** maps the accepted strict multi-call SSE projection into provider chunks and retains both source and fold certificates; replay metadata is rejected and structured failure/abort causes are normalized.                                                                                                                                                                                                                                                                                                                                                                                                                                                    | Accepted one-choice rich multi-stream subset only. Wire transport, image/tool-result schemas, provider-ID authenticity, and deployed TypeScript equivalence remain external.                                                                                                                                                                           |
| `DeepSeekStreamToolRound.executeBodyTools`, `appendRound`, `ValidatedStreamToolRound`                                                                                                                     | **Checked/proved wire-backed dependent continuation:** carries the composed stream through model-indexed execution and exact assistant/tool-result session append, with the local fixture reaching `5` from `2`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | Local strict-stream/provider/dependent/session composition. Network/authentication, external effects, persistence, retry/cancellation, and deployed Harness equivalence remain external.                                                                                                                                                               |
| `DeepSeekScopedStreamToolRound.executeBodyScopedTools`, `ScopedExecutionTrace`, `appendRound`                                                                                                             | **Checked/proved scoped stream continuation:** nearest-first resolution, terminal restriction, automatic/review approval, dependent model-indexed replies, and exact assistant/tool-result append are retained together; the fixture covers weather/clock execution plus restricted-shadow and denied-approval failures.                                                                                                                                                                                                                                                                                                                                                                                    | Scoped local composition only. Scope construction, approval authentication, external effects, persistence, cancellation, and deployed Harness equivalence remain external.                                                                                                                                                                             |
| `DeepSeekProcessStreamToolRound.executeWith`, `ProcessedRound`, `counterRun`                                                                                                                              | **Checked/proved process-backed continuation:** a configured local process returns a complete body with status/SSE certificates before the exact provider/dependent/session composition is reused; the fixture reaches `5` from `2`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Complete-body local process adapter. Network reachability, credentials, process trust, incremental delivery, cancellation, persistence, external effects, and deployed Harness equivalence remain external.                                                                                                                                            |
| `DeepSeekProcessScopedStreamToolRound.executeWith`, `ProcessedScopedRound`, `Example.scopedDualRun`                                                                                                       | **Checked/proved process-backed scoped continuation:** a configured local process returns a complete scoped body with status and strict-wire certificates before scoped approval, dependent execution, and exact assistant/tool-result append are reused; the fixture validates three frames and the dual-call endpoint.                                                                                                                                                                                                                                                                                                                                                                                    | Complete-body process adapter over the scoped stream/session seam. Network reachability, credentials, process trust, incremental delivery, cancellation, persistence, external effects, and deployed Harness equivalence remain external.                                                                                                              |
| `DeepSeekProcessScopedConversation.runAux`, `run`, `Example.twoStepSummary`, `Example.oneStepFuelSummary`                                                                                                 | **Checked/proved process-backed scoped conversation:** a round-indexed process family feeds successive scoped rounds, retaining each body, dependent execution, model successor, and session append; no-call completion and fuel exhaustion are distinct typed stops. The fixture checks a two-round four-message completion and one-round exhaustion.                                                                                                                                                                                                                                                                                                                                                      | Finite complete-body process conversation over scoped approval/session. Retries, cancellation, persistence, external effects, live provider behavior, and deployed Harness equivalence remain external.                                                                                                                                                |
| `DeepSeekProcessScopedRequestConversation.executePrepared`, `run`, `Example.twoStepSummary`, `Example.oneStepFuelSummary`                                                                                 | **Checked/proved request-indexed continuation:** each session state rebuilds a typed streaming request, and the prepared process/SSE/scoped result is indexed by the exact request; distinct bodies, terminal completion, and fuel exhaustion are exercised by the deterministic fixture.                                                                                                                                                                                                                                                                                                                                                                                                                   | Request-provenance refinement over the process/scoped conversation. Live network/provider behavior, credentials, retries, cancellation, persistence, external effects, and deployed Harness equivalence remain external.                                                                                                                               |
| `DeepSeekProcessScopedRequestBytePrefixConversation.executePrepared`, `run`, `Example.twoStepSummary`, `Example.prefixFuelSummary`                                                                        | **Checked/proved arbitrary-byte request-indexed continuation:** each round retains the exact typed request together with raw chunks, pending framing, status, strict SSE completion, scoped execution, and exact session append; the fixture checks two completed rounds and a typed prefix-fuel stop before completion.                                                                                                                                                                                                                                                                                                                                                                                    | Byte-prefix refinement over the request-indexed process/scoped conversation. Network/authentication, executable trust, blocked-read cancellation, backpressure, reconnects, retries, persistence, external effects, and deployed Harness equivalence remain external.                                                                                  |
| `DeepSeekHarnessLocalSseRequestBytePrefixConversation.runWithKey`, `LocalConversationResult`, `Example.twoStepSummary`, `Example.prefixFuelSummary`                                                       | **Checked/proved/exercised loopback request-indexed continuation:** a bounded HTTP server validates each typed request, selects distinct SSE bodies by request index, real curl delivers arbitrary byte chunks, and the scoped/dependent/session witnesses retain two completed rounds or a typed prefix-fuel stop. The result exposes request count, validity count, raw byte evidence, exact request/body provenance, and clean server exit.                                                                                                                                                                                                                                                              | Local HTTP/process evidence only; remote reachability, credential and executable authenticity, blocked-read interruption, backpressure, reconnects, retries, persistence, external effects, and deployed Harness equivalence remain external.                                                                                                          |
| `DeepSeekSessionBridge.finishAssistant`, `appendFinishedAssistant`                                                                                                                                        | Extracts a terminal rich assistant view and appends one assistant payload to the local session surface with a caller-supplied unique numeric call-ID assignment and earlier source-event evidence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Provider-ID authenticity, source-event provenance beyond supplied proofs, persistence, and whole-session equivalence remain outside the claim.                                                                                                                                                                                                         |
| `DeepSeekSessionRunner.finishText`, `finishTool`, `finishMixed`, `finishMulti`, `Runner.append`, `Runner.appendMixed`, `Runner.appendMulti`                                                               | Composes accepted text/one-tool/mixed/multi-call terminal responses into a pure append-only session runner with exact sequence, message-order, and tool-count invariants.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   | No transport, cancellation, persistence, external execution, or whole-session equivalence.                                                                                                                                                                                                                                                             |
| `DeepSeekApiSession.acceptResponse`, `Runner.appendApi`                                                                                                                                                   | Admits a decoded singleton index-zero response with supported terminal reason and nonempty payload, then appends via the pure local runner.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | Extra choices, unsupported/empty responses, transport, persistence, external execution, and whole-session equivalence are not claimed.                                                                                                                                                                                                                 |
| `DeepSeekHarness.buildChatRequest`, `executeRound`, `ExecutedTool`, `appendRoundToolResults`, `ConversationRunner`, `executeConversationRound`, `runConversation`                                         | **Checked/exercised:** local session messages become a typed request, the explicit transport and singleton response guard run, and each parsed call retains generic admission, policy, and dependent provider-reply evidence; certified outcomes can be encoded and appended as tool-result surface messages with exact local IDs, source references, message order, and protocol projection; the continuation runner feeds that updated session into subsequent typed requests, while `runConversation` bounds repetition by explicit fuel and distinguishes no-tool-call completion from exhaustion; deterministic tests exercise both paths, and malformed/unknown calls fail closed.                    | Persistence, remote credentials, scheduling, process trust, request-boundary treatment of error tool results, cancellation, and deployed DeepSeek-Harness equivalence remain outside this round boundary.                                                                                                                                              |
| `DeepSeekHarnessPersistence.RestoredRunner`, `restoreRunner`, `RequestCertificate`, `buildRequestCertificate`                                                                                             | **Checked/proved/exercised logical persistence attachment:** a validated JSONL archive restores a runner with an exact equality to the archive's final session; the restored request certificate is proven equal to the request rebuilt from that archive session, and the deterministic tool archive exercises the path.                                                                                                                                                                                                                                                                                                                                                                                   | Logical archive-to-harness continuation after the existing persistence refinement.                                                                                                                                                                                                                                                                     | No filesystem/compression/torn-tail/concurrent-writer/host-authenticity or complete deployed persistence equivalence claim is made.                                                                                                        |
| `DeepSeekHarnessEventArchive.SupportedEventLog`, `RestoredRunner`, `restoreRunner`, `buildRequestCertificate`                                                                                             | **Checked/proved/exercised certificate-gated current-event attachment:** lossless archive retention and stateful semantic validation are both required; restoration exposes exact final-session equality, raw-event order, and request rebuilding, while opaque/extension events reject.                                                                                                                                                                                                                                                                                                                                                                                                                    | Current-Harness event archive → typed runner seam over the existing `SessionEventArchive` and `SessionRefinement` certificates.                                                                                                                                                                                                                        | No semantics for opaque payloads, no dropping/replay of unsupported events, and no filesystem/compression/durability, credentials, or deployed-Harness equivalence claim.                                                                  |
| `DeepSeekHarnessEventIgnorableProjection.Projection`, `SupportedProjection`, `projectSupported`, `ignorable_fixture_summary`, `required_fixture_rejected`                                                 | **Checked/proved/exercised explicit-ignorable projection:** positional physical keep/drop decisions drop only opaque `ignorable: true` rows, retain supported wire/raw certificates, and reject a required opaque vendor row.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | Archive-only source exception below the fail-closed runner restore seam.                                                                                                                                                                                                                                                                               | No sequence renumbering, local session replay, payload semantics, persistence, or deployed-Harness equivalence claim.                                                                                                                      |
| `DeepSeekHarnessEventArchiveReplay.ArchiveReplay`, `archiveReplay`, `toolArchiveReplay`, `ArchiveReplay.droppedRaw_eq_decisionDrops`                                                                      | **Checked/proved/exercised archive-aware replay:** one dependent certificate pairs the indexed normalized `SourceReplay` with its inductive keep/drop ledger, retains exact archive/kept raw rows, and exposes dropped opaque rows and positions; the tool fixture checks nine physical rows, eight supported transitions, and one explicit opaque no-op.                                                                                                                                                                                                                                                                                                                                                   | Lossless current-event archive → occurrence-indexed supported transition replay.                                                                                                                                                                                                                                                                       | Finite supported subset only; dropped rows are explicitly ignorable no-ops, while opaque payload semantics, provider behavior, bytes, persistence, cancellation delivery, and deployed-Harness equivalence remain external.                |
| `DeepSeekHarnessEventIgnorableRunner.restoreRunner`, `buildRequestCertificate`, `toolNormalizedRunner`, `toolNormalizedRequest`                                                                           | **Checked/proved/exercised normalized runner attachment:** the validated normalized endpoint becomes a typed `ConversationRunner` with exact session/step/tool-count certificates, and the tool fixture rebuilds a dependent `ChatRequest` with expected user/assistant/tool messages.                                                                                                                                                                                                                                                                                                                                                                                                                      | Pure normalized-log → local runner/request attachment.                                                                                                                                                                                                                                                                                                 | No provider authenticity, transport, persistence, opaque payload semantics, or deployed-Harness equivalence claim.                                                                                                                         |
| `DeepSeekHarnessEventIgnorableTransport.runRestoredTransport`, `runToolNormalizedTransport`, `toolNormalizedTransport`, `RestoredTransportRun`                                                            | **Checked/proved/exercised normalized transport continuation:** the normalized runner enters the existing process-backed complete-response trace, retaining final runner/model/trace/stop evidence and the source session/step certificates; the deterministic fixture exercises one no-tool completion.                                                                                                                                                                                                                                                                                                                                                                                                    | Injected normalized-log → transport conversation attachment.                                                                                                                                                                                                                                                                                           | No credentials, provider authenticity, durable persistence, external effects, or deployed-Harness equivalence claim.                                                                                                                       |
| `DeepSeekHarnessEventText.restoreTextRunner`, `restoreBytesRunner`, `RestoredTextRunner`, `RestoredBytesRunner`                                                                                           | **Checked/proved/exercised text attachment:** UTF-8/JSONL text or bytes retain exact source/decoded text, archive lines, validated session, and restored-runner equalities; invalid UTF-8 and opaque/extension events reject.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | Text/byte ingress immediately above the certificate-gated current-event archive seam.                                                                                                                                                                                                                                                                  | No external logger framing, transport, persistence, provider authenticity, opaque replay, or deployed-Harness equivalence claim.                                                                                                           |
| `DeepSeekHarnessPayloadText.restoreTextPayloadRunner`, `restoreBytesPayloadRunner`, `RestoredPayloadRunner`, `RestoredBytesPayloadRunner`                                                                 | **Checked/proved/exercised payload-preserving attachment:** the restored runner and `SessionPayloadArchive.PayloadLog` share the exact parsed-line index; raw payload objects, block tags, usage, and tool-result metadata remain available beside the semantic runner.                                                                                                                                                                                                                                                                                                                                                                                                                                     | Payload-shape retention immediately above the text event-archive seam.                                                                                                                                                                                                                                                                                 | No provider schema semantics, opaque replay, logger/transport/persistence, or deployed-Harness equivalence claim.                                                                                                                          |
| `DeepSeekHarnessPayloadPersistence.restoreRunner`, `restoreBytesRunner`, `restoreRead`, `RestoredRunner`, `RestoredBytesRunner`, `ReadRestoredRunner`                                                     | **Checked/proved/exercised persisted payload attachment:** logical JSONL, pure bytes, and memory/temporary-file reads retain the expanded-event payload ledger beside the restored runner, with exact session, raw-event, and decode certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Persistence composition immediately above the payload archive seam.                                                                                                                                                                                                                                                                                    | Payload/storage failures stay typed; no provider schema semantics, fsync, crash atomicity, torn-tail repair, or deployed-Harness equivalence claim.                                                                                        |
| `UnifiedContext` constructors                                                                                                                                                                             | Enforce dependent realm/provider types, derived-parent indices, finite unfolding depth, and witnessed local recovery.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | No imperative alias identity, recursive fixed point, tenant sandbox, middleware execution, or runtime refinement.                                                                                                                                                                                                                                      |
| `DeepSeekHarnessErrors.ProviderFailedTool`, `executeFunctionCallRecoverable`, `executeFunctionCallsRecoverable`, `ConversationRunner.appendRecoverableToolResults`, `executeConversationRoundRecoverable` | **Checked/exercised opt-in failure path:** a provider error retains exact parsed/admission/policy/provider-message evidence and preserves the model; with `ErrorToolResultPolicy.include`, it is appended as an `isError` tool result and consumed by a later typed request.                                                                                                                                                                                                                                                                                                                                                                                                                                | Explicit policy seam for model-visible provider failures over the same pure, complete-body continuation.                                                                                                                                                                                                                                               | Parse/admission/policy failures remain fail-closed; retries, cancellation, persistence, asynchronous delivery, real provider behavior, and deployed Harness equivalence are not claimed.                                                   |
| `DeepSeekStreamHarnessErrors.executeConversationMultiStreamRoundRecoverable`, `runConversationMultiStreamRecoverable`, `StreamRecoverableRoundResult`                                                     | **Checked/exercised streamed failure path:** a complete-body terminal tool stream retains exact provider-failure evidence, preserves the model, and appends an `isError` tool result; under explicit `.include`, the fuel-bounded loop retains that failed round and a later streamed text terminal.                                                                                                                                                                                                                                                                                                                                                                                                        | Recoverable provider failures at the complete-body streamed Harness boundary.                                                                                                                                                                                                                                                                          | Incremental recovery, retries, cancellation, persistence, asynchronous delivery, real provider behavior, and deployed Harness error equivalence are not claimed.                                                                           |
| `DeepSeekStreamHarnessRetry.RetryPolicy`, `RetryHistory`, `executeWithRetry`, `executeConversationMultiStreamRound`                                                                                       | **Checked/exercised streamed retry path:** process and transient-HTTP failures are retried only under an explicit policy; exact ordered `SessionClientError` history carries a retry bound, and a successful round retains the existing streamed wire/session/tool certificates. Stream framing, semantic response, and tool failures are terminal.                                                                                                                                                                                                                                                                                                                                                         | Complete-body immediate retry over the streamed process boundary.                                                                                                                                                                                                                                                                                      | Provider backoff, idempotency of arbitrary tools, cancellation, persistence, asynchronous delivery, and deployed Harness retry equivalence remain outside.                                                                                 |
| `DeepSeekHarnessRetry.RetryPolicy`, `RetryHistory`, `executeWithRetry`, `executeConversationRoundRetry`                                                                                                   | **Checked/exercised bounded retry path:** transport and transient-HTTP failures are retried only under an explicit policy; prior `ClientError`s retain their exact order and a proof of the retry bound; successful responses and conversation rounds retain the existing parse/decode/session/tool certificates while reusing one request plan.                                                                                                                                                                                                                                                                                                                                                            | Complete-body immediate retry over the explicit transport boundary.                                                                                                                                                                                                                                                                                    | Provider backoff, idempotency of arbitrary requests/tools, cancellation, persistence, asynchronous delivery, and deployed Harness retry equivalence remain outside.                                                                        |
| `DeepSeekHarnessCancellation.CancellationPolicy`, `CancellableStop`, `CancellableRunResult`, `runConversationCancellable`                                                                                 | **Checked/exercised pre-round cancellation path:** the caller policy is evaluated before each complete request round; a cancellation result retains the exact completed witness prefix, unchanged runner/model endpoint, and proof of the decision, while completion and fuel exhaustion remain distinct.                                                                                                                                                                                                                                                                                                                                                                                                   | Boundary-safe control over the pure complete-body conversation runner.                                                                                                                                                                                                                                                                                 | No interruption of an in-flight process, HTTP request, stream reader, or external tool; no cleanup, backpressure, persistence, asynchronous delivery, or deployed Harness cancellation equivalence.                                        |
| `DeepSeekStreamHarnessRetryCancellation.RetryCancellableStop`, `RetryCancellableRunResult`, `runAux`, `run`                                                                                               | **Checked/exercised retry-aware pre-round cancellation path:** cancellation is checked before each process-backed retry round; the exact accepted streamed retry prefix, unchanged runner/model endpoint, decision certificate, and per-head retry histories are retained, while completion and fuel exhaustion remain distinct.                                                                                                                                                                                                                                                                                                                                                                            | Composition of the indexed streamed retry boundary with caller-controlled cancellation.                                                                                                                                                                                                                                                                | No interruption of in-flight process/HTTP/stream/tool IO; no cleanup, backpressure, persistence, reconnect, asynchronous delivery, or deployed Harness cancellation equivalence.                                                           |
| `Coeffect.Observational.Related`                                                                                                                                                                          | Makes presence/absence mismatches unconstructible and packages supplied key relations as a finite-context `Setoid`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         | The key relations are supplied; operational tests can replace them only under the separately documented laws.                                                                                                                                                                                                                                          |
| `OperationalEquivalence` / `QuotientEffect`                                                                                                                                                               | Checks finite partial test words and certifies finite quotient-respecting effect programs; the paired-inverse counterexample is kernel-checked.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             | Universal test equivalence is not decidable here; the stronger paired law needs a premise, and this layer alone does not prove mediated independence.                                                                                                                                                                                                  |
| `Transformation` / `OperationIndependence`                                                                                                                                                                | Constructs exact generated monoids, promotes full inverse/outcome stability, checks finite distinct-key words, and interprets outcome-mediated computations.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | Partial words are finite syntax, not abstract Kleisli monoids; the next row's whole-run closure does not supply the full computation transformation monoid.                                                                                                                                                                                            |
| `Removal`                                                                                                                                                                                                 | Builds indexed original/omitted finite traces with exact later inverse equalities and checks arbitrary permutations of the retained inverse list.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           | Exact pure effects only; no observational quotient, infinite family, asynchronous runtime, or real external recovery.                                                                                                                                                                                                                                  |
| `MediatedIndependence`                                                                                                                                                                                    | Reifies selected branches, states quotient closure, bridges it to exact closure under representative coherence, and checks a finite exact-representative counterexample.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | Its old individual-domain `PairwiseOverlapComplete` is false for partial computation versus unit; the next row supplies the corrected bounded theorem.                                                                                                                                                                                                 |
| `MediatedTheorem`                                                                                                                                                                                         | Corrects composite partial domains and constructively swaps arbitrary finite outcome-selected trees with exact after/undo and conditional inverse stability, then derives the observational form.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           | Finite whole-run analogue only; old `PairwiseOverlapComplete` is false for partial unit, and the next row proves the stronger partial monoid result.                                                                                                                                                                                                   |
| `PartialTransformation`                                                                                                                                                                                   | Builds the complete partial forward/actual-yielded-inverse Kleisli closures and proves all cross transformations commute plus success-conditional domain/inverse stability.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | Full finite exact partial D17/D19/T42 analogue; not the paper's literal total/quotient, external, asynchronous, or infinite setting.                                                                                                                                                                                                                   |
| `ObservationalPartialTransformation`                                                                                                                                                                      | Proves adaptive computation generators respect the finite context relation and descends exact closure independence to domain-sensitive related partial maps; checks a generic respect counterexample.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Finite observational partial/Kleisli analogue under exact `PairwiseOverlap`; not quotient-only operation independence or the paper's unrestricted total setting.                                                                                                                                                                                       |
| `TotalQuotientIndependence`                                                                                                                                                                               | Carries explicit success-at-every-context certificates, links total forward/yielded-inverse words to the exact closure, and proves quotient commutation, yield stability, recovery, and admissible total effects.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           | Finite totalized/quotient specialization of the D17/D19/T42 layer.                                                                                                                                                                                                                                                                                     | Totality is supplied over the finite context model and pairwise overlap remains exact; unrestricted total, external, asynchronous, infinite, and quotient-only operation theorems remain outside.                                          |
| `DomainTotalQuotientIndependence`                                                                                                                                                                         | Carries a named invariant-domain certificate for a partial computation, lifts totality/preservation through forward, yielded-inverse, and composition maps, and transports finite observational independence; the counter/label fixture is total only on that domain.                                                                                                                                                                                                                                                                                                                                                                                                                                       | Domain-certified finite total/quotient refinement of the D17/D19/T42 layer.                                                                                                                                                                                                                                                                            | The domain and exact overlap certificate are supplied; behavior outside the domain remains partial, and unrestricted total, quotient-only, external, asynchronous, and infinite theorems remain outside.                                   |
| `GlobalRegistry`                                                                                                                                                                                          | Checks code-only component/fiber/global data, unique providers/targets, birth-ranked acyclicity, and preservation by insert/retire/remove orchestration.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | Uses a strengthened parent invariant and noncomputable derived views; no code interpreter, read confinement, lifecycle rules, or full Theorem 59.                                                                                                                                                                                                      |
| `GlobalDynamics`                                                                                                                                                                                          | Interprets opaque codes externally and reconstructs ordinary/registration steps, recovery, confinement/read/WF evidence, and fueled traces with explicit exhaustion.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Most laws are integrator obligations; phase updates and unload policy are handled only by the next bounded layer.                                                                                                                                                                                                                                      |
| `GlobalLifecycle`                                                                                                                                                                                         | Checks exact target/phase guards, executed landings, inertia, unload recovery, all-edge WF preservation, and finite lifecycle traces.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Orchestration remains separate; general `RecoveryAdmission` is supplied, oracle rejection has no lifecycle edge, and full Definition 53/Theorem 59 are unclaimed.                                                                                                                                                                                      |
| `GlobalCalculus`                                                                                                                                                                                          | Unifies orchestration/lifecycle endpoints under ten rule names, retains acted-on names, separates state maps from edits, proves installation-boundary semantics, and packages empty-origin traces.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Finite sequential Definition 53 model; general recovery is admitted, oracle rejection remains absent, and full Theorem 59 is unclaimed.                                                                                                                                                                                                                |
| `GlobalTraceFacts`                                                                                                                                                                                        | Proves non-unload foreign exactness, conditional unload table/control/static continuity, aligned name-specific episodes, and a kernel bare-admission countermodel.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Bounded existing-fiber Lemma 54 fragments; new-entry/retire-write provenance and remaining global metatheory are unproved.                                                                                                                                                                                                                             |
| `GlobalTemporal`                                                                                                                                                                                          | Reifies fallible off-source step maps and proves per-step commutation composes to finite relation-indexed recovery with explicit inverse/reorder/unload certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Parameterized T61/Cor62 algebra only; the next row supplies a D60-to-per-step bridge, while canonical `≈`, totality, continuation stability, and arbitrary trace reordering remain absent.                                                                                                                                                             |
| `GlobalIteratorIndependence`                                                                                                                                                                              | Generates oracle-specific reachable partial forwards and actually yielded totalized inverses, promotes exact generator laws through the closures, descends to `EffectEquiv` only with supplied forward-map respect, exposes occurrence-indexed family independence, and derives `PerStepCommutes` from explicit provenance/membership.                                                                                                                                                                                                                                                                                                                                                                      | Partial/Kleisli Definition 60 analogue only. The oracle is fixed; finite reach/bounds are separate certificate types; `ProgramRespects` is supplied while only inverse respect follows from `EffectEquiv`; effect observation is not rule `≃`; totalization, owner inversion, reordering, T61, and Corollary 62 are not derived.                       |
| `GlobalTransposition`                                                                                                                                                                                     | Given `Independent`, constructs raw off-axis executions/common endpoint and exact commutation for two supplied totalized closure-member pre-edit maps; given `ObservationalIndependent`, proves the effect-relational square while retaining separate `ProgramRespects`; also separates exact lifecycle codes and phase edits.                                                                                                                                                                                                                                                                                                                                                                              | Bounded ingredients toward Lemma 71 only. `GlobalTransposition` itself constructs no phase-frame inhabitant; semantic inverse equality is weaker than stored-code equality; no guard/target preservation, edited endpoint square, or lifecycle transition swap is proved.                                                                              |
| `GlobalForeignPhase`                                                                                                                                                                                      | From explicit readability, ordinary exact-successor, and same-child oracle laws, derives exact strong-yield compatibility; combines two such certificates with independence into a framed raw diamond retaining the actual post-raw fibers; kernel-separates all three premises.                                                                                                                                                                                                                                                                                                                                                                                                                            | Lower contracts, distinct owners, reach/execution, post-raw fiber lookups, and typed phases are supplied. No `Transition`/`Step`, guard/target preservation, lifecycle phase provenance, Lemma 71 exchange, or mixed-trace reorder theorem.                                                                                                            |
| `GlobalLandingTransposition`                                                                                                                                                                              | Adds exact cross-forward yield syntax and fixed-program landing provenance, derives foreign positive-target preservation from WF, reframes off-axis landings, and constructs actual L-Iter/L-Finish transitions in both orders with one exact final state; includes positive and necessity models.                                                                                                                                                                                                                                                                                                                                                                                                          | Landing-only four-pair theorem. Requires WF, distinct owners, exact cross-forward stability, both phase compatibilities, and common-source program-aligned activations. No Begin pair, trace-step identity, episode assignment, or full Lemma 71.                                                                                                      |
| `GlobalActivationTransposition`                                                                                                                                                                           | Adds root-aligned Begin, exact foreign lookup/positive-target framing, fixed-program endpoint/rule determinism, all nine common-source Begin/Iter/Finish diamonds, and an actual-second-step swapped transition; includes branch and necessity witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                   | Partial fixed-oracle Lemma 71(1) analogue. Requires WF, distinct owners, common applicability, explicit provenance, and branch-relevant frame/exact-yield laws. No orchestration clause (2), arbitrary stored-trace rewrite, episode assignment, literal total/quotient Lemma 71, or confluence.                                                       |
| `GlobalActivationOrchestrationTransposition`                                                                                                                                                              | Kernel-refutes the literal clause-(2) child condition, classifies registration, derives legal early orchestration/positive targets, and proves an occurrence-framed exact exchange with the same template and endpoint; includes birth/frame gaps and structural/ordinary/registering examples.                                                                                                                                                                                                                                                                                                                                                                                                             | Corrected partial fixed-oracle Lemma 71(2) analogue. Registering×Insert is excluded, frames are supplied, and the parent countermodel is compact structural evidence. No birth-erasing quotient, arbitrary stored-trace rewrite, literal paper clause, Lemma 72, or confluence.                                                                        |
| `GlobalTraceRewrite`                                                                                                                                                                                      | Locates exact dependent two-step windows, identifies actual fixed-program activation/orchestration occurrences, splices the corrected transposition through retained context, and reconstructs the occurrence-indexed assignment ledger; rules and actors are adjacent permutations.                                                                                                                                                                                                                                                                                                                                                                                                                        | Exact stored-trace consequence of the bounded corrected Lemma 71 analogues. It does not derive occurrence laws, admit registering×Insert, weaken endpoints to a birth-erased relation, simulate arbitrary suffixes, normalize traces, delete vestiges, or prove Lemma 72/confluence.                                                                   |
| `GlobalDeletion`                                                                                                                                                                                          | Builds intrinsic relation-indexed keep/drop replay and output assignments; exactly replays safe foreign orchestration suffixes after finite already-vestigial families; kernel-checks parent, redraw, clock, and surviving-birth obstructions.                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Bounded deletion substrate below Lemma 72. It does not delete a general lifecycle episode, derive provenance or no-redraw, simulate lifecycle suffixes, define a birth-erased relation, normalize traces, or prove Lemma 72/Theorem 73/confluence.                                                                                                     |
| `GlobalPaperRelation`                                                                                                                                                                                     | Erases allocator clock/birth from current rule observation, proves full/outside/deletion Setoids and strict bridges, reconstructs orchestration bidirectionally between two WF full-domain states, and from a WF source with `VestigialNames` gives directional safe deleted-shadow replay.                                                                                                                                                                                                                                                                                                                                                                                                                 | Finite structural paper-relation slice. No one-sided WF transport, outside bisimulation, lifecycle simulation, name quotient, relation-aware activation swap, general episode deletion, Lemma 72, normalization, or confluence.                                                                                                                        |
| `GlobalPaperTraceSimulation`                                                                                                                                                                              | Lifts the birth-erased relation to finite intrinsic traces in both forward and backward orientations, retaining assigned steps, endpoint well-formedness, final relatedness, and exact rule/actor projections; it also provides forward/backward orchestration-only constructors and occurrence-specific lifecycle evidence, exercised by a concrete leave/unload replay witness.                                                                                                                                                                                                                                                                                                                           | Finite bidirectional relation-aware trace replay only. Lifecycle evidence is caller-supplied per occurrence, not global lifecycle bisimulation. No deletion, normalization, Lemma 72, or confluence is derived.                                                                                                                                        |
| `GlobalPaperTraceDeletion`                                                                                                                                                                                | Adds relation-indexed keep/drop replay and assignment transport over the richer paper-trace surface, with a concrete safe orchestration example and explicit lifecycle/episode gaps.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Assigned deletion substrate only. No general closing-episode deletion, lifecycle suffix simulation, no-redraw/lifetime theorem, normalization, Lemma 72, or Theorem 73.                                                                                                                                                                                |
| `GlobalPaperTraceNormalization`                                                                                                                                                                           | Packages a finite connected list of supplied `RelatedAdjacentRewrite` certificates; the terminal trace retains transported assignments, is birth-erased related to the source endpoint, and has permuted rules and actors. One-link and connected two-link activation/orchestration witnesses expose executable terminal rule and actor ledgers.                                                                                                                                                                                                                                                                                                                                                            | Certificate composition, not an automatic normalizer: no strategy, canonical form, termination, confluence, Lemma 72, or Theorem 73.                                                                                                                                                                                                                   |
| `GlobalPaperTraceNormalizer`                                                                                                                                                                              | Adds an explicit-authority terminating normalizer over `TracePackage`: normal-form decidability, a rewrite witness for each non-normal package, and a strictly decreasing Nat measure produce a finite dependent chain whose endpoint remains related and whose rule/actor ledgers are permutations.                                                                                                                                                                                                                                                                                                                                                                                                        | Conditional termination under caller-supplied authority. No strategy derivation, canonical form, dynamic global termination, Lemma 72, Theorem 73, or confluence.                                                                                                                                                                                      |
| `GlobalPaperTraceConfluence`                                                                                                                                                                              | Provides a generic decreasing/local-diamond Newman kernel and applies it to the actual authority-driven normalizer: `AuthorityLinked` reconstructs selected paths and `normalize_results_unique` proves equal final `TracePackage` endpoints under `ConfluentAuthority`; a Boolean witness exercises both reduction orders.                                                                                                                                                                                                                                                                                                                                                                                 | Conditional metatheory only. Local joins, a decreasing measure, and a normal-form strategy remain supplied; no CORDIS-specific canonical form, Theorem 73, or global confluence is derived.                                                                                                                                                            |
| `GlobalProgress`                                                                                                                                                                                          | Separates fixed-program oracle rejection from raw oracle-existential applicability, kernel-refutes raw progress under finite-name exhaustion, and proves state-local no-deadlock from explicit finite precedence, current execution/recovery readiness, and committed-provider soundness.                                                                                                                                                                                                                                                                                                                                                                                                                   | Corrected conditional no-deadlock fragment of Theorem 66. Printed assumptions omit admission/freshness totality. No quantitative bound, target-turn finiteness, maximal termination, fairness, trace program assignment, support, deletion, or confluence.                                                                                             |
| `GlobalProgressRun`                                                                                                                                                                                       | A supplied `ProgressAuthority` and strict `StepPotential` drive `runFuel`, which retains an exact dependent lifecycle trace, endpoint well-formedness, and either quiescent completion or certified full-fuel exhaustion; `certifiedRun_quiescent` rules out exhaustion at the initial potential.                                                                                                                                                                                                                                                                                                                                                                                                           | Conditional finite execution bridge for Theorem 66.                                                                                                                                                                                                                                                                                                    | Authorities are supplied rather than derived. No target-turn accounting, finite-name freshness, fairness, trace-wide assignment, maximal-execution semantics, support, confluence, or unrestricted Theorem 66.                             |
| `GlobalProgressAssignment`                                                                                                                                                                                | An `AssignedProgressAuthority` supplies a `StepProgramAssignment` for each lifecycle transition; `assignTrace` recursively reconstructs a dependent `TraceProgramAssignment` for every finite progress-run trace while retaining endpoint and stop certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                            | Explicit provenance bridge above the finite runner.                                                                                                                                                                                                                                                                                                    | Fixed programs, roots, oracles, and reachability are supplied rather than inferred; no full Definition 60/66 provenance, maximal execution, fairness, support, deletion, normalization, or confluence.                                     |
| `GlobalPaperProgressReplay`                                                                                                                                                                               | Composes an assigned finite progress-run trace with a caller-supplied `ForwardAssignedStepSimulation`, preserving source endpoint/length/stop evidence, transported assignment, exact rule/actor projections, and a well-formed related peer endpoint.                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Conditional relation-aware replay bridge above the assigned runner.                                                                                                                                                                                                                                                                                    | The simulator and lifecycle provenance remain supplied; no automatic lifecycle bisimulation, maximal execution, or unrestricted Theorem 66 is derived.                                                                                     |
| `GlobalSupport`                                                                                                                                                                                           | Kernel-refutes combined support order from separate acyclicity, defines the unique support predicate by edge-indexed well-founded recursion, and proves corrected support-equals-active under state-local provision totality, no failure, and active-parent closure; includes independent necessity models.                                                                                                                                                                                                                                                                                                                                                                                                 | Corrected local Definitions 67/69 and Lemmas 68/70 analogues. Combined order and parent closure are supplied rather than trace-derived; totality is state-local. No component-wide provenance, deletion, canonical form, or confluence.                                                                                                                |
| `GlobalRelations`                                                                                                                                                                                         | Defines key-indexed rule observation and ambient/table effect observation as setoids, bridges respectful undo to the temporal interface, and separates the candidates by executable models.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | Finite Equation 53/Lemmas 55–57 candidates only; rule bisimulation, name-action laws, and the full global lemmas remain unproved.                                                                                                                                                                                                                      |
| `GlobalRuleInvariance`                                                                                                                                                                                    | Matches every well-formed insert/retire/remove step bidirectionally across rule-related states with exact peer endpoints and related well-formed successors, without equating tables.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Orchestration-only L55 fragment; ambient-sensitive inertia is a checked lifecycle obstruction and further dynamics/recovery laws are absent.                                                                                                                                                                                                           |
| `GlobalRuleObservations`                                                                                                                                                                                  | Transports provider identity, dependent targets, committed resolution, reliance, phases, quiescence, and all structural lifecycle guards across well-formed rule-related states.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | Assumption-free L55 observation substrate; it executes no lifecycle step and leaves landing/error/inertia/oracle/recovery contracts explicit.                                                                                                                                                                                                          |
| `GlobalLifecycleBisimulation`                                                                                                                                                                             | Under noncircular landing, run-error, inertia, and recovery-admission contracts, matches all lifecycle/unified rules bidirectionally with exact valid related endpoints.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | Conditional well-formed L55 analogue; external contracts are supplied, raw no-WF bisimulation is uninhabited, and Finish requires related yielded tables.                                                                                                                                                                                              |
| `GlobalNameAction`                                                                                                                                                                                        | Defines executable bijections over all stored payloads, canonical dependent state action, identity/composition/inverse, WF equivalence, and exact bidirectional orchestration equivariance.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | Structural/orchestration L56 fragment; catalog entry, dynamics, oracle, recovery, inertia, and lifecycle action laws remain separate.                                                                                                                                                                                                                  |
| `GlobalNameLifecycle`                                                                                                                                                                                     | From exact dynamics/inertia/catalog-entry action laws, derives registration, oracle, execution, landing, recovery, lifecycle, inverse, and unified name actions with exact endpoints.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Conditional well-formed fixed-catalog L56 analogue; primitive semantic laws are supplied and arbitrary base Dynamics is not automatically equivariant.                                                                                                                                                                                                 |
| `GlobalVestigial`                                                                                                                                                                                         | Proves vestigial removal effect-equivalent and gives exact bidirectional orchestration removal squares under all kernel-necessary exceptions, with well-formed countermodels.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | Corrected L57 orchestration fragment only; pinned clauses omit parent adoption/removal, and iterator/lifecycle/oracle/inertia/recovery insensitivity is unproved.                                                                                                                                                                                      |
| `GlobalSpatial`                                                                                                                                                                                           | Proves dependency provision, explicit nested episode order, committed resolution/no-unload propagation, conditional table constancy, and local reloading-step classification.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | Finite T63/T64 fragments only; nesting/maximality, same-owner confinement, initial intervals, eventual close, and recovery conclusions remain premises or absent.                                                                                                                                                                                      |
| `CertifiedTwoBatch`                                                                                                                                                                                       | Requires same-successor, pointwise same-recovery, and result-stability certificate fields before either order is permitted.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | The certificate is supplied, exactly two pure calls are modeled, and no actual concurrency or external-effect safety follows.                                                                                                                                                                                                                          |
| `ParallelHarness`                                                                                                                                                                                         | Requires finite task IDs/modes, effect commutation, and result-permutation certificates; proves model-order commit, one exclusive barrier, and a no-effect cancellation drain.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | The bounded proof-carrying scheduler slice is pure and finite; no promise races, cleanup, fairness, persistence, or TypeScript equivalence follows.                                                                                                                                                                                                    |
| `ParallelSchedule`                                                                                                                                                                                        | Folds an arbitrary finite sequence of certified windows and exclusive barriers; proves exact composed endpoint/recovery equality, model-order reports, and global task-ID uniqueness.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | Pure finite schedule semantics only. No wall-clock overlap, worker IO, promise races, fairness, retries, cleanup, persistence, or TypeScript scheduler refinement follows.                                                                                                                                                                             |
| `AsyncHarness`                                                                                                                                                                                            | Proves indexed fiber phase transitions, successful finite traces with explicit completion order, drained permutation certificates, and concrete race/failure/cancellation witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Bounded pure fiber semantics only. No live task handles, wall-clock fairness, cancellation delivery, cleanup, external IO, or deployed Harness refinement follows.                                                                                                                                                                                     |
| `DurableSettlement`                                                                                                                                                                                       | Requires an indexed pure effect specification; proves frame/entry length and projection, exact newest-first recovery, supplied crash-prefix decomposition, and typed resume.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | The transcript digest is a collision-free Lean list, and the crash cut is supplied as a proof. No bytes-on-disk, fsync, cryptographic authentication, process coordination, or external exactly-once behavior follows.                                                                                                                                 |
| `DurableCodec`                                                                                                                                                                                            | Requires a JSON AST and an entry decoder certificate; proves raw-frame round trips and strict prefix scanning into an indexed `DurableSettlement.Log`, rejecting malformed/torn/unknown/non-contiguous frames.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | AST-level validation only. No byte parser, filesystem scanner, partial-write model, flush barrier, or arbitrary crash-cut inference is included.                                                                                                                                                                                                       |
| `DurableBytes`                                                                                                                                                                                            | Defines unary-length framing over `List UInt8`, proves one-frame and counted-list round trips, decodes the numeric `RawFrame` payload, and bridges a counted byte prefix to `DurableCodec.scanPrefix` while exposing the discarded suffix.                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | The binary format is an explicit Lean contract, not external JSON-byte compatibility; no filesystem, `fsync`, cryptographic authentication, or inference of an unknown frame count is included.                                                                                                                                                        |
| `DurableIO`                                                                                                                                                                                               | Provides typed append plans, an in-memory backend, a real `IO.FS` backend, and `readAndRecover`/`RecoveryCertificate` evidence that accepted bytes recover a typed prefix while exposing the suffix.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Runtime adapter evidence only. `IO` success is not an `fsync` or crash-atomicity theorem; no authenticated storage, multi-process coordination, arbitrary-file repair, or external-effect exactly-once behavior is proved.                                                                                                                             |
| `Registry.setAt`                                                                                                                                                                                          | Uses dependent equality transport so a value cannot be installed at a differently typed key.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | No runtime aliasing, notification, or mutable-store semantics are modeled.                                                                                                                                                                                                                                                                             |
| `View.resolve`                                                                                                                                                                                            | Requires `needs op` before a binding can be requested.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Construction of the view and completeness of its registry snapshot remain obligations.                                                                                                                                                                                                                                                                 |
| `ToolSpec.Invocation`                                                                                                                                                                                     | Requires proof fields before dispatch through the dependent API.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | The origin and adequacy of the propositions are not certified by the structure itself.                                                                                                                                                                                                                                                                 |
| `EmissionClass`                                                                                                                                                                                           | Records a classification.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   | No behavior is enforced from the label.                                                                                                                                                                                                                                                                                                                |
| `Lifecycle.Withdrawable`                                                                                                                                                                                  | Quantifies over a supplied finite list of supplied consumer records.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | The list is not proved to enumerate a live registry, and its Boolean `installed` fields are not linked to lifecycle states.                                                                                                                                                                                                                            |
| `Harness.RunnerState`                                                                                                                                                                                     | Sequential reference functions construct `replayProof` and a six-index `RecordChain` tying model history, IDs, records, final leases, and `callBoundaries log`; public theorems expose boundary/record equality and lease threading.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | The boundary projection erases coordinates and has no full Harness translation; there is no refinement to TypeScript Harness, real I/O, parallel scheduling, durable storage, or crash recovery.                                                                                                                                                       |
| `GenericSessionHarness.RunnerState`, `Examples.DependentChoiceSession`                                                                                                                                    | A reusable rich `Session` wrapper records request/surface/tool/lifecycle events for an arbitrary generic catalog and proves exact rich-to-structural projection, request reconstruction, replay, an indexed request-ready handoff, and preservation of request reconstruction across an accepted call/result append; the dependent-choice fixture supplies a non-counter instance with one success and one policy rejection.                                                                                                                                                                                                                                                                                | Pure finite in-memory evidence only; no transport, persistence, external tool execution, scheduling, crash recovery, or TypeScript/deployed Harness equivalence.                                                                                                                                                                                       |
| `DeepSeekSessionRequest`                                                                                                                                                                                  | An indexed `Session.ModelRequest` must carry explicit model/system/tool-schema agreement before the schema-generic DeepSeek builder produces a retained `PreparedRequest`; its exact `ChatRequest` can be lifted to a raw `RequestPlan` or to complete/streaming `TypedRequestPlan`s whose mode flag is proved. `executeComplete` exercises a complete plan through an injected transport, `executeStreamingSse` exercises a streaming plan through the local SSE process adapter, and `executeCompleteAndAppend` admits and appends the complete response to the same schema-indexed runner with body/header/sequence/local-ID/tool-count/request-reconstruction certificates.                             | Optional provider controls, parser-backed input-schema validity, credentials, remote transport, provider obedience, and deployed equivalence remain external.                                                                                                                                                                                          |
| `DeepSeekSessionRequestBytes`                                                                                                                                                                             | The byte-preserving continuation retains the canonical UTF-8 request body, executes an injected byte transport, and carries raw response bytes plus decoded text into typed response admission and the same schema-indexed append endpoint.                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | Invalid UTF-8, HTTP/transport failures, semantic rejection, live networking, credentials, provider behavior, persistence, and deployed equivalence remain external.                                                                                                                                                                                    |
| `DeepSeekSessionRequestStreaming`                                                                                                                                                                         | The indexed stream bridge accepts a caller-supplied certified finisher and retains a proved streaming `RequestPlan`, strict process/SSE frames, selected finished rich response, and exact schema-indexed append endpoint; text/tool/mixed/multi-call wrappers select existing finishers.                                                                                                                                                                                                                                                                                                                                                                                                                   | Unsupported stream kinds, malformed/incomplete bodies, blocked reads, live/provider behavior, persistence, and deployed equivalence remain external.                                                                                                                                                                                                   |

`Cordis.DeepSeekStreamHarnessCancellation` extends the checked complete-body streamed
conversation loop with a typed pre-round cancellation decision. A cancelled result retains the
completed streamed prefix and unchanged runner/model endpoint; interruption of an in-flight
process read, HTTP request, stream reader, or external tool remains outside this boundary.

`Cordis.DeepSeekAsyncStreamCancellation` carries that cancellation result through the cooperative
process race. Its fixture cancels one child before round zero and checks the typed reason, terminal
phase, unchanged runner/model endpoint, and empty completed prefix; it does not claim interruptible
reads, fairness, arbitrary cleanup, or deployed async cancellation equivalence.
`Cordis.DeepSeekAsyncStreamRetryCancellation` carries the retry-aware indexed result through the
same cooperative race. Its `JobResult` retains the dependent retry trace/error and final endpoint;
the fixtures check both a cancellation-first child with an exact round/reason stop and a delayed
success-first child with two accepted rounds. Blocked-read interruption, fairness, cleanup,
reconnect, and deployed async retry/cancellation equivalence remain external.

`Cordis.DeepSeekStreamHarnessPrefix` extends the same continuation over the line-oriented
process prefix. It retains either a completed multi-call tool append or the exact parsed prefix
with a typed line-cancellation/read-budget stop; byte framing and blocked-read interruption are
not proved.

`Cordis.DeepSeekStreamByteFraming` is the separate pure byte-ingress boundary below that line
prefix. It splits arbitrary `ByteArray` chunks at LF boundaries, retains an exact canonical
reconstruction, decodes complete lines as UTF-8 before typed prefix parsing, and bridges a complete
reconstruction to strict SSE validation. It does not prove process-level byte reads, blocked-read
interruption, backpressure, cancellation, reconnect, provider-complete assembly, or deployed
stream equivalence.
`Cordis.DeepSeekCurlByteFraming` is the finite process-backed companion: bounded stdout reads
retain raw `ByteArray` chunks and the private status/body parse equation, then feed the observed
body chunks unchanged through the pure byte framer. It returns typed process/status/read-limit
errors and a dependent strict-SSE certificate, but does not establish network reachability,
credential validity, executable trust, blocked-read interruption, backpressure, cancellation,
reconnect, provider-complete assembly, or deployed stream equivalence.
`Cordis.DeepSeekCurlBytePrefix` is the next process boundary: bounded byte reads retain raw
chunks, incomplete fragments, and a typed stop state; complete body lines advance the pure prefix
state before another read, while the private status trailer remains outside SSE parsing. It proves
neither blocked-read interruption nor backpressure, cancellation, reconnect, provider-complete
assembly, credential/executable trust, or deployed stream equivalence.
`Cordis.DeepSeekStreamHarnessBytePrefix` is the typed continuation above that boundary:
completed prefix witnesses feed the existing rich/tool/session append path, and prefix fuel stops
remain explicit nonterminal Harness stops. The tests establish only deterministic process/framing
and runner evidence; they do not establish blocked-read interruption, backpressure, reconnect,
provider-complete assembly, credentials, executable trust, or deployed equivalence.
`Cordis.DeepSeekCurlBytePrefixTimeout` adds a real `Std.Async.Sleep` race around each blocking byte
read. When the configured child deadline wins, the process is killed and the typed result retains
the accepted prefix state, raw chunks, pending fragment, stderr, exit observation, and timeout line.
Blocked, delayed-prefix, and fast-completion fixtures are executable. This is local configured-child
evidence only; arbitrary descendant cleanup, fairness, backpressure, authenticity, durability,
reconnects, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekStreamHarnessBytePrefixTimeout` composes completed timed prefixes with the dependent
streamed conversation runner and its fuel-bounded multi-round endpoint trace. Timeout, fuel, and
cancellation stops remain explicit nonterminal prefix errors; no in-flight provider interruption,
reconnect guarantee, or deployed asynchronous Harness equivalence is claimed.

When an adapter such as `ToolWire` is used, textual resolution, decoding, and admission can
fail closed before an `AuthorizedCall` is constructed. The adapter still supplies its resolver,
codecs, decidability procedures, and proof-producing `certifyAdmission` implementation. Its
existence does not prove correspondence to a deployed Harness registry.

`DeepSeekSchemaStreamConversation` is also checked/proved/exercised at the complete-body
process/SSE/rich-stream/session boundary: its registry-derived typed request proves `stream: true`,
the complete body is validated before heterogeneous dispatch, and its caller-fueled result keeps
text completion distinct from exhaustion. This does not prove incremental reading,
backpressure, cancellation, reconnect, provider-complete assembly, call-ID authenticity,
persistence, external effects, or deployed Harness equivalence.

`DeepSeekHarnessProcessSchema` is the process-provenance refinement of that boundary. It retains
the exact registry-certified streaming plan, processed response, schema-dispatched step, and
dependent runner endpoint in one indexed result; request, process/status, and registry-execution
failures remain distinct. It remains complete-body local evidence and does not prove provider
obedience, credential authenticity, incremental delivery, persistence, or deployed equivalence.

`DeepSeekHarnessProcessSchemaPrefix` carries the same exact plan through the line-oriented prefix
boundary. Fuel exhaustion and line cancellation retain the plan and typed stop evidence; only the
completed `[DONE]` branch carries the dependent schema step and runner update. This remains
synchronous complete-line evidence and does not prove byte framing, blocked-read interruption,
persistence, or deployed cancellation semantics.

`DeepSeekHarnessProcessSchemaPrefixConversation` lifts the same provenance through the finite
conversation loop. Completed tool-round witnesses retain their individual prepared plans and
accepted prefixes; the stop constructors retain the attempted plan for round exhaustion or
cancellation. This is still a local caller-fueled line adapter, not deployed interruption or
durability evidence.

`DeepSeekSchemaStreamPrefixConversation` additionally retains a process prefix at a caller-selected
line budget or cancellation boundary and refuses registry dispatch until the completed `[DONE]`
rich/session certificate exists. This is line-oriented evidence only; byte framing, blocked-read
interruption, backpressure, reconnects, provider-complete assembly, call-ID authenticity,
persistence, external effects, and deployed Harness equivalence remain unproved.

`DeepSeekSchemaStreamErrors` adds one more explicit trust boundary: a heterogeneous provider
failure is retained only after the selected entry's schema and generic admission/policy proofs are
present, then converted to a model-visible `isError` result with exact error text and unchanged
model evidence. The continuation fixture requires `.include` on the subsequent request source and
proves a later terminal response. This does not establish provider error honesty, retries,
cancellation, persistence, external effects, or deployed error semantics.

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
deployment or upstream interoperability. `Cordis/AxiomAudit.lean` runs `#print axioms` for 2344
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

`GlobalProgressTermination` is the deliberately separate quantitative bridge. A supplied strict
natural-valued potential telescopes over exact dependent lifecycle traces, so an initial `K + 4`
bound proves the corresponding trace-length bound and excludes nonempty cycles. Neither the
potential nor its strict-decrease law is derived from `GlobalProgress`; target-turn finiteness,
maximal-execution termination, fairness, trace-wide assignment, support, deletion, and confluence
remain outside the claim.

`GlobalProgressRun` is the finite execution bridge above those two modules. Its
`ProgressAuthority` re-supplies the local progress laws at each well-formed endpoint and its
`StepPotential` supplies strict decrease. `runFuel` retains the exact lifecycle trace and a
dependent endpoint proof, while `certifiedRun_quiescent` proves quiescence when fuel is the
initial potential. This does not derive either authority, recover the paper's target-turn charge,
or upgrade a finite-fuel certificate to maximal-execution termination, fairness, trace-wide
assignment, support, confluence, or unrestricted Theorem 66.

`GlobalProgressAssignment` is the explicit, supplied provenance bridge above this runner. Its
authority assigns each lifecycle transition to a `StepProgramAssignment`, and `assignTrace`
reconstructs the dependent assignment for the complete intrinsic trace. The bridge preserves the
runner's endpoint and stop proofs but intentionally does not infer a fixed program, root, oracle,
or continuation reachability from a raw transition.

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
- `DurableIO` moves one boundary outward for executable evidence: `MemoryStore` and `FileBackend`
  actually perform `IO` reads/writes/flush calls, while `AppendPlan` and `RecoveryCertificate`
  keep the semantic contract typed. A successful host call is not evidence that bytes survived
  a crash, reached stable media, were authenticated, or were coordinated with another process;
  `RecoveryCertificate.MatchesExpected` remains an explicit caller-supplied dependent equality;
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
  19, Theorem 20, Corollary 21, or real parallel scheduling; `ParallelHarness` and
  `ParallelSchedule` are only the bounded pure certificate slices documented above;
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
- `DeepSeekApi`, `DeepSeekCurlTransport`, `DeepSeekCurlStream`, and `DeepSeekCurlSession` prove no
  live HTTP delivery,
  credential validity,
  complete provider schema compatibility, streaming behavior, executable trust, or local
  `ToolSpec` validation; they provide typed codec and pure/process transport seams exercised by
  deterministic fixtures;
- `DeepSeekApiErrorEnvelope` proves only the response-body `{error: ...}` parse/decode certificate;
  it does not authenticate the provider's error, establish retry/backoff safety, or change the
  credential/network/deployment boundary;
- `DeepSeekOutcomeTransportLoop` proves only complete-body generic-transport continuation. Its
  non-success API-error branch preserves the typed error and unchanged runner, while malformed
  envelopes remain typed boundary errors; incremental IO, retries, cancellation, and deployed
  equivalence remain external;
- `DeepSeekCurlSession` proves no source-event or provider-ID authenticity, persistence,
  cancellation, external execution, or whole-session equivalence; it is a complete-body terminal
  composition that retains the process/wire certificate and local runner append proofs;
- `DeepSeekCurlIncremental` proves no byte-level framing, backpressure, cancellation, reconnect,
  network reachability, credential validity, executable trust, or provider-complete assembly; it
  supplies a bounded line-oriented callback and a separately strict-validated reconstructed body;
- `DeepSeekCurlPrefix` proves only synchronous line-boundary prefix advancement and child cleanup;
  it does not interrupt a blocked read or prove byte framing, backpressure, reconnect, network or
  credential validity, executable trust, provider-complete assembly, or deployed equivalence;
- `DeepSeekCurlPrefixSession` proves only completed-prefix semantic projection and local runner
  append invariants; it does not turn fuel/cancellation into in-flight interruption, external tool
  execution, persistence, provider-complete assembly, or deployed session equivalence;
- `DeepSeekAsyncHarness` proves only a cooperative race observation over two complete-body
  process-prefix/session jobs. It retains the first typed result and requests cancellation of the
  loser, but the synchronous line read is not interruptible by that request; fairness, arbitrary
  cleanup, and deployed async equivalence remain external;
- `DeepSeekAsyncStreamHarness` proves only the corresponding cooperative race over complete-body
  streamed tool/session continuations. The winning result retains typed tool executions, rounds,
  final model, and runner state; synchronous reads, fairness, arbitrary cleanup, and deployed async
  equivalence remain external;

- `DeepSeekAsyncStreamCancellation` proves only the policy-bearing pre-round extension: a
  cancellation-first child retains its typed reason, unchanged runner/model endpoint, and zero
  dispatched rounds while the sibling remains a real streamed continuation; blocked-read
  interruption, fairness, cleanup, and deployed cancellation equivalence remain external;
- `DeepSeekStream` proves a live reader, HTTP delivery, buffering/backpressure, cancellation,
  provider-complete stream assembly, or equivalence to the deployed DeepSeek stream protocol; it
  is a strict in-memory SSE/data-frame boundary with retained local certificates;
- `DeepSeekRichStream` proves a complete provider stream assembler, reasoning/tool-call semantics,
  multi-choice behavior, live transport, or deployed DeepSeek equivalence; it is a deliberately
  narrow one-choice assistant-text projection into the local `RichStream` language;
- `DeepSeekRichToolStream` proves complete multi-call/tool execution semantics, live transport,
  or deployed DeepSeek equivalence; it is a restricted one-tool projection whose raw arguments
  remain strings and whose stable IDs/names are required on the accepted deltas;
- `DeepSeekRichMixedStream` proves only the accepted one-choice interleaving subset: text,
  reasoning, and one indexed tool call across separate frames with exact local block assembly;
  it rejects same-frame mixed fields, multiple choices/calls, unsupported finishes, replay
  metadata, and live/deployed assembler behavior;
- `DeepSeekRichMultiStream` proves only the accepted one-choice finite multi-call subset: indexed
  function calls may be interleaved or introduced together, with first-seen local indices and
  independent IDs/names/raw arguments; it rejects same-frame cross-kind fields, multiple choices,
  unsupported finishes, replay metadata, and live/deployed assembler behavior;
- `DeepSeekProviderAssembler` proves the source-shaped post-decoder fold for text, reasoning, and
  tool-call blocks: first-seen order, open-block fallback, first-close-wins, latest tool metadata,
  last usage/finish/replay metadata, max-token tool pruning, and typed unknown-block errors are
  retained in a certificate; wire decoding, image/tool-result schemas, opaque replay JSON, and
  deployed TypeScript equivalence remain external;
- `DeepSeekAssemblerToolRound` proves only the post-assembly local seam: provider-shaped blocks
  become local `FunctionCall`s, the existing dependent counter configuration executes them, and
  assistant/tool-result messages append with exact session certificates; provider-ID authenticity,
  external effects, transport, persistence, and deployed equivalence remain external;
- `DeepSeekProviderStreamAssembly` proves the next source-honest seam: an accepted strict
  multi-call SSE body maps to provider chunks and retains both the rich-source and assembler
  fold certificates. Replay metadata is rejected and structured failure/abort causes are
  normalized rather than treated as wire-equivalent;
- `DeepSeekStreamToolRound` proves the wire-backed dependent continuation and session append.
  Its executable counter fixture reaches model `5` from `2`; network/authentication, external
  effects, persistence, and deployed Harness equivalence remain unproved;
- `DeepSeekScopedStreamToolRound` proves the scoped/approval-routed variant over the same
  accepted stream subset. It retains nearest-first resolution, typed approval, dependent
  replies, and exact assistant/tool-result append; scope construction, authenticated policy,
  external effects, persistence, cancellation, and deployed equivalence remain unproved;
- `DeepSeekProcessStreamToolRound` proves the configured complete-body process adapter in front
  of that round: status/SSE evidence is retained before provider assembly and dependent execution.
  The fixture is deterministic and local; network reachability, process trust, incremental
  delivery, cancellation, persistence, external effects, and deployed equivalence remain outside;
- `DeepSeekProcessScopedStreamToolRound` proves the corresponding complete-body process adapter
  over scoped approval and dependent execution. Its fixture retains status, strict-wire, approval,
  and exact session-append evidence for three accepted frames and two calls; network,
  authentication, process trust, incremental delivery, cancellation, persistence, external
  effects, and deployed equivalence remain outside;
- `DeepSeekProcessScopedConversation` proves a finite process-backed scoped continuation over a
  round-indexed process family. Its fixture checks the exact two-round terminal endpoint and the
  separate one-round fuel-exhaustion stop; retries, cancellation, persistence, external effects,
  live provider behavior, and deployed equivalence remain outside;
- `DeepSeekProcessScopedRequestConversation` proves the request-provenance refinement of that
  continuation: each round rebuilds a typed streaming request from the current session and stores
  the prepared result under the exact request index; distinct request bodies, terminal completion,
  and fuel exhaustion are exercised locally, while live network/provider behavior and deployed
  equivalence remain outside;
- `DeepSeekProcessScopedRequestBytePrefixConversation` carries that request index through raw byte
  chunks and pending framing before strict SSE completion, scoped execution, and session append;
  its fixture proves multi-chunk two-round completion plus a typed prefix-fuel stop. Network,
  executable trust, blocked-read cancellation, backpressure, reconnects, retries, persistence,
  external effects, and deployed equivalence remain outside;
- `DeepSeekCurlProviderAssemblyPrefix` composes the line-oriented process prefix with the terminal
  provider assembly certificate. It retains accepted-line/SSE evidence before the whole-body rich
  provider fold; live provider-incremental semantics, backpressure, cancellation, persistence,
  external effects, and deployed equivalence remain outside;
- `DeepSeekCurlProviderAssemblyIncremental` retains the parsed rich prefix, raw chunks, mapped
  provider chunks, and source-shaped assembler state after each accepted callback line. Its final
  certificate is exact; status-separator padding is explicit, while blocked reads, backpressure,
  cancellation, process trust, persistence, external effects, and deployed equivalence remain
  outside;
- `DeepSeekCurlProviderAssemblyToolRound` feeds the terminal incremental certificate directly into
  dependent `FunctionCall` execution and certified assistant/tool-result session append without
  reparsing the completed body. `DeepSeekCurlProviderAssemblyToolPrefix` also retains the typed
  provider/tool prefix on synchronous fuel or cancellation and admits execution only on completion;
  blocked-read interruption, backpressure, reconnects, process trust, persistence, external effects,
  and deployed equivalence remain outside;
- `DeepSeekCurlBytePrefixProviderAssemblyTool` composes arbitrary byte chunks and the timer-driven
  reader with provider assembly and dependent execution. Completion carries provider, assembly,
  execution, and session-append certificates; fuel, cancellation, and timeout retain a pending
  provider prefix. Byte backpressure, reconnects, persistence, process authenticity, and deployed
  Harness equivalence remain outside;
- `DeepSeekCurlProviderAssemblyToolConversation` lifts those round certificates into a bounded
  `ConversationRunner`. Each round preserves the prior-model index, allocates fresh local call IDs,
  appends certified tool results, and ends on a no-tool response or explicit fuel exhaustion. The
  deterministic fixture is local evidence only; deployed conversation equivalence remains outside;
- `DeepSeekTerminalOutcome` proves only the fixed-order complete-body classification over the
  provider-failure, text, one-tool, mixed, and finite multi-call certificates; it does not turn
  those certificates into a session message or claim deployed stream equivalence;
- `DeepSeekSessionBridge` proves provider-ID authenticity, persistence, source-event truth beyond
  its supplied proofs, or whole-session equivalence; it is a terminal local append seam whose
  numeric IDs and source sequence evidence are caller-supplied;
- `DeepSeekSessionRunner` proves no live transport, cancellation, persistence, external tool
  execution, provider-ID authentication, or full Harness session equivalence; it is a pure
  sequential composition for text, one-tool, mixed, and multi-call responses whose local IDs are
  allocated by an explicit tool-call count;
- `DeepSeekApiSession` proves no complete response schema, provider-ID authenticity, transport,
  persistence, external tool execution, or whole-session equivalence; it is a singleton-choice
  normalization with explicit rejection guards;
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
- `LoaderHMR` proves a deployed loader, dynamic-import, filesystem-watch, fiber-disposal, cache,
  or hot-replacement equivalence merely from its finite entry/reconciliation/classification and
  transactional rollback model;
- `RuntimeRefinement` accepts the full Harness stream union, is complete for the tolerant
  TypeScript assembler, verifies provider streaming, or proves chunk storage;
- `RuntimeFailureRefinement` reconstructs open-block failure state, chooses retry/cancellation,
  authenticates provider failure payloads, or equates its terminal certificate with a normal
  rich/session finish;
- `SessionRefinement` accepts the complete Harness event union, preserves every source field in
  the local event, validates persistence, or proves whole-session behavioral equivalence; its
  admitted text and complete assistant-tool-call surface subset retains selected source metadata
  in `State.wireSurface` but still intentionally projects into smaller local message types.
  `SessionArchive` preserves envelope-valid unsupported records losslessly, but does not assign
  them payload semantics or replay behavior; `SessionPayloadArchive` adds only typed raw shape
  retention and block-tag classification, not provider/tool interpretation;
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

`GlobalPaperTraceScopedConfluence` is an additional finite certificate layer. It indexes the
reachable package family explicitly, stores source/target equations for each selected rewrite,
and proves endpoint uniqueness for the supplied decreasing/local-join data. Its concrete
activation/orchestration fixture is nonempty, but it does not derive a CORDIS strategy, lifecycle
normalization, Lemma 72, or Theorem 73.

`DeepSeekAsyncStreamHarnessTimeout` is the timed companion to the cooperative streamed race:
configured children use the byte-prefix deadline adapter, retain the dependent success trace or
exact timed prefix, and project a deadline to a cancelled phase. Its fast, timeout, and race
fixtures are executable local-process evidence; task-cancellation delivery, arbitrary descendant
cleanup, fairness, backpressure, reconnects, authenticity, and deployed equivalence remain
outside.
`DeepSeekExternalToolProcess` is the source-honest external-tool seam: it retains the configured
command, stdout/stderr, exit code, parsed JSON, and typed decoded result as an observation.
`AcceptedResult.certified` requires an explicit `ToolSpec.post` proof before constructing a
`ToolSpec.CertifiedOutcome`; process output alone cannot certify its postcondition. Command
identity, sandboxing, authentication, exactly-once effects, cleanup, and deployed Harness
equivalence remain outside.
`DeepSeekExternalToolRound` is a narrower local proof boundary. Given that acceptance proof, its
`ExternalToolRound` certifies the exact two-event session append and its sequence/message/protocol
projections. The result renderer is explicit input, and this does not establish process identity,
provider wire compatibility, or deployed Harness behavior.
`DeepSeekExternalGenericRound` makes the process-to-generic handoff reusable: `observeAndDispatch`
retains the full typed observation and accepts only a caller-supplied dependent certificate that
also constructs the generic `ExternalDispatchResult`. Its executable counter fixture advances the
generic runner and rich-session state on success; a decodable nonzero-exit observation remains
uncertified. Process identity, sandboxing, authentication, exactly-once effects, cleanup, and
deployed Harness equivalence remain outside.
`DeepSeekExternalGenericConversation` composes those proof-carrying dispatches into a finite
dependent script. Continuations are chosen from the exact accepted dispatch, accepted edges form an
indexed runner trace, and completion, fuel exhaustion, uncertified stops, and observation errors
are separate results. `runCapturingErrors` retains the accepted prefix when a later process fails
to spawn or decode, while `run` preserves the error-returning API. Because heterogeneous
`ToolSpec` values are above the executable `IO` universe, each trace edge stores its external origin
in `Prop` rather than pretending to return a homogeneous wire payload. This proves finite
local-process orchestration only; process identity, sandboxing, authentication, exactly-once
effects, cleanup, persistence, provider obedience, and deployed Harness equivalence remain outside.
`DeepSeekExternalGenericSession` is the rich-session refinement of that finite runner. Its
dependent script carries the exact generic runner, `Session`, and protocol-projection equality;
the counter fixture also exposes a request-ready state with a present indexed `Session.ModelRequest`
before external dispatch. Accepted dispatches append one typed call/result pair exactly once, and
fuel, uncertified, or observation-error stops retain the current session prefix. The counter
fixtures cover a completed endpoint and a later malformed-observation stop. This is local finite evidence only; process
identity, sandboxing, authentication, exactly-once effects, cleanup, persistence, provider
obedience, and deployed Harness equivalence remain outside.

`DeepSeekHarnessLocalSseIndexed.runWithKey` is checked against the real one-shot loopback
HTTP/SSE fixture. The result retains local request/response/wire evidence plus exact indexed
streaming-plan and `ExtensionRunner.appendFinished` certificates; the executable example checks
one valid request, three frames, and the `2 -> 3` session endpoint. It does not claim returned-
body provenance, remote reachability, TLS, credentials, provider authenticity, persistence,
blocked reads, reconnects, or deployed Harness equivalence.

`DeepSeekHarnessLocalSseIndexedLoop` is the two-round continuation. Its first append is the exact
dependent input to a rebuilt second `Session.ModelRequest` and `PreparedRequest`; the resulting
`TwoRoundResult` retains both loopback wire certificates and proves the `2 -> 4` final sequence.
This is still local one-shot process/HTTP evidence and does not establish returned-body
provenance, remote/provider authenticity, persistence, reconnects, blocked reads, or deployed
Harness equivalence.

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
