# CORDIS Lean 0.2: Log-reconstructible generic harness

<!-- markdownlint-disable MD013 MD029 -->

## Status

This specification defines the active implementation slice after the finite `0.1.0` counter
kernel. The generic phase-indexed runner, exact-call allow/reject policy paths, structured
non-counter example, intrinsic rich session/surface kernel, model-request reconstruction, and
the reusable generic rich-session bridge (with both counter and dependent-choice
instantiations) are implemented. `SessionValidation`
proof-produces append/replacement and finite-suffix certificates from parsed-but-untrusted typed
events. A current-Harness `StreamChunk` subset is also decoded from `Lean.Json` ASTs into the
intrinsic rich-stream validator. `TextRefinement` now adds a supported UTF-8 JSONL ingress that
parses exact lines before invoking the stream/session/failure validators. Its
`validateFailureBytes` path retains a typed normalized `error`/`aborted` terminal without
coercing an open-block failure into a successful rich trace. `SessionEventArchive` now
recognizes every pinned core event tag and preserves unsupported known payloads as raw records;
`SessionPayloadArchive` adds typed raw retention for message/chunk payloads, content-block tags,
usage, tool-result error/meta, and malformed known shapes. Full payload semantics and the later
production/refinement layers listed below remain open;
this file is therefore an in-progress contract, not a completed `0.2.0` release claim.

The pure scheduler boundary is now multi-segment: `Cordis.ParallelSchedule` executes any finite
sequence of certified parallel windows and exclusive barriers, with exact composed endpoint and
recovery proofs, model-order reports, and globally unique task IDs. Wall-clock overlap, worker IO,
promise races, fairness, and deployed scheduler equivalence remain explicit non-claims.
`Cordis.AsyncHarness` adds a bounded indexed-fiber state machine over the same pure boundary:
typed start/complete/fail/cancel transitions, finite completion-order traces, drained schedule
certificates, and concrete race/cancellation witnesses are now executable and proved. Live task
handles, wall-clock fairness, cancellation delivery, cleanup, and deployed scheduler refinement
remain explicit non-claims.
`Cordis.DeepSeekAsyncHarness` adds a deliberately narrow executable bridge: two complete-body
text-prefix process jobs run in cooperative `ContextAsync` children, and `ContextAsync.race`
retains the first typed prefix/session result while requesting cancellation of the loser. A real
two-process fixture and pure terminal-phase facts are included. The underlying synchronous line
read is not made interruptible, so blocked-read cancellation, fairness, arbitrary cleanup, and
deployed asynchronous Harness equivalence remain external.
`Cordis.DeepSeekAsyncStreamHarness` lifts the race over the complete-body streamed Harness
continuation. Each child can execute a dependent tool-call round and a later text terminal under
explicit fuel, and the winning typed result retains tool executions, round witnesses, final model,
and runner endpoint. Synchronous reads, fairness, arbitrary cleanup, and deployed asynchronous
equivalence remain external.
`Cordis.DeepSeekAsyncStreamCancellation` carries the typed pre-round cancellation policy through
that race. Its fixture cancels one child before dispatch while the other remains a real streamed
tool/text continuation; the accepted cancellation result preserves its reason, unchanged
runner/model endpoint, and empty completed prefix. Blocked-read interruption and deployed async
cancellation equivalence remain external.
`Cordis.DeepSeekAsyncStreamRetryCancellation` composes the same cooperative race with retry-aware
streamed jobs. The dependent winner retains its indexed retry trace and endpoint; the
cancellation-first branch retains its pre-round reason and empty accepted prefix, while a
delayed-child success-first fixture exercises two accepted rounds. Blocked-read interruption,
fairness, cleanup, reconnect, and deployed retry/cancellation equivalence remain external.

`Cordis.DeepSeekHarnessExtensions` generalizes complete and streaming request construction to
every indexed `Session.ExtensionSchema`, and appends an accepted assistant view without changing
that schema. Custom log-only events remain in the append-only session but do not enter the model
request; custom surface events use the schema-provided message projection. The fixture proves the
exact one-message request shape and schema-preserving assistant append. Its indexed runner carries
the sequence/tool-count invariants through a validated terminal rich-response fixture.
`SessionExtensionRefinement` adds a bounded typed-ingress layer: a caller-supplied
`ExtensionCodec` constructs the dependent kind/payload sum, while the generic envelope decoder
checks the declared tag, safe sequence/time fields, rejected metadata, and exact append freshness.
`ExtensionReplay`/`ValidatedExtensionLog` extends that proof across an ordered list: every raw
event, dependent decode, append equation, and intermediate indexed session is retained, with final
sequence and typed-event-count theorems. The heartbeat/banner fixture exercises log-only and
surface visibility plus wrong-tag, ignorable, malformed-payload, and stale-sequence rejection.
Arbitrary JSON, provider compatibility, persistence, transport, and deployed Harness equivalence
remain external.

`Cordis.SessionExtensionArchive` composes the typed extension replay with the lossless full-event
archive. Its success type carries the same raw list in both certificates, proves every archived
record is a required extension, and exposes the final indexed session; known core and ignorable
records fail closed before semantic replay. It remains an in-memory archive attachment, not
durability or deployed persistence equivalence.

`Cordis.DeepSeekHarnessExtensionArchive` is the schema-indexed runner bridge above that archive.
`restoreRunner` derives the indexed runner's local tool-call count and proves exact equality to the
archive's final session, while `RequestCertificate` rebuilds a typed request from that exact
endpoint. It remains a caller-owned extension/schema certificate; mixed current-Harness replay,
provider compatibility, transport, durable persistence, and deployed equivalence are unclaimed.

`Cordis.DeepSeekHarnessExtensionRequest` composes that endpoint with the request-side tool-schema
certificate. `buildCertifiedRequest` accepts only a validated, duplicate-free tool source and
retains both its dependent proof and the exact request equation from the restored indexed session.
This does not prove provider-side tool obedience or any live transport/deployed equivalence.

`Cordis.DeepSeekHarnessExtensionPersistence` composes the extension archive with the persistence
boundary: a header plus required extension suffix is validated at the JSON-AST, text, UTF-8, and
`DurableIO.Backend` layers, with exact raw-row/header equations and a runner/request attachment.
Known core and ignorable rows fail closed. Mixed current-Harness replay, packed-row persistence,
crash repair, fsync, and deployed persistence equivalence are not claimed.

`Cordis.DeepSeekHarnessMixedPersistence` adds only a source-partition certificate for mixed rows.
Its explicit schedule reconstructs the complete archived input while the core and extension
projections are validated independently at their existing indexed endpoints. It does not claim
combined arbitrary-schema replay, extension surface integration with the core protocol, global
sequence normalization, or deployed persistence equivalence.

`Cordis.DeepSeekHarnessSchemaLift` supplies the exact adjacent transport: a validated core
session indexed by `Session.noExtensions` can be lifted into any `ExtensionSchema` while
retaining dependent kind/payload/intent indices, `ValidLog`, materialized surface, header, and
protocol-projection equations. The example uses a custom schema. Custom-row decoding and a
single mixed replay remain separate obligations.

`Cordis.DeepSeekHarnessMixedReplay` implements that next bounded obligation at the log level.
Its `Row` schedule interleaves core JSON rows with extension JSON rows. Core rows use the
stateful `SessionRefinement` decoder/refiner; extension rows are accepted only for custom
log-only kinds and are checked against the target session clock. The proof-carrying `MixedState`
keeps a shadow core session synchronized by a phantom clock event and proves exact final
sequence, surface/header, and protocol-projection equations. Extension surface rows and
extension encodings of core kinds reject explicitly. This is not arbitrary extension surface
integration, provider/transport/persistence compatibility, or deployed equivalence.

`Cordis.DeepSeekHarnessTransportContract` closes a separate local transport composition seam.
`executePrepared` sends a prepared request through an injected `DeepSeekApi.Transport`, checks a
successful HTTP status, decodes the body once, applies `acceptValidated` to that same certificate,
and returns the exact appended runner endpoint. `TransportRound` retains body, decoder,
acceptance, and endpoint equations, while fixtures cover a successful tool-call response and a
typed 503 rejection. This does not establish live network, credential, provider, TLS/retry,
persistence, or deployed Harness behavior.

`Cordis.DeepSeekHarnessTransportToolRound` composes the retained `TransportRound` with the
dependent tool executor. The response certificate is consumed directly, without a second decode
or session admission, and the resulting runner retains exact assistant-plus-tool-result sequence
and tool-count equations. Its process-backed fixture is local evidence only; external tool effects,
provider behavior, retries, persistence, and deployed Harness equivalence remain unproved.

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
- `Cordis.GenericSessionHarness` and `Cordis.Examples.DependentChoiceSession`, which append the
  request header, user/assistant surface, successful dependent revision call, and policy-rejected
  label call to one rich session while proving exact projection to the generic runner log;
- `Cordis.Session.EventIntent`, `SurfaceTransition`, `ValidLog`, `ModelRequest`, certified
  replacement examples, and rich-to-structural `ProtocolCertificate`;
- `Cordis.SessionValidation.RangeWitness`, `ValidatedAppend`, `ValidatedSuffix`, and
  `ValidatedLog`, including exact structured rejection examples;
- `Cordis.SessionTheoremBridge.SurfaceTransition.replace_shadowed`,
  `SurfaceTransition.replace_covers`, `ModelRequest.reconstructible`,
  `ValidatedAppend.applies`, and `ValidatedLog.replays`, which expose the exact intrinsic append
  and finite-log endpoint certificates;
- `Cordis.RichStream`, including block-kind-indexed deltas, interleaved first-seen ordering,
  exact block ends, usage/terminal discipline, error/abort terminals, and aligned replay data;
- `Cordis.Schedule.runEffects_eq_of_perm`, promoting the exactly-two batch result to arbitrary
  finite semantic orders under a real pairwise commuting-family certificate;
- `Cordis.Coeffect`, mechanizing paper Definitions 22–26 for dependent finite contexts, concrete
  reversible bindings, typed local operations, finite satisfaction, and exact notifications;
- `Cordis.UnifiedContext`, directly modeling paper Definitions 27–31 and exposing exact finite
  unfoldings of Definition 32's negatively recursive context equation;
- `Cordis.ContextualEquivalence`, mechanizing the finite-context portion of Definition 33 and
  proving satisfaction and notification invariance under the resulting `Setoid`;
- `Cordis.OperationalEquivalence`, executing Definition 34's heterogeneous finite tests,
  proving the generator-level coarsest relation of Lemma 35, and formally separating the
  stronger paired-inverse law by counterexample;
- `Cordis.QuotientEffect` and `Cordis.CoeffectQuotient`, implementing Definitions 36–37,
  finite quotient-respecting composition/recovery, and the context-lift preservation laws;
- `Cordis.Transformation`, mechanizing Definition 17 generated transformation monoids,
  Lemma 18 closure, and full Definition 19 effect independence with inverse-yield stability;
- `Cordis.OperationIndependence`, proving full total Definition 39, finite partial distinct-key
  Theorem 40, and Definition 41's outcome-mediated interpreter/recovery while exposing the
  initial Theorem 42 closure boundary;
- `Cordis.Removal`, proving Theorem 20's finite target/prefix/suffix removal and later-inverse
  equations plus Corollary 21 for every permutation of retained state-indexed inverses;
- `Cordis.GlobalRegistry`, encoding Definitions 43–46/49 with opaque execution codes,
  birth-ranked parents, provider/view uniqueness, and well-formedness preservation for
  orchestration insert/retire/remove traces;
- `Cordis.MediatedIndependence`, reifying exact outcome-selected branches, stating the initial
  observational closure surface, and proving by counterexample that exact representatives need an
  extra coherence law;
- `Cordis.MediatedTheorem`, correcting partial composite domains and proving exact plus
  observational finite whole-run interchange for arbitrary outcome-selected computation trees;
- `Cordis.PartialTransformation`, proving full finite partial/Kleisli transformation-monoid
  commutation and success-conditional domain/inverse stability for those computation trees;
- `Cordis.ObservationalPartialTransformation`, proving those adaptive forward and inverse
  generators respect contextual equivalence and descending the complete closure theorem to
  domain-sensitive related partial maps;
- `Cordis.GlobalDynamics`, interpreting opaque iterator/undo codes externally with exact ordinary
  recovery, observational registration recovery, explicit confinement/read/equivariance
  obligations, and a total fueled Definition 52 runner with accumulated recovery/WF evidence;
- `Cordis.GlobalLifecycle`, encoding all seven lifecycle rule names as eight phase-indexed
  constructors with exact executed landings, inertia, unload recovery admission, and finite
  well-formedness-preserving traces;
- `Cordis.GlobalCalculus`, combining orchestration and lifecycle into one ten-name exact-endpoint
  relation with acted-on-name, state-map/edit, installation-boundary, and empty-origin evidence;
- `Cordis.GlobalTraceFacts`, proving bounded Lemma 54 foreign/static/committed/episode facts under
  explicit unload confinement and giving a kernel countermodel to bare recovery admission;
- `Cordis.GlobalTemporal`, reifying fallible off-source step maps and deriving finite
  relation-indexed interleaved/unload recovery from explicit totality, commutation, inversion, and
  reordering certificates;
- `Cordis.GlobalIteratorIndependence`, generating oracle-specific iterator programs from reachable
  partial forwards and actually yielded inverses, proving exact and `EffectEquiv`-observational
  closure independence with separately supplied reachable-forward respect, occurrence-indexed
  families, and explicit finite-reach/continuation-bound certificate types, and discharging
  `GlobalTemporal.PerStepCommutes` from accumulator provenance, step-map membership, and supplied
  `TotalStepMap` witnesses;
- `Cordis.GlobalTransposition`, using `Independent` to derive the raw iterator diamond and exact
  commutation for two supplied totalized generated pre-edit maps, using
  `ObservationalIndependent` for the `EffectEquiv` square with its separate `ProgramRespects`, and
  exposing exact lifecycle undo-code agreement, structural phase-edit commutation, and a
  noninjective-undo counterexample without claiming a lifecycle transition swap;
- `Cordis.GlobalForeignPhase`, factoring foreign-phase compatibility into explicit readable-edit,
  ordinary exact-successor, and same-child oracle laws, deriving registration framing
  structurally, constructing exact one-/two-sided framed raw executions with retained lookups, and
  kernel-separating all three missing premises;
- `Cordis.GlobalLandingTransposition`, adding exact cross-forward lifecycle-yield stability and
  fixed-program landing provenance, deriving positive-target preservation from well-formedness,
  and constructing all four common-source L-Iter/L-Finish transition pairs with one exact final
  state plus syntax/applicability/provenance countermodels;
- `Cordis.GlobalActivationTransposition`, combining program-root-aligned L-Begin with those
  landings, proving fixed-program endpoint/rule determinism, and constructing all nine
  common-source Begin/Iter/Finish diamonds plus an actual-second-step transposition wrapper;
- `Cordis.GlobalActivationOrchestrationTransposition`, kernel-refuting the literal clause-(2)
  registration condition, exposing occurrence-specific orchestration framing, and proving the
  corrected exact exchange while excluding registering activation/O-Insert;
- `Cordis.GlobalTraceRewrite`, locating exact adjacent windows inside intrinsic dependent traces,
  assigning fixed programs to actual activation occurrences, and splicing assignment-preserving
  activation/activation or corrected activation/orchestration swaps into retained trace context;
- `Cordis.DeepSeekRichMixedStream`, projecting a single strict SSE choice that interleaves text,
  reasoning, and one indexed tool call across frames into an exact rich trace, while rejecting
  same-frame mixed fields and retaining explicit wire/projection/intrinsic certificates;
- `Cordis.DeepSeekRichMultiStream`, projecting one strict SSE choice with any finite list of
  indexed function calls, first-seen contiguous local block indices, per-call metadata and raw
  argument accumulation, exact block closure, and typed negative witnesses;
- `Cordis.DeepSeekRequestMode`, indexing complete versus streaming request plans by a proof that
  the serialized `stream` flag matches the mode and restricting terminal execution to complete
  plans;
- `Cordis.DeepSeekCurlTransport`, exercising a process-backed request/response adapter with
  stdin body delivery, direct executable arguments, explicit status-trailer parsing, typed
  process failures, and a deterministic `sh` fixture;
- `Cordis.DeepSeekCurlStream`, composing that process boundary with complete-body strict SSE
  validation and typed process/status/stream errors; incremental reader semantics remain external;
- `Cordis.DeepSeekCurlOutcome`, composing the process/status boundary with the unified provider-
  failure/text/tool/mixed/multi terminal-outcome certificate while keeping semantic errors typed;
- `Cordis.DeepSeekOutcomeSession`, preserving a validated provider failure with an unchanged
  runner or finishing/appending a successful rich outcome through the typed local session
  runner; source-event evidence and failure-to-message policy remain caller obligations;
- `Cordis.DeepSeekOutcomeConversation`, carrying those terminal outcomes into the larger
  `ConversationRunner`, preserving its model/tool-count invariant and exposing completed
  provider calls as `FunctionCall` values for the existing dependent executor, with an
  execution variant that appends certified typed tool results;
- `Cordis.DeepSeekOutcomeTransportLoop`, carrying the same rich terminal language across a
  generic `Transport`: each type-indexed streaming request is validated as a complete body,
  dependent tools are executed, and the updated runner is fed into the next request. Stream
  provider failures and non-success `{error: ...}` API envelopes are retained as distinct typed
  stops; transport/status/envelope/semantic/execution errors, text completion, and fuel exhaustion
  remain separate;
- `Cordis.DeepSeekApiErrorEnvelope`, validating a non-success OpenAI-compatible `{error: ...}`
  response body with exact JSON parse/decode certificates; provider-error authenticity and retry
  policy remain caller/runtime obligations;
- `Cordis.DeepSeekCurlSession`, composing a terminal process-backed text response through the
  rich/session bridge and append-only runner while retaining wire and runner certificates;
- `Cordis.DeepSeekHarnessProcess`, retaining the typed Harness request source, exact request plan,
  successful build equation, complete-body process response, and indexed runner append endpoint;
- `Cordis.DeepSeekHarnessExtensions`, generalizing the pure request adapter to arbitrary indexed
  `Session.ExtensionSchema`s and proving that custom log-only events stay out of the model surface
  while custom surface events contribute their certified message; complete/streaming mode
  certificates, a schema-preserving assistant append, and an indexed terminal-response runner
  are included;
- `Cordis.DeepSeekHarnessProcessOutcome`, retaining a typed `stream: true` request plan through
  complete-body provider-failure or rich terminal classification, dependent tool execution, and
  the final `ConversationRunner` endpoint;
- `Cordis.DeepSeekStreamHarness`, composing complete-body terminal rich tool streams with the
  generic conversation runner, dependent tool execution, and certified typed-result append;
  streamed rounds use a request source/body certificate proving `stream: true`, and an executable
  fixture rejects the non-streaming body; both the one-call path and the typed two-call
  `executeConversationMultiStreamRound` fixture are exercised, and `runConversationMultiStream`
  composes those rounds under explicit fuel until a text-only terminal response or typed exhaustion;
- `Cordis.DeepSeekStreamHarnessCancellation`, adding the same typed pre-round cancellation
  decision to the streamed loop while keeping in-flight process interruption external;
- `Cordis.DeepSeekStreamHarnessPrefix`, connecting the line-oriented process-prefix state to
  the multi-call continuation and retaining exact completion, fuel, or line-cancellation
  evidence while byte framing and blocked-read interruption remain external;
- `Cordis.DeepSeekHarnessPersistence`, attaching a validated logical JSONL archive to a
  `ConversationRunner` with exact final-session equality and a request certificate that is
  preserved when the request is rebuilt from the archive session; filesystem/compression,
  torn-tail repair, concurrent writers, and archive authenticity remain external;
- `Cordis.DeepSeekHarnessPersistenceIO`, composing the UTF-8/JSONL `ReadCertificate` from
  `HarnessPersistenceIO` with that logical DeepSeek restore seam over memory and temporary-file
  backends; backend acknowledgement, fsync, crash recovery, and stable-media semantics remain
  external;
- `Cordis.DeepSeekHarnessEventArchive`, requiring both a lossless full-event archive and a
  stateful semantic validation certificate before attaching current-Harness events to a
  `ConversationRunner`; opaque known/extension events reject restoration, while the supported
  tool-message fixture rebuilds a typed request;
- `Cordis.DeepSeekHarnessEventIgnorableProjection`, recording positional keep/drop decisions for
  the explicit `ignorable: true` envelope marker, retaining supported wire/raw certificates and
  rejecting required opaque rows;
- `Cordis.DeepSeekHarnessEventIgnorableNormalization`, continuing that projection for the
  supported subset by renumbering retained rows contiguously, remapping supported
  `sourceEventSeqs`/`surfaceOp` references, and validating the normalized local session; duplicate
  physical sequences, missing references, malformed rewrites, required opaque rows, and semantic
  failures reject, while opaque payload semantics and deployed Harness equivalence remain open;
- `Cordis.DeepSeekHarnessEventIgnorableRunner`, attaching that normalized endpoint to a typed
  `ConversationRunner` and rebuilding a `ChatRequest` with exact session/step and request-build
  certificates; the normalized tool-message fixture exercises the user/assistant/tool path, while
  opaque semantics, provider authenticity, persistence, transport, and deployed equivalence remain
  external;
- `Cordis.DeepSeekHarnessEventIgnorableTransport`, carrying that dependent runner through the
  existing process-backed complete-response conversation trace while retaining final runner/model/
  stop evidence in a dependent certificate;
- `Cordis.DeepSeekHarnessEventText`, lifting that certificate-gated event attachment to exact
  UTF-8/JSONL text and `ByteArray` ingress while retaining source/decoded text and rejecting
  invalid encoding or opaque/extension events;
- `Cordis.DeepSeekHarnessEventPrefix`, exposing the pure append-only dependent cursor beneath
  that ingress: each accepted JSON object extends `SessionRefinement.State` and a snoc protocol
  trace, while fuel/cooperative entry stops retain the unread suffix without claiming framing,
  blocked-read interruption, durability, or deployed Harness equivalence;
- `Cordis.DeepSeekHarnessEventProcessPrefix`, feeding that cursor from a configured local process
  one complete stdout line at a time, retaining observed lines, exit status, endpoint, and typed
  completion/fuel/cancellation stops, plus a proof that consumed count equals cursor-entry count;
  malformed lines and nonzero exits stay typed failures, while byte framing, blocked-read
  interruption, executable/provider authenticity, durability, and deployed equivalence remain open;
- `Cordis.DeepSeekHarnessEventProcessTimeout`, adding a per-read `Std.Async.Sleep` race that kills
  and waits for a blocked configured child, retaining the exact accepted cursor prefix, observed
  lines, exit code, stderr, and timeout index; completion and timeout fixtures cover both branches,
  while arbitrary descendant cleanup, fairness, backpressure, authenticity, durability, and
  deployed asynchronous equivalence remain open;
- `Cordis.DeepSeekHarnessPayloadText`, composing the same text/byte restore with the raw
  `SessionPayloadArchive.PayloadLog` so block tags, usage, and tool-result metadata remain aligned
  with the runner without inventing provider-owned semantics;
- `Cordis.DeepSeekHarnessPayloadPersistence`, carrying that payload log through logical persisted
  JSONL, pure `ByteArray`, and executable memory/temporary-file restore while retaining one
  dependent index for header/storage rows, expanded events, the runner, and raw payloads;
- `Cordis.DeepSeekHarnessOpaqueMetadata`, attaching the sanitized runner projection from
  `SessionOpaqueMetadata.RetainedLog` while retaining exact tool-result `error`/`meta` values in
  source order; the request path excludes those uninterpreted provider/tool fields;
- `Cordis.DeepSeekHarnessMetadataArchive`, composing that retained metadata log with the full
  `SessionEventArchive.ArchivedLog`, so the raw envelope ledger and the known opaque event remain
  available beside the sanitized runner;
- `Cordis.DeepSeekToolSchema`, adding a bounded proof-carrying function-tool schema admission
  layer with exact parameter-JSON retention, primitive property types, required-name checks,
  duplicate-name rejection, parsed argument-object certificates, and certified request
  construction;
- `Cordis.DeepSeekToolAdmission`, tying a provider `FunctionCall` to one certified tool name and
  carrying its parsed argument certificate before generic capability execution;
- `Cordis.DeepSeekGenericBridge`, composing that provider certificate with an explicit named
  `SchemaToolBinding` and generic dependent `Config.validate`, returning both certificates and an
  existentially indexed local call without claiming schema semantic equivalence or execution;
- `Cordis.DeepSeekSchemaHarness`, carrying a successful schema-aware execution into the existing
  `DeepSeekHarness.ExecutedTool` and exact session append surface without re-execution;
- `Cordis.DeepSeekSchemaRound`, composing an accepted singleton function-call response with
  schema-certified dispatch and the existing conversation runner while rejecting zero/multiple
  calls structurally;
- `Cordis.DeepSeekSchemaMultiRound`, lifting that composition to a nonempty homogeneous list under
  one explicit provider/generic binding, with sequential dependent model transitions, exact
  execution-list length, typed later-call failures, and certified multi-result runner append;
- `Cordis.DeepSeekSchemaRegistry`, lifting the same boundary to a finite heterogeneous registry
  whose dependent name lookup selects entry-specific schema/generic bindings, with mixed-operation
  execution, exact runner accounting, and typed unknown-name rejection;
- `Cordis.DeepSeekScopedRegistry`, adding nearest-first lexical scopes, terminal shadowing
  restrictions, and typed automatic/review approval tickets before dependent provider execution;
- `Cordis.DeepSeekSchemaConversation`, attaching registry-derived tool declarations to a typed
  complete-body transport request and validated response while retaining the exact plan, response,
  heterogeneous execution batch, and runner endpoint for one round;
- `Cordis.DeepSeekSchemaConversationLoop`, carrying those rounds through a caller-fueled dependent
  loop with an explicit validated no-tool terminal witness, accumulated round history, and a
  distinct fuel-exhaustion stop;
- `Cordis.DeepSeekSchemaTransportRetryCancellation`, composing that heterogeneous registry with
  single-decoder bounded retry and caller-controlled pre-round cancellation, retaining exact
  dependent tool-round endpoints and distinct completion/cancellation/exhaustion stops;
- `Cordis.DeepSeekSchemaProcessRetryCancellation`, instantiating that dependent boundary with the
  existing `IO.Process`/`sh` adapter and a 503→heterogeneous→terminal fixture while retaining the
  same retry history and exact endpoints;
- `Cordis.DeepSeekSchemaStreamConversation`, carrying the same registry through the typed
  `stream: true` SSE/rich-stream/session boundary, validating a complete streamed body before
  heterogeneous dispatch, and distinguishing a text terminal from caller-fuel exhaustion;
- `Cordis.DeepSeekHarnessProcessSchema`, retaining the registry-certified heterogeneous source
  and exact streaming plan through a complete-body SSE response, schema-dispatched step, and
  dependent runner endpoint, with request/process/registry-execution errors separated;
- `Cordis.DeepSeekHarnessProcessSchemaPrefix`, retaining that exact registry-certified streaming
  plan through a line-oriented prefix result, including typed fuel/cancellation stops and the
  completed `[DONE]` branch that carries the dependent schema step and runner endpoint;
- `Cordis.DeepSeekHarnessProcessSchemaPrefixConversation`, lifting that retained plan through the
  caller-fueled prefix loop so each completed tool round, attempted-round exhaustion, and
  cancellation keeps its own process provenance;
- `Cordis.DeepSeekSchemaStreamPrefixConversation`, preserving the accepted line prefix and typed
  line-budget/cancellation stop while deferring registry dispatch until the completed `[DONE]`
  rich/session certificate;
- `Cordis.DeepSeekStreamFailure`, preserving strict provider terminal-failure frames for
  `content_filter` and `insufficient_system_resource` without coercing them into a normal rich
  trace or session message;
- `Cordis.DeepSeekTerminalOutcome`, dispatching a complete strict body across the provider-failure
  language and the successful text, one-tool, mixed, and finite multi-call rich languages while
  retaining the selected dependent certificate;
- `Cordis.DeepSeekSchemaStreamErrors`, preserving entry-specific provider-failure certificates,
  converting them to opt-in `isError` results, and proving a later streamed terminal continuation;
- `Cordis.DeepSeekHarnessErrors`, adding an explicit fail-closed/default-versus-opt-in policy seam
  for provider failures: `.include` retains typed failure evidence and appends model-visible
  `isError` tool results without changing the model state;
- `Cordis.DeepSeekStreamHarnessErrors`, carrying that same typed provider-failure policy through
  a complete-body streamed tool round and fuel-bounded continuation while preserving the model
  and appending an opt-in `isError` tool result;
- `Cordis.DeepSeekHarnessRetry`, adding an explicit bounded complete-body retry policy whose
  history retains prior transport/transient-HTTP `ClientError`s while every attempt reuses the
  same request plan; provider backoff, idempotency, cancellation, and deployed retry semantics
  remain outside;
- `Cordis.DeepSeekStreamHarnessRetry`, adding the same bounded retry boundary to complete-body
  streamed rounds. Process and transient-HTTP failures retain ordered history and may retry under
  policy, while stream framing, semantic response, and tool failures remain terminal;
  backoff, idempotency, cancellation, persistence, and deployed retry semantics remain outside;
- `Cordis.DeepSeekStreamHarnessRetryConversation`, composing those process-backed retry rounds
  into an indexed fuel-bounded trace whose heads retain complete SSE bodies, retry histories,
  dependent assistant/tool endpoints, and exact runner/model tails; its fixtures cover streamed
  tool-to-text completion and an exhausted transient-HTTP policy, while backoff, idempotency,
  blocked-read cancellation, persistence, reconnects, and deployed retry equivalence remain
  outside;
- `Cordis.DeepSeekStreamHarnessRetryCancellation`, composing that indexed retry trace with the
  existing pre-round cancellation policy. Cancellation retains the accepted retry-aware prefix,
  unchanged runner/model endpoint, round/reason certificate, and retry history inside each head;
  it does not interrupt in-flight process/HTTP/stream/tool IO or claim deployed cancellation
  equivalence;
- `Cordis.DeepSeekHarnessCancellation`, adding a pre-round cancellation decision that retains the
  exact completed prefix, runner/model endpoint, and cancellation certificate; it does not claim
  mid-request IO interruption, cleanup, or deployed Harness cancellation semantics;
- `Cordis.DeepSeekHarnessTransportRetryCancellation`, composing that pre-round decision with the
  indexed injected-transport retry trace: cancellation retains the exact retry-aware prefix and
  endpoint, while the non-cancelled fixture retains the 503 retry history and terminal endpoint;
  blocked-read interruption, backoff/idempotency, persistence, and deployed equivalence remain
  external;
- `Cordis.DeepSeekStreamIncremental`, adding pure proof-carrying SSE prefix state: complete lines
  retain the accumulated body/frame equation, `finish` requires `[DONE]`, and a finite line policy
  can stop before the next line; live IO, backpressure, process cancellation, and reconnect remain
  external;
- `Cordis.DeepSeekStreamByteFraming`, adding pure arbitrary-byte ingress below that prefix state:
  LF-delimited chunks retain an exact canonical reconstruction, complete lines decode as UTF-8
  before typed prefix parsing, and invalid UTF-8/incomplete final lines are typed errors; process
  reads, blocked-read interruption, backpressure, cancellation, reconnect, and deployed semantics
  remain external;
- `Cordis.DeepSeekCurlByteFraming`, connecting that pure byte layer to bounded piped-process stdout:
  observed chunks, raw UTF-8 output, private status parsing, and the exact body-chunk framing
  certificate are retained, with typed process/status/read-limit failures; network, credentials,
  executable trust, blocked-read interruption, backpressure, cancellation, reconnect, and deployed
  semantics remain external;
- `Cordis.DeepSeekStreamHarnessByte`, carrying that dependent byte/framing/status witness through a
  complete streamed Harness round and fuel-bounded loop into the existing rich/tool/session runner;
  tool execution, certified result append, and text-terminal completion are exercised, while
  byte-level cancellation, blocked-read interruption, backpressure, reconnect, and deployed
  semantics remain external;
- `Cordis.DeepSeekCurlBytePrefix`, adding bounded process-byte prefix ingress: incomplete raw
  fragments remain explicit, complete body lines advance the typed prefix before the next read,
  and the private status trailer is kept outside the SSE body. The stop policy is read-boundary
  evidence only; blocked-read interruption, backpressure, cancellation, reconnect, and deployed
  semantics remain external;
- `Cordis.DeepSeekStreamHarnessBytePrefix`, carrying a completed process-byte prefix
  witness through rich/tool/session continuation and preserving prefix fuel stops as explicit
  Harness stops. The deterministic fixtures retain the framing/status evidence beside the runner;
  blocked-read interruption, backpressure, reconnect, and deployed semantics remain external;
- `Cordis.DeepSeekCurlIncremental`, delivering complete response lines through a process callback
  under an explicit read budget before strict validation of the reconstructed SSE body; byte-level
  and cancellation semantics remain external;
- `Cordis.DeepSeekCurlPrefix`, connecting the process line reader to the proof-carrying prefix
  state: each accepted line is parsed before the next read, synchronous fuel/cancellation stops
  clean up the child, and terminal success retains raw output plus normalized frame certificates;
  blocked-read cancellation, backpressure, reconnect, and deployment semantics remain external;
- `Cordis.DeepSeekCurlPrefixSession`, projecting only completed process prefixes through the accepted
  text/tool/mixed/multi validators and append-only runner; fuel/cancellation remain typed stops,
  while blocked-read interruption, external execution, and deployed equivalence remain external;
- `Cordis.DeepSeekAsyncHarness`, racing two complete-body text-prefix process jobs in cooperative
  `ContextAsync` children and retaining the first typed result plus terminal-phase bridge; the
  fixture is executable, while blocked-read interruption, fairness, cleanup, and deployed async
  semantics remain external;
- `Cordis.DeepSeekAsyncStreamHarness`, racing two complete-body streamed Harness continuations in
  cooperative `ContextAsync` children and retaining the winner's dependent tool executions, round
  witnesses, final model, and runner; synchronous reads, fairness, cleanup, and deployed async
  semantics remain external;
- `Cordis.DeepSeekAsyncStreamCancellation`, carrying typed pre-round cancellation through the same
  race and retaining the unchanged endpoint and empty completed prefix on the cancelled branch;
- `Cordis.DeepSeekAsyncStreamRetryCancellation`, carrying that cooperative race over retry-aware
  streamed jobs and retaining the dependent retry trace, endpoint, and typed pre-round stop, with
  a delayed-child success-first fixture covering the complementary terminal branch;
- `Cordis.DeepSeekSessionRunner`, composing accepted text, one-tool, mixed, and multi-call
  terminal traces into the pure append-only local session surface with exact sequence and
  tool-count invariants;
- `Cordis.GlobalDeletion`, constructing intrinsic relation-indexed keep/drop replays and exact
  assignment-carrying safe orchestration suffixes after finite families of already-vestigial
  entries, while kernel-separating parent, redraw, and allocator obstructions to full Lemma 72;
- `Cordis.DurableSettlement`, defining an intrinsically indexed append-only frame log with a
  collision-free list transcript, exact newest-first recovery, supplied crash-prefix certificates,
  and typed resume after a retained prefix;
- `Cordis.DurableCodec`, defining a JSON-AST raw-frame codec and strict dependent prefix scanner
  that rejects malformed, torn, unknown, and non-contiguous frames before constructing that typed
  log;
- `Cordis.DurableBytes`, defining an explicit unary-length binary format over `List UInt8`, a
  numeric `RawFrame` payload codec, and a counted byte-prefix bridge that exposes discarded bytes
  before delegating to the typed scanner;
- `Cordis.DurableIO`, defining typed append plans and executable memory/filesystem adapters whose
  read path returns a proof-carrying scanned prefix plus an explicit discarded byte suffix;
- `Cordis.GlobalPaperRelation`, erasing only the reference allocator clock/birth ranks from current
  rule observation, proving full-domain bidirectional well-formed orchestration replay, and
  constructing directed relation-aware vestigial suffix replay with lifecycle countermodels;
- `Cordis.GlobalPaperTraceNormalization`, packaging a finite certificate-driven chain of
  birth-erased adjacent trace rewrites with transported assignments and final rule/actor
  permutation facts, while leaving automatic normal-form search and confluence external;
- `Cordis.GlobalPaperTraceNormalizer`, adding an authority-driven terminating chain constructor
  from explicit normal-form, rewrite, and decreasing-measure certificates, while leaving strategy,
  canonical form, global dynamic termination, and confluence external;
- `Cordis.GlobalProgress`, distinguishing configured-oracle rejection from the permissive raw
  relation, kernel-refuting progress under exhausted names, and proving conditional state-local
  no-deadlock from finite precedence and exact execution/recovery authorities;
- `Cordis.GlobalProgressAssignment`, adding a supplied lifecycle-step provenance authority and
  recursively reconstructing a dependent `TraceProgramAssignment` for every finite progress run,
  while preserving endpoint and quiescence certificates;
- `Cordis.GlobalSupport`, kernel-refuting support well-foundedness from separate acyclicity,
  defining the unique support predicate under an explicit combined order, and proving corrected
  support-equals-active under state-local totality/failure/parent closure;
- `Cordis.GlobalRelations`, defining incomparable finite rule/effect observation setoids and an
  explicit respectful-undo bridge into the temporal algebra without claiming rule bisimulation;
- `Cordis.GlobalRuleInvariance`, proving well-formed bidirectional orchestration matching across
  rule-related states while preserving unequal observationally related private values;
- `Cordis.GlobalRuleObservations`, transporting provider identity, targets, reliance, phase
  patterns, quiescence, and structural lifecycle guards without external execution assumptions;
- `Cordis.GlobalLifecycleBisimulation`, deriving all-eight lifecycle and unified ten-rule matching
  from noncircular landing, error, inertia, and recovery-admission compatibility records;
- `Cordis.GlobalNameAction`, defining lawful executable nominal actions through dependent global
  state and proving inverse, strengthened well-formedness, and orchestration equivariance;
- `Cordis.GlobalNameLifecycle`, deriving registration/oracle/execution/landing/recovery actions and
  all lifecycle/unified name equivariance from exact dynamics, inertia, and catalog-entry laws;
- `Cordis.GlobalVestigial`, proving exact effect-equivalence to removal and corrected
  bidirectional orchestration squares, with well-formed witnesses for both paper insert exceptions
  and the two omitted parent-pointer exceptions;
- `Cordis.GlobalSpatial`, proving finite dependency provision, explicitly witnessed nested episode
  order, provider-resolution/no-unload consequences, conditional table constancy, and local
  reloading classification;
- `Cordis.RuntimeRefinement`, decoding the supported current-Harness stream-chunk JSON-AST
  shapes into `RichStream.ValidatedTrace` while explicitly rejecting non-equivalent fields;
- `Cordis.RuntimeFailureRefinement`, decoding the normalized current-Harness `error`/`aborted`
  finish union into an exact typed `LlmFailure` terminal certificate without claiming a normal
  rich-trace projection for open-block failures;
- `Cordis.RuntimeOutcomeRefinement`, dispatching the supported successful and normalized failure
  languages into one dependent outcome while retaining both structured errors when neither
  language accepts;
- `Cordis.RuntimeOutcomeSession`, composing that outcome with the pure local session runner:
  success appends a finished assistant view, while failure leaves the runner unchanged;
- `Cordis.SessionRefinement`, statefully translating a supported source-shaped Harness session
  prefix into joint `Session.ValidatedAppend` and intrinsic `Protocol.ValidatedEvent` witnesses;
- `Cordis.SessionOpaqueMetadata`, quarantining only provider/tool-owned tool-result `error` and
  `meta` JSON while retaining exact values and the sanitized Session/Protocol projection;
- `Cordis.SessionArchive`, retaining every syntactically valid current-Harness event envelope
  losslessly, classifying supported records versus required/ignorable opaque extensions, and
  attaching the existing typed decoder certificate where available;
- `Cordis.SessionEventArchive`, recognizing all thirteen pinned core event tags, enforcing
  object-shaped data and log-only metadata rules, and retaining unsupported known payloads and
  unknown extensions as exact raw records;
- `Cordis.SessionPayloadArchive`, classifying all current content-block tags (including unknown
  extensions), retaining exact message/chunk/content arrays and raw usage/error/meta fields, and
  preserving malformed known payloads without dropping their event ASTs;
- `Cordis.HarnessPersistenceRefinement`, validating the pinned logical JSONL session header and
  storage rows, expanding the three lossless packed chunk-row forms, and composing that result
  with the stateful session validator;
- `Cordis.HarnessPersistenceArchive`, retaining the typed session header, packed row tags, and
  ordinary envelope rows losslessly across JSONL text/UTF-8 boundaries without semantic expansion;
- `Cordis.HarnessPersistenceIO`, lifting that logical certificate to executable UTF-8 byte/text
  reads, canonical replacement, and validated append-only rows over memory/filesystem backends;
  host acknowledgement, fsync, torn-tail repair, locking, and stable-media durability remain
  external;
- `Cordis.HarnessPersistenceBytes`, composing a pure `ByteArray` UTF-8/JSONL witness with the
  logical persistence/session certificate while retaining source bytes, decoded text, parsed rows,
  packed expansion, and the final Session/Protocol projection;
- `Cordis.GenericSessionHarness`, factoring the rich Session/request/projection wrapper over an
  arbitrary `GenericHarness.Config`; the counter and dependent-choice configurations are both
  executable fixtures;
- `Cordis.ParallelSchedule`, composing arbitrary finite pure windows and exclusive barriers while
  preserving endpoint/recovery equality, model-order reports, and global task-ID uniqueness;
- `Cordis.AsyncHarness`, proving indexed pending/running/terminal fiber transitions, explicit
  completion-order traces, drained finite-schedule canonical endpoints, and race/cancellation
  witnesses without claiming live asynchronous execution;
- `Cordis.DeepSeekAsyncHarness`, exercising a real two-process cooperative race over the typed
  DeepSeek prefix/session adapter and retaining a legal winner/error plus pure phase facts; this is
  an observation bridge, not blocked-read cancellation or deployed Harness refinement;
- `Cordis.DeepSeekAsyncStreamHarness`, exercising the same real two-process race over streamed tool
  continuations, with a two-round tool-then-text winner and typed model/runner evidence; this is not
  blocked-read cancellation or deployed Harness refinement;
- `Cordis.DeepSeekAsyncStreamCancellation`, exercising a real cancellation-first streamed child
  alongside a process-backed sibling and checking the typed stop/endpoint evidence;
- `Cordis.DeepSeekAsyncStreamRetryCancellation`, exercising the same cancellation-first race over
  retry-aware streamed children and checking the indexed trace, endpoint, and reason evidence,
  alongside a delayed-child success-first two-round fixture;
- `Cordis.StreamSession`, making the provider-string-ID to unique numeric-session-`CallId`
  assignment explicit before a validated rich assistant view enters the canonical surface;
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

The session certificate bridge now checks all of the following in Lean. The first eight are the
intrinsic `Session` declarations; the final two are exported by
`Cordis.SessionTheoremBridge` over the proof-carrying validation structures:

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
   intrinsic transition and reaches the same physical, surface, header, sequence, and `ValidLog`
   endpoint.
10. `ValidatedLog.replays`: every successfully validated raw finite log retains its intrinsic
    suffix certificate and reaches the same physical events, derived messages, and `ValidLog`
    endpoint.

These are proof-producing propositions, not weaker executable assertions or mere endpoint
booleans.

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
second event list. `GenericSessionHarness.RunnerState` packages the same relationship for every
catalog configuration; `Examples.DependentChoiceSession` proves the bridge is not counter-
specialized.

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

## Paper context and executable refinement

The bounded transposition slice is specified in
[`GLOBAL_TRANSPOSITION_SPEC.md`](GLOBAL_TRANSPOSITION_SPEC.md) and implemented by
`Cordis.GlobalTransposition`. It deliberately separates the proved raw Definition 60 execution
diamond from the stronger foreign-phase, exact-undo-code, guard, and edited-endpoint laws required
by paper Lemma 71.

The lower foreign-phase frame slice is specified in
[`GLOBAL_FOREIGN_PHASE_SPEC.md`](GLOBAL_FOREIGN_PHASE_SPEC.md) and implemented by
`Cordis.GlobalForeignPhase`. It kernel-separates iterator independence from foreign control
blindness and derives the required compatibility only from explicit read, ordinary-successor, and
registration-oracle frame laws.

The landing activation slice is specified in
[`GLOBAL_LANDING_TRANSPOSITION_SPEC.md`](GLOBAL_LANDING_TRANSPOSITION_SPEC.md) and implemented by
`Cordis.GlobalLandingTransposition`. It covers only the four common-source L-Iter/L-Finish
combinations under explicit fixed-program landing provenance, well-formedness, semantic plus exact
cross-forward independence, and foreign-phase compatibility.

The complete bounded activation slice is specified in
[`GLOBAL_ACTIVATION_TRANSPOSITION_SPEC.md`](GLOBAL_ACTIVATION_TRANSPOSITION_SPEC.md) and implemented
by `Cordis.GlobalActivationTransposition`. It adds program-root-aligned Begin, exact positive-target
transport, fixed-program endpoint/rule determinism, and all nine common-source
Begin/Iter/Finish pairs. Its actual-second-step wrapper is a partial, fixed-oracle,
exact-representative Lemma 71(1) analogue; activation/orchestration exchange, arbitrary trace
rewriting, episode assignment, and the literal paper theorem remain separate.

The corrected activation/orchestration slice is specified in
[`GLOBAL_ACTIVATION_ORCHESTRATION_TRANSPOSITION_SPEC.md`](GLOBAL_ACTIVATION_ORCHESTRATION_TRANSPOSITION_SPEC.md)
and implemented by `Cordis.GlobalActivationOrchestrationTransposition`. It exposes two failures of
the literal Lemma 71(2) condition—new-parent enablement and birth-rank order—then proves the
strongest exact representative theorem under orchestration-sensitive registration safety and one
occurrence-specific execution frame. Registering activation/O-Insert remains excluded.

The exact trace-rewrite slice is specified in
[`GLOBAL_TRACE_REWRITE_SPEC.md`](GLOBAL_TRACE_REWRITE_SPEC.md) and implemented by
`Cordis.GlobalTraceRewrite`. Its exact pair and located-window indices make an incompatible suffix
unrepresentable. Actual stored activation occurrences carry their fixed program, root, reach, and
oracle evidence; both semantic adapters return fresh assignments for the moved steps. The module
proves exact rule/actor adjacent permutations and locates the original selected records; the
rewritten complete trace separately retains alignment, length, and final well-formedness. It does
not weaken endpoint equality to a
birth-erased relation, because a merely related local endpoint cannot typecheck against the exact
retained suffix without a separate suffix-simulation theorem.

The bounded deletion slice is specified in
[`GLOBAL_DELETION_SPEC.md`](GLOBAL_DELETION_SPEC.md) and implemented by
`Cordis.GlobalDeletion`. `DeletionReplay` constructs one shadow trace positionally from local keep
or drop evidence and derives its assignment ledger, final relation, alignment, sublist facts, and
length bounds. A separate exact theorem iterates the corrected vestigial forward square over a
finite family and an arbitrary safe foreign orchestration trace, retaining a full positional edit
template and matched assignment. Full-trace countermodels show parent enablement, `nextBirth`,
surviving birth ranks, and bare-name redraw each require stronger deletion semantics. The module
does not delete a general closed lifecycle episode or claim Lemma 72/Theorem 73.

The paper-visible relation slice is specified in
[`GLOBAL_PAPER_RELATION_SPEC.md`](GLOBAL_PAPER_RELATION_SPEC.md) and implemented by
`Cordis.GlobalPaperRelation`. It defines full-domain and outside-deleted rule observations that
retain component, parent, retirement, and the complete dependent phase while omitting only the
reference allocator clock and per-fiber birth relative to current `RuleRelated`; the deletion
relation conjoins outside control with exact effect observation. Actual peer orchestration steps,
successor relations, and assignment transports are proved in both directions for the full-domain
relation. Finite vestigial removal and safe foreign orchestration traces use the combined deletion
relation directionally from a well-formed source carrying a `VestigialNames` certificate. A real
clock-sensitive L-DivertAbort with no exact-rule peer refutes
unconditional lifecycle simulation.

The corrected progress slice is specified in
[`GLOBAL_PROGRESS_SPEC.md`](GLOBAL_PROGRESS_SPEC.md) and implemented by `Cordis.GlobalProgress`.
It exposes configured-oracle rejection and raw freshness exhaustion, defines provider precedence
and a finite increasing rank, derives fixed-program landing-or-raise readiness from explicit oracle
totality, and proves conditional state-local lifecycle no-deadlock. It does not prove the
quantitative or maximal-termination clauses of Theorem 66.

`Cordis.GlobalProgressRun` adds the finite dependent execution bridge: callers supply a
`ProgressAuthority` and strict `StepPotential`, and `runFuel` retains exact lifecycle traces,
well-formed endpoints, and a quiescent/full-fuel stop certificate. Funding a run with its initial
potential proves quiescent completion. This remains conditional finite execution; the authorities,
target-turn accounting, freshness, fairness, trace-wide assignment, maximal termination, support,
and confluence are not derived.

The corrected support slice is specified in
[`GLOBAL_SUPPORT_SPEC.md`](GLOBAL_SUPPORT_SPEC.md) and implemented by `Cordis.GlobalSupport`. A
reachable legal two-insert trace gives well-founded provider precedence and an acyclic parent
relation whose union cycles, so the module requires `SupportOrder` directly. It defines support by
combined-edge well-founded recursion, proves uniqueness, and derives support-equals-active at
quiescence under state-local provision totality, failure exclusion, and active-parent closure.

The bounded algebra/context/global layer now has sixty-two explicit pieces:

1. `Cordis.Coeffect` implements Definitions 22–26 over finite dependent maps.
2. `Cordis.UnifiedContext` distinguishes witnessed in-place effects from indexed derived
   children, implements typed isolation and interception, and unfolds Definition 32 to any
   selected finite depth.
3. `Cordis.ContextualEquivalence` lifts each key's Definition 24 equivalence through optional
   bindings, proves that this is exactly same-domain plus pointwise-related values, and supplies
   the finite context `Setoid` used by observational effects.
4. `Cordis.OperationalEquivalence` defines finite tests from typed forward maps and concrete
   seeded inverses, retains heterogeneous outcomes, and proves the largest relation respected by
   every fixed generator. A finite counterexample proves that same-word tests do not imply the
   stronger comparison between two differently yielded inverses; `PairedInverseCoherent` names
   the additional premise needed to rebuild a full `CoeffectAt` over that relation.
5. `Cordis.QuotientEffect` defines quotient-respecting and pointwise-related maps, proves
   Definition 37 admissibility is closed under finite sequential composition, and exposes the
   accumulator-respect/recovery core of Lemma 38. `Cordis.CoeffectQuotient` connects the local
   Definition 24 laws to related lifted contexts and outcomes.
6. `Cordis.Transformation` represents Definition 17 as the least identity/composition closure
   of an effect's forward map and every state-indexed yielded inverse. It proves both parts of
   Lemma 18, promotes generator commutation/inverse stability through the closures, and shows
   full Definition 19 implies the existing exact batch/schedule commutation certificate.
7. `Cordis.OperationIndependence` adds heterogeneous outcome stability for full total
   Definition 39, proves arbitrary finite operation words at distinct dependent keys commute
   with complete forward-data stability, and implements Definition 41's outcome-selected
   computation syntax with exact LIFO recovery. Its initial `MediatedClosure` boundary is later
   shown too strong for partial domains and replaced by the finite whole-run theorem below.
8. `Cordis.Removal` keeps each application state and yielded inverse in an indexed execution,
   builds a paired original/omitted suffix trace, proves every later effect yields the same
   inverse after removal, and promotes pairwise Definition 19 independence to recovery under
   every inverse permutation.
9. `Cordis.GlobalRegistry` avoids recursive functions in state by storing component, iterator,
   and undo codes. It derives active providers/values and targets from a finite registry, adds a
   birth-order strengthening to the paper's parent-present invariant, proves parent acyclicity,
   and proves insert/retire/remove plus orchestration traces preserve the strengthened registry
   well-formedness.
10. `Cordis.MediatedIndependence` reifies each realized Definition 41 branch with the exact typed
    outcome selecting its continuation. It states the initial `ObservationalMediatedClosure`,
    proves representative coherence promotes that certificate to exact closure, and gives a
    finite quotient counterexample showing the coherence premise is genuinely extra. The next
    module separately refutes this initial API's individual-domain requirement for partial runs.
11. `Cordis.MediatedTheorem` proves primitive stage interchange without erasing typed outcomes,
    bubbles a root through arbitrary foreign continuations, and swaps complete finite computation
    trees. The final exact and observational results compare composite partial domains and retain
    conditional yielded-inverse stability; they are whole-run analogues, not full Definition 19.
12. `Cordis.GlobalDynamics` interprets codes only after `GlobalState` exists. Ordinary steps carry
    exact recovery, write/read/respect/WF obligations; registration consumes explicit admission
    and yields child retirement as observational recovery. A total fueled runner retains exact
    continuation code on exhaustion and carries an intrinsic trace plus newest-first recovery and
    global well-formedness preservation.
13. `Cordis.GlobalLifecycle` gives exact endpoints to L-Begin, L-Iter, L-Finish, both L-Divert
    alternatives, L-Raise, L-Leave, and L-Unload. Successful landing constructors retain their
    `executeOne` equation, and every rule preserves strengthened well-formedness. General unload
    recovery remains the explicit `RecoveryAdmission`; the concrete heterogeneous path discharges
    it for two ambient-only inverses.
14. `Cordis.GlobalCalculus` retains the exact source endpoints while projecting both source
    relations to the paper's ten rule names and acted-on names. It separates Equation 51 state
    maps from edit footprints, proves actual installed status changes only at L-Begin/L-Unload,
    and packages a heterogeneous empty-registry-origin trace back to an empty registry.
15. `Cordis.GlobalTraceFacts` proves exact foreign preservation away from unload and makes unload
    table/control/static preservation conditional on `RecoveryConfinement`. Aligned trace records
    derive name-specific episode boundaries and committed/static continuity. A finite kernel
    countermodel shows bare `RecoveryAdmission` can mutate a pre-existing foreign table while
    preserving well-formed endpoints.
16. `Cordis.GlobalTemporal` separates exact source step evidence from off-source state maps.
    Iterator maps remain partial unless totalized explicitly; per-step recovery commutation folds
    over a foreign replay, then owner inverse and reorder certificates yield finite relational
    recovery and an exact unload package. Countermodels separate this algebra from canonical paper
    `≈`, off-source totality, and structural RecoveryConfinement alone.
17. `Cordis.PartialTransformation` treats computation forward maps as Kleisli partial maps and
    actual yielded inverses as total Kleisli generators. Pairwise operation overlap promotes all
    forward/forward, forward/inverse, and inverse/inverse laws through the complete closures and
    preserves the other computation's domain and inverse under every successful foreign map. The
    whole-run theorem follows, while a kernel countermodel refutes its converse.
18. `Cordis.GlobalRelations` supplies key-indexed value setoids, observes the active context and
    exact registry domain/control for rule equivalence, and observes exact ambient state plus
    normalized tables for effect equivalence. Both candidates are setoids; a named undo-respect
    law instantiates `GlobalTemporal.EffectEquiv`. Executable examples prove the two candidates are
    incomparable and that an arbitrary dynamics relation may be too weak. Full raw rule
    bisimulation, lifecycle name equivariance, and full vestigial simulation remain missing.
19. `Cordis.ObservationalPartialTransformation` relates partial maps on all related input
    representatives, requiring identical `Option` definedness and related successful outputs. It
    derives forward and yielded-inverse generator respect structurally from existing `CoeffectAt`
    domain/successor/inverse/outcome laws, including exact heterogeneous outcomes and branch
    choices, then descends full exact partial closure independence. A generic finite model proves
    exact commutation alone does not imply observational commutation without this respect law.
20. `Cordis.GlobalSpatial` proves that a well-formed begin target provides every dependency and
    that installed committed provider resolution persists through a sufficiently confined,
    consumer-boundary-free trace, preventing provider unload. `NestedEpisodes` supplies the exact
    shared-master decomposition needed for strict boundary inequalities. Table constancy composes
    from an explicit per-record premise, with a foreign-actor sufficient-confinement corollary.
    Reloading steps are locally classified as target-stable, diverting, or raising; maximal
    episodes, same-owner table confinement, eventual close, and recovery are not inferred.
21. `Cordis.GlobalVestigial` packages the exact retired/inactive-success/empty-table/childless
    witness and proves it `EffectRelated` to entry removal. Safe foreign orchestration steps form
    exact forward and backward removal squares retaining kind, actor, endpoint deletion, and
    vestigiality. The forward theorem excludes adopting the vestigial entry as parent. The backward
    theorem excludes drawing its name, claiming its provision, and removing its parent. A
    well-formed kernel model proves all four cases necessary and exposes two omissions in the
    pinned raw Lemma 57. Full lifecycle and iterator invisibility remain unproved.
22. `Cordis.GlobalRuleInvariance` transports exact fiber controls but never private table equality.
    Under well-formedness, insert/retire/remove preserve each side's active context; every source
    step therefore has a same-kind/name peer with exact well-formed endpoint and a rule-related
    successor. A heterogeneous example uses unequal parity-related naturals and length-related
    strings. A separate well-formed ambient-sensitive inertia model proves `RuleRelated` alone
    cannot transport L-DivertAbort, so full Lemma 55 still needs explicit lifecycle laws.
23. `Cordis.GlobalRuleObservations` proves same-name active-provider identity, dependent
    target-view transport, committed resolution, reliance/non-reliance, exact phase patterns,
    quiescence, and five structural guard-availability equivalences from well-formed
    `RuleRelated` sources alone. Active matched tables are pointwise related. Reloading tables are
    private, so a future Finish landing must explicitly relate the newly active tables. Examples
    separate rule observation from effect observation and ambient equality in both directions.
24. `Cordis.GlobalLifecycleBisimulation` names four external contracts without mentioning rules:
    peer landing with exact undo/next and a completion-table relation, exact iterator-error
    transport, inertia respect, and peer recovery admission with related endpoint. These produce
    exact bidirectional matches for all eight lifecycle constructors and combine with orchestration
    into a well-formed ten-rule certificate. A parity countermodel proves Finish cannot recover the
    newly active table relation from reloading source observation. The contracts remain supplied.
25. `Cordis.GlobalNameAction` gives executable bijections for names and every payload carrier,
    then derives actions on dependent tables, committed providers, undo lists, phases, fibers,
    finite registries, and states. Identity/composition/inverse and exact lookup/state recovery are
    proved layer by layer. Strengthened well-formedness is invariant, and all orchestration rules
    commute bidirectionally with renaming. A Boolean swap exercises parents/views/undos/values;
    a constant noninjective action proves the old placeholder insufficient. The next row adds the
    conditional lifecycle laws.
26. `Cordis.GlobalNameLifecycle` acts ordinary and registration results, conjugates child-dependent
    continuations and oracles, maps both `Except` branches, and derives acted admissions,
    proof-carrying iterator steps, Landing, recovery, targets, and reliance. Exact dynamics-output,
    external-undo, dynamics-equivalence, inertia, and fixed-entry laws yield forward/backward
    equivariance for all lifecycle and unified rules on well-formed states. A nonidentity L-Raise
    and entry/error/run counterexamples exercise the boundary; primitive laws remain external.
27. `Cordis.GlobalIteratorIndependence` fixes the owner, root code, registration oracle, and
    dynamics of one iterator program; closes successful continuation reach under partial forwards
    and actually yielded inverse maps; and promotes generator commutation plus complete yield
    stability to exact program independence. Given separate `ProgramRespects` witnesses for both
    programs' reachable forwards, that result descends to effect-relational independence; only
    yielded inverse respect follows from `EffectEquiv.applyUndo_respects`. Families are indexed by
    occurrences, so duplicate values require self-independence. `YieldedAccumulator`,
    `StepMapMember`, and `ObservationalPerStepGenerated` retain the provenance, acted owner,
    closure membership, foreign-name, and pre-existing `TotalStepMap` evidence needed for
    `perStepCommutes_of_generated`. This is an oracle-specific finite partial/Kleisli Definition 60
    analogue, not the displayed rule relation and not Theorem 61 or Corollary 62.
28. `Cordis.GlobalTransposition` constructs the two off-axis successful iterator executions and
    their exact common raw endpoint from all three `Independent` fields. Two `TotalProgramStep`s
    retain supplied totality plus acted-owner closure provenance and commute exactly under
    `Independent`; `ObservationalIndependent` gives the effect-relational square while retaining
    separately supplied `ProgramRespects`. `LifecycleYieldAgrees` separately keeps exact stored
    undo-code equality, distinct phase edits commute, and `ForeignPhaseCompatibility` names a
    noncircular foreign-edit law for which this module constructs no inhabitant. A finite
    interpreter proves semantic inverse equality does not imply exact stored-code equality. No
    lifecycle transition or paper Lemma 71 case is transposed.
29. `Cordis.GlobalForeignPhase` uses `Dynamics.run_read_confined` only after
    `ForeignPhaseReadable` admits the point update, then refines the ordinary successor with an
    exact frame and stabilizes registration with same-child oracle certification. The registration
    successor equation is derived from request equality, freshness, and insertion/phase
    commutation. `phase_framed_diamond` combines two compatibility certificates with the raw
    independent diamond and retains both actual post-raw owner lookups. Independent, readable, and
    raw-registration-stable countermodels separately prove that none of the three lower laws is
    implicit. Supplied phases remain arbitrary typed edits; no lifecycle `Transition`, guard,
    target, or Lemma 71 exchange is constructed.
30. `Cordis.GlobalLandingTransposition` separates `LifecycleYieldStable` from semantic stability
    and packages both cross-forward directions in `ForwardLifecycleIndependent`; a countermodel
    proves the strengthening necessary. `LandingProgramWitness` fixes each existential landing to
    the chosen program oracle. Foreign exact lookups and source well-formedness derive preservation
    of already-valid target views. Off-axis framed executions are rebuilt from the common landing's
    fiber/control template, and `landing_activation_diamond` constructs actual Iter/Finish
    transitions in both orders with one exact final state for all four outcome combinations. The
    positive example is Iter/Finish; separate models prove common-source applicability and fixed
    program provenance necessary. That module alone contains no Begin pair.
31. `Cordis.GlobalActivationTransposition` packages a program-root-aligned Begin together with the
    existing program-aligned landing activation. Every activation derives its exact endpoint and
    actual lifecycle transition; exact foreign lookup and a non-active source actor preserve an
    already-valid positive target under well-formedness. Fixed-program execution proves endpoint
    and rule uniqueness. `ActivationSwapLaws` is branch-minimal, and
    `program_activation_diamond` covers all nine common-source Begin/Iter/Finish pairs. The
    paper-shaped wrapper receives an actual normal-order second activation, identifies its endpoint
    by uniqueness, and derives the swapped actual transition. Root mismatch and same-owner phase
    updates are kernel counterexamples. This is a partial, fixed-oracle bounded Lemma 71(1)
    analogue, not clause (2), arbitrary trace rewriting, episode assignment, or confluence.
32. `Cordis.GlobalActivationOrchestrationTransposition` proves that the literal paper clause-(2)
    side condition is insufficient: registration can enable a distinct O-Insert parent, and two
    legal insertion orders differ in their exact per-fiber birth ranks and current rule relation.
    `RegistrationSafe` therefore forbids any registration before O-Insert and requires only
    child/actor inequality before Retire/Remove. `ExecutionFrameFor` is `True` for Begin and one
    occurrence-specific moved fixed-oracle execution/yield/raw square for a landing. The headline
    theorem reconstructs the earlier legal orchestration occurrence with the same replay template,
    rebuilds the moved activation, and proves the supplied normal final endpoint exactly.
    Birth-clock and state-sensitive-oracle models prove the frame is not derivable; structural,
    ordinary, and registering examples exercise the corrected matrix. This is not literal Lemma
    71(2), a birth-erasing quotient, stored-trace rewriting, Lemma 72, or confluence.
33. `Cordis.GlobalTraceRewrite` packages exact two-step paths, located dependent trace windows,
    and rule/actor permutation certificates, then splices the corrected activation swaps into
    arbitrary retained before/after trace context without weakening the outer endpoint indices.
    `ProgramOccurrence`, `TraceProgramAssignment`, and assigned swaps retain fixed-program/oracle
    provenance for the actual stored steps and rebuild it after the rewrite. A nonempty-prefix
    example rewrites the selected Begin/Insert window while retaining a preceding O-Insert. The
    layer excludes registering activation/O-Insert, relation-only endpoints, suffix simulation,
    deletion, arbitrary normalization, and confluence.
34. `Cordis.GlobalDeletion` gives deletion a constructor-indexed replay semantics rather than
    filtering existential `StepRecord` values. Each retained step supplies an actual matched step
    and assignment transport; each dropped position is explicitly authorized; rules and actors
    form sublists, and the shadow relation, alignment, length, and assignment facts are derived.
    For finite entries already proved vestigial, safe foreign orchestration suffixes replay exactly
    after removal with positional same-template evidence. A real `[drop, keep]` example and
    parent/clock/redraw/birth countermodels keep the boundary executable. General closing-episode
    deletion, lifecycle suffix simulation, birth-erased endpoints, Lemma 72, automatic
    normalization, and
    confluence remain absent.
35. `Cordis.GlobalPaperRelation` defines the finite paper-visible control obtained by erasing only
    `nextBirth` and per-fiber birth from current rule observation. It proves three observation
    Setoids, weakening from strict `RuleRelated`, allocator-gap relatedness, and actual bidirectional
    O-Insert/O-Retire/O-Remove replay with related well-formed successors and assignment-carrying
    `RetainedStep`s. From a well-formed source carrying `VestigialNames`, finite erasure satisfies
    combined effect/outside control and safe orchestration traces replay directionally. Outside
    reverse replay and lifecycle simulation are
    kernel-refuted; there is no birth-erased activation swap, general episode deletion,
    automatic normalization, or confluence.
36. `Cordis.GlobalProgress` gives Definition 65 its exact state-local provider precedence and an
    explicit finite increasing rank. A configured oracle-rejection model separates fixed-program
    applicability from the raw existential-oracle relation; a Boolean freshness-exhaustion model
    is well formed and nonquiescent yet admits no raw lifecycle rule. `OracleTotal` constructs
    fixed-program landing-or-raise totality, while the headline theorem consumes only exact current
    reloading and recovery witnesses. With committed-provider soundness, a maximal-rank unloading
    argument proves state-local no-deadlock for every lifecycle phase. The module stops before the
    quantitative `(K + 4)` bound, target-turn finiteness, maximal termination, fairness, or
    trace-wide program assignment.
37. `Cordis.GlobalProgressTermination` supplies the quantitative bridge only as an explicit
    certificate: a strict natural-valued potential over exact dependent lifecycle edges yields
    telescoping trace budgets, a conditional `K + 4` length bound, and a no-nonempty-cycle theorem.
    The potential, strict-decrease law, and initial bound are not derived from `GlobalProgress`;
    target-turn finiteness, maximal termination, fairness, trace-wide assignment, support,
    deletion, and confluence remain unproved.
38. `Cordis.GlobalSupport` proves the printed Lemma 68 inference false with a reachable
    `FromEmpty` mixed parent/provider cycle and two distinct Definition 67 solutions.
    `SupportOrder` therefore stores well-foundedness of the combined relation itself; `supported`
    uses edge-indexed well-founded recursion and is the unique solution. `TotalOnProvisionAt`,
    `NoFailedFiber`, and `ActiveParentClosed` make active names a support solution, yielding the
    corrected `support_eq_active` theorem by uniqueness. A separate active-parent model proves that
    closure assumption necessary, while a root-only positive state exercises the corrected theorem.
    The module does not derive combined order or parent provenance from `FromEmpty`, does not prove
    component-wide Definition 69 or printed Lemma 70, and stops before deletion/confluence.
39. `Cordis.GlobalProgressRun` connects the conditional progress theorem to a finite
    dependent runner. `ProgressAuthority` and `StepPotential` are explicit inputs;
    `runFuel` retains endpoint `WellFormed` proofs and exact lifecycle traces, while
    `certifiedRun_quiescent` rules out full-fuel exhaustion at the initial potential.
    This is a finite conditional execution bridge, not derived quantitative/maximal
    termination, target-turn accounting, fairness, trace assignment, support, or confluence.
40. `Cordis.GlobalPaperTraceNormalization` packages a finite list of supplied
    `RelatedAdjacentRewrite` certificates. The dependent-safe chain representation connects each
    link to the next rewritten trace package, retains each transported `TraceProgramAssignment`,
    and proves final `BirthErasedRuleRelated` plus `List.Perm` facts for trace rules and actors.
    Its executable examples include a one-link activation/orchestration rewrite and a connected
    two-link reverse cycle. This is not a strategy, canonical-form, termination, confluence,
    Lemma 72, or Theorem 73 proof.
41. `Cordis.GlobalProgressAssignment` adds an explicit provenance bridge above
    `GlobalProgressRun`: `AssignedProgressAuthority` supplies one `StepProgramAssignment` for
    each lifecycle transition, and `assignTrace` reconstructs the dependent assignment for the
    complete intrinsic trace. The runner's endpoint, length, stop, and initial-potential
    quiescence proofs are retained. Fixed programs, roots, oracles, reachability, and the full
    paper Definition 60/66 provenance remain supplied or unproved.
42. `Cordis.GlobalPaperTraceNormalizer` adds a terminating dependent normalizer above the
    supplied rewrite-chain layer. An `Authority` carries normal-form decidability, a source-indexed
    rewrite witness, and a strictly decreasing natural measure; `normalize_some` constructs a
    finite chain whose endpoint is birth-erased related to the source and whose rule/actor lists
    are permutations. This is conditional termination for the supplied authority, not an inferred
    strategy, canonical-form theorem, global dynamic termination, Lemma 72, Theorem 73, or
    confluence.
43. `Cordis.GlobalPaperTraceScopedConfluence` makes the reachable package family an explicit
    finite index type instead of hiding it behind a proposition. `IndexedAuthority` carries
    package injectivity, a decreasing measure, normal-form decisions, and source/target equations
    for every selected adjacent rewrite; `normalizeFuel`, `path_of_indexedLinked`, and
    `normalize_results_unique` then reconstruct the independent rewrite path and equal package
    endpoints. The nonempty activation/orchestration fixture exercises a real link and exposes
    its rewritten rule and actor ledgers. This remains a supplied finite confluence certificate,
    not a derived CORDIS strategy, global termination, Lemma 72, or Theorem 73.
44. `Cordis.DeepSeekHarnessEndToEnd` composes the byte-backed validated restore with the
    retry-aware indexed conversation without erasing the restored runner from the trace index.
    Its executable memory/injected-transport fixture reaches archive `nextSeq = 8`, final
    `nextSeq = 11`, two rounds, one transient failure, model `0`, and a typed completed stop.
    This is a local composition certificate only: fsync, live provider behavior, backoff,
    idempotency, cancellation, external effects, and deployed Harness equivalence remain open.
45. `Cordis.DeepSeekHarnessPersistenceProcessOutcome` composes that restored runner with the
    actual `IO.Process` outcome adapter. `PersistedProcessRound` retains the streaming request
    plan, complete process body, classified rich outcome, dependent execution, and exact final
    runner endpoint; its shell fixture checks archive `nextSeq = 8`, endpoint `nextSeq = 10`, and
    body length `523`. Process/credential trust, incremental delivery, blocked-read cancellation,
    durability, external effects, and deployed Harness equivalence remain open.
46. `Cordis.DeepSeekHarnessPersistenceStreamRetry` extends the byte-backed restore through a real
    process-backed two-round streamed continuation. The first shell response emits two counter
    tool calls; the next request contains their certified `[true,0]` results and therefore receives
    terminal text. The dependent fixture checks `8 -> 12`, two rounds, two first-round calls, one
    attempt, model `0`, and a typed completed stop. Provider/process trust, durability,
    cancellation, external effects, and deployed Harness equivalence remain open.
47. `Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation` adds a pre-round cancellation
    certificate to that process-backed continuation. It accepts the first tool round, decides
    cancellation before round one, and checks `8 -> 11`, one retained round, two first-round calls,
    timeout reason, model `0`, and an exact cancellation stop. In-flight interruption, process
    cleanup, durability, external effects, and deployed cancellation equivalence remain open.
48. `Cordis.DeepSeekHarnessPersistenceFileStreamRetryCancellation` reruns that dependent
    cancellation path after writing and reading the archive through a temporary-file
    `DurableIO.FileBackend`. Its executable projection checks the same `8 -> 11` prefix and
    records the file-backed route beside the exact restored-session equality. `withTempFile`
    cleanup is real, but fsync, stable media, crash recovery, in-flight interruption, process
    cleanup, external effects, and deployed Harness equivalence remain open.
49. `Cordis.DeepSeekHarnessEventFileStreamRetryCancellation` writes the supported current-Harness
    event JSONL fixture to a temporary file, reads it back as bytes, proves byte equality before
    restoring the event archive/session, and feeds that restored runner to the existing
    process-backed streamed cancellation trace. Its executable projection checks source/read byte
    equality, `8 -> 11`, one retained round, two first-round calls, timeout cancellation, and model
    `0`. Scoped cleanup is real; fsync, stable media, crash recovery, blocked-read interruption,
    process cleanup, provider authenticity, external effects, and deployed Harness equivalence
    remain open.
50. `Cordis.DeepSeekHarnessPersistenceStreamBytePrefixTimeout` composes the memory-backed
    validated archive reader with the timed byte-prefix process adapter. Its fuel fixture restores
    archive `nextSeq = 8`, accepts one streamed tool round, then stops at `nextSeq = 10`; the
    terminal companion switches bodies after the first tool result and completes at `nextSeq = 11`
    after two rounds. Both retain model `0` and restored-session equality. Durable media, crash
    recovery, blocked-read interruption, provider/process authenticity, cleanup, external effects,
    and deployed Harness equivalence remain open.
51. `Cordis.DeepSeekHarnessEventPrefix` exposes the stateful pure target beneath that text seam.
    `Cursor.push` decodes and refines one JSON object at a time, while `PrefixSequence` retains
    the exact snoc protocol trace, raw entries, and endpoint state. `run` adds explicit fuel and
    cooperative entry cancellation, preserving the unread suffix; JSONL framing, blocked-read
    interruption, crash durability, and deployed Harness equivalence remain open.
52. `Cordis.DeepSeekHarnessEventProcessPrefix` feeds the cursor from one configured local process
    stdout line at a time. Its result retains the observed line ledger, endpoint, exit status, and
    typed completion/fuel/cancellation stop, with a proof that consumed count equals the cursor-entry
    count. Fuel and policy stops kill and wait for the child; malformed lines and nonzero exits are
    typed failures. Byte framing, blocked-read interruption, executable/provider authenticity, crash
    durability, and deployed Harness equivalence remain open.
53. `Cordis.DeepSeekHarnessEventProcessTimeout` races each blocking stdout-line read against a real
    `Std.Async.Sleep`; a timeout kills and waits for the configured child, and the dependent result
    retains the accepted prefix, observed lines, exit code, stderr, and timeout index. This is a
    local configured-child interruption fixture, not arbitrary descendant cleanup, fairness,
    backpressure, authenticity, crash durability, or deployed asynchronous equivalence.
54. `Cordis.DeepSeekHarnessEventProcessTimeoutRefinement` transports the timed cursor's existing
    per-entry refinement proofs into an intrinsic `SessionRefinement.ValidatedSequence`, retaining
    the exact entries, final state, and protocol projection without reparsing. This is
    noncomputable proof packaging above the executable timeout module; raw `decodeEvents` equality,
    byte framing, authenticity, persistence, and deployed Harness refinement remain external.
55. `Cordis.DeepSeekCurlBytePrefixTimeout` races each blocking process-byte read against a real
    `Std.Async.Sleep`. A configured-child timer winner returns a typed timeout retaining the accepted
    byte-prefix state, raw chunks, pending fragment, stderr, exit observation, and timeout line;
    blocked, delayed-prefix, and fast-completion fixtures are executable. Arbitrary descendant
    cleanup, fairness, backpressure, authenticity, durability, reconnects, and deployed semantics
    remain external.
56. `Cordis.DeepSeekStreamHarnessBytePrefixTimeout` composes completed timed byte prefixes with
    the existing dependent streamed conversation runner and a fuel-bounded multi-round trace.
    Finish, assistant/tool append, and session indexing occur only for `.completed`; timeout, fuel,
    and cancellation stops are explicit nonterminal prefix errors. In-flight provider behavior,
    reconnects, and deployed asynchronous Harness equivalence remain outside this local adapter.
57. `Cordis.DeepSeekHarnessEventIgnorableProjection` adds the source-authorized archive exception
    for explicit `ignorable: true` rows. Its indexed ledger drops only opaque ignorable entries,
    retains supported wire/raw certificates and source positions, and rejects required opaque
    rows.
58. `Cordis.DeepSeekHarnessEventIgnorableNormalization` continues the supported subset: it maps
    each retained physical sequence to a contiguous local sequence, rewrites supported source-event
    and surface-operation references through that map, and validates the rewritten JSON log into an
    exact local session endpoint. Duplicate physical sequences, missing references, malformed
    rewrites, and semantic failures reject; this remains a bounded source-honest slice rather than
    complete opaque-payload or deployed-Harness equivalence.
59. `Cordis.DeepSeekHarnessEventSimulation` consumes the normalized occurrences through an
    occurrence-indexed `SourceReplay`. Its typed `DecisionLedger` records every keep/drop decision,
    each `ReplayStep` carries the exact pre-state `RefinedEvent`, and the replay proves source
    positions, local sequence renumbering, protocol erasure, and final session-projection equality.
    This is a finite supported-subset transition simulation; opaque semantics, provider behavior,
    bytes, persistence, cancellation delivery, and complete deployed-Harness equivalence remain
    external.
60. `Cordis.DeepSeekHarnessEventArchiveReplay` packages that normalized source replay with the
    physical archive's inductive keep/drop ledger. `ArchiveReplay` retains exact archive and kept
    raw rows, projects dropped opaque rows and positions, and shares one indexed source transition
    trace with the simulation certificate. The nine-row tool fixture checks eight supported
    transitions plus one explicit opaque no-op; required opaque rows still fail closed.
61. `Cordis.DeepSeekHarnessEventIgnorableRunner` attaches the normalized validated endpoint to the
    pure `ConversationRunner`, preserves exact session/step equalities, and rebuilds a typed
    `ChatRequest` through a dependent request certificate. The executable tool fixture verifies the
    normalized user/assistant/tool messages; provider authenticity, transport, persistence, opaque
    payload semantics, and deployed-Harness equivalence remain external.
62. `Cordis.DeepSeekHarnessEventIgnorableTransport` carries that restored runner through the existing
    process-backed complete-response conversation trace. `RestoredTransportRun` retains the original
    normalized session/step certificates beside the final runner, model, trace, and stop evidence;
    the deterministic fixture exercises one no-tool completion. Injected transport, credentials,
    provider authenticity, persistence, external effects, and deployed-Harness equivalence remain
    external.

The displayed fixed point in Definition 32 is not declared as a Lean inductive: its recursive
variable occurs negatively in `Gamma -> Gamma`. `Approximation Base Sigma depth` is therefore a
finite unfolding theorem surface, not a claimed construction of the equirecursive fixed point.

`Cordis.RuntimeRefinement` starts after JSON text has already become a `Lean.Json` AST. It
accepts current upstream block starts, text/reasoning/tool-call deltas, supported block ends,
usage, and successful finishes. Successful decoding is then passed to
`RichStream.validateTrace`, and the returned object contains both the exact decoded chunks and
the intrinsic trace witness. Opaque replay state, image/tool-result blocks, upstream
`LlmFailure` error/abort shapes, unsafe integers, and malformed fields fail closed. This is a
sound supported-subset refinement; it is not a completeness or behavioral-equivalence theorem
for the TypeScript `BlockAssembler`.

`Cordis.RuntimeFailureRefinement` is the separate normalized failure branch. It requires a finite
JSON-AST list whose last chunk is an in-band `error` or `aborted` finish, decodes the ordinary
prefix with the existing supported-chunk decoder, and retains the exact `LlmFailure` fields
(`message`, `code`, optional `status`, optional `providerRetryAfterMs`, and optional `requestId`).
This certificate intentionally does not run `RichStream.validateTrace`: current Harness failures
may end with open blocks, so no local rich/session finish, retry decision, cancellation policy, or
provider-authenticity claim follows.

`Cordis.RuntimeOutcomeRefinement` composes the two adjacent languages without erasing their
dependent witnesses. It tries the successful validator first, then the normalized failure
validator; a successful result contains the existing rich-stream certificate, a failure result
contains the exact ordinary prefix and terminal, and a rejection contains both structured errors.
This is a dispatcher rather than a policy layer: it does not reconstruct open blocks, choose
retry/cancellation behavior, append a session message, authenticate a provider, or claim runtime
equivalence.

`Cordis.RuntimeOutcomeSession` is the next policy-free boundary. Given a validated outcome and
the existing pure runner, it appends only a terminal successful assistant view. A normalized
failure returns its exact failure certificate and the unchanged runner. It does not synthesize
an assistant error message, retry/cancellation event, source-event list, persistence row, or
provider/deployed-session equivalence.

`Cordis.DeepSeekRichMixedStream` is a separate provider-wire projection, not an extension of
`RuntimeRefinement`'s current-Harness JSON-AST decoder. It accepts one choice and at most one
indexed tool call, interleaving text, reasoning, and tool fragments across distinct frames;
same-frame mixed fields, multiple choices/calls, unsupported finishes, replay metadata, and live
transport remain explicit rejection or nonclaim boundaries. `DeepSeekSessionRunner` now accepts
this mixed certificate alongside the text-only and one-tool certificates, but remains a pure
local append surface rather than a deployed Harness session equivalence.

`Cordis.DeepSeekRichMultiStream` extends that provider-wire boundary to multiple indexed
function calls. It retains a per-provider-index accumulator and maps first-seen calls to local
rich-stream indices, so calls may be interleaved or introduced together in one frame. The
cross-kind ordering rule is unchanged: a frame cannot carry content/reasoning and tool calls
together. The validator still accepts one choice only, successful terminal usage/finish, and no
replay metadata or live transport. `DeepSeekSessionRunner.appendMulti` composes the resulting
terminal view with the same local numeric-ID assignment proof used by the smaller validators.

`Cordis.SessionRefinement` covers a separate stateful subset of current `SessionEvent` JSON:
turn/step boundaries, selected request/header snapshots, route context, whole-list todo snapshots,
empty seed markers, and text/reasoning index-zero assistant chunks,
text/reasoning/image user/assistant blocks, complete assistant tool-call blocks, tool calls, restricted
singleton-text tool results, and exact append/replacement surface operations. It retains source sequence/time values in wire witnesses, derives
local zero-based steps and `turn/end.nextStep` only from the validated prefix, and assigns
provider string call IDs to fresh numeric local IDs with uniqueness proofs, reusing those IDs in
later call/result events. Header wire records retain provider/model, optional system text, selected
tool schemas, and header reason; the local header projection retains the fields it represents. All
six pinned turn-end reason tags (`completed`, `aborted`, `blocked`, `error`, `max-tokens`, and
`interrupted`) remain in the wire witness; the local projection normalizes cancellation and failed
string cases explicitly. Text
surface IDs, provider/model metadata, usage, and source references
remain in `State.wireSurface`, while the local session stores projected text plus typed tool calls.
Every admitted event passes the rich
Session append validator; runtime events also pass the intrinsic Protocol validator. Unsupported
header fields, unknown todo statuses, nonempty seed payloads, unsupported chunk kinds, replay state,
reasoning and image surface blocks are retained in the wire witness while multimodal tool-result
blocks, error/meta payloads, and extension events fail closed. The
structured cancellation/failure payload remains in wire/refinement state rather than being claimed
as a local `TurnEndReason` variant.

`Cordis.SessionArchive` is the complementary lossless envelope boundary. It validates the required
`type`/`seq`/`time`/`data` envelope shape and conditional `ignorable`, `sourceEventSeqs`, and
`surfaceOp` fields while retaining the original `Lean.Json` AST. Supported records carry a
`SessionRefinement.WireEvent` certificate; unknown or semantically unsupported records are retained
as `opaqueRequired` or `opaqueIgnorable` rather than discarded. This does not assign extension
payload types, replay semantics, or a local session projection to opaque records.

`Cordis.SessionOpaqueMetadata` is a narrower bridge for a supported tool-result session whose
`data.error` and `data.meta` fields are provider/tool-owned. It removes only those two fields
before invoking the existing dependent session validator, retains each original JSON value in
order, and proves that the sanitized Session/Protocol projection is unchanged. The certificate
does not interpret either field or claim provider/tool schema equivalence.

`Cordis.SessionEventArchive` closes the adjacent wire-vocabulary gap. It recognizes all thirteen
pinned core tags, requires object-shaped `data`, rejects surface metadata on log-only tags, and
delegates accepted payloads to `SessionRefinement`. Known payloads outside that semantic subset
remain typed opaque records with their exact raw AST, so assistant image blocks,
provider usage/failure objects, tool-result `error`/`meta`, and future request fields are retained
without an invented local meaning.

`Cordis.DeepSeekHarnessEventArchive` consumes both sides of that boundary. A
`SupportedEventLog` carries the lossless archive, the stateful `ValidatedJsonLog`, and a proof
that every archived event is non-opaque. `RestoredRunner` then exposes exact equality between the
runner session and the validated final session, preserves the archive's raw-event ledger, and
supports a proof-carrying request rebuild. The fixture is executable; known opaque and extension
events are rejection cases rather than silently ignored records.

`Cordis.DeepSeekHarnessEventIgnorableProjection` is the intentionally smaller source-authorized
exception. It retains the full archive and a positional keep/drop ledger, drops only opaque rows
marked `ignorable: true`, retains supported wire/raw certificates and positions, and rejects a
required opaque vendor row. `Cordis.DeepSeekHarnessEventIgnorableNormalization` then handles the
supported subset: it rewrites retained sequence numbers and supported source references before
calling `SessionRefinement.validateJsonLog`, with typed rejection for duplicate physical sequences,
missing references, malformed rewrites, and semantic failures. Opaque payload semantics and
deployed-Harness equivalence remain external.

`Cordis.DeepSeekHarnessEventIgnorableRunner` is the next pure attachment: it sets the
`ConversationRunner` session definitionally to the normalized final session, records the local step
and tool-call-count witnesses, and rebuilds a typed request from that endpoint. This is a local
request/session certificate, not provider execution or deployed-Harness equivalence.
`Cordis.DeepSeekHarnessEventIgnorableTransport` then feeds that same dependent runner into the
existing process-backed complete-response conversation loop. Its result retains final
runner/model/stop evidence and the original normalized-session certificates; it does not infer
credentials, provider authenticity, durable persistence, external effect correctness, or deployed
Harness equivalence.

`Cordis.DeepSeekHarnessEventText` is the direct text/byte ingress for this seam. Its text result
retains the parsed source, archive lines, validated session, and restored runner; its byte result
adds the exact UTF-8 decoding equality before reusing the text certificate. Invalid UTF-8 and
opaque/extension events remain typed failures. This is still a pure parser/validator boundary,
not a logger, transport, persistence, or deployed-Harness equivalence theorem.

`Cordis.DeepSeekHarnessPayloadText` adds one lossless view without widening the semantic runner.
The payload log and runner are indexed by the same parsed JSONL lines, so reasoning/image blocks,
assistant usage, tool-result `error`/`meta`, and unknown block tags remain available as exact raw
JSON beside the supported Session/Protocol projection. Provider-owned payload schemas remain
outside the local type system.

`Cordis.DeepSeekHarnessPayloadPersistence` composes that view with the logical persistence
certificate, pure byte validation, and the executable memory/file backend. A successful result
retains the header/storage split, expanded event ASTs, exact restored session, and raw payload log
at one dependent index. This closes the payload-preservation composition at the persistence seam;
it does not claim provider schema semantics, fsync, crash recovery, or deployed Harness
equivalence.

`Cordis.DeepSeekHarnessOpaqueMetadata` is the narrow quarantined exception to that fail-closed
event path. It consumes the sanitized `RetainedLog`, restores its validated final session to a
runner, and carries the exact `error`/`meta` JSON ledger beside the runner. The local request
projection intentionally ignores those fields; no provider/tool schema meaning is assigned.

`Cordis.DeepSeekHarnessMetadataArchive` adds the alignment certificate for that exception: its
`AttachedLog` contains one raw current-event archive and one sanitized metadata validation over
the same source list. The executable fixture proves that a known opaque `tool/result` survives in
the raw ledger while the runner and request are built from the sanitized endpoint.

`Cordis.DeepSeekToolSchema` closes a small request-side gap without claiming a full provider
schema implementation. Its `ValidatedParameters` certificate accepts object roots whose finite
properties use primitive JSON Schema `type` tags, optional string descriptions, and an optional
boolean `additionalProperties`; required names must be unique and present in the property map.
`ValidatedToolDefinition` additionally rejects empty names, and `CertifiedRequestSource` rejects
duplicate tool names before exposing request builders. `ValidatedArguments` parses a candidate
object and proves duplicate-free fields, required names, primitive value kinds, and restrictive
unknown-field rejection. Every accepted certificate retains the exact source parameter AST.
Nested schemas, unions, constraints, defaults, enums, provider extensions, provider-side
validation, and model obedience remain outside this bounded vocabulary.

`Cordis.DeepSeekToolAdmission` then checks exact provider-call name agreement and carries the
argument certificate into a `CertifiedFunctionCall`. It is intentionally not a capability
resolver or provider-obedience theorem: call-ID authenticity, generic execution correspondence,
and deployed Harness equivalence remain separate boundaries.

`Cordis.DeepSeekGenericBridge` composes that certificate with a named `SchemaToolBinding` and
generic `Config.validate`. The successful result retains the provider certificate and an
existentially indexed generic call, with an equality proving that the generic resolver selected
the bound catalog operation. This is a pre-execution admission bridge, not a proof of provider
schema/`ToolSpec` semantic equivalence, external execution, call-ID authenticity, or deployed
Harness equivalence.

`Cordis.DeepSeekSchemaExecution` is the separate dispatch adapter for this certified path. It
consumes only the existential call returned by `validateAndAdmit`, applies the generic policy, and
invokes the committed dependent `View` on `.allow`, retaining policy and reply equalities. It
does not alter raw-call compatibility execution or prove live external-tool, provider-obedience,
call-ID, or deployed Harness semantics.

`Cordis.DeepSeekSchemaHarness` is a local post-execution transport seam. It retains the provider
certificate, reconstructs the existing `DeepSeekHarness.ExecutedTool` from the exact parsed JSON
and dependent equalities, and delegates result appending to the existing certified session
surface and `ConversationRunner.appendToolResults`. Its append theorems therefore prove only
local message, sequence, protocol-projection, and runner-continuation facts; no second execution,
provider obedience, call-ID authenticity, persistence, or deployed Harness equivalence is claimed.

`Cordis.DeepSeekSchemaRound` is the bounded complete-body response composition for exactly one
assistant function call. It retains the accepted response and singleton tool-call equality,
dispatches through `DeepSeekSchemaExecution`, and appends via the existing runner. It remains the
one-tool certificate used as the base case for `Cordis.DeepSeekSchemaMultiRound`.

`Cordis.DeepSeekSchemaMultiRound` accepts a nonempty list of calls for one explicit homogeneous
provider/generic binding. Its recursive result carries each schema/generic/policy/execution
certificate, the exact final model, an execution-list length equality, typed failure position,
and the runner endpoint after appending every certified result. Heterogeneous schema registries,
live transport, provider obedience, call-ID authenticity, persistence, and deployed Harness
equivalence remain outside.

`Cordis.DeepSeekSchemaRegistry` removes only the homogeneous-binding restriction in a bounded,
source-local way. `SchemaToolRegistry` stores entry-specific provider declarations and dependent
`SchemaToolBinding`s, `resolveSchemaTool` returns the chosen entry together with exact name
equality, and `executeSchemaRegistryCalls` threads the selected operation's certified successor
model through a mixed call list. `executeSchemaRegistryRound` appends the assistant plus all
certified results to the existing runner; the fixture covers weather followed by clock and a
later unknown-name rejection. This is not a provider-complete registry, live transport, call-ID
authenticator, persistence layer, or deployed Harness-equivalence theorem.

`Cordis.DeepSeekScopedRegistry` is a pure routing layer above that registry boundary. It orders
finite scopes nearest-first, makes a matching restriction terminal rather than falling through,
and retains an automatic/review approval ticket before the dependent provider `View` executes.
The fixture proves shadowing, restricted and unknown-name rejection, review routing, and approval
rejection. Scope construction, authenticated approval, asynchronous policy waterfalls, persistence,
external effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekSchemaConversation` closes the adjacent one-round transport seam by deriving the
typed request's tool list from that registry, executing an explicit complete-body `Transport`, and
retaining the request plan, validated response, accepted calls, heterogeneous batch, and runner
endpoint together. `Cordis.DeepSeekSchemaConversationLoop` then recurses under explicit fuel,
advances the dependent model after every certified tool round, preserves an existential history,
and retains a validated no-tool response as terminal rather than confusing it with exhaustion.
These modules remain complete-body and caller-fueled; provider obedience, retries, cancellation,
persistence, external effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekSchemaTransportRetryCancellation` composes the same heterogeneous registry with
the single-decoder retry boundary and pre-round cancellation. A successful validated response is
used directly for either terminal admission or dependent weather/clock execution; the tool-round
trace retains retry history and exact runner/model endpoints. The timeout-before-send and 503-to-
200 fixtures are local injected-transport evidence only: in-flight interruption, backoff,
idempotency, persistence, external effects, and deployed Harness retry/cancellation equivalence
remain outside.

`Cordis.DeepSeekSchemaProcessRetryCancellation` instantiates that exact dependent result through
the existing process adapter. Its `sh` fixture returns one transient 503, then the heterogeneous
weather/clock response, then a terminal no-tool response, so local process execution and retry
history are observed together. Cancellation still happens before process dispatch. Network,
credentials, provider obedience, shell/process trust, in-flight interruption, backoff/idempotency,
persistence, external effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekSchemaStreamConversation` applies the same dependent registry to the existing
complete-body SSE/rich-stream/session boundary. Its request certificate proves `stream: true`,
the process body is validated through the strict rich/session projection before calls are
dispatched, and a finite run retains heterogeneous tool rounds or a typed exhaustion stop. The
fixture also exercises a text-only terminal body. Incremental readers, backpressure, cancellation,
reconnects, provider-complete assembly, call-ID authenticity, persistence, external effects, and
deployed Harness equivalence remain outside this slice.

`Cordis.DeepSeekHarnessProcessSchemaPrefix` keeps the exact registry-certified streaming plan
attached to that prefix result. Fuel exhaustion and line cancellation retain plan and stop
evidence, while only a completed `[DONE]` prefix exposes the dependent schema step and runner
endpoint. It remains a synchronous complete-line adapter rather than a byte-level or deployed
cancellation theorem.

`Cordis.DeepSeekHarnessProcessSchemaPrefixConversation` lifts this provenance through the
caller-fueled loop. Every completed tool-round witness retains its own prepared plan and accepted
prefix; an attempted round's plan remains available on typed round exhaustion or cancellation.
The loop is still local, line-oriented, and caller-fueled, with no deployed Harness equivalence.

`Cordis.DeepSeekSchemaStreamPrefixConversation` sits immediately below that complete-body loop. A
process line policy can return a proof-carrying prefix at a caller-selected boundary; a finite read
budget is a separate stop, and only completion of the strict SSE/rich/session validator unlocks
the dependent weather/clock dispatch. This remains line-oriented: byte framing, blocked-read
interruption, backpressure, reconnects, provider-complete assembly, call-ID authenticity,
persistence, external effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekSchemaStreamErrors` then lifts the existing fail-closed provider-error policy into
the heterogeneous streamed registry. Each failed entry retains its dependent schema and generic
admission/policy evidence, exact provider message, and unchanged model; the runner appends an
opt-in `isError` tool result, and the fixture proves a subsequent text terminal when the request
source includes error tool results. This is still a complete-body, deterministic process fixture,
not a retry, cancellation, persistence, external-effect, or deployed-error-equivalence theorem.

`Cordis.DeepSeekStreamFailure` covers the adjacent wire-only terminal-failure language. It accepts
only complete strict bodies ending in `content_filter` or `insufficient_system_resource`, retaining
the leading `DataFrame`s, terminal raw frame, singleton choice/reason, and optional usage. Ordinary
rich finishes, provider SSE `error`/`aborted` envelopes, and any normal rich/session projection
remain outside this failure certificate. The normalized JSON `StreamChunk` failure union is
handled separately by `Cordis.RuntimeFailureRefinement`.

`Cordis.DeepSeekTerminalOutcome` composes that failure certificate with the four existing successful
rich validators. It classifies failures first, then text, one-tool, mixed, and multi-call bodies,
retaining whichever dependent wire/projection/rich witness was accepted. This remains a complete-
body dispatcher; it does not widen the wire vocabulary or produce a session message for failures.

`Cordis.DeepSeekHarnessPersistenceIO` composes the same runner attachment with the executable
`HarnessPersistenceIO.ReadCertificate`. A successful memory or temporary-file read retains the
decoded bytes/text/rows certificate before restoring the runner, and the request certificate is
linked back to that exact read endpoint. This closes the byte-backed attachment seam only; it does
not claim stable media, fsync, locking, torn-tail repair, authenticity, or deployed crash recovery.
`replaceAndRestore` and `appendAndRestore` re-enter the same certificate after a canonical
replacement or validated append, so the updated runner is never returned without a fresh logical
read/validation boundary.

`Cordis.DeepSeekHarnessPersistenceTransportRound` composes that restored runner with the
execution boundary. `executeRestored` carries the archive/session equality into a complete typed
request plan, sends the plan through an injected transport, validates the response once, admits
the same `ValidatedResponse`, executes the admitted function calls, and returns the exact
assistant-plus-tool-result endpoint. `PersistedRound.plan_build_archive` proves that the request
plan can be rebuilt from the persisted archive endpoint, while the executable memory fixture
checks the archive, response, tool, sequence, and allocator projections. This is still a local
certificate: it does not establish filesystem durability, live provider behavior, retries,
cancellation, external effect correctness, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessTransportConversation` is the corresponding multi-round composition.
`TransportTrace` indexes every tail by the previous round's exact final runner and model;
`runTransport` therefore retains a single-decoder certificate for each request/response/tool
round, and its stop value distinguishes certified no-tool completion from fuel exhaustion. The
deterministic two-response fixture exercises both branches. It remains a bounded injected
transport model, not a live-provider, retry, cancellation, durability, external-effect, or
deployed-Harness equivalence theorem.

`Cordis.DeepSeekHarnessTransportRetry` adds the next bounded boundary without adding a second
decoder. It builds one complete request plan, records retryable transport/transient-HTTP failures
in `RetryHistory`, validates the successful body exactly once, and sends that same dependent
response through `acceptValidated` and typed tool execution. The executable fixture covers a
503-to-200 retry and the exact assistant/tool endpoint. Provider backoff, idempotency,
cancellation, persistence, external effects, live-provider behavior, and deployed Harness
equivalence remain outside this immediate injected-transport model.

`Cordis.DeepSeekHarnessTransportRetryConversation` composes those retried rounds into an indexed,
fuel-bounded trace. Each head retains its retry history and the tail starts from the exact final
runner/model endpoint of the previous round; the fixture retries a tool round once and then
reaches a no-tool terminal response. Completion and fuel exhaustion remain distinct certificates,
and the model does not add provider backoff, idempotency, cancellation, persistence, external
effects, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessEndToEnd` composes that retry trace with the byte-backed persistence read.
`PersistedRetryRun` keeps the restored archive runner, final runner/model, retry trace, and typed
completion stop in one dependent result. The executable fixture checks archive `nextSeq = 8`,
final `nextSeq = 11`, two rounds, one transient failure, and model `0`; it remains an
in-memory/injected-transport certificate rather than a durability, provider, or deployed-Harness
theorem.

`Cordis.DeepSeekHarnessPersistenceProcessOutcome` takes the same byte-backed restored runner
through `DeepSeekHarnessProcessOutcome.executeSourceOutcome`. The dependent result retains the
streaming request-plan proof, process/body certificate, rich outcome classification, typed tool
execution, and exact endpoint, and its deterministic shell fixture reaches `8 -> 10` with a body
of length `523`. This is an executable local process boundary, not provider authenticity,
incremental-stream, blocked-read, durability, external-effect, or deployed-Harness evidence.

`Cordis.DeepSeekHarnessPersistenceStreamRetry` composes that actual process outcome with the
fuel-bounded streamed conversation loop. The restored runner remains the initial trace index; the
fixture emits two counter calls, executes them through the dependent generic configuration, then
returns terminal text when the next serialized request contains `[true,0]`. It reaches `8 -> 12`
with two typed rounds and a completed stop. This remains deterministic local process evidence,
not provider authenticity, durable recovery, cancellation, external-effect, or deployed-Harness
equivalence evidence.

`Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation` adds the same cancellation policy at
the continuation boundary. After the first process-backed tool round, the policy decides before
the next request and retains the one-round prefix plus exact runner/model endpoint. This proves a
pre-round cancellation certificate, not interruption of an in-flight process or HTTP read,
process cleanup, durable recovery, external effects, or deployed cancellation equivalence.

`Cordis.DeepSeekHarnessTransportRetryCancellation` composes that trace with a caller-controlled
pre-round cancellation decision. The cancellation fixture stops before issuing a request and
retains the empty typed prefix; the success fixture retains the retried tool round and terminal
no-tool round. This is still a complete-body injected-transport boundary, not in-flight IO
interruption or deployed retry/cancellation equivalence.

`Cordis.SessionPayloadArchive` moves one layer inward without inventing provider semantics. It
classifies the five current content-block tags plus unknown block extensions, retains exact message
content arrays and source objects, preserves assistant-chunk objects and raw usage, and retains
tool-result `error`/`meta` JSON. Malformed known payload shapes become attached shape errors while
event order and raw records remain exact. This is typed raw retention, not provider/tool schema
validation, replay, or complete local Session equivalence.

`Cordis.TextRefinement` composes these AST-level validators with the Lean JSON parser and UTF-8
decoder. `parseJsonLines` rejects empty sources and interior blank lines, preserves zero-based
line numbers for malformed JSON, and `parseJsonLinesBytes` rejects invalid UTF-8 before parsing.
Successful `validateStreamBytes` and `validateSessionBytes` values retain the decoded source
text, exact AST lines, and the existing rich/protocol proof certificates; `validateFailureBytes`
retains the same text boundary together with the normalized failure terminal certificate. The
parser and
canonical compact printer are library boundaries; this does not prove an external logger's
framing, schema compliance, timestamps, transport, or persistence behavior.

`Cordis.HarnessPersistenceRefinement` starts one layer below that text parser at the logical
JSON-AST storage format pinned in the Harness `session-persistence-jsonl` package. It recognizes
the required `type: "session"` header, retains ordinary event rows, and validates/expands
`text-chunks`, `reasoning-chunks`, and `tool-call-chunks` using exact safe sequence/time-gap
reconstruction before calling `SessionRefinement`. Unknown non-packed rows remain delegated to
the event decoder. Packed-row malformations, foreign versions/tags, retired header fields, and
unsafe reconstructions fail closed. This deliberately excludes Zstandard, path sanitization,
byte offsets, torn-tail repair, coordinator/indexing behavior, and filesystem durability.

`Cordis.HarnessPersistenceArchive` is the lossless companion when semantic expansion is not yet
available. It validates the same logical session header, retains each packed row with its exact
raw AST and typed tag, and delegates ordinary rows to `SessionArchive`, preserving supported
certificates and required/ignorable opaque envelopes. Storage indices remain attached to malformed
envelope errors. It deliberately does not expand packed rows, assign opaque payload semantics, or
claim replay, persistence, or crash recovery.

`Cordis.HarnessPersistenceIO` is the executable byte/text adapter above that logical boundary. It
reads UTF-8 bytes through the existing memory/filesystem backend interface, retains the exact
bytes/text/rows and semantic certificate, revalidates canonical replacement writes, and permits
an append-only row only after the existing document validates. Invalid UTF-8, malformed JSONL,
header/packed-row failures, and session-refinement failures remain distinct structured errors.
The adapter does not infer fsync, stable media, torn-tail repair, locking, or crash durability
from a host write acknowledgement.

`Cordis.HarnessPersistenceBytes` is the pure immutable-byte companion to that executable adapter.
`validatePersistedBytes` retains the original `ByteArray`, its decoded `String`, parsed JSONL rows,
the validated packed-row expansion, and the composed Session/Protocol projection in one dependent
certificate. It has executable accepted, malformed, empty, and invalid-UTF-8 fixtures. The Lean JSON
parser/printer remains a library boundary, so this does not claim deployed rendering, compression,
filesystem behavior, torn-tail repair, or crash durability.

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
- a second non-counter catalog instantiation proving the runner is genuinely generic;
- negative construction tests for mismatched catalog/wire/view indices and forged joint
  session/record history;
- heterogeneous realm isolation and metadata interception, including exact recovery;
- context-equivalence preservation of satisfaction and notification;
- current-Harness stream JSON success plus exact decode and semantic rejection paths;
- UTF-8 JSONL stream/session fixtures, exact parsed-line retention, and invalid-encoding rejection;
- logical Harness JSONL persistence fixtures covering header/tag/version rejection, packed
  text-row expansion, safe sequence/time reconstruction, and composition with session validation;
- lossless archive fixtures covering one supported core event, one required opaque extension, and
  one explicitly ignorable extension, with raw-AST order preserved exactly;
- finite operational tests with heterogeneous outcomes, failed domains, and the formal
  paired-inverse counterexample;
- quotient-effect composition and lifted coeffect context preservation;
- a complete supported current-Harness turn/step/tool session prefix plus stateful rejection
  cases;
- an executable finite multi-segment scheduler fixture covering windows, exclusive barriers,
  model-order reports, globally unique IDs, endpoint equality, and exact recovery;
- an executable bounded fiber fixture covering guarded start/complete/fail/cancel transitions,
  completion-order races, a drained permutation certificate, and no-effect cancellation;
- full generator-to-transformation-monoid promotion and inverse stability; and
- exact total operation independence, finite partial distinct-key words, outcome-dependent
  mediated execution, and the forward-only inverse-stability counterexample;
- arbitrary middle-effect removal, explicit later inverse agreements, and non-LIFO inverse
  permutation recovery; and
- global registry insert/retire/remove preservation, used-name/provision rejection, parent
  acyclicity, and heterogeneous active-context/target examples;
- realized heterogeneous branch paths plus the observational-versus-exact Theorem 42
  representative counterexample; and
- ordinary/registration global iterator steps, fuel exhaustion, accumulated code recovery, and
  trace-level well-formedness;
- reachable-root/continuation and actual-inverse generation for the existing lifecycle iterator
  program, together with the real-program self-independence failure;
- registration-child dependence of both continuation and retirement inverse, the duplicate-family
  whole-run-versus-full-independence gap, and the indexed-step totalization counterexample; and
- the `PerStepCommutes` bridge under explicit yielded-accumulator, step-membership,
  observational-independence, and `TotalStepMap` witnesses;
- the raw independent iterator diamond and both totalized pre-edit map squares; and
- a runtime probe on which distinct stored undo codes produce the same projection, plus static
  proof that their interpreted functions are equal but lifecycle-visible exact agreement fails;
- a fully independent two-owner program whose observed undo syntax changes after a foreign phase
  edit, with static proof that compatibility fails; and
- readable ordinary and registration models that separately fail exact successor framing and
  same-child oracle stability;
- a positive program-aligned L-Iter/L-Finish pair whose exact lifecycle diamond retains that rule
  pair; and
- kernel models showing semantic cross-forward stability, post-Finish Begin applicability, and
  bare landing data do not respectively provide exact undo syntax, common applicability, or fixed
  program/oracle provenance.

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
uv run scripts/check_lean_hygiene.py --self-test .
```

Then rerun the Lean gates from a clean `git archive HEAD` materialization. A local `.olean` or
Jujutsu working-copy artifact is not release evidence.

## Non-claims

This slice does not by itself prove:

- behavioral equivalence with the complete TypeScript DeepSeek Harness;
- byte-level JSON parsing, rendering, or storage compatibility;
- semantic completeness for the Harness event/storage union: `HarnessPersistenceRefinement` is a
  logical semantic AST refinement for the pinned header and three packed-row forms, while
  `HarnessPersistenceArchive` preserves the header, packed row tags, and envelope-valid opaque
  records without expanding or assigning them semantics; `DeepSeekHarnessEventArchive` attaches
  only the subset for which every retained event is both losslessly archived and semantically
  validated, and does not assign meanings to opaque records;
- byte-level persistence refinement beyond the supported `ByteArray` UTF-8/JSONL witness in
  `Cordis.HarnessPersistenceBytes`;
- filesystem/database persistence beyond the narrow tested adapters, stable-media/flush barriers,
  cryptographic authentication, arbitrary crash-file repair, or fork correctness.
  `DeepSeekHarnessPersistenceIO` proves only the read-certificate-to-runner attachment over its
  memory and temporary-file fixtures; it does not upgrade those backend calls into durability.
  `Cordis.DurableSettlement` and `Cordis.DurableCodec` prove a pure typed crash-prefix/resume
  model plus strict JSON-AST frame validation, `Cordis.DurableBytes` proves its explicitly
  defined binary format over immutable Lean byte lists with a supplied frame count, and
  `Cordis.DurableIO` and `Cordis.HarnessPersistenceIO` exercise host memory/file calls without turning acknowledgement into
  fsync, crash atomicity, or external-effect exactly-once evidence;
- wall-clock task/fiber scheduling, fairness, cancellation delivery, or concurrency. The pure
  finite schedule certificate above does not model worker IO, promise races, or deployed behavior;
- the stronger paired-inverse law from same-word tests without its explicit coherence premise;
- identification of the finite exact partial/Kleisli theorem with the paper's literal
  total/quotient Theorem 42;
- full Theorem 59 or the paper's global composability results;
- new-entry or retirement-write provenance for opaque accumulated recovery;
- canonical identification of global `≃` and `≈`, an oracle-free or paper-total Definition 60,
  automatic `TotalStepMap`, owner inverse stability, mixed-trace reordering, or arbitrary
  Theorem 61/Corollary 62;
- promotion of the raw iterator diamond or totalized pre-edit map squares to lifecycle
  transposition without exact code, fixed program/oracle, foreign-phase, guard, and
  edited-endpoint laws;
- derivation of foreign-phase readability, ordinary exact framing, or same-child oracle stability
  from `Independent`, base `Dynamics`, or raw request equality; or promotion of the framed raw
  diamond to lifecycle-rule phases, guards, targets, transitions, or either Lemma 71 clause;
- derivation of exact cross-forward `UndoCode` stability from semantic `Independent`, reassignment
  of a bare landing to an arbitrary program oracle, omission of source well-formedness or
  common-source applicability, or identity with an arbitrary stored trace step;
- derivation of orchestration execution framing from registration safety, well-formedness,
  independence, or base dynamics; exact registering-activation/O-Insert exchange; repair of the
  literal Lemma 71(2) premise without the corrected parent/birth restrictions; or arbitrary trace
  rewriting from the occurrence-local exchange theorem;
- paper Theorem 66 from finite names/precedence alone, the quantitative lifecycle-step bound,
  target-turn finiteness, maximal-execution termination, or scheduler fairness;
- pinned Lemma 68 from separate provider/parent acyclicity, support-equals-active without explicit
  combined order and active-parent closure, component-wide Definition 69, or printed Lemma 70;
- native plugin isolation, process confinement, filesystem safety, executable/network/credential
  trust, or remote-service behavior;
- global exactly-once execution across workers; or
- that a model follows supplied schemas or chooses an appropriate tool.

Those remain later proof/refinement layers. The new work is valuable because it makes the pure
kernel's session and request boundary materially closer to the current Harness architecture
while retaining an exact, auditable theorem boundary.
