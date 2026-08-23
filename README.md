# CORDIS Lean

[![CI](https://github.com/alok/cordis-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/alok/cordis-lean/actions/workflows/ci.yml)

<!-- markdownlint-disable MD013 -->

CORDIS Lean `0.1.0` is a delivered, executable finite reference kernel for
proof-carrying agent harnesses. It validates raw counter-tool calls into
dependent calls, threads each admitted call through an exact-subject policy
trace, executes a verified local provider, stores a request-indexed encoded
result, and maintains proof fields that jointly connect protocol replay, model
and lease endpoints, monotone IDs, records, and tool-boundary events across
finite steps and turns.

The current development line extends that reviewed `0.1.0` baseline with the
[`0.2` implementation contract](docs/V0_2_SPEC.md). The reusable runner is now
generic over one coherent model/catalog/wire/view/capability/policy
configuration and its trusted transitions are indexed by the exact session
phase. The counter is a thin instantiation; a second `Workspace` example proves
that a Boolean request can select either a `Nat` or `String` result while an
exact-call policy allows one branch and rejects the other without dispatch.
`Cordis.SessionValidation` validates parsed-but-untrusted typed events into
exact append/replacement range, provenance, surface-uniqueness, and `ValidLog`
certificates.

The same development line now adds further source-grounded proof layers:
`Cordis.RichStream` validates interleaved text, reasoning, and raw tool-call
blocks with terminal usage/replay invariants; `Cordis.Schedule` proves arbitrary
finite semantic reordering for certified commuting pure effects; and
`Cordis.Coeffect` mechanizes the paper's local reactive-coeffect Definitions
22–26 over a finite dependent context. `Cordis.UnifiedContext` then models
Definitions 27–31 directly and Definition 32 by exact finite unfoldings, while
`Cordis.ContextualEquivalence` proves the finite-context part of Definition 33
and its satisfaction/notification invariance. `Cordis.RuntimeRefinement`
decodes a fail-closed subset of the current Harness `StreamChunk` JSON shape
into the intrinsic rich-stream validator. `Cordis.StreamSession` explicitly
assigns unique numeric session IDs to provider string tool IDs before a
validated rich assistant view enters the canonical surface.
`Cordis.RuntimeFailureRefinement` separately decodes current-Harness in-band
`error`/`aborted` finishes and preserves every typed `LlmFailure` field in a
terminal certificate; it does not coerce an open-block failure into a normal
rich trace.
`Cordis.RuntimeOutcomeRefinement` then dispatches the supported successful and
normalized failure languages into one dependent outcome, retaining both branch
certificates or both structured rejection reasons without choosing retry or
cancellation policy.
`Cordis.RuntimeOutcomeSession` composes that outcome with the pure local session
runner: JSON/UTF-8 text certificates append a finished assistant view, while normalized
failures retain their typed certificate and leave the runner unchanged.
`Cordis.TextRefinement` parses newline-delimited UTF-8 JSON into exact AST lines
before composing the stream/session/failure validators, so executable fixtures exercise
the real text boundary without claiming deployed schema compliance.
`Cordis.HarnessPersistenceRefinement` then models the pinned Harness JSONL
storage vocabulary: a required `type: "session"` header, verbatim event rows,
and the three lossless packed chunk-row forms. It expands safe timestamp/sequence
gaps into exact event ASTs before invoking `SessionRefinement`, with structured
malformed-row/version/tag rejection. Compression, filesystem repair, indexing,
and crash durability remain outside this logical JSON-AST boundary.
`Cordis.HarnessPersistenceIO` lifts that certificate to an executable UTF-8 byte
boundary over the existing memory and filesystem backends: reads retain the exact
bytes/text/rows and semantic certificate, replacement writes can be revalidated,
and append-only rows are accepted only after the existing document validates.
Host acknowledgements remain separate from semantic validity; fsync, torn-tail
repair, locking, and stable-media durability remain outside.
`Cordis.HarnessPersistenceBytes` is the pure `ByteArray` companion: it retains
the source bytes, decoded UTF-8 text, parsed JSONL rows, packed-row expansion,
and final Session/Protocol projection in one dependent certificate. Valid and
malformed byte fixtures are executable evidence; JSON parsing/printer behavior,
compression, filesystems, and crash durability remain explicit boundaries.
`Cordis.DeepSeekApi` adds a typed OpenAI-compatible `/chat/completions` request
plan and a fail-closed response decoder with dependent parse/decode certificates.
`ChatRequest` retains the provider's `stream` flag; `buildRequest` preserves the
non-streaming default while `buildStreamingRequest` and its body certificate
construct the explicit `stream: true` variant. Its transport is an explicit
`IO` seam; the repository tests deterministic pure and process-backed fixtures,
not credentials or a live model call.
`Cordis.DeepSeekApiBytes` closes the adjacent byte boundary without coercing raw
responses into strings: request plans retain exact UTF-8 body bytes, successful
responses retain decoded text plus parse/decode certificates, and invalid UTF-8 or
non-2xx byte bodies remain distinct typed errors. The executable fixture uses an
injected byte transport; network reachability, credential validity, provider
obedience, and deployed Harness equivalence remain external.
`Cordis.DeepSeekApiErrorEnvelope` closes the adjacent non-success response seam:
an OpenAI-compatible `{ "error": ... }` body is retained with its parsed
`ApiErrorBody` and exact JSON decode equation, while malformed or successful
non-error bodies remain typed validation failures. It does not authenticate
provider errors or choose retry/backoff policy.
`Cordis.DeepSeekRequestMode` adds the type-indexed `TypedRequestPlan`: complete
and streaming plans carry a proof tying the request's serialized `stream` flag
to their mode, and the terminal execution wrapper accepts only a complete plan.
`Cordis.DeepSeekCurlTransport` supplies the first process-backed adapter:
configured executables (normally `curl`) receive the request body on stdin,
the URL and headers as direct arguments, and return a typed HTTP status/body
through a private trailer protocol. The `sh` fixture exercises that path
without claiming network reachability, credential validity, or process trust.
`Cordis.DeepSeekStream` adds the adjacent strict `data: <JSON>` / `[DONE]` SSE
boundary with typed delta frames, retained raw payloads, and UTF-8 rejection.
It does not claim a live reader, buffering/backpressure, cancellation, or full
provider stream assembly.
`Cordis.DeepSeekStreamIncremental` adds a pure, proof-carrying prefix state over
complete SSE lines: each accepted line retains the exact accumulated body and
frames, a terminal `[DONE]` is required at `finish`, and a finite line policy
can stop before consuming the next line. This is prefix control rather than a
live HTTP reader, backpressure, process cancellation, reconnect, or deployed
assembler theorem.
`Cordis.DeepSeekStreamByteFraming` adds the pure byte-ingress seam below that
line machine: arbitrary `ByteArray` chunks split at LF boundaries, complete
lines decode as UTF-8 only after framing, and the prefix state retains an exact
canonical reconstruction. `finish` rejects an incomplete final line and
bridges the reconstructed text to the strict SSE validator. Process-level
reads, blocked-read interruption, backpressure, cancellation, reconnect, and
deployed stream semantics remain external.
`Cordis.DeepSeekCurlByteFraming` connects that pure layer to a real piped
process fixture: stdout is read as bounded `ByteArray` chunks, the raw output
and private HTTP status trailer are retained, and the observed body chunks are
fed unchanged through the byte-framed validator. This is finite process
evidence, not a proof of network reachability, credential validity, executable
trust, blocked-read interruption, backpressure, cancellation, reconnects, or
deployed Harness equivalence.
`Cordis.DeepSeekStreamHarnessByte` carries that byte witness through a complete streamed Harness
round and fuel-bounded loop: the decoded body reaches the same rich/tool/session continuation,
while raw chunks, status, framing, and exact runner/tool-result evidence remain indexed together.
It does not claim byte-level cancellation, blocked-read interruption, backpressure, reconnects, or
deployed Harness equivalence.
`Cordis.DeepSeekCurlBytePrefix` is the live process-byte prefix boundary below that composition:
bounded stdout reads preserve incomplete raw fragments, decode only complete body lines, feed the
typed prefix before the next read, and classify the private status trailer separately. Its typed
stop policy is checked before each subsequent read; blocked-read interruption, backpressure,
reconnects, and deployed Harness equivalence remain external.
`Cordis.DeepSeekStreamHarnessBytePrefix` carries a completed process-byte prefix witness
through the rich/tool/session continuation and turns a prefix fuel stop into an explicit Harness
stop instead of a fabricated terminal response. The deterministic round and two-round loop retain
the raw/framing/status evidence beside the runner endpoint; blocked-read interruption, backpressure,
reconnects, and deployed Harness equivalence remain external.
`Cordis.DeepSeekCurlBytePrefixTimeout` adds a real `Std.Async.Sleep` deadline around each
blocking process-byte read. A timer winner kills the configured child and returns a typed timeout
that retains the accepted byte-prefix state, raw chunks, pending fragment, stderr, exit observation,
and timeout line; blocked, delayed-prefix, and fast-completion fixtures exercise the three outcomes.
This is local configured-child evidence only: arbitrary descendant cleanup, fairness, backpressure,
provider/executable authenticity, durability, reconnects, and deployed Harness equivalence remain
external.
`Cordis.DeepSeekStreamHarnessBytePrefixTimeout` attaches that timed byte prefix to the existing
dependent streamed conversation runner. Completed prefixes continue through finish, assistant/tool
append, and session indexing; its fuel-bounded multi-round trace carries those exact endpoints,
while timeout, fuel, and cancellation stops remain explicit nonterminal errors rather than fabricated
completions. The adapter does not claim in-flight provider semantics, reconnect behavior, or deployed
asynchronous Harness equivalence.
`Cordis.DeepSeekStreamFailure` preserves the two provider terminal-failure tags
currently decoded by the wire layer (`content_filter` and
`insufficient_system_resource`) as a raw, typed failure certificate. It does
not fabricate a normal rich/session finish and does not claim unmodeled
`error`/`aborted` envelopes.
`Cordis.DeepSeekTerminalOutcome` composes that failure certificate with the
successful text, one-tool, mixed, and finite multi-call rich validators. Its
dependent result retains whichever exact wire/projection/rich certificate was
accepted, while malformed or unsupported bodies retain a typed rejection. This
is a complete-body language dispatcher, not a live transport, retry policy, or
session-message construction theorem.
`Cordis.DeepSeekCurlStream` composes that process boundary with the strict SSE
validator for complete response bodies, preserving typed process, HTTP-status,
and stream errors before any frame is exposed. It deliberately does not claim
incremental reads, backpressure, cancellation, reconnects, or provider-complete
stream assembly.
`Cordis.DeepSeekCurlOutcome` runs the same process/status boundary directly into
the proof-carrying terminal-outcome dispatcher, so a deterministic process can
return either a retained provider failure or any accepted rich certificate. It
keeps process errors, HTTP statuses, and semantic rejection distinct.
`Cordis.DeepSeekOutcomeSession` is the typed next step: it preserves an accepted
provider failure without appending a fabricated assistant message, while finishing
and appending successful text/tool/mixed/multi outcomes through `Runner.append`.
The dispatch result retains the failure or finished witness and the resulting runner;
source-event sequence evidence remains an explicit caller obligation.
`Cordis.DeepSeekOutcomeConversation` carries the same terminal outcomes into the
larger `ConversationRunner`: successful rich assistants append with the model/tool-count
invariant and expose completed provider calls as `FunctionCall` values for the existing
dependent executor. Its execution variant routes those calls through the existing typed
admission/policy/execution path and appends certified tool results, while provider failures
preserve the conversation unchanged. It does not choose retry, persistence, cancellation, or
failure-message policy.
`Cordis.DeepSeekOutcomeTransportLoop` moves that rich continuation across the generic
`Transport` boundary: each round builds a proof-carrying streaming request, validates a
complete terminal body, validates a typed non-success API-error envelope when the status is not
successful, executes dependent tools, and feeds the updated runner into the next request. Transport,
status, API-envelope, semantic, execution, provider-failure, completion, and fuel stops remain
distinct; error authenticity, incremental IO, retry, cancellation, and deployed equivalence remain
outside.
`Cordis.DeepSeekCurlSession` composes a terminal process-backed SSE body with the
accepted rich-stream projections and the append-only session runner, retaining
both the wire certificate and the resulting runner. It uses a terminal text
fixture for this end-to-end path; source-event evidence, local numeric IDs, and
all live/deployed semantics remain explicit caller/runtime boundaries.
`Cordis.DeepSeekHarnessProcess` adds request provenance to that seam: a prepared
request retains the typed Harness source, exact `RequestPlan`, and successful
`buildRequestPlan` equation before process launch, while a successful round retains
the process/wire/semantic response and exact append endpoint. Request construction
and process/response failures remain distinct; this is still a complete-body local
runner bridge, not persistence or deployed-Harness equivalence.
`Cordis.DeepSeekHarnessProcessOutcome` carries the same provenance through the richer
streaming outcome boundary: the typed `stream: true` plan, provider-failure or rich
terminal certificate, dependent tool execution, and final `ConversationRunner` endpoint
remain one indexed result. Request, process/status/stream, and tool-execution failures
remain distinct; this still does not authenticate providers or credentials, interrupt
blocked reads, persist state, execute trusted external tools, or prove deployed equivalence.
`Cordis.DeepSeekHarnessLiveProbe` makes the final credential/runtime handoff explicit without
turning it into a provider theorem: a caller-named environment variable is classified as missing,
empty, or a nonempty `ApiKey`, a complete-mode `PreparedRequest` retains its exact build equation,
and `runFromEnvironment` uses the existing curl adapter and bounded conversation runner. The
deterministic fixture runs the same path with an injected two-response transport; network reachability,
credential validity, process trust, provider obedience, backoff, idempotency, and deployed
Harness equivalence remain outside.
`Cordis.DeepSeekHarnessLiveStreamProbe` carries that handoff into the arbitrary-byte prefix
continuation: the environment credential remains typed and unlogged, the prepared request is
provably streaming, and a configured curl process feeds raw byte chunks through the dependent
stream/session runner. Its fixture retains the byte-prefix witness, one streamed round, model and
session endpoint, and an explicit fuel-exhaustion stop; credential validity, remote reachability,
provider obedience, process trust, blocked-read cancellation, backpressure, retries, persistence,
and deployed Harness equivalence remain outside.
`Cordis.DeepSeekHarnessLocalHttp` adds a credential-safe loopback witness: a one-shot Python
standard-library HTTP server validates the actual curl method, route, authorization header, model,
and complete `stream: false` body before returning the two typed fixture responses. The retained
result links the observed port/request counts and server exit to the prepared request and final
runner endpoint; `runCompleteAppendWithKey` also sends one response through the same real curl
boundary and retains the dependent accepted-response/append certificate in an indexed
`ExtensionRunner`. Remote reachability, TLS, provider authenticity, and deployed equivalence
remain outside.
`Cordis.DeepSeekSchemaLocalHttp` crosses the heterogeneous schema loop through the same real
process/HTTP boundary: a one-shot server checks the two declared tools and complete mode, curl
returns the weather/clock tool body followed by a terminal body, and the retained result links the
prepared plan, one dependent tool round, terminal witness, final model/runner endpoint, request
counts, and server exit. This is local process evidence only; remote reachability, TLS, credential
authenticity, provider obedience, process trust, retries, cancellation, persistence, external
effects, and deployed Harness equivalence remain outside. The fixture checks the exact
`get_weather`/`get_time` declaration order and `tool_choice: "auto"`; a wrong bearer key is
retained as a typed HTTP-status rejection rather than being accepted as a conversation result.
`Cordis.DeepSeekHarnessLocalSse` crosses the corresponding streaming boundary: a one-shot Python
standard-library server validates a typed `stream: true` request, emits the real SSE body in line
chunks, and the real curl process feeds those lines through `DeepSeekCurlIncremental`. The retained
result keeps the prepared streaming plan, delivered lines, reconstructed body, strict wire proof,
finished text projection, and appended runner endpoint together; backpressure, blocked-read
cancellation, reconnects, and deployed stream equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseRetry` adds a real two-attempt loopback reconnect: the first valid
request receives a typed transient HTTP 503, the second receives the flushed SSE body, and
`runWithRetryAndFinish` passes only that accepted body to a caller-supplied text/tool/mixed/multi
finisher; `runWithRetry` remains the text wrapper. Provider backoff, tool idempotency, arbitrary
retry policy, blocked-read cancellation, and deployed retry equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseRetryConversation` lifts that retry boundary over two dependent
conversation rounds. `runTwoRoundsWithFinish` carries the selected finisher through both rounds,
retains each transient failure and accepted append, and rebuilds the second typed request from the
first round's exact session endpoint; the executable variants cover tool, mixed, and multi-call
responses as well as text. Provider backoff, idempotency, arbitrary retry policy, cancellation,
persistence, external effects, and deployed retry/conversation equivalence remain outside.
`Cordis.DeepSeekHarnessPersistenceFileLocalSseRetryConversation` composes the same two dependent
rounds with a real temporary-file archive read. The returned result keeps the `ReadCertificate`
beside the restored runner, retains the exact archive/session equality, and checks the executable
`8 -> 10` progression, one typed 503 per round, and distinct rebuilt request bodies. The file is
removed by `withTempFile`; fsync, stable media, crash recovery, provider authenticity, external
effects, and deployed Harness equivalence remain outside. `RequestProvenance` additionally proves
that the first plan rebuilds from the validated archive session, the second from the first
appended session, and both serialized bodies equal their typed request sources.
`Cordis.DeepSeekHarnessPersistenceFileLocalSseApiErrorRetryConversation` carries the same
temporary-file-origin runner through two real HTTP-429-then-SSE-success rounds. Its dependent
result retains both parsed API-error envelopes, both request-build equations, both valid-request
counts, distinct rebuilt request bodies, clean exits, and the executable `8 -> 10` endpoint. The
file lifetime is scoped to `withTempFile`; fsync, stable media, crash recovery, provider
authenticity, retry policy, external effects, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseTimeout` closes the adjacent in-flight boundary: a loopback server
flushes two valid SSE lines and then stalls, while a real asynchronous timer races the blocking curl
read and retains the exact typed prefix after cleanup. A fast fixture follows the same path to a
completed append. Arbitrary descendant cleanup, fairness, backpressure, credential/TLS
authenticity, provider-complete assembly, reconnect semantics, and deployed cancellation
equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseMultiTool` crosses that same loopback HTTP/SSE boundary into the
dependent multi-tool continuation: the fixture validates `stream: true`, emits two streamed
function calls, and the typed runner allocates both local IDs, executes both admitted calls, and
appends both certified tool results. Provider-complete assembly, backpressure, cancellation,
reconnects, credential/TLS authenticity, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseMultiToolPrefix` lifts the proof-carrying line-prefix runner over
that real loopback server: completion still executes both tools, while a line policy or read
budget retains the exact parsed prefix and returns before dependent dispatch. Byte framing,
backpressure, fairness, blocked-read interruption, reconnects, provider-complete assembly,
authenticity, and deployed equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseMultiToolBytePrefix` drives the same dependent continuation through
the process-byte prefix seam: bounded curl chunks retain raw bytes and incomplete fragments,
completion executes both tools, and a one-read budget returns the typed raw prefix before any
dispatch. Byte-level backpressure, blocked-read interruption, reconnects, provider-complete
assembly, authenticity, and deployed equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseProviderAssemblyTool` closes the provider-complete local seam:
the loopback server validates the typed streaming request, emits the incremental provider tool
body, and real curl lines flow through provider assembly, dependent execution, and certified
session append. Its fixture reaches model `5` with one assembled call; provider obedience,
backpressure, cancellation, reconnects, authenticity, and deployed equivalence remain external.
`Cordis.DeepSeekHarnessLocalSseBytePrefixProviderAssemblyTool` repeats that witness through real
curl byte chunks: the loopback request is validated, the provider body is assembled from the
byte-prefix state, and the dependent execution reaches model `5`. Timeout/fuel/cancellation remain
typed pending states; provider obedience, backpressure, reconnects, authenticity, and deployed
equivalence remain external.
`Cordis.DeepSeekHarnessProcessSchema` carries the registry-derived certificate through the
same process/SSE boundary: the exact streaming plan, validated body, heterogeneous schema step,
and final dependent runner endpoint remain linked, with process, request, and registry-execution
failures distinct. This is still complete-body local evidence, not provider obedience or deployed
Harness equivalence.
`Cordis.DeepSeekHarnessProcessSchemaPrefix` keeps that exact registry-certified streaming plan
attached to the line-oriented prefix result, including fuel-exhausted and cancelled outcomes.
Only a completed `[DONE]` prefix can carry the dependent schema step and runner update; the plan
and stop evidence remain available when dispatch is intentionally deferred.
`Cordis.DeepSeekHarnessProcessSchemaPrefixConversation` lifts that certificate through the
caller-fueled prefix loop: each retained tool round carries its own prepared plan and accepted
prefix, while an attempted round's plan remains visible on fuel exhaustion or cancellation.
`Cordis.DeepSeekCurlIncremental` adds a line-oriented process reader: each body
line is delivered to a typed callback before the private status trailer is
consumed, while the complete reconstructed body still receives strict SSE
validation under an explicit read budget. Byte framing, backpressure,
cancellation, and deployment semantics remain explicit runtime obligations.
`Cordis.DeepSeekCurlIncrementalOutcome` composes that line reader with the typed terminal outcome
sum and local session runner: provider failures retain their exact certificate and unchanged
runner, while successful rich outcomes finish and append. Byte-level framing, backpressure,
cancellation, reconnects, provider-complete assembly, and deployed equivalence remain external.
`Cordis.DeepSeekHarnessLocalSseOutcome` carries that outcome sum across the real loopback HTTP/SSE
boundary: the typed streaming request is checked by the one-shot server, curl lines are retained
with the strict wire certificate, provider failures leave the indexed runner unchanged, and
successful text/tool/mixed/multi outcomes append through the dependent conversation runner. This
remains local process/HTTP evidence; byte framing, backpressure, cancellation, reconnects,
provider obedience, credential/TLS authenticity, and deployed equivalence remain external.
`Cordis.DeepSeekHarnessLocalSseApiError` exercises the other one-shot loopback branch: a valid
streaming request receives a real HTTP 429 with an OpenAI-compatible `{ "error": ... }` body, and
the dependent result retains the exact status/body transport error, parsed `ApiErrorBody`, request
report, and clean server exit. It proves neither error authenticity nor retry/backoff safety.
`Cordis.DeepSeekHarnessLocalSseApiErrorRetry` then drives a bounded two-attempt loopback: the first
valid request is retained as a typed 429/API-error envelope, the second returns strict SSE success,
and only that accepted outcome advances the dependent runner. The request/valid-request counts and
clean process exit are proved; backoff, idempotency, cancellation, reconnect, and deployed retry
semantics remain external.
`Cordis.DeepSeekHarnessLocalSseApiErrorRetryConversation` repeats that certified retry from the
first accepted runner: both rounds retain their own typed 429 envelope, strict success body, and
append endpoint, while the second request is indexed by the first round's actual session. The
fixture proves two-round sequence growth; provider policy, persistence, and deployed equivalence
remain external.
`Cordis.DeepSeekCurlPrefix` connects that process boundary to the proof-carrying
prefix state: each accepted process line updates the typed body/frame state,
and a line policy can stop before the next read while cleanup kills and waits
for the child. The result retains both the raw process body and normalized
prefix state; asynchronous blocked-read cancellation, backpressure, reconnect,
and deployed stream equivalence remain external.
`Cordis.DeepSeekCurlProviderAssemblyIncremental` attaches a second prefix state
to that callback boundary: each accepted line retains the parsed multi-call
state, raw rich chunks, mapped provider chunks, and source-shaped assembler
state before the next read. Terminal completion exposes the exact assembly
certificate; status-separator padding is explicit, and blocked reads,
backpressure, cancellation, credentials, process trust, persistence, external
effects, and deployed equivalence remain external.
`Cordis.DeepSeekCurlProviderAssemblyToolRound` feeds that exact terminal
certificate directly into dependent `FunctionCall` execution and certified
assistant/tool-result session append, without reparsing the completed body.
`Cordis.DeepSeekCurlProviderAssemblyToolPrefix` preserves the provider/tool
prefix on synchronous fuel or cancellation and admits dependent execution only
on the completed branch; blocked-read interruption, backpressure, reconnects,
credentials, process trust, persistence, external effects, and deployed
equivalence remain external.
`Cordis.DeepSeekCurlBytePrefixProviderAssemblyTool` composes the same dependent
round with arbitrary byte chunks and the timer-driven reader: completion carries
the provider, assembly, execution, and session certificates, while fuel,
cancellation, and timeout retain a typed provider prefix instead of fabricating
a terminal response. Byte-level backpressure, reconnects, process/authenticity,
persistence, and deployed equivalence remain external.
`Cordis.DeepSeekCurlProviderAssemblyToolConversation` lifts those certificates
into a bounded `ConversationRunner`: each round is indexed by its prior model,
allocates fresh local call IDs, appends certified tool results, and either stops
on a no-tool response or returns an explicit fuel stop. Its deterministic fixture
reaches `2 → 5 → 8`; deployed conversation equivalence remains external.
`Cordis.DeepSeekCurlPrefixSession` consumes only the completed prefix branch,
projects it through the accepted text/tool/mixed/multi stream validators, and
appends the resulting proof-carrying assistant to the typed session runner.
Fuel and cancellation remain typed stops rather than fabricated responses;
blocked-read interruption, external tool execution, and deployed equivalence
remain external.
`Cordis.DeepSeekAsyncHarness` is the first process-backed asynchronous bridge:
two complete-body text-prefix jobs run in separate cooperative `ContextAsync`
children, and `ContextAsync.race` retains the first typed prefix/session result
while requesting cancellation of the loser. The fixture exercises a real
two-process race and the result has a pure bridge to a terminal phase. The
underlying line-oriented read is not interruptible by that cooperative request,
so blocked-read cancellation, fairness, arbitrary cleanup, and deployed
equivalence remain external.
`Cordis.DeepSeekAsyncStreamHarness` lifts the same race over the complete-body streamed Harness
continuation. Each child can execute a tool-call round and a later text terminal under explicit
fuel, preserving the typed runner, final model, and round witnesses in the winning result. Its
fixture exercises two real processes; synchronous line reads, fairness, cleanup, and deployed
asynchronous equivalence remain external.
`Cordis.DeepSeekAsyncStreamHarnessTimeout` carries that race over the timer-backed arbitrary-byte
prefix adapter. A completed child follows the same dependent tool/session path, while a deadline
retains the exact prefix and projects to a cancelled phase. The fast, timeout, and race fixtures
are real configured processes; task-cancellation delivery, arbitrary cleanup, fairness,
backpressure, reconnects, authenticity, and deployed equivalence remain external.
`Cordis.DeepSeekExternalToolProcess` adds the adjacent external-tool seam: a configured local
process observation retains its exact command configuration, stdout, stderr, exit code, parsed
JSON, and typed decoded result. `AcceptedResult.certified` requires the declared `ToolSpec.post`
proof before constructing a `CertifiedOutcome`; process output alone is never treated as a
certified tool result. Command identity, sandboxing, authentication, exactly-once effects,
cleanup, and deployed Harness equivalence remain external.
`Cordis.DeepSeekExternalToolRound` carries that accepted dependent outcome into the canonical
append-only `Session`: `ExternalToolRound` records a log-only tool call followed by a cited,
model-visible tool result, and proves the exact `nextSeq`, message, and protocol-projection
endpoints. Its result renderer is supplied by the caller; it does not claim provider-specific
wire semantics or deployed Harness equivalence.
`Cordis.DeepSeekAsyncStreamCancellation` carries the typed pre-round cancellation policy through
that process-backed race. Its executable fixture makes one child cancel before dispatch while the
other remains a real streamed continuation; the accepted result retains the unchanged runner,
model, empty completed-round prefix, and cancellation reason. This still does not interrupt a
blocked read or prove fairness, cleanup, or deployed cancellation equivalence.
`Cordis.DeepSeekAsyncStreamRetryCancellation` lifts that cooperative race over retry-aware streamed
jobs. `RetryProcessJob.runWithFinish` and `executeRaceWithFinish` accept a caller-supplied certified
text/tool/mixed/multi finisher, while `run` and `executeRace` remain multi-tool wrappers. The winner
retains an indexed retry trace and dependent final endpoint; text and multi-tool fixtures cover
cancellation-first and delayed-child success-first branches. Blocked-read interruption, fairness,
cleanup, reconnect, and deployed async retry/cancellation equivalence remain external.
`Cordis.DeepSeekRichStream` composes that wire certificate with `RichStream` for
one source-honest text-only subset: exactly one assistant choice at index zero,
terminal usage, and stop/max-token completion. Reasoning, tool-call, extra-choice,
unsupported-finish, missing-usage, and missing-finish cases fail closed with a
typed projection error; the accepted result retains wire, projection, and rich
trace certificates.
`Cordis.DeepSeekRichToolStream` is the separate tool-call companion: it accepts
at most one indexed function call, preserves raw argument fragments and stable
provider identifiers, and projects a terminal `tool_calls` finish into the rich
tool-call block language. Multiple calls, missing IDs/names, reasoning, and
mixed text/tool deltas remain typed rejection cases.
`Cordis.DeepSeekRichMixedStream` adds the composed subset: one choice can
interleave text, reasoning, and one indexed function call across frames, with
first-seen contiguous block indices, stateful tool-id/name repetition, exact
block-end assembly, usage, and a terminal `tool_calls` finish. A frame that
simultaneously presents more than one block kind is rejected because the wire
delta does not carry an ordering for those fields; multiple choices/calls,
provider failure/content-filter finishes, replay metadata, and live transport
remain outside the accepted language.
`Cordis.DeepSeekRichMultiStream` widens only the call cardinality: one choice can
interleave any finite list of indexed function calls, including calls introduced
in the same frame and resumed in later frames. Provider indices are mapped to
contiguous first-seen local block indices, each call retains its own stable
id/name and raw arguments, and all calls close exactly before usage and finish.
Same-frame cross-kind fields, multiple choices, unsupported finishes, replay
metadata, live transport, and deployed assembler completeness remain outside.
`Cordis.DeepSeekProviderAssembler` now models the canonical post-decoder assembly
state separately: it retains source-shaped open blocks and metadata overwrite rules,
then returns an exact state/assembly certificate or a typed unknown-block error.
Image/tool-result schemas, wire decoding, opaque replay JSON, and deployed
TypeScript equivalence remain outside this slice.
`Cordis.DeepSeekAssemblerToolRound` carries that successful assembly into the existing
dependent tool boundary: provider calls become local `FunctionCall` values, the generic
counter configuration executes them with an exact model-indexed certificate, and the
assistant plus certified tool-result messages append to a session surface. Provider-ID
authenticity, external effects, transport, persistence, and deployed equivalence remain
caller obligations.
`Cordis.DeepSeekProviderStreamAssembly` composes the strict multi-call SSE projection with
that source-shaped assembler. It retains both the rich wire certificate and the exact
provider fold certificate, while explicitly rejecting replay metadata and normalizing
structured failure/abort causes to the provider failure vocabulary.
`Cordis.DeepSeekStreamToolRound` carries the same wire-backed result through dependent
execution and appends the assistant/tool-result pair to a session. The executable fixture
starts at model `2` and reaches model `5`; network/authentication, external effects,
persistence, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekScopedStreamToolRound` closes the adjacent scoped-dispatch seam: every
assembled call is resolved in nearest-first scope order, checked against the supplied
automatic/review approval policy, and threaded through an execution trace indexed by the
dependent model before and after each call. The fixture executes weather then clock,
appends one assistant plus two tool-result messages, and separately proves terminal
restriction and explicit-approval rejection. Scope construction, authenticated approval,
external effects, persistence, cancellation, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekProcessStreamToolRound` places the configured process adapter in front of
that exact round. A deterministic local process returns the body and HTTP/SSE certificates,
then the same provider assembly, dependent execution, and session append proofs are reused.
Network reachability, credentials, process trust, incremental delivery, cancellation,
persistence, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekProcessScopedStreamToolRound` carries the scoped round through that complete-body
`IO.Process`/SSE adapter. Its dependent result retains process/status evidence, the strict wire
certificate, scoped approval, model-indexed execution, and the exact session append endpoint;
the local dual-call fixture validates three SSE frames and reaches the same two-call session
endpoint. This remains deterministic local process evidence: network/authentication,
incremental delivery, cancellation, persistence, external effects, and deployed Harness
equivalence remain outside.
`Cordis.DeepSeekProcessScopedConversation` lifts that process-backed scoped round into a finite
dependent conversation. A `Nat → ProcessConfig` supplies the next complete-body process by round
index; each accepted round retains its body, scoped execution, model successor, and session
append, while a no-call body is a typed terminal and exhausted fuel is a separate stop. The
fixture takes two process-backed rounds to a four-message session and separately checks one-step
fuel exhaustion. This remains local complete-body evidence: retries, cancellation, persistence,
external effects, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekProcessScopedRequestConversation` closes request provenance around that loop:
each round builds a typed `stream = true` request from the current session, and the successful
process result is indexed by exactly that `HttpRequest` before scoped dispatch and session append.
The fixture proves that the two round request bodies differ as the session grows, while retaining
the same terminal and fuel-exhaustion distinctions. Live network/provider behavior, retries,
cancellation, persistence, external effects, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekProcessScopedRequestBytePrefixConversation` carries the same exact request index
through arbitrary-byte process reads: raw chunks, pending framing, status, strict SSE completion,
scoped execution, and session append are retained in one dependent round witness. Its fixture
checks two request-distinct completed rounds with multi-chunk evidence and separately exposes a
typed prefix-fuel stop before a body is complete. It remains bounded local process evidence:
network/authentication, executable trust, blocked-read cancellation, backpressure, reconnects,
retries, persistence, external effects, and deployed Harness equivalence remain outside.
`Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation` lifts that same contract to a real
loopback HTTP/SSE server: the server chooses the dual-tool and terminal bodies by request index,
real curl consumes arbitrary byte chunks, and the dependent session runner retains both exact
request/body witnesses. Its fixture also exercises the prefix-fuel stop and validates the server's
request count, request validity, and clean exit; remote reachability, credentials, executable
authenticity, backpressure, reconnects, retries, persistence, external effects, and deployed
Harness equivalence remain outside.
`Cordis.DeepSeekSessionBridge` then accepts only a certified terminal rich view:
it exposes the terminal witness and appends the assistant payload to the local
session surface only when the caller supplies a unique numeric `CallId` assignment
and source-event sequence evidence. This is a local projection seam, not provider-ID
authentication or persistence.
`Cordis.DeepSeekSessionRunner` composes the text, one-tool, mixed, and multi-call validators
into a pure append-only runner: each accepted terminal response advances the
session sequence, allocates local IDs from a proved tool-call count, and
preserves exact message order.
It still leaves transport, cancellation, persistence, and external execution outside
the model.
`Cordis.DeepSeekApiSession` applies the same fail-closed boundary to a decoded
non-streaming response: it admits only a singleton index-zero assistant choice with a
supported terminal reason and nonempty content/tool payload, then appends through the
same local runner with exact sequence and local-ID/count certificates. Extra choices,
unsupported finishes, empty payloads, transport, persistence, provider-ID authentication,
and external execution remain outside.

`Cordis.DeepSeekHarness` closes one bounded typed model-round seam over these pieces: it converts
the canonical session surface into a request plan, runs an explicit transport, admits the decoded
assistant response, and routes each returned function call through generic dependent admission,
policy, and provider execution. Typed replies and failure classes are retained, and
`appendRoundToolResults` encodes successful or failed typed outcomes back into the canonical
session with exact local IDs, source-sequence references, message order, and protocol projection.
`ConversationRunner` carries the resulting session into a subsequent request, and
`executeConversationRound` composes request construction, transport, response acceptance, typed
tool execution, and result append. `runConversation` repeats that certified round under explicit
fuel and returns every round witness together with either a terminal no-tool-call certificate or
an explicit `fuelExhausted` stop; the test suite exercises both completion and exhaustion on a
deterministic two-response loop.
Persistence, credentials, scheduling, and deployed-Harness equivalence remain outside.

`Cordis.DeepSeekHarnessExtensions` generalizes the request-construction boundary from
`Session.noExtensions` to any indexed `ExtensionSchema`, for both complete and streaming request
modes. Log-only custom events remain in the append-only session without entering the model
request, while surface custom events contribute the schema-certified message. A generic assistant
append preserves that schema and proves the exact surface result. The indexed runner now carries
the same sequence/tool-count invariants through an accepted terminal rich response and exercises
that path with the existing process/stream fixture. `SessionExtensionRefinement` adds a bounded
typed-ingress API: a caller-supplied `ExtensionCodec` must construct the dependent kind/payload
sum, while the generic envelope decoder checks the declared tag, safe sequence/time fields,
metadata rejection, and exact append freshness. `ExtensionReplay` and
`ValidatedExtensionLog` recursively retain the raw input order, each dependent event, every
intermediate indexed session, and the final sequence/event-count equations across a multi-event
validation. The heartbeat/banner codec and wrong-tag/ignorable/malformed/stale rejection
fixtures are executable. This does not decode arbitrary JSON or claim provider compatibility,
persistence, transport, or deployed Harness equivalence.

`Cordis.SessionExtensionArchive` composes that dependent replay with the lossless
`SessionEventArchive`: a successful certificate retains the exact archive AST/order and proves
that every record is a required extension. Known core tags and ignorable extensions reject before
semantic replay, so archive retention cannot silently become a typed-session claim.

`Cordis.DeepSeekHarnessExtensionArchive` carries that certificate-gated endpoint into the
schema-indexed `DeepSeekHarnessExtensions.ExtensionRunner`. `restoreRunner` derives the local
tool-call count, preserves exact runner/session equality, and `RequestCertificate` rebuilds a
typed request from that same indexed endpoint. This is a schema-owned in-memory attachment; it
does not claim mixed current-Harness replay, provider compatibility, transport, durable storage,
or deployed Harness equivalence.

`Cordis.DeepSeekHarnessExtensionRequest` adds the request-side tool-schema certificate to that
bridge. `buildCertifiedRequest` requires a validated, duplicate-free `RequestSource` before it
returns the request/build equation tied to the restored indexed session; the fixture proves both
the positive path and duplicate-tool rejection. Provider-side obedience, credentials, transport,
and deployed Harness equivalence remain external.

`Cordis.DeepSeekHarnessExtensionPersistence` carries the same extension-only certificate through
the logical JSONL header, canonical text, UTF-8 bytes, and `DurableIO.Backend` read/replace/append
boundaries. A successful result retains the exact header/raw suffix, restores the indexed runner,
and links a schema-certified request back to that persisted endpoint. Known core rows and
ignorable rows reject; mixed core/extension replay, packed-row persistence, crash repair, fsync,
and deployed persistence equivalence remain external.

`Cordis.DeepSeekHarnessMixedPersistence` makes the next boundary explicit rather than silently
claiming a mixed-schema replay. A schedule-indexed certificate losslessly archives the complete
row stream and independently validates its core projection with `SessionRefinement` and its
dependent extension projection with `SessionExtensionArchive`. The two indexed endpoints and
source AST equations are retained together; extension surface edits, global sequence
normalization, packed rows, and one combined arbitrary-schema session remain external.

`Cordis.DeepSeekHarnessSchemaLift` closes the adjacent type-index seam for the core itself:
`liftSession` transports every validated `Session.noExtensions` event, surface transition,
header snapshot, sequence proof, and protocol projection into any `ExtensionSchema`. Its
`SchemaLiftCertificate` packages the target endpoint and those exact equations, and the
executable example lifts the certified five-event core session into the custom extension
schema. This is core-constructor transport, not extension-row decoding, mixed interleaving,
surface integration for custom events, provider compatibility, or deployed persistence
equivalence.

`Cordis.DeepSeekHarnessMixedReplay` closes the next bounded log-level seam. A tagged schedule
interleaves decoded core rows with extension rows, replays core rows through the existing
`SessionRefinement` certificate, and accepts only custom log-only extension payloads. The
shadow core advances with a phantom log-only clock row, so the certificate proves exact global
sequence growth, surface/header invariance, and equality of the target and shadow protocol
projections. Core-kind extension rows, custom surface rows, malformed extension rows, and
stale sequence numbers reject with typed errors. Arbitrary custom surface interleaving,
provider/persistence/transport compatibility, and deployed Harness equivalence remain
external.

`Cordis.DeepSeekHarnessTransportContract` closes the adjacent injected-transport seam. A prepared
typed request is sent through a `DeepSeekApi.Transport`, successful HTTP status is checked, the
response is decoded once, and `DeepSeekApiSession.acceptValidated` admits that same dependent
response before appending it to the runner. `TransportRound` retains the exact response body,
decoder, acceptance, and session-endpoint equations; fixtures cover a successful tool-call body
and a typed 503 rejection. This is a pure local transport contract: live network reachability,
credential validity, provider obedience, TLS/retry behavior, persistence, and deployed Harness
equivalence remain external.

`Cordis.DeepSeekHarnessTransportToolRound` carries that same single-decoder certificate through
dependent tool execution. It executes the certified response's tool calls without reparsing or
re-admitting the response, then reconstructs the session-runner endpoint with exact sequence and
tool-count equations. The local counter fixture covers one successful tool call and the 503
transport failure remains typed. External tool effects, provider behavior, persistence, retries,
and deployed Harness equivalence remain outside this local injected-transport slice.

`Cordis.DeepSeekHarnessPersistence` now attaches that bounded runner to the logical JSONL
persistence refinement. A successful archive restores a `ConversationRunner` with an exact
equality to the archive's final session, and a proof-carrying request rebuilt from the restored
runner is proven to be the same request rebuilt from the archive session. Filesystem I/O,
compression, torn-tail repair, concurrent writers, and archive authenticity remain outside.

`Cordis.DeepSeekHarnessPersistenceIO` composes that logical attachment with the existing
UTF-8/JSONL `HarnessPersistenceIO.ReadCertificate`. Memory- and temporary-file-backed reads now
restore the runner only after decoded text, parsed rows, persistence validation, and the exact
archive endpoint are all present; the request certificate is linked back to the same read
certificate. Backend acknowledgement is still not fsync, and compression, torn-tail repair,
concurrency, authenticity, and deployed crash recovery remain outside.

The same adapter exposes `replaceAndRestore` and `appendAndRestore`: after a canonical replacement
or a validated append, it re-enters the read certificate and returns the updated typed runner.
The append fixture grows a header into a validated packed-text session; it does not imply atomic
commit, locking, or crash durability.

`Cordis.DeepSeekHarnessPersistenceTransportRound` is the high-level persistence-to-execution
bridge above these two adapters. `executeRestored` builds a complete typed request from the
restored runner, sends it through an injected transport, validates the response exactly once,
passes that same dependent response to `acceptValidated`, executes its admitted tool calls, and
returns a `PersistedRound` carrying the archive/session equality, request-plan certificate,
assistant endpoint, typed executions, and final runner. The memory archive plus local counter
transport exercise this path; live providers, durable commits, retries, cancellation, external
effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekHarnessTransportConversation` composes those single-decoder rounds into a
fuel-bounded dependent trace. Each cons cell is indexed by the preceding runner/model endpoint,
retains the complete round certificate, and either terminates with a certified no-tool response
or preserves an exact trace prefix at fuel exhaustion. The two-response counter fixture exercises
both completion and exhaustion; this remains injected-transport evidence, not live-provider,
durability, retry, cancellation, external-effect, or deployed-Harness equivalence evidence.

`Cordis.DeepSeekHarnessTransportRetry` closes the adjacent bounded-retry seam without introducing
a second decoder. It builds one complete request plan, retains retryable transport/transient-HTTP
failures in `RetryHistory`, validates the successful body once, and feeds that same dependent
response through `acceptValidated` and typed tool execution. The fixture performs a 503-to-200
retry and checks the exact assistant/tool endpoint plus the retry bound. Backoff, idempotency,
cancellation, persistence, external effects, live-provider behavior, and deployed Harness
equivalence remain outside this immediate injected-transport slice.

`Cordis.DeepSeekHarnessTransportRetryConversation` lifts that retry evidence into the same
fuel-bounded dependent trace shape as the non-retrying conversation. Every head retains its
`RetryHistory`, and the next request is indexed by the exact final runner/model endpoint of the
previous retried round. The fixture retries the tool round once, then reaches a no-tool terminal
round; completion and fuel exhaustion remain separate typed stops.

`Cordis.DeepSeekHarnessEndToEnd` composes the byte-backed persistence fixture with that
retry-aware conversation without erasing either dependent index. Its `PersistedRetryRun` keeps the
validated archive runner, final runner/model, retry trace, and typed completion stop in one result;
the executable projection reaches archive `nextSeq = 8`, final `nextSeq = 11`, two rounds, one
transient failure, and model `0`. This remains an in-memory/injected-transport certificate: it
does not claim fsync, live provider reachability, backoff/idempotency, cancellation, external
effects, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessPersistenceProcessOutcome` then attaches the same byte-restored runner to
the repository's `IO.Process` outcome adapter. `PersistedProcessRound` keeps the streaming request
plan, complete process body, rich outcome, dependent execution, and exact final runner endpoint
together; the shell fixture reaches archive `nextSeq = 8`, process endpoint `nextSeq = 10`, and a
streaming body of length `523`. Process/credential trust, incremental delivery, blocked-read
cancellation, durable persistence, external effects, and deployed Harness equivalence remain
explicitly outside.

`Cordis.DeepSeekHarnessPersistenceStreamRetry` extends that actual process boundary to a
two-round continuation from the restored archive runner. The shell fixture emits the two-call
counter stream first, then switches to terminal text after the first tool result appears in the
next serialized request. The dependent trace checks archive `nextSeq = 8`, final `nextSeq = 12`,
two rounds, two first-round tool calls, one attempt, model `0`, and a typed completed stop. This is
still a deterministic local process certificate: provider authenticity, durable recovery,
backoff/idempotency, blocked-read cancellation, external effects, and deployed Harness
equivalence remain outside.

`Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation` adds the pre-round cancellation
decision to that same process-backed continuation. The fixture accepts the first tool round, then
cancels before round one, retaining archive `nextSeq = 8`, prefix endpoint `nextSeq = 11`, one
typed round, two first-round calls, timeout reason, model `0`, and the exact cancellation boundary.
It proves no later request is selected after the decision; blocked-read interruption, process
cleanup, durability, external effects, and deployed cancellation equivalence remain outside.

`Cordis.DeepSeekHarnessPersistenceFileStreamRetryCancellation` reruns that exact dependent path
after writing the archive through the temporary-file `DurableIO.FileBackend`. Its
`runRestoredWithFinish`/`runFixtureWithFinish` APIs carry a caller-supplied certified finisher,
while the legacy fixture uses the multi-tool wrapper. Its executable
projection checks the same `8 -> 11` cancellation prefix and additionally records the
temporary-file storage route. The file is cleaned up by `withTempFile`; fsync, stable media,
crash recovery, in-flight interruption, process cleanup, external effects, and deployed Harness
equivalence remain outside.

`Cordis.DeepSeekHarnessEventFileStreamRetryCancellation` carries the same process-backed
cancellation trace one level closer to the current Harness surface. It writes the supported
current-event JSONL fixture to a temporary file, reads the bytes back, proves byte equality to
the source before restoring the event archive/session, and then runs the restored runner through
the caller-supplied streamed cancellation finisher; the default fixture selects multi-tool. Its
executable summary checks source/read byte equality,
`8 -> 11`, one retained round, two first-round calls, timeout cancellation, and model `0`.
The dependent result also retains a streaming request plan rebuilt from that restored session,
with exact plan-build and serialized-body equations. This is request reconstruction evidence, not
an assertion that the process adapter exposes or authenticates its internally consumed request.
`withTempFile` cleanup is scoped; fsync, stable media, crash recovery, blocked-read interruption,
process cleanup, provider authenticity, external effects, and deployed Harness equivalence remain
outside.
`Cordis.DeepSeekHarnessEventFileLocalSseRetryConversation` takes the same current-event file
restore into the real two-round loopback HTTP/SSE retry conversation. Its dependent result keeps
the event archive/session equality, one typed 503 per round, distinct second-round request body,
and exact `8 -> 10` session growth; `RequestProvenance` proves both the archive-origin first-plan
build and the second build from the first accepted session. The loopback server and temporary file
remain local evidence, not provider authenticity, durable recovery, blocked-read interruption,
or deployed Harness equivalence.

`Cordis.DeepSeekHarnessEventFileProcessSchema` takes that temporary-file event endpoint through
the heterogeneous weather/clock schema process. Its dependent result retains the source/read
bytes, restored archive/session, registry-derived streaming plan, complete body, schema-dispatched
tool step, and exact `8 -> 11` runner endpoint together. It remains local process evidence:
provider obedience, credential authenticity, durable storage, byte framing, cancellation, external
effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekHarnessEventFileLocalSseSchema` takes the same restored event-session endpoint
through two real loopback HTTP/SSE byte-prefix rounds. The fixture uses the explicitly named local
deterministic model while retaining the heterogeneous weather/clock registry, validates both
requests, keeps complete byte-prefix evidence and distinct rebuilt bodies, executes the first
two-tool round, then appends the terminal streamed response at exact `8 -> 12`. The server,
temporary file, model choice, and scoped approval policy are fixture evidence, not provider
obedience, credential authenticity, durable storage, blocked-read cancellation, external effects,
or deployed Harness equivalence.

`Cordis.DeepSeekHarnessEventFileLocalSseSchemaErrors` keeps that file restore and loopback shape but
opts into typed provider-failure results: the weather and clock providers both fail with their exact
messages, the certified `isError` tool results become the next model-visible request, and a terminal
text round completes the same restored session at `8 -> 12`. The two requests, two failed attempts,
failure messages, and completed stop are executable local evidence; provider obedience, credential
authenticity, durable storage, blocked-read cancellation, external effects, and deployed Harness
equivalence remain outside.

`Cordis.DeepSeekHarnessPersistenceStreamBytePrefixTimeout` composes the memory-backed archive
reader with the timed byte-prefix streamed tool round. Its fuel fixture restores archive
`nextSeq = 8`, accepts one real streamed tool round, then stops on caller fuel at final `nextSeq = 10`; its companion process switches to terminal text after the first tool result and completes at
`nextSeq = 11` after two rounds. Both projections retain model `0` and the restored-session
certificate. These are local process and memory-store certificates: durable media, crash recovery,
blocked-read interruption, provider or executable authenticity, cleanup, external effects, and
deployed Harness equivalence remain outside.

`Cordis.DeepSeekHarnessTransportRetryCancellation` composes that indexed injected-transport
trace with the pre-round `CancellationPolicy`. A cancellation-first fixture retains an empty
typed prefix, unchanged runner/model endpoint, round/reason decision, and no issued request; a
non-cancelled fixture retains the 503 retry history and the two-round terminal endpoint.
Blocked-read interruption, provider backoff/idempotency, persistence, external effects, and
deployed Harness retry/cancellation equivalence remain outside.

`Cordis.DeepSeekHarnessEventArchive` attaches the broader current-Harness event vocabulary to
the same runner only when both certificates are present: `SessionEventArchive` must preserve
every envelope exactly and `SessionRefinement` must validate every event semantically. Known
opaque and extension events therefore cause restoration to fail closed rather than being
dropped, while the deterministic tool-message fixture restores a runner and rebuilds its typed
request.

`Cordis.DeepSeekHarnessEventIgnorableProjection` is the narrower archive-side escape hatch for
the source's explicit `ignorable: true` marker. It records positional keep/drop decisions, drops
only opaque ignorable rows, retains supported wire certificates and raw source positions, and
rejects required opaque rows. `Cordis.DeepSeekHarnessEventIgnorableNormalization` continues that
source-authorized path for the supported subset: it renumbers retained rows contiguously, remaps
supported `sourceEventSeqs` and `surfaceOp` references, and validates the resulting local session.
`Cordis.DeepSeekHarnessEventSimulation` then consumes those normalized occurrences through an
occurrence-indexed `SourceReplay`: each retained row carries its exact pre-state `RefinedEvent`,
while a `DecisionLedger` proves the keep/drop partition and the replay preserves source
positions, source sequences, normalized local sequences, protocol erasure, and the final session
projection. This is a finite supported-subset transition simulation, not a complete deployed-
Harness equivalence theorem.
`Cordis.DeepSeekHarnessEventArchiveReplay` packages those two certificates into an archive-aware
replay: its indexed `ArchiveReplay` stores the normalized state trace beside the inductive
keep/drop ledger, retains exact archive rows, and exposes the dropped opaque rows and positions as
first-class projections. The nine-row tool fixture therefore retains all physical rows while
chaining only the eight supported transitions; required opaque rows still fail closed.
`Cordis.DeepSeekHarnessEventIgnorableRunner` then attaches that validated endpoint to a typed
`ConversationRunner` and rebuilds a `ChatRequest` with proof-carrying session/request equalities.
`Cordis.DeepSeekHarnessEventIgnorableTransport` carries the same dependent runner through the
existing process-backed complete-response conversation trace, retaining final runner/model/stop
certificates without upgrading the fixture into provider or deployed-Harness equivalence.
Duplicate physical sequences, missing references, malformed rewrites, and semantic failures reject;
opaque payload semantics, provider authenticity, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekHarnessEventText` is the UTF-8/JSONL ingress for that same certificate-gated
seam. It parses text (or decodes a `ByteArray` first), retains the exact source/line and archive
certificates, restores the typed runner only when every event is semantically supported, and
exposes the same final-session/request equalities. Invalid UTF-8 and opaque/extension events
remain structured failures; no logger, transport, or deployed Harness equivalence is inferred.

`Cordis.DeepSeekHarnessEventPrefix` is the pure incremental target for that ingress. Its
append-only dependent `Cursor` decodes and refines one JSON object at a time, retaining the raw
entry, the `SessionRefinement.State`, and a snoc-shaped intrinsic protocol trace after every
accepted event. A fuel-bounded `run` can stop before the next object for an explicit cooperative
policy; this is not JSONL framing, blocked-read interruption, crash durability, or deployed
Harness equivalence.

`Cordis.DeepSeekHarnessEventProcessPrefix` feeds that cursor from a configured local process one
complete stdout line at a time. The result retains every observed line, the exact cursor endpoint,
exit status, and typed completion/fuel/cancellation stop, with a proof that the consumed count
equals the dependent cursor-entry count. Fuel and policy stops kill and wait for the child before
returning; malformed lines and nonzero exits remain typed failures. This is still line-oriented
local process evidence, not byte framing, blocked-read interruption, executable/provider
authenticity, crash durability, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessEventProcessTimeout` adds a real per-read deadline to that executable
cursor adapter. A Lean `Std.Async.Sleep` races each blocking `stdout.getLine`; when the deadline
wins, the child is killed and waited, and the typed result retains the exact accepted prefix,
observed lines, exit code, stderr, and timeout index. Completion and timeout fixtures exercise both
branches. This proves local timer-driven blocked-read interruption for the configured child only;
it does not prove arbitrary descendant cleanup, fairness, backpressure, provider or executable
authenticity, crash durability, or deployed asynchronous Harness equivalence.

`Cordis.DeepSeekHarnessEventProcessTimeoutRefinement` attaches the already accepted timeout
cursor to an intrinsic `SessionRefinement.ValidatedSequence` without reparsing observed lines.
Its `PrefixValidatedLog` preserves the cursor entries, final state, and exact protocol-projection
equation. The attachment is proof packaging (`noncomputable` because the snoc-to-cons transport
is erased); the executable timeout path and fixtures remain in
`DeepSeekHarnessEventProcessTimeout`. It does not claim raw `decodeEvents` equivalence, JSONL byte
framing, provider authenticity, persistence, or deployed Harness refinement.

`Cordis.DeepSeekHarnessEventProcessOutcome` carries that restored runner through the existing
complete process-backed rich-outcome adapter. Its dependent result keeps the prepared streaming
request, process/response certificate, optional dependent tool execution, final runner endpoint,
raw event archive, restored-session equality, and exact protocol projection together. The caller
still supplies the request source; provider/schema/credential authenticity, blocked-read
cancellation, persistence, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekHarnessEventProcessSchema` closes the corresponding heterogeneous-schema seam.
It keeps the restored text event archive/session certificate attached to the registry-derived
streaming plan, complete process body, schema-dispatched step, and dependent runner endpoint;
text and byte entry points preserve the same index discipline. The executable fixture restores
the eight-row event session, validates the two-tool weather/clock request, and reaches the
`8 -> 11` assistant-plus-tool endpoint. This remains local complete-body process evidence:
provider obedience, credentials, bytes, persistence, cancellation, external effects, and
deployed Harness equivalence remain separate obligations.

`Cordis.LoaderHMR` adds a source-grounded pure slice of the pinned loader/HMR boundary. It models
Definition 74 entry fields, stable-ID keyed configuration reconciliation, Algorithm 8's
accepted/declined/pending fixed-point classification (including unresolved-cycle fallback),
Algorithm 9's declined-boundary stale-entry walk, and Algorithm 10's indexed transactional
invalidate/import/dispose/install/commit or exact rollback sequence. Dynamic imports, filesystem
watches, real fiber lifetimes, cache mutation, and deployed plugin-loader equivalence remain
explicitly outside this finite model.

The same module's `executeRestoredStreamConversation` and byte twin launch the existing
fuel-bounded streamed tool conversation from that restored endpoint. The result retains the
prepared first request, every typed streamed round, final runner/model, and explicit completion or
fuel-exhaustion stop, while the original event archive remains attached. This is still a complete-
body process fixture boundary, not blocked-read cancellation or deployed-runtime equivalence.

`Cordis.DeepSeekHarnessPayloadText` adds the raw payload ledger to that result. Every archived
event retains its payload object and block-tag classification, including reasoning/image blocks,
usage, tool-result `error`/`meta`, and unknown block extensions, while the runner continues to use
only the narrower validated semantic subset. The two views are indexed by the same parsed lines;
provider-owned payloads remain uninterpreted.

`Cordis.DeepSeekHarnessPayloadPersistence` carries the same payload ledger through the logical
JSONL archive, pure `ByteArray` ingress, and executable memory/temporary-file backends. Its
dependent result ties the persisted header/storage split, expanded event list, restored runner,
and raw payload objects to one index, so a persisted request can be rebuilt without losing the
provider-owned payload view. Storage and payload failures remain separate; this is not a durability,
crash-recovery, or deployed-Harness equivalence theorem.

`Cordis.DeepSeekHarnessOpaqueMetadata` is the deliberately narrower exception for
`tool/result.data.error` and `tool/result.data.meta`. It restores the sanitized typed session while
carrying the exact provider/tool JSON values in a parallel metadata ledger, so request rebuilding
still excludes fields whose semantics are not modeled locally.

`Cordis.DeepSeekHarnessMetadataArchive` composes that quarantine with the full
`SessionEventArchive`: the runner uses the sanitized endpoint, while the retained value exposes
the raw envelope ledger and proves that the known opaque `tool/result` event was not dropped.

`Cordis.DeepSeekToolSchema` adds a bounded typed admission layer for DeepSeek function tools.
It accepts only object parameter schemas with primitive property types, optional string
descriptions, duplicate-free required names that are present in the property object, and an
optional boolean `additionalProperties` field. For an admitted tool, `ValidatedArguments`
also checks parsed argument objects for duplicate-free fields, required names, primitive value
kinds, and unknown names when `additionalProperties: false`. Successful certificates retain the
exact source JSON and the original tool list, and certified request construction consumes that
dependent certificate. Nested schemas, unions, constraints, provider extensions, complete
JSON-Schema semantics, provider-side validation, and model/provider compliance remain outside
this deliberately small vocabulary.

`Cordis.DeepSeekGenericBridge` composes that provider-side certificate with an explicit
`SchemaToolBinding` to one generic catalog operation. Its `validateAndAdmit` result retains the
provider certificate, the generic `Config.validate` equality, and an existentially indexed local
call whose request/response types come from the generic catalog. It does not identify provider
schema semantics with `ToolSpec`, execute the call, authenticate the call ID, or claim deployed
Harness equivalence.

`Cordis.DeepSeekSchemaExecution` consumes that combined certificate, applies the existing generic
policy, and dispatches only allowed calls through the committed dependent `View`. The follow-on
`Cordis.DeepSeekSchemaHarness` transport reifies a successful execution as the existing
`DeepSeekHarness.ExecutedTool`, retains the provider certificate, and reuses the exact local
tool-result message, sequence, protocol-projection, and `ConversationRunner` append theorems
without re-executing it.
These are pure local seams: provider obedience, call-ID authenticity, persistence, live external
effects, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekSchemaRound` closes the bounded complete-body response seam for one accepted
assistant choice with exactly one function call. It retains the singleton response/tool-call
witness, dispatches through the schema-aware executor, and appends the result into the existing
conversation runner; zero- and multi-call payloads receive typed structural errors.

`Cordis.DeepSeekSchemaMultiRound` lifts that seam to a nonempty homogeneous list of calls for one
explicit provider/generic binding. Each call is schema-, admission-, policy-, and execution-
certified against the preceding model, and the exact execution list is appended to the runner.
Heterogeneous schema registries, live transport, provider obedience, call-ID authenticity,
persistence, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekSchemaRegistry` removes the homogeneous-binding restriction for a bounded local
registry. Each entry carries its own provider `ToolDefinition` and dependent `SchemaToolBinding`,
name lookup returns the selected entry with its exact name equality, and a heterogeneous weather/
clock fixture proves sequential execution, runner accounting, and typed unknown-name rejection.
This remains a pure registry/runner boundary: live transport, provider obedience, call-ID
authenticity, persistence, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekScopedRegistry` adds the next local routing seam: nearest-first lexical scopes,
same-name shadowing, fail-closed restrictions that do not fall through to a farther declaration,
and an approval ticket retained before the dependent provider view executes. Its weather/clock
fixture exercises automatic versus review routing, restricted and unknown-name rejection, and an
approval rejection with no provider execution. Scope construction, authenticated approval,
provider discovery, persistence, and deployed Harness equivalence remain outside.

`Cordis.DeepSeekScopedStreamToolRound` composes that routing certificate with the strict
provider-stream assembly and the canonical session append path. Its dependent
`ScopedExecutionTrace` retains the resolved entry, approval ticket, parsed call, provider
reply, and model-indexed successor for every call; `appendRound` then converts that trace to
the existing generic execution surface without losing the exact message and sequence proofs.
The executable dual-call fixture reaches the expected model/session endpoint, while restricted
shadowing and denied explicit approval remain typed failures. This is still a finite local
adapter, not live scope construction, policy authentication, external tool execution,
persistence, cancellation, or deployed Harness equivalence.

`Cordis.DeepSeekProcessScopedStreamToolRound` is the process-provenance companion to that
scoped round. `executeWith` runs the configured complete-body process, retains its status and
strict SSE certificate, then feeds the exact body into scoped approval, dependent execution,
and certified session append. The deterministic fixture checks process success, three accepted
frames, two dependent calls, and the final three-message session. Network/authentication,
incremental delivery, cancellation, persistence, external effects, and deployed Harness
equivalence remain outside.

`Cordis.DeepSeekSchemaConversation` attaches that heterogeneous registry to the typed complete-body
DeepSeek transport seam, retaining the request plan, validated response, accepted calls, and
runner endpoint for one round. `Cordis.DeepSeekSchemaConversationLoop` then distinguishes a
certified no-tool terminal response from fuel exhaustion while carrying a finite history of
dependent tool rounds. The loop is still caller-fueled and complete-body; it does not claim
provider obedience, retries, cancellation, persistence, external effects, or deployed Harness
equivalence.

`Cordis.DeepSeekSchemaConversationBytes` closes the raw-byte version of that seam. A successful
result retains the typed complete request, exact UTF-8 request bytes, exact response bytes, decoded
text, response parse/decode certificate, accepted heterogeneous calls, dependent execution batch,
and final runner endpoint together. Invalid UTF-8 and non-2xx responses remain typed before the
schema registry is reached; this is still injected transport and local provider-shaped JSON, not
remote reachability or deployed Harness equivalence.

`Cordis.DeepSeekSchemaTransportRetryCancellation` composes that registry with bounded
single-decoder retry and pre-round cancellation. The successful validated response is reused
directly for terminal admission or heterogeneous weather/clock execution, while the dependent
trace retains retry history and exact runner/model endpoints. The executable fixtures cover
timeout-before-send and 503-to-200 completion; in-flight interruption, backoff/idempotency,
persistence, external effects, and deployed Harness retry/cancellation equivalence remain outside.

`Cordis.DeepSeekSchemaProcessRetryCancellation` runs that same dependent result through the
existing `IO.Process`/`sh` transport adapter. Its deterministic process fixture emits 503, the
heterogeneous weather/clock body, and a terminal no-tool body on successive invocations, so the
retry history and process-backed endpoint are exercised together. This remains local process
evidence: network, credentials, provider obedience, shell trust, in-flight interruption,
backoff/idempotency, persistence, external effects, and deployed equivalence remain outside.

`Cordis.DeepSeekSchemaStreamConversation` carries the same registry certificate through the
complete-body SSE/rich-stream/session boundary: the request is indexed as `stream: true`, a
terminal streamed body is validated before its heterogeneous calls are dispatched, and a
caller-fueled loop preserves the dependent round history or typed exhaustion. The executable
fixtures cover two different registry operations and a text-only terminal body. This remains a
complete-body process adapter; incremental delivery, backpressure, cancellation, reconnects,
provider-complete assembly, call-ID authenticity, persistence, external effects, and deployed
Harness equivalence remain outside.

`Cordis.DeepSeekSchemaStreamPrefixConversation` adds the line-oriented process-prefix boundary for
that same heterogeneous loop. It preserves the exact accepted prefix on read-budget exhaustion or
line cancellation and refuses to dispatch calls until a complete `[DONE]` rich/session certificate
exists. The boundary remains line-oriented and does not claim blocked-read interruption,
backpressure, reconnects, provider-complete assembly, call-ID authenticity, persistence, external
effects, or deployed Harness equivalence.

`Cordis.DeepSeekSchemaStreamErrors` adds the explicit heterogeneous failure policy on top of that
streamed boundary. A failed registry provider retains its entry-specific schema, generic
admission, policy, exact error, and unchanged-model evidence, then becomes an opt-in `isError`
tool result; a later streamed text response can continue only from a request source with
`errorToolResults := .include`. The fixture proves two dependent failures and the subsequent
terminal request. This remains complete-body and fixture-backed; retry, cancellation, persistence,
external effects, and deployed error semantics remain outside.

`Cordis.DeepSeekStreamFailure` preserves the wire-level terminal failures that the strict decoder
already recognizes: `content_filter` and `insufficient_system_resource`. It retains the typed
prefix, terminal raw frame, singleton choice/reason, and optional terminal usage certificate, while
refusing ordinary stop/length/tool finishes. It intentionally does not turn a provider failure
into a `RichStream` finish or session message, and does not claim support for unmodeled `error` or
`aborted` envelopes, live delivery, retry, cancellation, or deployed provider semantics.

`Cordis.DeepSeekTerminalOutcome` is the adjacent complete-body sum over that failure language and
the four successful rich languages. It tries provider-failure classification first, then text,
one-tool, mixed, and multi-call projections, preserving the selected dependent certificate and
typed wire/projection rejection. It does not broaden any accepted language or imply that a failure
is a normal session message.

`Cordis.DeepSeekHarnessErrors` is the explicit opt-in continuation policy for provider failures.
`ErrorToolResultPolicy.reject` is the default fail-closed request behavior; selecting `.include`
lets a proof-carrying `ProviderFailedTool` become an `isError` tool-result message while retaining
the parsed call, admission, policy, exact provider error, and model-stability evidence. The
recoverable round path is still a complete-body pure adapter: it does not claim retries,
cancellation, persistence, asynchronous delivery, or deployed-Harness equivalence. The separate
`Cordis.DeepSeekHarnessRetry` layer adds an explicit bounded immediate-retry policy for transport
and transient HTTP failures, retaining the prior `ClientError` history and reusing the exact
request plan; it does not claim provider backoff, idempotency, cancellation, or deployed retry
semantics.

`Cordis.DeepSeekHarnessCancellation` adds a typed pre-round cancellation boundary. A caller policy
is checked before each complete request round, and cancellation retains the unchanged runner/model
endpoint plus the completed-round prefix. It does not interrupt an already running process, HTTP
request, stream reader, or external tool, and it does not claim deployed Harness equivalence.

`Cordis.DeepSeekStreamHarness` is the corresponding complete-body process-backed
tool-stream continuation: it finishes a validated rich tool stream, assigns local
numeric call IDs, routes every streamed call through the same dependent admission,
policy, and provider path, and appends certified tool results to the generic
`ConversationRunner`. Both the one-call entry point and the typed
`executeConversationMultiStreamRound` path are exercised by deterministic process
fixtures, including a two-call terminal stream whose executable fixture rejects a
request unless its serialized body contains `"stream":true`. The round builder
retains a proof of that source flag. `runConversationMultiStream` then
reuses those round certificates under explicit fuel, stopping on a text-only terminal
response or returning typed exhaustion. Its returned runner is suitable for a
subsequent request or fuel-bounded round. Incremental delivery, cancellation,
backpressure, reconnects, provider-complete assembly, and deployed equivalence remain
outside this adapter.

`Cordis.DeepSeekStreamHarnessCancellation` adds the same typed pre-round cancellation
decision to that streamed loop. It retains the completed streamed prefix and unchanged
runner/model endpoint when cancellation is selected; it does not interrupt an in-flight
process read or claim deployed cancellation semantics.

`Cordis.DeepSeekStreamHarnessPrefix` moves the same continuation over the line-oriented
process-prefix adapter. It returns either a completed multi-call tool round or the exact parsed
prefix with a typed line-cancellation/read-budget stop; byte framing, blocked-read interruption,
and deployed stream semantics remain external.

`Cordis.DeepSeekStreamHarnessByte` is the complete-body byte-backed companion: bounded stdout
chunks are framed and status-checked before the decoded body enters the same dependent streamed
tool/session continuation. Its round and fuel-bounded loop retain the byte/framing witness beside
the runner endpoint; byte-level cancellation, blocked-read interruption, backpressure, reconnect,
and deployed semantics remain external.

`Cordis.DeepSeekStreamHarnessErrors` lifts the explicit recoverable provider-failure policy over
the complete-body streamed round. A failed streamed call retains its parsed/admission/policy/
provider evidence, keeps the model unchanged, and appends an `isError` tool result that a later
request may consume when `RequestSource.errorToolResults := .include`. Its fuel-bounded streamed
loop retains the failed round and a later text terminal under that explicit policy; incremental
recovery, retries, persistence, and deployed error semantics remain external.

`Cordis.DeepSeekStreamHarnessRetry` adds the corresponding bounded complete-body retry seam for
streamed rounds. `executeWithRetryAndFinish` accepts a caller-supplied text/tool/mixed/multi
finisher, while `executeConversationStreamRound` carries the same dependent finisher into the
assistant/tool continuation; the existing multi-tool entry points remain wrappers. An explicit
policy may retry process and transient-HTTP failures, while stream framing, semantic response,
and tool failures remain terminal. Backoff, idempotency, cancellation, persistence, and deployed
retry semantics remain external.

`Cordis.DeepSeekStreamHarnessRetryConversation` composes those process-backed retry rounds into
an indexed, fuel-bounded trace. `runWithFinish` carries the selected finisher through each round;
every head retains the accepted streamed body, ordered retry history, dependent assistant/tool
endpoint, and exact final runner/model, while `run` remains the multi-tool wrapper. Direct retry
fixtures cover text/tool/mixed/multi semantic raw counts, and the dependent loop covers text plus
the admitted counter tool. Backoff, idempotency, cancellation of blocked reads, persistence,
reconnects, external effects, and deployed retry equivalence remain external.

`Cordis.DeepSeekStreamHarnessRetryCancellation` composes that indexed retry trace with the
existing pre-round cancellation policy. `runWithFinish` carries a caller-supplied text/tool/mixed/multi
finisher through the cancellation boundary, while `run` remains the multi-tool wrapper. A cancellation
stop retains the exact accepted retry-aware prefix, unchanged runner/model endpoint, round/reason
decision, and typed retry histories inside each accepted head. Direct text completion and tool
cancellation fixtures exercise the two finisher paths. It is not an in-flight process/read
cancellation or a deployed Harness cancellation equivalence claim.

The next paper layer is explicit rather than assumed. `Cordis.OperationalEquivalence` models
Definition 34's heterogeneous finite tests and proves the generator-level coarsest relation of
Lemma 35, while a compiled counterexample shows that same-word tests do not imply the stronger
paired-inverse law. `Cordis.QuotientEffect` implements Definitions 36–37 and the
finite-composition core of Lemma 38; `Cordis.CoeffectQuotient` proves that Definition 24
operations retain related successors, inverses, and outcomes when lifted through Definition 33.
`Cordis.SessionRefinement` statefully decodes a source-shaped current-Harness session prefix and
jointly validates every supported event in both the rich Session and intrinsic Protocol layers.
Its admitted subset includes restricted `request/header` snapshots, typed `request/context` route
metadata, whole-list `todo/write` snapshots, empty `session/end-seed` markers, text/reasoning
index-zero `assistant/chunk` records, and surface-message text/reasoning/image blocks plus complete assistant
`tool-call`
blocks in `user/message` and `assistant/message` events. Complete assistant calls allocate fresh local
numeric IDs in the same binding state reused by later `tool/call` and `tool/result` events;
source IDs/provider metadata remain in the refinement state, while the local projection retains
assistant text and typed tool calls. Reasoning and image blocks remain wire-visible but are omitted from that
smaller local projection. Header wire records retain provider/model, optional system
text, selected tool schemas, and header reason; route context, todo items, and the empty seed marker
are retained as typed log-only payloads. Unsupported header configuration, unknown todo statuses,
nonempty seed payloads, and unsupported chunk kinds fail closed; reasoning and image surface blocks
remain wire-visible and are omitted from the local text/tool projection.
`Cordis.SessionRefinementSurfaceCodec` supplies the opposite direction for a deliberately narrow
source-shaped subset: text-only user messages, text/reasoning/tagged-raw-image/complete-tool-call
assistant messages, and singleton-text tool results encode to canonical ASTs, preserve safe integers,
assistant usage, source-event references, replacement ranges, call IDs, raw tool-call arguments, and
exact `isError` values, and compose with the existing JSONL text/UTF-8 byte parser. Its successful
`decode_encode` and list-level text/byte theorems are certificates for this local subset only;
the metadata-aware tool-result emitter can retain quarantined `error`/`meta` JSON before
sanitization, while image schema semantics, provider metadata semantics, unsupported surface
operations, and complete event-union coverage remain external or fail-closed.
`Cordis.SessionOpaqueMetadata` adds a lossless middle boundary for the two provider/tool-owned
fields that the semantic subset does not interpret: it sanitizes only `tool/result.data.error`
and `tool/result.data.meta` before validation, retains their exact source JSON in an ordered
certificate, and proves that the existing Session/Protocol projection is unchanged. It does not
assign semantics to either field or claim provider/tool schema equivalence.
`Cordis.ParallelHarness` adds a bounded proof-carrying scheduler slice: a certified parallel
window evaluates in an arbitrary supplied order, commits results in model order, can be followed
by an explicitly exclusive barrier, and can drain pending work into synthetic cancellation
reports without changing the model. This remains a pure Lean scheduler model, not `IO`
concurrency or a refinement of the TypeScript scheduler.
`Cordis.ParallelSchedule` composes an arbitrary finite sequence of those certified windows and
exclusive barriers, preserving the canonical endpoint, exact composed recovery, model-order
reports, and global task-ID uniqueness. It remains a pure finite schedule certificate: wall-clock
overlap, worker IO, promise races, fairness, and deployed scheduler equivalence are external.
`Cordis.AsyncHarness` adds the next bounded state-machine slice: indexed fibers move through
pending/running/terminal phases under typed start, complete, fail, and cancel transitions;
successful finite traces expose completion order separately from declaration order, and a
drained schedule certificate proves the canonical pure endpoint for any certified permutation.
This is still a pure proof-carrying model: it has no live task handles, wall-clock fairness,
promise cancellation delivery, cleanup, or TypeScript/deployed Harness refinement.
`Cordis.DurableSettlement` adds the next persistence-facing boundary: an intrinsically indexed
append-only frame log, collision-free list transcript, supplied crash-prefix certificate, exact
prefix recovery, and typed resume. It is a pure torn-prefix model, not a filesystem, `fsync`,
cryptographic, multiprocess, or external exactly-once theorem.
`Cordis.DurableCodec` adds the JSON-AST edge before that typed log: raw frame encoding, entry-code
decoding, and a strict dependent prefix scanner that rejects malformed, torn, unknown, or
non-contiguous frames before constructing a `Log`.
`Cordis.DurableBytes` adds a separate pure binary edge over `List UInt8`: a unary-length frame
format, a checked numeric `RawFrame` payload codec, counted prefix decoding, and a byte-prefix
bridge that exposes discarded torn suffix bytes before delegating to the typed scanner. This is
an explicit Lean binary format, not TypeScript JSON-byte compatibility or filesystem I/O.
`Cordis.DurableIO` adds a deliberately narrow stateful adapter: typed append plans can be
acknowledged by an in-memory store or a real temporary/file backend, and reads return the
counted byte-prefix certificate plus any discarded suffix. The adapter is executable evidence
at the `IO` boundary, not a proof of `fsync`, crash atomicity, authentication, process
coordination, or external-effect exactly-once behavior.

`Cordis.Transformation` supplies Definition 17 generated transformation monoids, Lemma 18
closure results, and full Definition 19 effect independence, including inverse-yield stability
and a bridge to the existing batch/schedule certificates. On top of that,
`Cordis.OperationIndependence` proves full Definition 39 for total exact operations, a finite
partial-operation Theorem 40 at distinct keys, and Definition 41's outcome-dependent computation
interpreter with exact recovery. Full Theorem 42 remains unclaimed: its missing branch-indexed
closure law is named `MediatedClosure` rather than replaced by an adjacent-swap result.

`Cordis.Removal` then proves Theorem 20's target/prefix/suffix removal equations, retains every
later original/omitted application state and inverse equality, and proves Corollary 21 for every
permutation of the exact yielded inverse functions. `Cordis.GlobalRegistry` starts the global
calculus without recreating the negative recursion: fibers store opaque iterator/undo codes in a
birth-ranked registry. It implements the data portions of Definitions 43–46 and 49, proves active
provider/value and target uniqueness, and proves insert/retire/remove plus orchestration traces
preserve a strengthened well-formedness invariant and an acyclic parent relation.

`Cordis.MediatedIndependence` makes the Theorem 42 frontier type-correct: realized paths retain
every heterogeneous branch decision, while a finite universal-equivalence cell proves exact
representatives require `ExactRepresentativeCoherence`. `Cordis.MediatedTheorem` then fixes the
partial-domain formulation: it compares the two composite orders directly, retains conditional
yielded-inverse stability, and constructively swaps arbitrary finite outcome-selected trees. The
result is an exact finite whole-run analogue and observational consequence, not the paper's full
transformation-monoid Definition 19/Theorem 42; the older `PairwiseOverlapComplete` API is
kernel-refuted by a partial computation versus unit.

`Cordis.PartialTransformation` closes that distinction inside the finite partial semantics. A
computation generates its Kleisli partial forward map and every actual totalized yielded inverse;
the least identity/composition closure is the partial Definition 17 monoid. Pairwise operation
overlap proves all cross-closure transformations commute and every successful foreign
transformation preserves the other computation's domain and complete yielded inverse. The
whole-run theorem follows from this full certificate, while a kernel counterexample proves the
converse false. This is the exact finite partial/Kleisli analogue, not the paper's literal total or
quotient setting.

`Cordis.ObservationalPartialTransformation` descends that complete closure theorem through the
Definition 33 context relation. Related partial maps must agree on `Option` definedness for every
pair of related representatives and return related successors when defined. The existing
`CoeffectAt` domain, successor, inverse, and outcome laws prove that every adaptive computation
generator respects the relation—including identical heterogeneous outcomes and branch choices—so
exact pairwise overlap yields full observational closure independence. A kernel counterexample
shows exact commutation alone is insufficient when a map leaks representation-private state.

`Cordis.TotalQuotientIndependence` adds the next proof layer without silently filling undefined
cases: `TotalComputation` carries a success-at-every-context certificate, and the module proves
that its finite total forward/inverse words are exact images of the existing closure. It derives
quotient commutation, yield stability, exact recovery, and an admissible observational effect.
This is a finite totalized specialization, not the paper's unrestricted total/quotient theorem.

`Cordis.DomainTotalQuotientIndependence` keeps the more realistic partial evaluator and makes
the totality boundary explicit in the type: `DomainTotalComputation` supplies an invariant
domain, `DomainMap` carries totality and preservation on that domain, and `Closure` transports
those witnesses through forward, yielded-inverse, and composition generators. The existing
finite observational independence theorem is recovered on that certified domain, with an
executable counter/label fixture that succeeds on the domain and remains partial outside it.
This still does not prove the paper's unrestricted total/quotient theorem.

`Cordis.GlobalDynamics` then interprets opaque iterator/undo codes outside stored state, validates ordinary and
registration steps with recovery/confinement/well-formedness evidence, and provides a total fueled
Definition 52 runner whose exhaustion retains the exact next code.

`Cordis.GlobalLifecycle` adds the seven lifecycle rule names as eight exact-endpoint constructors,
splitting aborting and landing L-Divert. Each landing retains a proof that `executeOne` returned its
exact dependent step, while L-Unload alone consumes the accumulated recovery program. Every edge
and finite lifecycle trace preserves the strengthened registry invariant. General recovery after
arbitrary interleavings remains the named `RecoveryAdmission` obligation; the heterogeneous
example discharges it concretely for an explicit Begin/Iter/Finish, O-Retire, Leave/Unload path.

`Cordis.GlobalCalculus` then folds the three orchestration rules and those lifecycle edges into one
exact-endpoint relation with the paper's ten rule names. It preserves the acted-on name `n` for
every step, keeps Equation 51 state maps separate from edit footprints, and proves actual
installation-status changes occur only at L-Begin/L-Unload. Its `FromEmpty` witness runs one
heterogeneous insert/activate/retire/unload/remove trace from an empty registry back to an empty
registry with the ambient observation restored. This is finite trace preservation, not Theorem 59.

`Cordis.GlobalTraceFacts` audits the first global trace lemma against that relation. All non-unload
rules preserve every pre-existing foreign fiber exactly; unload needs the separate
`RecoveryConfinement` law for foreign tables/control and actor static fields. A kernel countermodel
proves bare `RecoveryAdmission` is insufficient even when both endpoints are well formed. Aligned
trace records derive name-specific episode opening at L-Begin and closing at L-Unload while other
fibers may cross their own boundaries. New-entry and retirement-write provenance remain explicit
gaps for opaque undo codes.

`Cordis.GlobalTemporal` reifies each exact step's paper-style state map as a partial off-source
function. Iterator-backed maps may fail away from their indexed source, so totalization,
edit-invisibility, relation preservation, per-step recovery commutation, owner inverse stability,
and mixed-trace reordering remain explicit certificates. Under a separately supplied
`EffectEquiv`, those laws prove finite interleaved and terminal unload recovery. Countermodels show
that an exact landing need not totalize, arbitrary `Dynamics.equivalence` can be vacuous, and
`RecoveryConfinement` alone does not imply temporal recovery.

`Cordis.GlobalIteratorIndependence` gives an oracle-specific finite executable partial/Kleisli
analogue of paper Definition 60. A `Program` fixes an owner, root iterator code, dynamics
interpreter, and registration oracle; `Reach` follows only continuations actually yielded by
successful `executeOne` calls. Its closure is generated by reachable partial forward maps and the
totalized inverses actually yielded by those executions. `Independent` requires cross-closure
commutation plus stability of the yielded inverse, continuation code, and
ordinary-versus-registration source kind, including the registered component. Families are indexed
by occurrences, so two distinct occurrences of the same program require genuine
self-independence. Finite reach and continuation bounds are separate caller-supplied certificate
types; independence and the temporal bridge neither require nor derive them.

The separate observational version uses `GlobalTemporal.EffectEquiv`; it is not an identification
with the paper's displayed rule relation `≃`. `ProgramRespects` is supplied separately for each
program's reachable forward maps; only yielded inverse respect follows from
`EffectEquiv.applyUndo_respects`. Given that observational independence, a provenance-carrying
`YieldedAccumulator`, an owner-and-closure-membership `StepMapMember`, and an already supplied
`TotalStepMap` for each foreign trace step, `perStepCommutes_of_generated` discharges only
`GlobalTemporal.PerStepCommutes`. It does not construct totalization, the owner's inverse law, a
mixed-trace reorder certificate, Theorem 61, or Corollary 62.

`Cordis.GlobalTransposition` derives the next bounded consequences without upgrading them to paper
Lemma 71. `independent_forward_diamond` uses both yield-stability directions to construct the two
off-axis raw iterator executions and closure commutation to prove their exact common endpoint.
`TotalProgramStep` combines explicit `TotalStepMap` evidence with acted-owner-aware closure
membership. Given `Independent`, two such maps commute exactly; given `ObservationalIndependent`,
they commute under its supplied `EffectEquiv`. The observational certificate still contains the
separately supplied `ProgramRespects` obligations and is not derived from `EffectEquiv` alone.

Lifecycle phases store syntactic undo codes, so `LifecycleYieldAgrees` separately requires exact
`UndoCode` equality; it implies semantic `YieldAgrees`, but the converse is kernel-refuted by a
finite dynamics that interprets distinct Boolean undo codes as the same identity function. Distinct
`setPhase` edits commute structurally, while `ForeignPhaseCompatibility` names the fixed-program,
exact-code, foreign-control law still needed to move a raw diamond through lifecycle edits; this
module constructs no inhabitant. No lifecycle transition is transposed, and Lemmas 68, 70–72,
Theorem 61, and Corollary 62 remain outside this slice.

`Cordis.GlobalForeignPhase` then factors that missing law into three noncircular,
program-scoped contracts. `ForeignPhaseReadable` admits distinct phase edits to
`Dynamics.run_read_confined`; `OrdinaryForeignPhaseFrame` strengthens its related successor to the
exact point-update equation; and `RegistrationOracleForeignPhaseFrame` preserves the selected
child. `ForeignPhaseCompatibility.of_read_frames` derives exact strong-yield compatibility in both
branches, deriving the registration successor equation from freshness and insertion/phase
commutation rather than assuming it.

`PhaseFramedExecution` packages one such moved run, while `phase_framed_diamond` combines two
compatibility certificates, the raw independent diamond, retained post-raw fiber lookups, and
distinct phase updates into one exact framed raw endpoint. Three kernel models prove the premises
independent: full iterator independence need not give foreign-phase compatibility, readable
ordinary runs need not satisfy an exact successor frame, and an identical readable registration
request need not be accepted by the same state-dependent oracle after the edit. Supplied phases are
not claimed to be lifecycle-rule outputs; no `Transition`, guard/target theorem, or Lemma 71 result
is constructed.

`Cordis.GlobalLandingTransposition` is the first actual lifecycle-transition lift, deliberately
restricted to the four L-Iter/L-Finish pairs. `ForwardLifecycleIndependent` retains semantic
`Independent` and adds only exact syntactic yield stability under the two cross-forward maps; a
separate kernel model proves semantic independence plus both phase-frame laws do not imply this
representation-strengthened premise. `LandingProgramWitness` ties each existential landing's exact
step to the fixed program oracle without equating dependent oracle carriers.

Program-aligned landing activations construct their real Iter/Finish phase and `Transition`.
Foreign source fibers and already-valid target views are preserved from raw confinement and source
well-formedness. `landing_activation_diamond` reframes the off-axis raw steps from a common landing
template, composes exact cross-forward and foreign-phase yield agreements, and constructs both
lifecycle orders with one exact shared final state. The executable example is an Iter/Finish pair;
separate models prove common-source applicability and landing/program provenance cannot be
dropped. That module alone covers no Begin-containing pair.

`Cordis.GlobalActivationTransposition` adds a fixed-program `ProgramActivation` for L-Begin and the
existing program-aligned Iter/Finish landings. Begin retains the equation between the program root
and catalog entry; every activation derives its exact endpoint and actual lifecycle `Transition`.
Exact foreign lookup plus a non-active source actor preserve already-valid positive targets under
well-formedness. Fixed-program execution determinism then proves both endpoint and rule uniqueness.

`program_activation_diamond` covers all nine common-source Begin/Iter/Finish pairs. Its
branch-indexed law record consumes no iterator law for Begin/Begin, only the landing program's
foreign-phase compatibility for a mixed pair, and `ForwardLifecycleIndependent` plus both
compatibilities for a landing pair. `transpose_program_activations` additionally accepts an actual
normal-order second activation, identifies its endpoint by fixed-program uniqueness, and derives the
swapped actual lifecycle transition. This is the bounded local content of Lemma 71(1), not the
paper theorem verbatim: execution remains partial and oracle-specific, exact undo syntax and
common-source applicability are explicit. The literal clause (2), episode assignment, stored-trace
rewriting, and global confluence remain outside that activation-only module.

`Cordis.GlobalActivationOrchestrationTransposition` then audits clause (2) itself and finds its
literal side condition insufficient. A registering activation may create a distinct parent that
enables the following O-Insert, and two otherwise legal insertion orders allocate opposite
per-fiber birth ranks; the current exact state and `RuleRelated` both observe that difference.
Kernel countermodels certify both failures.

The corrected theorem classifies the exact child registered by an activation, requires no
registration at all before O-Insert, and requires only child/actor inequality before O-Retire or
O-Remove. Begin exchanges structurally. A landing consumes one occurrence-specific
`ExactExecutionFrame` containing the moved fixed-oracle execution, exact lifecycle-visible yield,
and raw orchestration-replay square. `transpose_activation_orchestration` reconstructs the earlier
legal orchestration occurrence with the same kind, actor, and replay function, rebuilds the moved
activation, and reaches the supplied normal final state exactly. Registering activation/O-Insert is
excluded in the birth-ranked representative. Separate models prove that nonregistration,
well-formedness, and registration safety do not imply the required frame.

`Cordis.GlobalProgress` next audits Definition 65/Theorem 66. It kernel-separates configured
program progress from the permissive raw relation: a fixed oracle may reject registration while an
unrelated oracle can still witness a raw Landing. More strongly, a Boolean name carrier with both
names occupied yields a well-formed nonquiescent state with no possible registration admission and
no lifecycle transition under any oracle. Finite names therefore do not imply fresh-name or
admission totality.

The positive theorem is conditional and state-local. `FinitePrecedenceRank` gives the
provider-to-consumer order a finite increasing rank; exact reloading occurrences carry one
root-aligned reachable program and landing-or-raise witness; unrelied unloading occurrences carry
recovery readiness; and `CommittedProvisionSound` turns reliance into a precedence edge.
`lifecycle_progress` covers every phase, selecting a maximal-rank unloading fiber to close the
relied-provider case. It proves only that some exact lifecycle rule applies. The quantitative
`(K + 4)` bound, target-turn finiteness, maximal-execution termination, trace-wide program
assignment, and fairness remain unproved.

`Cordis.GlobalProgressTermination` adds the narrow quantitative bridge without hiding that gap. A
supplied strict natural-valued potential gives a telescoping budget for every exact dependent
lifecycle trace; an initial bound of `K + 4` therefore yields a trace-length bound and rules out
nonempty cycles. The potential is an explicit authority, not something derived from
`lifecycle_progress`, so target-turn finiteness, maximal termination, fairness, support, and
trace-wide program assignment remain unclaimed.

`Cordis.GlobalProgressRun` now connects those two layers with a finite dependent runner. A supplied
`ProgressAuthority` re-establishes the local lifecycle laws at each well-formed endpoint, while a
supplied `StepPotential` strictly decreases along every exact unified step. `runFuel` retains the
intrinsic lifecycle trace, endpoint well-formedness, and either a quiescent stop or a certified
full-fuel boundary; `certifiedRun_quiescent` rules out the latter when fuel is the initial
potential. This is a conditional finite runner, not a derivation of the authority/potential and
not maximal Theorem 66 termination, fairness, target-turn accounting, or trace-wide program
assignment.

`Cordis.GlobalProgressAssignment` adds the explicit provenance bridge that the runner deliberately
does not infer. An `AssignedProgressAuthority` supplies a `StepProgramAssignment` for each
lifecycle transition; `assignTrace` then reconstructs a dependent `TraceProgramAssignment` for
every runner trace, while preserving the runner's endpoint and quiescence proofs. Fixed programs,
roots, oracles, and reachability remain supplied evidence rather than consequences of a raw
transition.

`Cordis.GlobalPaperProgressReplay` composes an assigned finite progress run with a caller-supplied
`ForwardAssignedStepSimulation`. `replayRun` replays the exact source trace from a related
well-formed peer and preserves source endpoint/length/stop evidence, transported assignment, and
exact rule/actor projections. The simulator and lifecycle provenance are still supplied; no
automatic lifecycle bisimulation, maximal execution, or unrestricted Theorem 66 is claimed.

`Cordis.EffectContext` now covers the paper's function-level effect-context tower through
Definitions 1–3, 6, and 8–12 and Theorems 4–5, 7, and 10–16. It carries a state-indexed inverse
inside `WitnessedEffect`, proves twisted tracking/recovery and effect composition, exposes the
exact next-level lifted-inverse formula, and gives an indexed finite `Run` whose selected
inverses recover the initial raw context in reverse order. It remains a finite exact slice;
arbitrary interleaving, quotient independence, and deployed Harness equivalence remain explicit
boundaries.

`Cordis.GlobalSupport` then kernel-refutes the printed Lemma 68 inference. A legal `FromEmpty`
two-O-Insert trace has well-founded provider precedence and an acyclic birth-ranked parent relation,
yet their union contains a two-cycle; the Definition 67 equations admit both the empty and
present-name solutions. `SupportOrder` therefore requires well-foundedness of the combined relation
directly. Under that authority, `supported` is defined by genuine edge-indexed well-founded
recursion and is proved the unique solution.

The corrected quiescent theorem is also conditional. `TotalOnProvisionAt` supplies the missing
active-table direction of Definition 69, `NoFailedFiber` excludes error-inactive states, and
`ActiveParentClosed` records the parent/registration provenance absent from arbitrary non-root
O-Insert. With those laws, `support_eq_active` proves the unique support predicate equals active
names. Independent models show that both combined well-foundedness and active-parent closure are
necessary. This does not derive either law from `FromEmpty`, prove component-wide totality, or
establish deletion/confluence.

`Cordis.GlobalTraceRewrite` turns the two corrected local transposition results into actual
rewrites of intrinsic dependent traces. `AdjacentOccurrence` retains an exact before/window/after
decomposition, and `ExactAdjacentSwap` can be spliced only when the replacement pair has the same
indexed source and endpoint. Rule and actor projections are proved to differ by exactly one
adjacent permutation. Membership certificates locate both original selected records; the rewritten
trace separately retains intrinsic alignment, list-length invariants, and final well-formedness.

The module also supplies occurrence-indexed `ProgramOccurrence` and recursive
`TraceProgramAssignment` evidence. Both activation/activation and activation/orchestration
adapters consume the actual stored pair and return assignments for the moved steps;
`AssignedAdjacentOccurrence.rewrittenAssignment` combines those with the retained contexts to
reconstruct the complete rewritten ledger. A nonempty-prefix example rewrites
`[O-Insert, L-Begin, O-Insert]` to `[O-Insert, O-Insert, L-Begin]` with actors `[0, 1, 0]`.
Registering activation/O-Insert, birth-erased endpoints, suffix simulation, arbitrary
normalization, deletion, and confluence remain outside this exact-state layer.

`Cordis.GlobalDeletion` adds the corrected bounded deletion substrate. `DeletionReplay` consumes an
intrinsic source trace positionally: a keep supplies one real replayed dependent step and transports
its program assignment, while a drop leaves the shadow state fixed and forces the recursive tail
to re-establish the chosen relation. The generated shadow trace is intrinsically adjacent; its
rules and actors are sublists of the source, its final state is related, and its complete assignment
ledger is derived rather than assumed.

The substantive exact theorem removes a finite family of entries already proved vestigial and
replays an arbitrary safe foreign orchestration suffix with the same rule, actor, and full edit
template at every position. Separately, a positive keep/drop certificate filters
`[O-Remove(1), O-Retire(0)]` to `[O-Retire(0)]` with decisions `[drop, keep]`. Countermodels prove
why this is not paper Lemma 72: a surviving insertion may require a deleted parent, removing a
newly allocated entry does not restore `nextBirth`, fixed names can receive different birth ranks, and a
removed bare name can be redrawn. General lifecycle episode deletion, a birth-erased suffix
simulation, canonical form, and confluence remain absent.

`Cordis.GlobalPaperRelation` removes the allocator mismatch from the observation language itself.
Relative to current `RuleRelated`, `PaperFiberControl` erases only `Fiber.birth` and the state-level
`nextBirth` clock while retaining component, parent, retirement, and the complete dependent phase.
The full-domain, outside-deleted, and combined effect/outside-control relations are proved Setoids;
the stricter current rule relation weakens into the new full relation.

This relation has operational content. Between two independently well-formed full-domain related
states, all three orchestration constructors reconstruct real peer steps in both directions, with
related successors and actual `RetainedStep` assignment transport. From a well-formed source
carrying a finite `VestigialNames` certificate, removal is `DeletionRelated` and safe foreign
orchestration traces replay directionally to the erased shadow through a genuine
`DeletionReplay`. Opposite insertion-order endpoints are now
related while remaining unequal and not current-`RuleRelated`. Outside-deleted reverse replay and
lifecycle simulation are still false in general; a clock-sensitive L-DivertAbort model proves no
assigned lifecycle simulation bundle exists for its instance.

`Cordis.GlobalPaperTraceSimulation` and `Cordis.GlobalPaperTraceDeletion` retain those relation
certificates at the intrinsic trace level, including assigned-step transport, forward replay,
backward replay, and positional keep/drop replay. The simulation layer also has forward and
backward orchestration-only replay constructors, plus occurrence-specific forward/backward
lifecycle evidence and a concrete leave→unload replay witness. Those lifecycle declarations
consume exact per-occurrence matches; they do not fabricate a global lifecycle bundle. `Cordis.GlobalPaperTraceNormalization` composes a finite connected list of
supplied adjacent-rewrite witnesses: its terminal trace remains birth-erased related to the
source endpoint and has permuted rule and actor lists. Its executable example composes one
activation/orchestration rewrite and then a connected reverse link, exposing the one-link
ledger `[O-Insert, O-Insert, L-Begin]` with actors `[0, 1, 0]` and the two-link cycle's return
ledger `[O-Insert, L-Begin, O-Insert]` with actors `[0, 0, 1]`. This is a proof-carrying
rewrite-chain surface, not an automatic normalizer; strategy, canonical form, termination,
Lemma 72, and confluence remain outside.

`Cordis.GlobalPaperShiftedLifecycle` adds a deliberately non-reflexive lifecycle replay witness:
the peer shifts only `nextBirth`, rebuilds the dependent `L-Leave` and `L-Unload` transitions,
and transports their assigned trace while preserving exact rules, actors, endpoint
well-formedness, and birth-erased relatedness. It is a concrete allocator-clock replay, not a
global lifecycle bisimulation; the clock-sensitive unmatched-transition countermodel remains
in force.

`Cordis.GlobalPaperTraceNormalizer` adds a terminating, dependent normalizer under an explicit
authority: the caller supplies normal-form decidability, a rewrite witness for every non-normal
package, and a strictly decreasing natural measure. The resulting finite chain preserves the
birth-erased endpoint relation and rule/actor permutations; it does not derive a strategy,
canonical form, or the paper's global normalization/confluence theorems.

`Cordis.GlobalPaperTraceConfluence` now supplies the generic conditional metatheory that the
normalizer can consume: a decreasing rewrite system with local joinability has a global join, and
irreducible endpoints are unique. `AuthorityLinked` reconstructs the authority-selected path from
the existing dependent `normalizeFuel` result, and `normalize_results_unique` applies the theorem
to actual `TracePackage` endpoints under a `ConfluentAuthority`. Its Boolean branch witness
exercises two genuinely different reduction orders. This is still conditional rather than a
CORDIS-specific confluence proof: the current dynamics do not provide the required local joins,
decreasing measure, or canonical strategy, so the paper's Theorem 73 remains open.

`Cordis.GlobalPaperTraceScopedConfluence` is the indexed follow-up: a finite package family is a
type, each selected rewrite stores exact source/target equations, and the dependent normalizer
reconstructs an independent rewrite path before applying endpoint uniqueness. Its nonempty
activation/orchestration fixture proves one real link and checks the rewritten rule/actor ledgers;
it remains a supplied finite certificate rather than a derived global strategy or Theorem 73.

`Cordis.GlobalRelations` supplies the two deliberately incomparable global observation candidates
that the temporal layer had left abstract. Rule observation keeps the derived dependent context up
to key-indexed value setoids and keeps registry domain/control exactly; effect observation keeps
ambient state and normalized per-name tables exactly while forgetting lifecycle control. Both are
proved setoids, and a named undo-respect law bridges the effect candidate to `GlobalTemporal`.
Executable separations show neither candidate, nor an arbitrary dynamics setoid, can silently stand
in for the others. Rule bisimulation remains an explicit obligation, so Lemma 55 is not claimed.

`Cordis.GlobalRuleInvariance` discharges the well-formed orchestration portion of that obligation.
Every O-Insert, O-Retire, or O-Remove step at either of two `RuleRelated` states reconstructs a
same-kind, same-name peer step with exact dependent endpoints, well-formed successors, and another
`RuleRelated` pair. `FiberControl` transports only component, parent, birth, retirement, and phase;
private tables may remain unequal. A parity/length example exercises unequal related Nat/String
values. Full lifecycle Lemma 55 is not derivable: an ambient-sensitive abort policy distinguishes
well-formed `RuleRelated` states, and iterator, oracle, landing, and recovery transport laws are
also absent.

`Cordis.GlobalRuleObservations` proves the assumption-free lifecycle observation layer shared by
the remaining rules. Across well-formed `RuleRelated` states it transports the same active-provider
names, dependent target views, committed resolutions, reliance/non-reliance, exact phase patterns,
quiescence, and the begin/reloading/leave/divert/unload structural guards. Matched active fibers'
tables are related, not equal. A deliberate seam remains at L-Finish: a reloading fiber's private
table was unobserved before the landing makes it active, so future landing transport must relate
the yielded tables explicitly. Examples separate rule observation from both effect observation and
ambient equality.

`Cordis.GlobalLifecycleBisimulation` then proves all eight lifecycle constructors—and the unified
ten-rule relation—under four noncircular external contracts: landing transport, exact iterator
error transport, inertia respect, and recovery-admission transport. Matched transitions retain
their exact dependent endpoints, rule, actor, endpoint validity, and successor `RuleRelated`.
Only L-Finish consumes the landing's related-table clause, because it exposes a previously private
reloading table; a well-formed 7-versus-8 parity countermodel proves that clause necessary. This is
a conditional well-formed Lemma 55 analogue, not a theorem derived from base `Dynamics` and not an
inhabitant of the raw no-well-formedness `RuleBisimulation` API.

`Cordis.GlobalNameAction` replaces the earlier opaque equivariance placeholder with an executable
bijection-based action. It fixes catalog keys/components, acts lawfully on ambient data, dependent
values, errors, iterator/external-undo codes, and derives the action on tables, committed provider
names, retire undos, phases, fibers, registries, and states. Identity, composition, inverse, lookup,
and exact state-inverse laws are proved at every layer; strengthened `WellFormed` is invariant; and
all three orchestration constructors commute exactly with renaming in both directions. A
nontrivial Boolean swap exercises parents, views, undo names, values, and an acted retirement. A
constant noninjective old-style action still satisfies the prior single run equation, formally
showing why that placeholder was insufficient. Lifecycle/dynamics equivariance remains separate.

`Cordis.GlobalNameLifecycle` closes that conditional boundary for well-formed states. Three
primitive contracts—exact dynamics action, inertia action, and fixed catalog entry codes—derive
the action on results, child-conjugated registration continuations, error-aware run outputs,
registration admissions, a conjugated oracle, iterator steps, `executeOne`, landings, accumulated
recovery, target views, reliance, all eight lifecycle transitions, and all ten unified rules.
Backward equivariance is derived from inverse actions. A nonidentity L-Raise renames its owner and
stored error exactly; entry-code, success-only error mapping, and constant-error counterexamples
show why the primitive laws matter. The theorem is a conditional fixed-catalog finite Lemma 56
analogue, not an unconditional property of arbitrary `Dynamics`.

`Cordis.GlobalVestigial` proves the effect-observation sentence of Lemma 57 exactly and then
mechanizes the corrected orchestration fragment. Removing a retired, successful-inactive,
empty-table, childless entry is `EffectRelated`; safe foreign insert/retire/remove steps form exact
removal squares in both directions. The types expose two omissions in the pinned paper: forward
O-Insert may adopt the vestigial entry as parent, and backward O-Remove may delete the vestigial
entry's parent. The latter is a genuine third backward exception beyond the paper's draw-name and
provision-conflict cases. Well-formed kernel models certify all four exceptions. Iterator,
lifecycle, oracle, inertia, and recovery insensitivity remain outside this corrected slice.

`Cordis.GlobalSpatial` proves the strongest spatial episode fragment supported by the exact trace
API. Well-formed L-Begin targets satisfy every declared dependency; an explicit shared-master
`NestedEpisodes` decomposition yields strict provider/consumer opening and closing order; and a
consumer's installed committed resolution persists through its boundary-free interior, blocking
the provider's L-Unload. Provider table values remain constant only under a named per-record
confinement premise, which sufficient confinement discharges for foreign actors but not same-owner
iterator edits. The T64 result classifies one reloading lifecycle step as target-stable,
diverting, or raising; it does not assert maximal episodes, eventual close, or recovery.

The included demo is deterministic and credential-free. Starting from counter
state `2`, it reads, increments by `3` under limit `10`, reads again, and rejects
an unknown `counter_destroy` call. It finishes at counter state `5`, protocol
state `ready 1`, with four model-ordered call records and a replay-certified
12-event structural log. Its canonical rich session contains 15 events and six
model-visible messages, and a `ModelRequest` reconstructs its exact latest
header, message surface, and log length.

Every generic runner carries
`RecordChain initialModel nextCall records model leases (callBoundaries log)`.
The chain begins with the initial model, an empty lease pool, no records, and no
tool boundaries. Each successor record starts at both the preceding model and
lease endpoints. Its ID is the next session ID, and the projected log satisfies
`callBoundaries log = recordBoundaries records`.

The reusable `GenericSessionHarness` wrapper carries the same proof for any
`GenericHarness.Config`: request headers, user/assistant surface messages, tool
calls, tool results, and lifecycle boundaries are appended to one rich
`Session` while its structural projection remains exactly the generic runner
log. `RunnerState.prepareRequestStep` stops at an empty-pending step after
recording the exact request header and surface prompts, and its indexed
certificate proves that `Session.mkRequest` is present before an external
dispatch. `attachCompletedDispatch_modelRequest` proves that an accepted
call/result append preserves request reconstructibility. `Examples.DependentChoiceSession`
exercises that wrapper with the non-counter dependent `Bool → (String | Nat)`
catalog; the counter wrapper remains the original regression fixture. Rich
surface placement is type-indexed: request headers and chunks cannot carry a
surface mutation, while user, assistant, and tool-result events must. A model
request cannot substitute a history or header assembled independently of that
log.

`Cordis.DeepSeekSessionRequest` closes the next seam: a `Session.ModelRequest`
can feed a DeepSeek `ChatRequest` only alongside an explicit `SourceAgreement`
for the model, system prompt, and encoded tool schemas. The prepared request
retains the successful builder equation and can be lifted to an exact raw
`RequestPlan`, or to complete/streaming plans whose `stream` flag is proved by
the type. Optional DeepSeek controls remain adapter policy; provider behavior,
parser-backed schema validity, credentials, and remote transport are not
inferred here. Complete plans can be exercised through an injected transport,
and streaming plans through the existing local SSE process adapter, but these
remain local transport evidence rather than deployed-provider proof. The
complete-plan path can also fail-closed-admit its response and append it to the
same schema-indexed runner, retaining body, header, sequence, local-ID,
tool-count, and request-reconstruction certificates.

`Cordis.DeepSeekSessionRequestBytes` carries the same append path across the raw-byte
boundary. `buildCompleteBytePlan` retains the exact canonical UTF-8 request body, while
`executeCompleteBytesAndAppend` uses an injected byte transport and returns a dependent
raw-body/decoded-text/accepted-response/runner-endpoint witness. This is byte-level local
evidence only: invalid UTF-8, HTTP, transport, and semantic response errors stay typed,
and live networking, credentials, provider behavior, persistence, and deployed equivalence
remain external.

`Cordis.DeepSeekSessionRequestStreaming` closes the corresponding indexed streaming seam with
a caller-supplied certified finisher. `executeStreamingAndAppend` retains the mode-indexed
streaming plan, strict wire frames, finished rich response, and exact `ExtensionRunner` endpoint;
`executeStreamingTextAndAppend`, `executeStreamingToolAndAppend`,
`executeStreamingMixedAndAppend`, and `executeStreamingMultiAndAppend` select the existing
finishers. Unsupported, malformed, incomplete, and provider-failure responses remain typed
errors; the process configuration is injected local evidence, not live-provider or
deployed-Harness equivalence.

`Cordis.DeepSeekHarnessLocalSseIndexed` composes that request-indexed surface with the real
one-shot loopback HTTP/SSE fixture. `runWithKey` retains the local request/response and wire
evidence while adding exact equalities for the indexed streaming plan and
`ExtensionRunner.appendFinished`; `Example.run` exercises one validated request, three delivered
frames, and the `2 -> 3` session endpoint. The fixture does not prove that its returned body
matches the supplied process argument, nor remote reachability, TLS, credentials, provider
authenticity, persistence, blocked-read behavior, reconnects, or deployed Harness equivalence.

`Cordis.DeepSeekHarnessLocalSseIndexedLoop` composes that same seam for two rounds. Its
`runWithFinish` carries a caller-supplied text/tool/mixed/multi finisher through both rounds; the
first indexed append rebuilds the second dependent `Session.ModelRequest` and `PreparedRequest`,
while `TwoRoundResult` retains both real loopback responses and proves the final
`ExtensionRunner` sequence is the initial sequence plus two. The executable fixture checks all
four finishers and their expected frame/tool-count projections. This remains local process/HTTP
evidence only, with provider authenticity, persistence, reconnects, blocked-read behavior, and
deployed Harness equivalence outside the claim.

There is no public generic runner event emitter. Non-tool events use a private
emitter that requires proof that the event is not a call boundary. A private
settlement transition validates and appends one adjacent call/result pair and
its record in the same successful immutable-state update. That is atomicity in
the pure `Except` transition only; it is not a filesystem, database,
multi-process, or external exactly-once guarantee.

This is a small Lean kernel inspired by CORDIS and the DeepSeek Harness. It is
not a full port of the CORDIS paper, an asynchronous scheduler, a live model
client, or a drop-in replacement for the TypeScript harness.

See the [manual implementation guide](docs/IMPLEMENTATION_GUIDE.md) to rebuild
the reviewed `0.1.0` kernel in dependency order. See the
[`0.2` specification](docs/V0_2_SPEC.md) for the refreshed current-Harness
source boundary, new obligations, and deliberately unfinished production work.

## Prerequisite

The exact required toolchain is recorded in `lean-toolchain`:

```text
leanprover/lean4:v4.33.0
```

Install [elan](https://lean-lang.org/lean4/doc/quickstart.html), Lean's official
toolchain manager. Running `lake` in this checkout selects that exact Lean
release; no additional Lake dependencies are declared.

## Five verified commands

Run these from the repository root:

```bash
# Build the library, static rejection target, and both default executables.
lake build

# Compile the expected-failure API attacks directly.
lake lean Cordis/NegativeTests.lean

# Run the executable adversarial and integration suite.
lake exe cordis_tests

# Run the deterministic counter harness.
lake exe cordis_demo

# Elaborate the axiom audit in Lake's module context and print every dependency.
lake lean Cordis/AxiomAudit.lean
```

The static rejection module uses guarded expected compiler errors. It is a
separate default library target and is intentionally not imported into the
native test executable. GitHub Actions runs these five commands plus a
warnings-as-errors build, an exact toolchain check, a self-testing lexical
hygiene scan, and an allow-list check over the axiom report; see
[the workflow](.github/workflows/ci.yml) and
[the checker](scripts/check_lean_hygiene.py).

The test command exits successfully after printing:

```text
CORDIS adversarial and integration tests passed
```

Among its joint-invariant checks, the suite compares
`callBoundaries state.log` with `recordBoundaries state.records` and type-checks
`LeasesThreaded .empty state.records state.leases` for both the demo and a
multi-turn run.

The demo prints:

```text
CORDIS Lean 0.1.0 proof-carrying harness
final modeled counter: 5
final protocol state: Cordis.RuntimeState.ready 1
replay-certified events: 12
canonical rich-session events: 15
derived model-visible messages: 6
request reconstructible from log: true
call 0 counter_read: Cordis.GenericHarness.CallOutcome.succeeded; policy-dispatches=1; encoded-result
call 1 counter_increment: Cordis.GenericHarness.CallOutcome.succeeded; policy-dispatches=1; encoded-result
call 2 counter_read: Cordis.GenericHarness.CallOutcome.succeeded; policy-dispatches=1; encoded-result
call 3 counter_destroy: Cordis.GenericHarness.CallOutcome.admissionRejected (Cordis.AdmissionError.unknownTool "counter_destroy"); policy-dispatches=0; no-result
```

The axiom audit prints one line per selected theorem. The current results use
only Lean's standard logical principles where needed: `propext`,
`Classical.choice`, and `Quot.sound`; several constructive theorems report no
axioms. The project defines no custom axioms and contains no proof
placeholders.

The finite external conversation layer also exposes `runCapturingErrors`: it
retains an accepted indexed trace prefix when a later local process fails to
spawn or decode, while the original `run` API preserves the typed
`Except ObservationError` boundary.

## What is verified

| Guarantee                                                                                                                                                                                                                                                   | Lean evidence                                                                                                                                                                                                                                                                                                                                                                                                 | Exact boundary                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Encoded values decode to the original value                                                                                                                                                                                                                 | `Codec.decode_encode`                                                                                                                                                                                                                                                                                                                                                                                         | Starts and ends at the `Lean.Json` AST; byte parsing, rendering, and external schema compliance are excluded.                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| Sequential modeled effects recover their indexed predecessor in LIFO order                                                                                                                                                                                  | `Effect.seq_recovers`, `UndoStack.recover_after`                                                                                                                                                                                                                                                                                                                                                              | One-sided recovery of the modeled state, not arbitrary external side effects.                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| Distinct dependent-registry updates commute and recover                                                                                                                                                                                                     | `Registry.setEffect_commute`, `Registry.setEffect_recovers`                                                                                                                                                                                                                                                                                                                                                   | Requires distinct operation keys; it does not isolate native code.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| A committed capability view resolves only declared operations to present providers                                                                                                                                                                          | `View.provider_present` and the `View.resolve` type                                                                                                                                                                                                                                                                                                                                                           | The view is supplied constructively; arbitrary host/plugin code can bypass it unless separately isolated.                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| A strongly certified two-call pure batch has the same applied effect and model-ordered outputs in either allowed evaluation order                                                                                                                           | `CertifiedTwoBatch.execute_order_irrelevant`, `execute_outputs_in_model_order`, `execute_recovers`                                                                                                                                                                                                                                                                                                            | Exactly two pure calls with explicit recovery and result-stability evidence; no tasks, `IO`, or asynchronous execution.                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| Raw tool calls fail closed before becoming dependent calls                                                                                                                                                                                                  | `ToolWire.validate`, `ToolWire.validate_declared`                                                                                                                                                                                                                                                                                                                                                             | Input is already a `Lean.Json` AST; name resolution, declaration, decoding, contract, and capability checks are covered.                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| Success and failure results round-trip through request-dependent tagged codecs                                                                                                                                                                              | `ToolWire.decode_encoded_result`, `decode_encoded_certified_result`                                                                                                                                                                                                                                                                                                                                           | Covers the exact typed `Except` result, not transport or storage.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| Typed session events cannot produce orphan results or close a step with pending calls                                                                                                                                                                       | `Event`, `Event.noOrphanResult`                                                                                                                                                                                                                                                                                                                                                                               | Applies to the finite indexed protocol model.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| A validated raw event list reconstructs an intrinsic typed trace and replays to its exact terminal state                                                                                                                                                    | `ValidatedTrace`, `ValidatedTrace.replays`, `replayRaw_eraseTrace`                                                                                                                                                                                                                                                                                                                                            | Finite in-memory logs; durable storage integrity is outside the theorem.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| A bounded assistant text stream cannot accept post-finish chunks or a second finish, and reconstructs exact concatenated text                                                                                                                               | `Stream.noChunkAfterFinished`, `Stream.replayRaw_eraseTrace`, `Stream.replay_completeTrace`                                                                                                                                                                                                                                                                                                                   | Text chunks only; tool payload parsing and network streaming are excluded.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| One explicitly threaded exact-subject policy trace dispatches at most once, and a completed trace dispatches exactly once                                                                                                                                   | `SubjectPolicyTrace.dispatchCount_le_one`, `dispatchCount_to_completed`                                                                                                                                                                                                                                                                                                                                       | A pure trace property, not global exactly-once execution across duplicated processes.                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| Lifecycle unload recovers the modeled activation origin and requires the dependency guard                                                                                                                                                                   | `Lifecycle.Transition.unload_recovers`, `unload_rejects_relied`                                                                                                                                                                                                                                                                                                                                               | Finite synchronous lifecycle model; no fairness or hot-module acquisition.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| Harness records jointly thread model and lease endpoints from the initial model and empty lease pool, and use session-wide IDs `0 .. nextCall - 1`                                                                                                          | `Harness.RecordChain`, `length_eq_nextCall`, `ids_eq_range`, `RecordChain.leases_threaded`, `RunnerState.leases_threaded`                                                                                                                                                                                                                                                                                     | The delivered counter runner commits sequentially in model order.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| The tool-boundary projection of the log is exactly the records' ordered call/result pairs                                                                                                                                                                   | `RecordChain.boundaries_eq_records`, `RunnerState.callBoundaries_eq_records`                                                                                                                                                                                                                                                                                                                                  | Equality concerns finite in-memory lists; it does not prove persistence integrity.                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| A call event, matching result event, record, model endpoint, and lease endpoint appear together in one successful runner settlement                                                                                                                         | The private settlement transition, indexed `RecordChain.snoc`, and absence of a public generic emitter                                                                                                                                                                                                                                                                                                        | Atomic only as one pure immutable `Except` result; not durable or globally exactly-once.                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| The runner's stored protocol state agrees with replaying its complete in-memory log                                                                                                                                                                         | `RunnerState.replayProof`, `Harness.replayRaw_append`                                                                                                                                                                                                                                                                                                                                                         | The runner remains in-memory; the separate `DurableSettlement` module supplies a typed crash-prefix model, not actual persistence or crash repair.                                                                                                                                                                                                                                                                                                                                                                                                       |
| A typed append plan can be written/read through memory or a filesystem backend, and a counted prefix exposes a discarded torn suffix                                                                                                                        | `DurableIO.AppendPlan`, `DurableIO.readAndRecover`, `DurableIO.Example.memoryResume`, `memoryTornPrefix`, `fileResume`                                                                                                                                                                                                                                                                                        | Executable adapter evidence only: `IO` acknowledgement is not `fsync`, crash atomicity, authentication, process coordination, or external-effect exactly-once behavior.                                                                                                                                                                                                                                                                                                                                                                                  |
| Catalog, wire, needs, registry, view, model-dependent grants, and exact-call policy cannot drift across the reusable runner                                                                                                                                 | `GenericHarness.Config`, `Runner cfg phase`, `DispatchResult`                                                                                                                                                                                                                                                                                                                                                 | Pure sequential execution; external adapters still require refinement evidence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| A reusable generic runner can carry a rich append-only `Session`, prepare an indexed request-ready handoff, preserve request reconstruction across an accepted call/result append, and erase that session exactly to the runner log                         | `GenericSessionHarness.RunnerState.prepareRequestStep`, `prepareRequestStep_modelRequest`, `attachCompletedDispatch_modelRequest`, `protocolProjection_eq_log`, `protocolProjection_replays`, `Examples.DependentChoiceSession`                                                                                                                                                                               | Pure finite in-memory bridge; external transport, persistence, scheduling, and TypeScript/deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                                                                   |
| Admission rejection and admitted policy rejection dispatch zero times; a completed exact-call trace dispatches once and restores its lease pool                                                                                                             | `CallEvidence.*dispatchCount*`, `completed_terminal_lease_absent`, `leases_restored`                                                                                                                                                                                                                                                                                                                          | One explicitly threaded pure runner, not a global cross-worker guarantee.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| A non-counter Boolean request definitionally selects `Nat` or `String`, and policy rejects the exact string branch before provider execution                                                                                                                | `Examples.DependentChoice.request_selects_exact_output_type` and its allowed/rejected run theorems                                                                                                                                                                                                                                                                                                            | Deterministic in-memory example over a structured `Workspace`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| Rich surface intent is selected by event visibility; replacement retains a nonempty exact shadow interval with unique earlier covering sources                                                                                                              | `Session.EventIntent`, `SurfaceTransition.replace`, `SurfaceTransition.replace_shadowed`, `SurfaceTransition.replace_covers`                                                                                                                                                                                                                                                                                  | Intrinsic path plus proof-producing validation after kind-specific payload parsing; byte/JSON parsing remains external.                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| Rich session sequence numbers are contiguous; surface nodes are unique earlier events; request header and messages are exact log projections                                                                                                                | `ValidLog.*`, `ModelRequest.reconstructible`, `mkRequest`                                                                                                                                                                                                                                                                                                                                                     | In-memory typed events; timestamps, JSON bytes, durability, resume, and fork are excluded.                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| The counter wrapper's canonical rich session erases exactly to the replay-certified structural protocol log                                                                                                                                                 | `RunnerState.protocolProjection_eq_log`, `protocolProjection_replays`                                                                                                                                                                                                                                                                                                                                         | The rich vocabulary is a finite core subset, not full TypeScript session equivalence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| Parsed typed rich events validate into exact append/range/provenance/uniqueness witnesses and finite `ValidLog` suffixes                                                                                                                                    | `SessionValidation.validateAppend`, `ValidatedAppend`, `ValidatedSuffix`, `ValidatedLog`, `ValidatedAppend.applies`, `ValidatedLog.replays`                                                                                                                                                                                                                                                                   | Begins after kind-specific payload parsing; bytes, persistence, and unknown required extension kinds remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| Interleaved text, reasoning, and raw tool-call deltas retain first-seen order, exact block-end assembly, terminal discipline, and aligned metadata                                                                                                          | `RichStream.Event`, `ValidatedTrace`, `replayRaw_eraseTrace`, `AlignedMetadata`                                                                                                                                                                                                                                                                                                                               | Images, tool-result blocks, transport, and metadata pruning are deferred.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Any finite permutation of a certified commuting pure-effect family denotes the same complete effect and recovery function                                                                                                                                   | `Schedule.runEffects_eq_of_perm`, `CertifiedSchedule.*`                                                                                                                                                                                                                                                                                                                                                       | Semantic sequential reordering only; no tasks, failures, outputs, fairness, or wall-clock overlap.                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| A certified finite parallel window may evaluate in a supplied task order, commit model-order results, run one exclusive barrier afterward, and drain pending tasks without model effects                                                                    | `ParallelHarness.ParallelWindow`, `WindowOutcome`, `Plan`, `drain.*`                                                                                                                                                                                                                                                                                                                                          | Bounded proof-carrying scheduler analogue for the pinned Harness tool-call shape.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | Task IDs, result permutations, effect commutation, barrier behavior, and cancellation are certificate fields; no `IO`, wall-clock concurrency, fairness, failure racing, or TypeScript refinement.                                            |
| An arbitrary finite pure schedule of certified windows and exclusive barriers preserves endpoint/recovery equality, model-order reports, and globally unique task IDs                                                                                       | `ParallelSchedule.Plan`, `Plan.execute`, `Plan.execute_reports_ids_nodup`, `Plan.execute_recovers`                                                                                                                                                                                                                                                                                                            | Finite multi-segment extension of the proof-carrying scheduler boundary.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | The schedule is a pure fold over supplied certificates; no `IO`, wall-clock overlap, promise races, fairness, or TypeScript scheduler refinement.                                                                                             |
| Indexed fibers can start, complete, fail, or cancel; a successful finite race records completion order separately and a drained permutation reaches the canonical pure endpoint                                                                             | `AsyncHarness.Step`, `Trace.model_eq_runEffects`, `SuccessfulSchedule.final_model_eq_canonical`, `exampleRaceTrace`, `exampleCancelStep`                                                                                                                                                                                                                                                                      | Bounded proof-carrying async/fiber state-machine analogue for the Harness lifecycle.                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | No live task handles, wall-clock fairness, cancellation delivery/cleanup, external IO, or deployed Harness refinement is proved.                                                                                                              |
| A finite dependent coeffect context enforces typed presence/absence, concrete local recovery, decidable satisfaction, and exact notifications                                                                                                               | `Coeffect.Context`, `setEffect_recovers`, `CoeffectAt.lift_recovers`, `activating_iff`, `deactivating_iff`, `neutral_iff`                                                                                                                                                                                                                                                                                     | This module is Definitions 22–26; the next two rows state the separate bounded 27–33 results.                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| Isolation resolves logical keys through typed realm stores; interception merges key-indexed metadata; finite unified layers retain LIFO recovery                                                                                                            | `UnifiedContext.IsolatedContext`, `InterceptionContext`, `Layer.record_twice_recovers`, `Layer.liftCoeffect_recovers`                                                                                                                                                                                                                                                                                         | Definitions 27–31 are direct finite models; Definition 32 is represented only by finite unfoldings, not its fixed point.                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| Related finite contexts have exactly the same domain and key-wise related values, and satisfaction and notifications respect that relation                                                                                                                  | `Coeffect.Observational.related_iff`, `contextSetoid`, `satisfies_iff_of_related`, `notify_eq_of_related`                                                                                                                                                                                                                                                                                                     | Finite-context portion of Definition 33; the next rows state the separate bounded Definitions 34–38 results.                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| Finite heterogeneous operation tests define a coarsest fixed-generator relation, while a compiled model separates differently yielded inverses                                                                                                              | `OperationalEquivalence.indistinguishable_admissible`, `contained_in_indistinguishable`, `PairedGap.pairedInverseCoherent_fails`                                                                                                                                                                                                                                                                              | Definition 34 and generator-level Lemma 35; the stronger paired-inverse bridge remains an explicit extra premise.                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| Quotient-respecting effects compose and recover through finite programs; lifted key operations preserve contextual successor/inverse/outcome laws                                                                                                           | `Observational.Quotient.Admissible.seq`, `Program.recovers`, `Coeffect.Quotient.lift_results_related`                                                                                                                                                                                                                                                                                                         | Definitions 36–37 and finite Lemma 38 core; the next rows state exact transformation/operation independence results.                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| Effect transformation monoids close generator commutation/stability and imply equal adjacent proof-carrying orders                                                                                                                                          | `Transformation.Closure.commute`, `seq_monoid_subset_joint`, `Transformation.Independent.of_generators`, `independentAt`                                                                                                                                                                                                                                                                                      | Definitions 17–19 and Lemma 18 for exact effects; arbitrary removal/inverse order are the next row.                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| Removing any effect from an independent finite execution preserves later inverse yields, and any permutation of retained inverses recovers                                                                                                                  | `Removal.removal_inverse_relation`, `later_inverses_unchanged`, `inverse_permutation_recovers`                                                                                                                                                                                                                                                                                                                | Theorem 20 and Corollary 21 for finite exact effects; no observational, asynchronous, or external-effect claim.                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| Full total-operation independence and finite partial distinct-key words retain inverse and heterogeneous outcome stability; mediated runs recover                                                                                                           | `ExactOperationIndependent`, `distinctKeys_finiteIndependent`, `Computation.run_recovers`                                                                                                                                                                                                                                                                                                                     | Definitions 39–41 and finite-word Theorem 40; the observational/exact Theorem 42 boundary is the next row.                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| Realized paths retain exact branch choices; quotient closure promotes to exact only under representative coherence                                                                                                                                          | `RealizedPath.run_eq_some`, `ObservationalMediatedClosure.toExact`, exact-representative counterexample                                                                                                                                                                                                                                                                                                       | Initial Theorem 42 specification; its old individual-domain closure is too strong for partial computations.                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| Pairwise finite operation certificates swap arbitrary outcome-selected computation trees with exact whole-run results and inverse stability                                                                                                                 | `pairwiseOverlap_boundedPartialIndependence`, `partialPairwiseOverlapComplete`, heterogeneous example                                                                                                                                                                                                                                                                                                         | Finite whole-run analogue only; it does not quantify over every transformation-monoid word of full Definition 19.                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| Pairwise overlap makes the complete partial forward/yielded-inverse Kleisli monoids commute with success-conditional inverse stability                                                                                                                      | `PartialTransformation.pairwiseOverlap_independent`, `Independent.toBoundedPartial`, strict-converse counterexample                                                                                                                                                                                                                                                                                           | Full finite partial analogue of Definitions 17/19 and T42; not the paper's total/quotient or external-effect setting.                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| Exact pairwise overlap descends the same complete closure theorem to relation-respecting partial maps and related representatives                                                                                                                           | `ObservationalPartialTransformation.pairwiseOverlap_independent`, `closure_iff_exact`, `evaluate_related`, respect counterexample                                                                                                                                                                                                                                                                             | Finite observational partial/Kleisli analogue; exact overlap is stronger than quotient-only operation independence.                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| Birth-ranked global insert/retire/remove steps preserve registry/provider/view invariants and an acyclic parent relation                                                                                                                                    | `GlobalRegistry.OrchestrationStep.preservesWellFormed`, `parent_acyclic`, `Trace.preservesWellFormed`                                                                                                                                                                                                                                                                                                         | Data portions of Definitions 43–46/49 and orchestration part of Theorem 59; external code semantics are the next row.                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| External iterator/undo codes produce certified ordinary or registration steps, newest-first recovery, well-formed traces, and explicit fuel status                                                                                                          | `GlobalDynamics.executeOne`, `Accumulator.seq`, `RunResult.recovers`, `RunResult.preservesWellFormed`                                                                                                                                                                                                                                                                                                         | Definitions 47–48/51 and fueled Definition 52 substrate; supplied laws and phase updates remain separate.                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Phase-indexed lifecycle edges retain exact targets, executed landings, inertia, recovery, and well-formed endpoints                                                                                                                                         | `GlobalLifecycle.Transition.preservesWellFormed`, `Trace.preservesWellFormed`, lifecycle example facts                                                                                                                                                                                                                                                                                                        | Seven lifecycle rule names/eight constructors; orchestration is separate and general unload recovery is admitted explicitly.                                                                                                                                                                                                                                                                                                                                                                                                                             |
| One exact-endpoint global relation has all ten rule names, acted-on names, map/edit projections, and empty-origin traces                                                                                                                                    | `GlobalCalculus.Step`, `installation_semantics`, `FromEmpty.final_wellFormed`, unified example facts                                                                                                                                                                                                                                                                                                          | Finite sequential Definition 53 model; recovery admission remains supplied and full Theorem 59 is unclaimed.                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| Foreign tables/control and episode boundaries satisfy bounded Lemma 54 facts under explicit unload confinement                                                                                                                                              | `foreignTables_preserved`, `actorStatic_continuous`, `Trace.aligned`, `BoundedEpisode.*`, countermodel                                                                                                                                                                                                                                                                                                        | Existing-fiber facts only; opaque recovery may add names, retire-write provenance and full temporal metatheory are open.                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| Per-step commutation certificates compose to finite interleaved recovery under an explicit effect relation and reorder certificate                                                                                                                          | `EffectEquiv`, `TotalStepMap`, `accumulatedCommutes_of_perStep`, `recover_interleaved`, temporal counterexamples                                                                                                                                                                                                                                                                                              | Parameterized relational algebra; the next row supplies only the D60-to-per-step bridge, while totality, canonical `≈`, reordering, and arbitrary T61/Cor62 remain.                                                                                                                                                                                                                                                                                                                                                                                      |
| Oracle-specific reachable iterator programs generate partial forward/actual-inverse closures, and observational independence discharges temporal per-step recovery commutation                                                                              | `Reach`, `Generator`, `Independent.of_generators`, `ProgramRespects`, `ObservationalIndependent`, `YieldedAccumulator`, `StepMapMember`, `ObservationalPerStepGenerated`, `perStepCommutes_of_generated`                                                                                                                                                                                                      | Partial/Kleisli Definition 60 analogue; forward respect and finite/bound certificates are supplied separately, effect observation is not rule `≃`, and totalization, reordering, T61/Cor62 remain separate.                                                                                                                                                                                                                                                                                                                                              |
| Given `Independent`, reachable iterators form an exact raw diamond and two `TotalProgramStep`s commute exactly; `ObservationalIndependent` gives the effect-relational square                                                                               | `ForwardDiamond`, `independent_forward_diamond`, `TotalProgramStep.commute_exact`, `commute_effect`, `setPhase_commute`, noninjective-undo counterexample                                                                                                                                                                                                                                                     | Bounded ingredients toward Lemma 71 only; the observational certificate retains supplied `ProgramRespects`, while exact lifecycle codes, foreign-phase opacity, guards/targets, and actual step transposition remain separate.                                                                                                                                                                                                                                                                                                                           |
| Explicit read, ordinary-successor, and same-child oracle frames derive foreign-phase compatibility and an exact two-sided framed raw diamond                                                                                                                | `ForeignPhaseCompatibility.of_read_frames`, `PhaseFramedExecution`, `phase_framed_diamond`, independence/readability/oracle countermodels                                                                                                                                                                                                                                                                     | Caller-supplied raw/frame laws and phase payloads only; the module constructs no lifecycle transition, guard/target proof, or paper Lemma 71 exchange.                                                                                                                                                                                                                                                                                                                                                                                                   |
| Exact cross-forward yield syntax plus program-aligned landings lift the framed raw diamond to all four common-source L-Iter/L-Finish lifecycle pairs                                                                                                        | `ForwardLifecycleIndependent`, `LifecycleForwardDiamond`, `LandingProgramWitness`, `targetView_preserved_by_foreign_landing`, `landing_activation_diamond`                                                                                                                                                                                                                                                    | Requires source WF, distinct owners, exact program/oracle provenance, both phase compatibilities, and exact cross-forward syntax; no Begin pair, trace rewrite, or full Lemma 71.                                                                                                                                                                                                                                                                                                                                                                        |
| Fixed-program activations transpose all nine common-source L-Begin/L-Iter/L-Finish pairs and reconcile a supplied actual second activation by endpoint uniqueness                                                                                           | `ProgramActivation`, `ActivationSwapLaws`, `ProgramActivation.after_unique`, `program_activation_diamond`, `transpose_program_activations`                                                                                                                                                                                                                                                                    | Bounded Lemma 71(1) analogue under partial fixed-oracle execution, explicit root/reach/frame/exact-yield evidence, distinct owners, WF, and common applicability; no clause (2), trace rewrite, or confluence.                                                                                                                                                                                                                                                                                                                                           |
| Corrected activation/orchestration exchange reconstructs the earlier legal orchestration template and moved activation at one exact endpoint, while kernel-refuting the literal weaker paper premise                                                        | `RegistrationSafe`, `ExactExecutionFrame`, `reconstructOrchestration`, `transpose_activation_orchestration`, parent/birth/frame countermodels                                                                                                                                                                                                                                                                 | Corrected bounded Lemma 71(2) analogue: registering×Insert is excluded; landing branches require a supplied occurrence frame; no birth-erasing quotient, trace rewrite, Lemma 72, or confluence.                                                                                                                                                                                                                                                                                                                                                         |
| Finite provider precedence plus occurrence-local execution/recovery authorities gives state-local lifecycle no-deadlock, while fixed-oracle rejection and exhausted names refute the printed assumptions                                                    | `PrecedesAt`, `FinitePrecedenceRank`, `OracleTotal.toLandingOrRaiseTotal`, `LocalProgressLaws`, `lifecycle_progress`, rejection/freshness gaps                                                                                                                                                                                                                                                                | Corrected no-deadlock fragment of Theorem 66 only; no quantitative bound, target-turn finiteness, maximal termination, trace program assignment, fairness, support, or confluence.                                                                                                                                                                                                                                                                                                                                                                       |
| Explicitly well-founded combined parent/provider edges yield a unique recursive support set and, under active-table/failure/parent closure, exact support-equals-active at quiescence                                                                       | `SupportEdge`, `SupportOrder`, `supported_iff`, `support_solution_unique`, `support_eq_active`, mixed-cycle and active-parent gaps                                                                                                                                                                                                                                                                            | Corrected local Lemmas 68/70 and state-local Definition 69 analogue. Combined order and parent closure are supplied, not derived; no trace provenance, deletion, or confluence.                                                                                                                                                                                                                                                                                                                                                                          |
| Rule and effect observations are explicit incomparable setoids, and respectful undo interpretation instantiates temporal effect equivalence                                                                                                                 | `GlobalRelations.RuleRelated`, `EffectRelated`, `EffectUndoRespect.temporalEffectEquiv`, separation examples                                                                                                                                                                                                                                                                                                  | Finite candidates for Equation 53/Lemmas 55–57; full lifecycle bisimulation, renaming, and the lemmas remain obligations.                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Every well-formed orchestration step has a same-kind/name peer step at a `RuleRelated` state with related well-formed successors                                                                                                                            | `matchOrchestrationForward`, `matchOrchestrationBackward`, `orchestrationRuleBisimulation`, heterogeneous and inertia examples                                                                                                                                                                                                                                                                                | Orchestration-only L55 fragment; ambient-sensitive inertia refutes full lifecycle invariance under the current relation.                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| Rule-related well-formed states have the same provider names, targets, reliance, quiescence, phase patterns, and structural lifecycle guards                                                                                                                | `activeProvider_iff`, `targetView_*`, `relied_iff`, `quiescent_iff`, five guard-availability iff theorems                                                                                                                                                                                                                                                                                                     | Assumption-free lifecycle-observation substrate; landing, run-error, inertia, oracle, and recovery transport remain open.                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Four noncircular external contracts yield exact bidirectional matching for all eight lifecycle constructors and all ten unified rule names                                                                                                                  | `LifecycleTransportAssumptions`, `matchLifecycleForward/Backward`, `wellFormedRuleBisimulation`, Finish seam countermodel                                                                                                                                                                                                                                                                                     | Conditional well-formed L55 analogue; the contracts are supplied rather than derived from base `Dynamics`.                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| A lawful bijection acts through every stored payload and preserves state inversion, well-formedness, and all three orchestration rules                                                                                                                      | `NameAction`, `actState_*`, `wellFormed_act_iff`, `orchestrationEquivariance`, swap and old-skeleton examples                                                                                                                                                                                                                                                                                                 | Structural/orchestration L56 fragment; dynamics, oracle, recovery, inertia, and lifecycle action laws remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| Three primitive semantic action laws derive registration, execution, landing, recovery, all-eight lifecycle, and unified ten-rule equivariance                                                                                                              | `DynamicsNameEquivariant`, `actRegistrationAdmission`, `executeOne_equivariant`, `unifiedNameEquivariance`, nonidentity examples                                                                                                                                                                                                                                                                              | Conditional well-formed fixed-catalog L56 analogue; the primitive dynamics/inertia laws remain supplied.                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| Vestigial removal is effect-equivalent and safe orchestration steps commute with it under complete, kernel-necessary exceptions                                                                                                                             | `Vestigial.effectRelated_remove`, `forward_orchestration`, `backward_orchestration`, four well-formed exception witnesses                                                                                                                                                                                                                                                                                     | Corrected orchestration fragment of L57; the pinned raw clauses omit two parent-pointer cases, and lifecycle is unproved.                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Located dependency episodes retain provider resolution and no-unload facts, with explicit nesting offsets and conditional table constancy                                                                                                                   | `begin_dependencies_provided`, `NestedEpisodes.*`, `resolution_throughout_interior`, `provider_noUnload_core`, `tableValue_throughout`                                                                                                                                                                                                                                                                        | Finite fragments of T63/T64; maximal episodes, same-owner table confinement, eventual close, and recovery remain open.                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| Supported current-Harness stream JSON refines to an intrinsic validated trace with exact replay, or fails with a structured decode/stream error                                                                                                             | `RuntimeRefinement.validateJsonTrace`, `ValidatedJsonTrace.replay_eq`, exact rejection theorems                                                                                                                                                                                                                                                                                                               | JSON AST only; unsupported blocks/failures/replay state are rejected, and completeness for Harness is not claimed.                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| Current-Harness in-band `error`/`aborted` finish JSON retains the exact typed `LlmFailure` and decoded ordinary prefix                                                                                                                                      | `RuntimeFailureRefinement.validateFailureTrace`, `ValidatedFailureTrace.decoded_exact`, exact error/abort fixtures                                                                                                                                                                                                                                                                                            | JSON AST only; no open-block reconstruction, retry/cancellation policy, provider authenticity, or normal rich/session projection is claimed.                                                                                                                                                                                                                                                                                                                                                                                                             |
| Supported successful and normalized-failure current-Harness JSON dispatch into one dependent outcome                                                                                                                                                        | `RuntimeOutcomeRefinement.validateOutcome`, `ValidatedOutcome`, exact success/failure/neither theorems                                                                                                                                                                                                                                                                                                        | Composition only; no retry/cancellation choice, open-block reconstruction, provider authenticity, or whole-runtime equivalence is claimed.                                                                                                                                                                                                                                                                                                                                                                                                               |
| Successful current-Harness JSON/text/UTF-8 outcomes append through the pure local runner while normalized failures leave it unchanged                                                                                                                       | `RuntimeOutcomeSession.validateAndDispatch`, `validateBytesAndDispatch`, `DispatchResult`, exact success/failure fixtures                                                                                                                                                                                                                                                                                     | No fabricated failure message, retry/cancellation policy, source-event synthesis, persistence, provider authenticity, or whole-runtime equivalence is claimed.                                                                                                                                                                                                                                                                                                                                                                                           |
| Newline-delimited UTF-8 JSON parses into exact AST lines and composes with the supported stream/session/failure validators                                                                                                                                  | `TextRefinement.parseJsonLinesBytes`, `validateStreamBytes`, `validateSessionBytes`, `validateFailureBytes`, `Validated*Text` certificates                                                                                                                                                                                                                                                                    | Uses Lean's JSON parser and canonical printer; no deployed JSONL schema, logger framing, timestamp, transport, or whole-runtime equivalence theorem is claimed.                                                                                                                                                                                                                                                                                                                                                                                          |
| UTF-8/JSONL current-Harness event text restores the certificate-gated typed runner                                                                                                                                                                          | `DeepSeekHarnessEventText.restoreTextRunner`, `restoreBytesRunner`, `RestoredTextRunner`, `RestoredBytesRunner`, `buildRequestCertificate`                                                                                                                                                                                                                                                                    | Text/byte ingress only; opaque or extension events reject, and logger framing, transport, persistence, provider authenticity, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                          |
| Explicitly ignorable current-Harness archive rows project to positional keep/drop evidence without silent required-row loss                                                                                                                                 | `DeepSeekHarnessEventIgnorableProjection.projectSupported`, `SupportedProjection`, `ignorable_fixture_summary`, `required_fixture_rejected`                                                                                                                                                                                                                                                                   | Archive projection only; physical sequence renumbering, local session replay, payload semantics, persistence, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                                          |
| Explicitly ignorable rows normalize into a contiguous supported local session with remapped source references                                                                                                                                               | `DeepSeekHarnessEventIgnorableNormalization.normalize`, `NormalizedLog`, `ignorable_middle_summary`, `ignorable_middle_source_positions`                                                                                                                                                                                                                                                                      | Supported-subset normalization only; required opaque rows, duplicate physical sequences, missing references, unsupported payload semantics, persistence, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                               |
| Normalized supported occurrences replay as an intrinsic source-indexed local transition trace                                                                                                                                                               | `DeepSeekHarnessEventSimulation.replayOccurrences`, `SourceReplay`, `SourceLedger`, `toolNormalizedSimulation`, `SourceReplay.protocolTrace_erase`, `SourceReplay.sessionProjection_eq`                                                                                                                                                                                                                       | Finite occurrence-indexed supported-subset simulation only; opaque semantics, provider behavior, bytes, persistence, cancellation delivery, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                                            |
| Archive decisions and normalized transitions compose into one archive-aware dependent replay                                                                                                                                                                | `DeepSeekHarnessEventArchiveReplay.ArchiveReplay`, `archiveReplay`, `toolArchiveReplay`, `ArchiveReplay.droppedRaw_eq_decisionDrops`                                                                                                                                                                                                                                                                          | The indexed source trace and keep/drop ledger share one certificate; exact physical archive rows, retained raw rows, dropped opaque rows/positions, and the normalized endpoint are checked together.                                                                                                                                                                                                                                                                                                                                                    | This is still a finite supported-subset bridge: dropped rows are explicitly ignorable no-ops, while opaque payload semantics, provider behavior, bytes, persistence, cancellation delivery, and deployed Harness equivalence remain external. |
| A normalized explicit-ignorable log attaches to the typed runner and rebuilds a request with exact endpoint certificates                                                                                                                                    | `DeepSeekHarnessEventIgnorableRunner.restoreRunner`, `buildRequestCertificate`, `toolNormalizedRunner`, `toolNormalizedRequest`                                                                                                                                                                                                                                                                               | Pure normalized-log → local `ConversationRunner`/request attachment; opaque semantics, provider authenticity, persistence, transport, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                  |
| A normalized explicit-ignorable runner enters the process-backed complete-response conversation trace with final endpoint certificates                                                                                                                      | `DeepSeekHarnessEventIgnorableTransport.runRestoredTransport`, `toolNormalizedTransport`, `RestoredTransportRun`                                                                                                                                                                                                                                                                                              | Injected/deterministic transport continuation only; credentials, provider authenticity, durable persistence, external effects, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                                                                                                                                                         |
| UTF-8/JSONL current-Harness event text restores a runner while retaining typed raw payload classifications                                                                                                                                                  | `DeepSeekHarnessPayloadText.restoreTextPayloadRunner`, `restoreBytesPayloadRunner`, `RestoredPayloadRunner`, `RestoredBytesPayloadRunner`, `payload_raw_eq_lines`                                                                                                                                                                                                                                             | Payload shape/tag retention only; reasoning/image/usage/error/meta JSON remains uninterpreted, and no provider schema, transport, persistence, or deployed Harness equivalence is claimed.                                                                                                                                                                                                                                                                                                                                                               |
| Persisted current-Harness JSONL restores a runner while retaining the same expanded-event payload ledger                                                                                                                                                    | `DeepSeekHarnessPayloadPersistence.restoreRunner`, `restoreBytesRunner`, `restoreRead`, `RestoredRunner`, `RestoredBytesRunner`, `ReadRestoredRunner`                                                                                                                                                                                                                                                         | Logical/byte/backend attachment only; payload errors, storage errors, durability, crash recovery, and deployed Harness equivalence remain separate.                                                                                                                                                                                                                                                                                                                                                                                                      |
| A typed DeepSeek chat request becomes an exact POST plan, and a successful response becomes a dependent parse/decode certificate or a structured transport/status/API error                                                                                 | `DeepSeekApi.buildRequest`, `buildRequest_body_eq`, `ValidatedResponse`, `validateResponse`, `execute`                                                                                                                                                                                                                                                                                                        | OpenAI-compatible non-streaming chat subset with tool calls, reasoning, finish reasons, and usage; no live HTTP, credential validity, provider completeness, stream transport, or local `ToolSpec` validation is claimed.                                                                                                                                                                                                                                                                                                                                |
| A typed DeepSeek request/response crosses an explicit UTF-8 byte boundary while preserving raw bytes, decoded text, and typed response certificates                                                                                                         | `DeepSeekApiBytes.ByteRequestPlan`, `buildRequest_bodyBytes_eq`, `ValidatedResponseBytes`, `validateResponseBytes`, `execute`, `exampleRun`                                                                                                                                                                                                                                                                   | Injected byte transport and canonical UTF-8/JSON behavior only; no network delivery, credential validity, provider obedience, byte-level deployed compatibility, or Harness equivalence is claimed.                                                                                                                                                                                                                                                                                                                                                      |
| A strict DeepSeek SSE body becomes typed delta frames with raw-frame parse/decode certificates, or a structured framing/UTF-8/JSON error                                                                                                                    | `DeepSeekStream.parseSse`, `validateSse`, `validateSseBytes`, `DataFrame`                                                                                                                                                                                                                                                                                                                                     | Strict `data:` / `[DONE]` subset only; no live reader, buffering/backpressure, cancellation, assembler, provider-complete stream schema, or HTTP delivery is claimed.                                                                                                                                                                                                                                                                                                                                                                                    |
| A complete strict DeepSeek SSE body ending in `content_filter` or `insufficient_system_resource` retains its raw prefix, terminal choice/reason, and optional usage certificate                                                                             | `DeepSeekStreamFailure.projectFrames`, `validateFailureStream`, `ValidatedFailureStream`, `FailureView`                                                                                                                                                                                                                                                                                                       | Provider terminal-failure wire subset only; no normal rich/session projection, `error`/`aborted` envelope, retry, cancellation, live delivery, or deployed provider-equivalence claim.                                                                                                                                                                                                                                                                                                                                                                   |
| A complete strict DeepSeek SSE body is classified as a provider failure or one of the four successful rich languages, retaining the selected dependent certificate                                                                                          | `DeepSeekTerminalOutcome.validateTerminalOutcome`, `TerminalOutcome`, `TerminalOutcomeError`, `TerminalOutcome.kind`                                                                                                                                                                                                                                                                                          | Fixed-order complete-body dispatcher only; it does not add wire languages, session-message semantics, retry, cancellation, live delivery, or deployed provider equivalence.                                                                                                                                                                                                                                                                                                                                                                              |
| A complete process-backed DeepSeek SSE response validates HTTP status and then becomes typed delta frames, or a structured process/status/stream error                                                                                                      | `DeepSeekCurlStream.executeSse`, `fixtureResponse`, `StreamClientError`                                                                                                                                                                                                                                                                                                                                       | Complete-body process composition only; no incremental reader, buffering/backpressure, cancellation, reconnect, network, credential, or provider-complete assembler claim is made.                                                                                                                                                                                                                                                                                                                                                                       |
| A complete process-backed DeepSeek SSE response becomes a typed provider-failure or successful rich terminal outcome, or a distinct process/status/outcome error                                                                                            | `DeepSeekCurlOutcome.executeOutcome`, `ProcessedOutcome`, `OutcomeClientError`, `fixtureContentFilter`, `fixtureText`                                                                                                                                                                                                                                                                                         | Deterministic complete-body process composition only; no incremental delivery, retry, cancellation, network/credential trust, or deployed provider-equivalence claim.                                                                                                                                                                                                                                                                                                                                                                                    |
| A validated terminal outcome either remains a typed provider failure with the runner unchanged or appends a finished rich assistant through the proof-carrying runner                                                                                       | `DeepSeekOutcomeSession.dispatchOutcome`, `executeAndDispatchOutcome`, `fixtureFailureDispatch`, `fixtureTextDispatch`, `fixtureToolDispatch`, `fixtureMixedDispatch`, `fixtureMultiDispatch`                                                                                                                                                                                                                 | Typed local dispatch only; failure-to-message policy, source-event evidence, persistence, retries, cancellation, external tools, and whole-session equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                           |
| A process-backed terminal outcome either preserves a provider failure or appends a finished rich assistant to `ConversationRunner`; its execution variant routes projected calls through the existing dependent executor and appends certified tool results | `DeepSeekOutcomeConversation.dispatchOutcome`, `executeAndDispatchOutcome`, `executeOutcomeWithTools`, `executeAndRunOutcome`, `projectedFunctionCalls`, `fixtureFailureExecution`, `fixtureTextExecution`, `fixtureCounterToolExecution`                                                                                                                                                                     | Typed conversation-runner and dependent-execution bridge only; provider-ID authentication, failure/retry policy, persistence, cancellation, external process trust, and whole-session/deployed equivalence remain outside.                                                                                                                                                                                                                                                                                                                               |
| A generic transport can run a bounded sequence of complete rich terminal outcomes, preserving typed failures, executing tool rounds, and feeding the updated runner into the next streaming request                                                         | `DeepSeekOutcomeTransportLoop.executeOutcomeTransportRound`, `runOutcomeTransport`, `Example.run`                                                                                                                                                                                                                                                                                                             | Complete-body transport continuation only; incremental IO, retry, cancellation, credential trust, external tool trust, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                                  |
| A complete process-backed terminal SSE response retains its wire certificate and appends a typed rich assistant to the local session runner, or returns a typed process/response error                                                                      | `DeepSeekCurlSession.executeText`, `executeAndAppendText`, `ProcessedResponse`, `appendProcessed_nextSeq`, `appendProcessed_nextCall`                                                                                                                                                                                                                                                                         | Text fixture and pure runner composition only; source-event evidence, provider-ID authenticity, persistence, incremental transport, cancellation, external execution, and whole-session equivalence remain outside the claim.                                                                                                                                                                                                                                                                                                                            |
| A typed Harness request source is retained through exact request-plan construction, complete-body process execution, semantic response validation, and the indexed runner append endpoint                                                                   | `DeepSeekHarnessProcess.PreparedRequest`, `prepareRequest`, `executePreparedText`, `executeSourceText`, `ProcessRound`, `ProcessRound.nextSeq`, `ProcessRound.nextCall`                                                                                                                                                                                                                                       | Request/process provenance over the local complete-body runner only; credentials, provider/schema authenticity, incremental transport, persistence, external tools, cancellation, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                       |
| A typed Harness source is retained through a streaming request plan, complete-body terminal-outcome classification, dependent tool execution, and the final `ConversationRunner` endpoint, with provider failure preserved separately                       | `DeepSeekHarnessProcessOutcome.PreparedStreamingRequest`, `prepareStreamingRequest`, `executePreparedOutcome`, `executeSourceOutcome`, `ProcessOutcomeRound`, `ProcessOutcomeRound.result_exact`, `ProcessOutcomeRound.endpoint_exact`                                                                                                                                                                        | Complete-body process-backed rich-outcome provenance only; provider/credential authenticity, incremental delivery, cancellation, persistence, external tool trust, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                      |
| A caller-named environment credential is classified without logging, a complete-mode request plan retains its exact build equation, and the bounded conversation runner can use either curl or an injected transport                                        | `DeepSeekHarnessLiveProbe.parseApiKey`, `readApiKey`, `PreparedRequest`, `runFromEnvironment`, `Example.run`                                                                                                                                                                                                                                                                                                  | Credential/runtime handoff only; missing/empty-key handling and deterministic fixture behavior are checked, but credential validity, network reachability, process trust, provider obedience, backoff, idempotency, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                     |
| A caller-named credential feeds a typed streaming request through configured curl byte chunks and the dependent prefix conversation runner, retaining a fuel stop and exact endpoint                                                                        | `DeepSeekHarnessLiveStreamProbe.PreparedRequest`, `prepareRequest`, `runFromEnvironment`, `Example.run`, `Example.fixtureSummary`                                                                                                                                                                                                                                                                             | Credential-safe live streaming handoff over the arbitrary-byte prefix seam.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Credential validity, remote reachability, provider obedience, process trust, blocked-read cancellation, backpressure, retries, persistence, and deployed Harness equivalence remain outside.                                                  |
| A real local loopback HTTP server validates the curl request shape and returns typed responses through the bounded conversation runner or the indexed response-to-append bridge                                                                             | `DeepSeekHarnessLocalHttp.runWithKey`, `runCompleteAppendWithKey`, `LocalProbeResult`, `CompleteAppendProbeResult`, `Example.run`, `Example.summarize`                                                                                                                                                                                                                                                        | Local process/HTTP evidence only; the fixture does not prove remote reachability, TLS, credential validity, provider obedience, executable trust, backoff, idempotency, or deployed Harness equivalence.                                                                                                                                                                                                                                                                                                                                                 |
| A real local loopback HTTP server validates a typed streaming request, emits SSE lines through curl, and appends the strict text-stream result to the dependent conversation runner                                                                         | `DeepSeekHarnessLocalSse.runWithKey`, `PreparedStreamingRequest`, `LocalSseResult`, `Example.run`, `Example.summarize`                                                                                                                                                                                                                                                                                        | Local incremental line-delivery evidence only; byte framing, backpressure, blocked-read cancellation, reconnects, provider authenticity, executable trust, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                              |
| A loopback HTTP validates a two-tool schema loop and terminal                                                                                                                                                                                               | `DeepSeekSchemaLocalHttp.runWithKey`, `LocalSchemaHttpResult`, `Example.run`, `Example.summarize`                                                                                                                                                                                                                                                                                                             | Local heterogeneous process/HTTP evidence only; remote reachability, TLS, credential validity, provider obedience, executable trust, retries, cancellation, persistence, external effects, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                              |
| A loopback SSE retry fixture returns one transient 503 before a flushed success, retaining the exact failure history and one accepted runner append                                                                                                         | `DeepSeekHarnessLocalSseRetry.runWithRetry`, `LocalSseRetryResult`, `Example.run`                                                                                                                                                                                                                                                                                                                             | Local bounded retry/reconnect evidence only; provider backoff, idempotency, arbitrary retry policy, blocked-read cancellation, backpressure, authenticity, and deployed retry equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                |
| A loopback SSE retry fixture repeats that boundary over two dependent conversation rounds, retaining one typed transient failure and one accepted append per round while rebuilding the second request from the first session endpoint                      | `DeepSeekHarnessLocalSseRetryConversation.runTwoRounds`, `RetryConversationResult`, `RetryConversationResult.session_advance_twice`, `Example.run`, `Example.summarize`                                                                                                                                                                                                                                       | Local request/session-indexed retry conversation evidence only; provider backoff, idempotency, arbitrary retry policy, cancellation, persistence, external effects, and deployed retry/conversation equivalence remain outside.                                                                                                                                                                                                                                                                                                                          |
| A loopback SSE timeout fixture flushes a typed prefix before a real timer interrupts the blocking curl read, while a fast sibling completes and appends                                                                                                     | `DeepSeekHarnessLocalSseTimeout.runWithTimeout`, `TimedPrefix`, `Completed`, `Example.timeoutRun`, `Example.fastRun`                                                                                                                                                                                                                                                                                          | Local in-flight timeout evidence only; arbitrary cleanup, fairness, backpressure, authenticity, provider-complete assembly, reconnects, and deployed cancellation equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                            |
| A loopback SSE fixture crosses into the dependent two-tool continuation, retaining both local call IDs, executions, certified tool results, and the final runner endpoint                                                                                   | `DeepSeekHarnessLocalSseMultiTool.runWithKey`, `PreparedMultiToolRequest`, `LocalSseMultiToolResult`, `Example.run`, `Example.summarize`                                                                                                                                                                                                                                                                      | Local rich multi-tool HTTP/SSE evidence only; provider-complete assembly, backpressure, cancellation, reconnects, credential/TLS authenticity, process trust, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                           |
| A loopback SSE prefix fixture parses each complete line before the next read, completes into the two-tool continuation, and retains typed cancellation/fuel prefixes without dispatch                                                                       | `DeepSeekHarnessLocalSseMultiToolPrefix.runWithPolicy`, `PreparedMultiToolPrefixRequest`, `LocalSseMultiToolPrefixResult`, `Example.completeRun`, `Example.cancelledRun`, `Example.exhaustedRun`                                                                                                                                                                                                              | Local line-prefix multi-tool HTTP/SSE evidence only; byte framing, backpressure, fairness, blocked-read interruption, reconnects, provider-complete assembly, authenticity, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                             |
| A loopback SSE fixture drives bounded curl byte chunks into the dependent two-tool continuation, retaining raw/framed completion evidence or a one-read prefix before dispatch                                                                              | `DeepSeekHarnessLocalSseMultiToolBytePrefix.runWithReads`, `LocalSseMultiToolBytePrefixResult`, `Example.completeRun`, `Example.exhaustedRun`                                                                                                                                                                                                                                                                 | Local byte-prefix multi-tool HTTP/SSE evidence only; byte-level backpressure, blocked-read interruption, reconnects, provider-complete assembly, authenticity, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                          |
| A loopback SSE fixture validates a typed streaming request, emits the incremental provider tool body, and routes real curl lines through provider assembly, dependent execution, and certified session append                                               | `DeepSeekHarnessLocalSseProviderAssemblyTool.runWithKey`, `PreparedRequest`, `LocalProviderAssemblyResult`, `Example.run`, `Example.summary`                                                                                                                                                                                                                                                                  | Local provider-complete assembly HTTP/SSE evidence only; provider obedience, byte/backpressure semantics, blocked-read cancellation, reconnects, credential/TLS authenticity, arbitrary cleanup, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                        |
| A loopback SSE fixture validates a typed streaming request, consumes the provider body through real curl one-byte chunks, and routes byte-prefix state through provider assembly and dependent execution                                                    | `DeepSeekHarnessLocalSseBytePrefixProviderAssemblyTool.runWithKey`, `PreparedRequest`, `LocalByteProviderAssemblyResult`, `Example.run`, `Example.summary`                                                                                                                                                                                                                                                    | Local byte-framed provider-complete assembly evidence only; timeout fairness, provider obedience, backpressure, reconnects, credential/TLS authenticity, arbitrary cleanup, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                             |
| A process-backed SSE response delivers body lines incrementally to a callback under an explicit read budget, then retains the reconstructed body and strict wire certificate, or returns a typed process/status/stream/callback/limit error                 | `DeepSeekCurlIncremental.executeSseIncremental`, `readBodyLines`, `IncrementalResponse`                                                                                                                                                                                                                                                                                                                       | Line-oriented complete-response adapter only; byte framing, backpressure, cancellation, reconnect, network, credential, executable-trust, and provider-complete assembler semantics remain external.                                                                                                                                                                                                                                                                                                                                                     |
| A validated strict DeepSeek SSE text-only stream projects to an exact `RichStream.ValidatedTrace`, or fails with a typed wire/projection error                                                                                                              | `DeepSeekRichStream.validateTextStream`, `ValidatedTextStream`, `projectFrames`                                                                                                                                                                                                                                                                                                                               | Exactly one assistant choice at index zero with text deltas, terminal usage, and stop/max-token finish; reasoning, tool calls, extra choices, unsupported finishes, and deployed assembler semantics remain outside the claim.                                                                                                                                                                                                                                                                                                                           |
| A restricted DeepSeek SSE tool stream projects to an exact rich tool-call trace, or fails with a typed projection error                                                                                                                                     | `DeepSeekRichToolStream.validateToolStream`, `ValidatedToolStream`, `projectFrames`                                                                                                                                                                                                                                                                                                                           | At most one provider tool call at index zero with IDs on every delta and terminal `tool_calls`; provider-complete multi-call assembly, reasoning, transport, and tool execution remain outside the claim.                                                                                                                                                                                                                                                                                                                                                |
| A composed DeepSeek SSE stream interleaves text, reasoning, and one tool call into an exact rich trace, or fails closed with a typed projection error                                                                                                       | `DeepSeekRichMixedStream.validateMixedStream`, `ValidatedMixedStream`, `projectFrames`, `project_mixed_chunks_exact`                                                                                                                                                                                                                                                                                          | One choice/call only; same-frame mixed fields, multiple choices/calls, provider failure/content-filter finishes, replay metadata, live transport, and deployed assembler completeness remain outside the claim.                                                                                                                                                                                                                                                                                                                                          |
| A composed DeepSeek SSE stream interleaves text, reasoning, and any finite list of indexed tool calls into an exact rich trace, or fails closed with a typed projection error                                                                               | `DeepSeekRichMultiStream.validateMultiStream`, `ValidatedMultiStream`, `projectFrames`, `project_multi_chunks_exact`                                                                                                                                                                                                                                                                                          | One choice only; same-frame cross-kind fields, unsupported finishes, replay metadata, live transport, and deployed assembler completeness remain outside the claim.                                                                                                                                                                                                                                                                                                                                                                                      |
| A canonical post-decoder provider chunk list folds into a source-shaped assistant assembly with exact certificates and typed unknown-block rejection                                                                                                        | `DeepSeekProviderAssembler.push`, `assemble`, `validate`, `Certificate`, `Example.multiTool_result_exact`, `Example.first_close_wins`, `Example.max_tokens_drops_tools`                                                                                                                                                                                                                                       | Models the current text/reasoning/tool-call `BlockAssembler` branches only; wire decoding, image/tool-result schemas, opaque replay JSON, transport, and deployed TypeScript equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                 |
| A successful assembled assistant view becomes dependent `FunctionCall` execution and a certified assistant/tool-result session round                                                                                                                        | `DeepSeekAssemblerToolRound.toFunctionCalls`, `executeAssembledTools`, `appendAssistant`, `appendToolResults`, `Example.counterExecution`, `Example.counterFinalSummary`                                                                                                                                                                                                                                      | Local post-assembly composition only; provider-ID authenticity, external effects, transport, persistence, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                                               |
| A strict multi-call SSE body composes with the source-shaped provider assembler and retains both rich-source and provider-fold certificates                                                                                                                 | `DeepSeekProviderStreamAssembly.validateBody`, `mapRawChunks`, `ValidatedProviderAssembly.source_exact`, `ValidatedProviderAssembly.assembly_exact`, `counterAssemblySummary`                                                                                                                                                                                                                                 | Accepted one-choice text/reasoning/tool-call subset only; replay metadata is rejected and structured failure/abort causes are normalized; wire transport, image/tool-result schemas, call-ID authenticity, and deployed TypeScript equivalence remain outside.                                                                                                                                                                                                                                                                                           |
| A wire-backed assembled tool call reaches dependent execution and appends certified assistant/tool-result messages                                                                                                                                          | `DeepSeekStreamToolRound.executeBodyTools`, `appendRound`, `appendRound_messages`, `counterSummary`, `counterSessionSummary`                                                                                                                                                                                                                                                                                  | Local composition over the strict accepted subset; network/authentication, external effects, persistence, retry/cancellation, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                           |
| A wire-backed assembled tool call is resolved through nearest-first scopes and approval before dependent execution/session append                                                                                                                           | `DeepSeekScopedStreamToolRound.executeBodyScopedTools`, `ScopedExecutionTrace.toExecutedTools`, `appendRound`, `appendRound_messages`, `appendRound_nextSeq`, `Example.scopedDualRoundSummary`, `Example.scopedDualSessionSummary`                                                                                                                                                                            | Scoped/approval-routed local composition; scope construction, authenticated approval, external effects, persistence, cancellation, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                                      |
| A configured local process returns a complete stream body whose status/SSE certificate feeds the same provider/dependent/session round                                                                                                                      | `DeepSeekProcessStreamToolRound.executeWith`, `ProcessedRound`, `counterRun`, `counterSummary`                                                                                                                                                                                                                                                                                                                | Deterministic complete-body process evidence only; network reachability, credentials, process trust, incremental delivery, cancellation, persistence, external effects, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                 |
| A configured process returns a complete scoped stream body and preserves scoped approval/execution through assistant/tool-result append                                                                                                                     | `DeepSeekProcessScopedStreamToolRound.executeWith`, `ProcessedScopedRound`, `Example.scopedDualRun`, `Example.scopedDualProcessSummary`                                                                                                                                                                                                                                                                       | Deterministic complete-body process/SSE evidence only; network reachability, credentials, process trust, incremental delivery, cancellation, persistence, external effects, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                             |
| A process-backed incremental provider assembly feeds dependent execution directly, while a fuel/cancellation prefix retains typed provider/tool state without dispatch                                                                                      | `DeepSeekCurlProviderAssemblyToolRound.executeWith`, `ProcessedToolRound`, `appendRound_messages`, `counterSummary`; `DeepSeekCurlProviderAssemblyToolPrefix.executeWith`, `PendingProviderPrefix`, `CompletedToolPrefix`, `counterPendingSummary`, `counterTerminalSummary`                                                                                                                                  | Synchronous line-oriented local evidence only; blocked-read interruption, backpressure, reconnects, credentials, process trust, persistence, external effects, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                          |
| A certified terminal rich assistant view appends to the local session surface with explicit numeric call-ID and source-event certificates                                                                                                                   | `DeepSeekSessionBridge.finishAssistant`, `appendFinishedAssistant`, `appendFinishedAssistant_messages`                                                                                                                                                                                                                                                                                                        | The caller supplies unique numeric IDs and earlier source sequences; provider-ID authenticity, persistence, and whole-session equivalence remain outside the claim.                                                                                                                                                                                                                                                                                                                                                                                      |
| Accepted text, one-tool, mixed, and multi-call responses compose into a pure append-only session runner with contiguous sequence and tool-call-count certificates                                                                                           | `DeepSeekSessionRunner.finishText`, `finishTool`, `finishMixed`, `finishMulti`, `Runner.append`, `Runner.appendMixed`, `Runner.appendMulti`, `Runner.append_session_messages`, `Runner.append_nextCall`                                                                                                                                                                                                       | Local sequential composition only; transport, cancellation, persistence, external execution, and full Harness event/session equivalence remain outside the claim.                                                                                                                                                                                                                                                                                                                                                                                        |
| A decoded non-streaming DeepSeek response admits only one indexed terminal assistant choice and appends through the same local runner with exact sequence/message/tool-count certificates                                                                   | `DeepSeekApiSession.acceptResponse`, `DeepSeekApiSession.view`, `DeepSeekApiSession.Runner.appendApi`, `DeepSeekApiSession.Runner.appendApi_session_messages`                                                                                                                                                                                                                                                 | Singleton index-zero success subset only; extra choices, unsupported finishes, empty payloads, transport, persistence, provider-ID authentication, external execution, and whole-session equivalence remain outside.                                                                                                                                                                                                                                                                                                                                     |
| An indexed `Session.ModelRequest` crosses an injected complete transport, admits the response, and appends it to the same schema-indexed session runner with header/request continuity                                                                      | `DeepSeekSessionRequest.executeCompleteAndAppend`, `appendAccepted`, `appendAccepted_messages`, `appendAccepted_nextSeq`, `appendAccepted_nextCall`, `appendAccepted_latestHeader`, `appendAccepted_modelRequest_isSome`                                                                                                                                                                                      | Local injected-transport composition only; credentials, remote/provider behavior, parser-backed tool-schema validity, persistence, external effects, and deployed Harness equivalence remain outside.                                                                                                                                                                                                                                                                                                                                                    |
| A counted prefix of explicitly framed `List UInt8` bytes decodes to exact raw frames and a typed durable log, exposing any discarded suffix bytes                                                                                                           | `DurableBytes.decodeFrame_encode`, `decodeFrames_encodeMany`, `scanBytesPrefix_encode`, `Example.valid_bytes_scan`                                                                                                                                                                                                                                                                                            | The format and raw-frame codec are pure Lean contracts; no JSON rendering compatibility, filesystem, `fsync`, cryptographic authentication, or arbitrary EOF/count inference follows.                                                                                                                                                                                                                                                                                                                                                                    |
| A supported current-Harness session prefix assigns fresh local call IDs and jointly validates rich appends plus intrinsic protocol events                                                                                                                   | `SessionRefinement.RefinedEvent`, `ValidatedJsonLog.projection_exact`, `validate_example`, `validate_message_example`, `validate_message_example_retains_reasoning`, `accept_assistantImageBlock`, `validate_tool_message_example`, `validate_replacement_message_example`, `validate_header_chunk_example`, `validate_metadata_example`, `accept_assistantChunk_reasoning`, `accept_assistantReasoningBlock` | Restricted turn/step/tool plus request headers, route context, todo snapshots, seed markers, text and reasoning assistant chunks, text/reasoning/image/complete-tool-call surface blocks, and exact append/replacement operations; malformed ranges, incomplete source coverage, unsupported header fields, unknown todo statuses, nonempty seed payloads, unsupported chunk kinds, multimodal tool-result blocks, and extensions fail closed. Reasoning and image surface blocks remain wire-visible and are omitted from the smaller local projection. |
| A tool-result session carrying provider-owned `error`/`meta` fields can be validated without losing those fields                                                                                                                                            | `SessionOpaqueMetadata.validateLogRetainingMetadata`, `metadata_example_projection`                                                                                                                                                                                                                                                                                                                           | Only the two named fields are quarantined and retained as raw JSON; no provider/tool metadata semantics, schema equivalence, replay, or complete event-union claim follows.                                                                                                                                                                                                                                                                                                                                                                              |
| A rich provider assistant view cannot enter a session without one unique numeric `CallId` per ordered provider tool call                                                                                                                                    | `StreamSession.CallIdAssignment`, `toSessionToolCalls_length`, `appendAssistant`                                                                                                                                                                                                                                                                                                                              | Assignment authenticity and provider-ID globalization remain adapter obligations.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |

## Module map

| Module                                                         | Delivered responsibility                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| -------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Cordis.Api`                                                   | Dependent signatures, providers, registries, restricted committed views, authorized calls, and call-indexed replies.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.Effect`                                                | Exact and observational reversible effects, LIFO composition, accumulators, and indexed undo stacks.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.EffectContext`                                         | Paper effect-context Definitions 1–3, 6, 8–12 and Theorems 4–5, 7, 10–16: tracking, recovery, composition, lifting, and finite indexed reverse-order recovery.                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.Codec`                                                 | Proof-carrying `Lean.Json` AST codecs with structured nested decode errors.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.Tool`                                                  | Request-indexed tool contracts, capabilities, certified outcomes, catalogs, and policy decisions.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.ToolWire`                                              | Raw-call admission plus request-dependent success/failure result codecs and certified-result encoding.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.Registry`                                              | Dependent provider updates, exact recovery, distinct-key commutation, and satisfaction witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.Protocol`                                              | Indexed turn/step/pending-call protocol, raw validation, typed trace reconstruction, and replay theorems.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.Policy`                                                | Single-use lease pools and exact-subject proposed/decided/dispatched/settled traces.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.Batch`                                                 | Strongly certified, pure, heterogeneous two-call evaluation-order equivalence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.Stream`                                                | Bounded typed assistant-text streams and raw-chunk replay/reconstruction.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.Lifecycle`                                             | Finite synchronous component lifecycle with committed views, recovery stacks, diversion, and withdrawal guards.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.Examples.Counter`                                      | Verified local read/increment contracts and providers over a modeled natural-number counter.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.Examples.CounterWire`                                  | Counter name resolution, codecs, admission proofs, capabilities, and raw examples.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.GenericHarness`                                        | Generic phase-indexed dependent runner, exact-call policy rejection/completion evidence, dispatch results, and joint model/lease/ID/log history.                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.GenericSessionHarness`                                 | Reusable rich `Session` wrapper over any `GenericHarness.Config`, with request reconstruction, an indexed request-ready handoff, exact rich-to-structural projection, and generic lifecycle/call append transitions.                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.Session`                                               | Visibility-indexed rich events, exact append/replacement surface witnesses, contiguous logs, header/message reconstruction, and structural protocol projection.                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.SessionValidation`                                     | Terminating range location and proof-producing validation from typed untrusted events to `ValidatedAppend`, `ValidatedSuffix`, and `ValidatedLog`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.SessionTheoremBridge`                                  | Stable `ValidatedAppend.applies` and `ValidatedLog.replays` theorems exposing the exact intrinsic transition, physical log, surface/message, header, sequence, and `ValidLog` endpoints.                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.RichStream`                                            | Indexed interleaved content blocks, exact raw validation/replay, terminal usage/error/abort discipline, and replay-metadata alignment.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.Schedule`                                              | Arbitrary finite `List.Perm` invariance for certified commuting pure effects, including exact successor, undo, and recovery equality.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.ParallelHarness`                                       | Bounded proof-carrying parallel windows, model-order commits, exclusive barriers, and pure cancellation drains, all with endpoint/recovery witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.ParallelSchedule`                                      | Arbitrary finite sequences of certified windows and exclusive barriers, with exact composed endpoint/recovery equality, model-order reports, and global task-ID uniqueness; pure schedule semantics only.                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.AsyncHarness`                                          | Indexed pending/running/terminal fibers, typed start/complete/fail/cancel transitions, completion-order traces, drained schedule certificates, and a concrete race/cancellation witness; bounded pure state-machine semantics only.                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekAsyncHarness`                                  | Cooperative `ContextAsync.race` over two process-backed complete-body text-prefix jobs, retaining the first typed result and a terminal-phase bridge; the fixture is real, while blocked-read interruption, fairness, cleanup, and deployed async semantics remain external.                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekAsyncStreamHarness`                            | Cooperative race over two process-backed complete-body streamed Harness continuations; the winner retains dependent tool executions, two round witnesses, the final model, and runner endpoint. The fixture is real, while blocked-read interruption, fairness, cleanup, and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekAsyncStreamHarnessTimeout`                     | Cooperative race over timer-backed byte-prefix streamed continuations; fast and timeout children retain dependent endpoints, and timeout is represented by an exact prefix plus cancelled phase. Task-cancellation delivery, arbitrary cleanup, fairness, backpressure, reconnects, authenticity, and deployed equivalence remain external.                                                                                                                                                                                                                                                                            |
| `Cordis.DeepSeekExternalToolProcess`                           | Configured local process observation retains command configuration, stdout/stderr, exit code, parsed JSON, and a typed decoded result; `AcceptedResult.certified` requires an explicit `ToolSpec.post` proof before constructing `CertifiedOutcome`. Process identity, sandboxing, authentication, exactly-once effects, cleanup, and deployed Harness equivalence remain external.                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekExternalToolRound`                             | Accepted dependent process results are paired with an exact two-event Session append and proven sequence, message, and protocol projections; result rendering is supplied explicitly and provider/deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekExternalGenericRound`                          | Reusable process-to-generic-runner handoff: `observeAndDispatch` keeps the full typed observation and requires a caller-supplied dependent acceptance/dispatch certificate; the executable counter fixture advances model, lease, ID, record, and rich-session invariants, while a decodable nonzero-exit process remains uncertified. Process identity, sandboxing, authentication, exactly-once effects, cleanup, and deployed Harness equivalence remain external.                                                                                                                                                  |
| `Cordis.DeepSeekExternalGenericConversation`                   | Finite dependent scripts over proof-carrying external dispatches; each accepted edge is retained in an indexed runner trace, and completion, fuel exhaustion, and uncertified stops are distinct. Heterogeneous tool/process payloads remain in proof-only edge provenance so the executable result stays usable by `IO`; process identity, sandboxing, authentication, exactly-once effects, cleanup, persistence, provider obedience, and deployed Harness equivalence remain external.                                                                                                                              |
| `Cordis.DeepSeekAsyncStreamCancellation`                       | Cooperative race over policy-bearing streamed children; a cancellation-first fixture retains the typed pre-round stop, unchanged runner/model endpoint, and empty completed prefix while the other branch is a real process-backed continuation. Blocked-read interruption, fairness, cleanup, and deployed equivalence remain external.                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekAsyncStreamRetryCancellation`                  | Cooperative race over retry-aware streamed children; `runWithFinish`/`executeRaceWithFinish` accept a caller-supplied certified finisher while `run`/`executeRace` remain multi-tool wrappers. The winner retains its dependent indexed retry trace, and text plus multi-tool fixtures cover cancellation-first and delayed-child success-first branches. Blocked-read interruption, fairness, cleanup, reconnect, and deployed async retry/cancellation equivalence remain external.                                                                                                                                  |
| `Cordis.DurableSettlement`                                     | Indexed append-only commit frames, collision-free transcript digests, crash-prefix recovery, and typed resume after a retained prefix.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DurableCodec`                                          | JSON-AST raw-frame codec, entry-code decoding, and strict dependent prefix scanning into `DurableSettlement.Log`; malformed, torn, unknown, and non-contiguous frames fail closed.                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DurableBytes`                                          | Pure unary-length binary framing over `List UInt8`, numeric `RawFrame` payload encoding, counted prefix decoding, and exact byte-prefix/scanner witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DurableIO`                                             | Typed append plans plus executable memory and filesystem adapters; tests cover typed resume, an explicit torn suffix, and a temporary-file round trip without claiming fsync or crash atomicity.                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.Coeffect`                                              | Finite dependent contexts, typed get/set/remove and local-operation lift, concrete recovery, specifications, satisfaction, and notifications.                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.UnifiedContext`                                        | In-place/derived realizations, typed realm isolation, metadata interception, and exact finite unfoldings of the unified-context equation.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.ContextualEquivalence`                                 | Key-wise observational equivalence for finite coeffect contexts, a context `Setoid`, and satisfaction/notification quotient invariance.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.OperationalEquivalence`                                | Heterogeneous finite operation tests, partial observations, coarsest generator relation, and the formal paired-inverse counterexample/boundary.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.QuotientEffect`                                        | Definition 36 map relations, Definition 37 admissible effects, and finite composition/recovery of quotient-respecting programs.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.CoeffectQuotient`                                      | Generator bridge proving lifted key-local operations preserve contextual successor, inverse-map, and typed-outcome relations.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.Transformation`                                        | Generated transformation monoids, Lemma 18 closure, full inverse-stable Definition 19 independence, and the Batch/Schedule bridge.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.OperationIndependence`                                 | Full total Definition 39, finite partial distinct-key Theorem 40, Definition 41 interpreter/recovery, and explicit Theorem 42 boundary.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.Removal`                                               | Indexed exact executions, Theorem 20 removal/later-inverse equations, and Corollary 21 recovery under arbitrary inverse permutation.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.MediatedIndependence`                                  | Intrinsic realized branches, observational mediated-closure specification, exact representative bridge, and finite quotient counterexample.                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.MediatedTheorem`                                       | Corrected partial domains, outcome-preserving stage/tree interchange, exact finite whole-run independence, and observational consequence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.PartialTransformation`                                 | Kleisli partial transformation monoids, full cross-closure commutation/yield stability, whole-run consequence, and strictness counterexample.                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.ObservationalPartialTransformation`                    | Relation-respecting partial-map closures, generator descent, observational independence, and a respect-gap counterexample.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.TotalQuotientIndependence`                             | Explicit totality certificates, total forward/yielded-inverse closure transport, quotient independence, admissible effects, and a pure executable fixture.                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DomainTotalQuotientIndependence`                       | Invariant-domain totality and preservation certificates for partial computations, domain-aware closure transport, finite observational independence, and a counter/label fixture that is total only on its certified domain.                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.GlobalRegistry`                                        | Code-only component/fiber/global data, active context/target uniqueness, birth-ranked acyclicity, and orchestration preservation.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.GlobalDynamics`                                        | External code interpretation, ordinary/registration certification, confinement/read obligations, fueled traces, and accumulated recovery.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.GlobalLifecycle`                                       | Phase-indexed lifecycle rules, exact executed landings, inertia/recovery admissions, preservation traces, and a concrete activation/deactivation path.                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.GlobalLifecycleBisimulation`                           | Noncircular external transport contracts, all-eight lifecycle matching, unified well-formed ten-rule certificate, and Finish seam evidence.                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.GlobalNameAction`                                      | Executable bijection action on dependent global data, group/inverse laws, well-formedness and orchestration equivariance, and a weak-old-API counterexample.                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.GlobalNameLifecycle`                                   | Canonical result/oracle/landing/recovery actions and conditional bidirectional lifecycle/unified name equivariance with necessity witnesses.                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.GlobalCalculus`                                        | Unified ten-name exact-endpoint steps, state-map/edit projections, installed-status semantics, and empty-registry-origin traces.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.GlobalTraceFacts`                                      | Conditional recovery confinement, foreign/static/committed continuity, aligned trace episodes, and a bare-admission countermodel.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.GlobalTemporal`                                        | Partial off-source step maps, relation-indexed totalization/commutation/reordering, finite recovery, unload bridge, and countermodels.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.GlobalIteratorIndependence`                            | Oracle-specific continuation reach, partial forward/actual-inverse closures, exact occurrence-indexed family independence, forward-respect-qualified effect-relational independence, separate finite-bound certificate types, a temporal per-step bridge, and boundary counterexamples.                                                                                                                                                                                                                                                                                                                                |
| `Cordis.GlobalTransposition`                                   | Raw `Independent` execution diamonds, exact `Independent` and relation-indexed `ObservationalIndependent` total-map squares, lifecycle-visible exact yield agreement, structural phase commutation, a future frame contract, and a noninjective-undo counterexample.                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.GlobalForeignPhase`                                    | Program-scoped read/ordinary/oracle frame laws, derived compatibility, one- and two-sided framed raw executions with retained lookups, and three finite countermodels separating the required premises.                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.GlobalLandingTransposition`                            | Exact cross-forward lifecycle-yield stability, fixed-program landing provenance, derived target preservation, four-case shared-final Iter/Finish transition diamond, executable example, and necessity models.                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.GlobalActivationTransposition`                         | Fixed-program Begin/Iter/Finish activations, positive-target framing, endpoint/rule determinism, all-nine exact lifecycle diamonds, an actual-second-step transposition wrapper, and root/same-owner necessity witnesses.                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.GlobalActivationOrchestrationTransposition`            | Literal-clause parent/birth countermodels, occurrence-minimal orchestration framing, corrected exact activation/orchestration exchange, frame-necessity models, and representative structural/ordinary/registering examples.                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.GlobalProgress`                                        | Fixed-oracle and freshness-exhaustion deadlocks, finite provider precedence/rank, exact landing-or-raise and recovery authorities, maximal-unloading reasoning, conditional state-local no-deadlock, and executable examples.                                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.GlobalProgressTermination`                             | A supplied strict natural-valued lifecycle potential, exact trace budget/telescoping inequalities, conditional `K + 4` length and cycle bounds, and an executable descending witness; it does not derive the potential or full Theorem 66.                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.GlobalProgressRun`                                     | A supplied progress authority and strict potential drive an exact dependent finite lifecycle runner with retained endpoint `WellFormed` proofs, intrinsic traces, quiescent/full-fuel stop certificates, and initial-potential quiescence; it does not derive the authorities or maximal Theorem 66.                                                                                                                                                                                                                                                                                                                   |
| `Cordis.GlobalProgressAssignment`                              | An explicit lifecycle-step assignment authority recursively reconstructs a dependent `TraceProgramAssignment` for every finite progress-run trace and preserves the runner's endpoint/stop certificates; it does not infer fixed programs, roots, oracles, or reachability.                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.GlobalPaperProgressReplay`                             | Composes an assigned finite progress run with a caller-supplied birth-erased forward trace simulator, retaining source endpoint/stop/length evidence, exact transported assignment, rule/actor projections, and peer relatedness; it does not derive the simulator or maximal Theorem 66.                                                                                                                                                                                                                                                                                                                              |
| `Cordis.GlobalSupport`                                         | Reachable mixed-order/nonunique-support countermodels, combined-order recursion and uniqueness, state-local provision/failure/parent laws, corrected support-equals-active theorem, and necessity/positive examples.                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.GlobalTraceRewrite`                                    | Exact indexed adjacent trace windows, occurrence/program assignment, assignment-preserving activation and orchestration adapters, rule/actor permutations, and a nonempty-context executable rewrite.                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.GlobalDeletion`                                        | Intrinsic relation-indexed keep/drop replay, assignment reconstruction, multi-vestigial exact orchestration suffixes, positional templates, semantic redraw detection, and parent/allocator countermodels.                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.GlobalPaperRelation`                                   | Birth/clock-erased rule and outside-deletion Setoids, strict-rule bridges, bidirectional well-formed orchestration simulation, certified-WF directional deleted-shadow replay, and lifecycle countermodels.                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.GlobalPaperTraceSimulation`                            | Birth-erased finite forward/backward trace replay with assigned-step transport, endpoint well-formedness, exact rule/actor projections, forward/backward orchestration-only constructors, and occurrence-specific lifecycle evidence exercised by a leave/unload witness; global lifecycle matching remains explicit.                                                                                                                                                                                                                                                                                                  |
| `Cordis.GlobalPaperShiftedLifecycle`                           | A concrete non-reflexive birth-erased replay whose peer shifts only `nextBirth`, rebuilds dependent L-Leave/L-Unload transitions, and transports their assigned trace with exact rules, actors, well-formed endpoints, and final relatedness; it is not global lifecycle bisimulation.                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.GlobalPaperTraceDeletion`                              | Relation-indexed positional keep/drop replay with assigned shadow traces and a safe orchestration deletion example.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.GlobalPaperTraceNormalization`                         | Finite connected composition of supplied adjacent-rewrite certificates, retaining assignments and proving terminal relation plus rule/actor permutations; includes one-link and connected two-link activation/orchestration witnesses with executable terminal ledgers; no automatic normal form or confluence.                                                                                                                                                                                                                                                                                                        |
| `Cordis.GlobalPaperTraceNormalizer`                            | A terminating dependent normalizer driven by an explicit normal-form predicate, rewrite authority, and decreasing Nat measure; it proves finite-chain endpoint relation plus rule/actor permutations while keeping strategy, canonical form, and global confluence as external obligations.                                                                                                                                                                                                                                                                                                                            |
| `Cordis.GlobalPaperTraceConfluence`                            | A generic decreasing/local-diamond Newman kernel proving global joins and unique irreducible endpoints; `AuthorityLinked` reconstructs selected `normalizeFuel` paths and `normalize_results_unique` proves equal final `TracePackage` endpoints under `ConfluentAuthority`.                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.GlobalPaperTraceScopedConfluence`                      | An indexed finite-family confluence layer: package identity, selected source/target equations, decreasing fuel, independent path lifting, and a nonempty activation/orchestration normalization fixture with executable endpoint projections.                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.GlobalRelations`                                       | Key-indexed rule observation, ambient/table effect observation, setoid and temporal-undo bridges, and incomparability examples.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.GlobalRuleInvariance`                                  | Dependent fiber-control transport, exact bidirectional orchestration matching, heterogeneous related tables, and an inertia countermodel.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.GlobalRuleObservations`                                | Provider/target/reliance/quiescence transport, dependent phase guards, active-table relations, and explicit relation-separation examples.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.GlobalVestigial`                                       | Exact effect-equivalence to removal, corrected bidirectional orchestration squares, and well-formed counterexamples to omitted parent cases.                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.GlobalSpatial`                                         | Located/nested episode order, persistent dependency resolution, provider no-unload, conditional table constancy, and local reloading classification.                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.RuntimeRefinement`                                     | Path-aware current-Harness `StreamChunk` JSON-AST decoding into proof-producing rich-stream validation with explicit unsupported cases.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.RuntimeFailureRefinement`                              | Exact terminal `error`/`aborted` `LlmFailure` decoding with an ordinary-prefix certificate, kept separate from successful rich-stream validation.                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.RuntimeOutcomeRefinement`                              | Unified dependent dispatcher for successful rich-stream and normalized `error`/`aborted` certificates, retaining both structured rejection reasons when neither language accepts.                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.RuntimeOutcomeSession`                                 | Session-runner boundary for the unified outcome: successful traces append a finished assistant view, while normalized failures preserve the runner and typed failure certificate without policy fabrication.                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.SessionRefinement`                                     | Stateful supported-subset Harness session decoding with restricted request headers, route context, todo snapshots, seed markers, text/reasoning assistant chunks, fresh call-ID assignment, text/reasoning/image/tool-call surface retention, exact append/replacement witnesses, and joint Session/Protocol proof-producing validation.                                                                                                                                                                                                                                                                               |
| `Cordis.SessionRefinementSurfaceCodec`                         | Proof-carrying canonical AST, JSONL-text, and UTF-8-byte encoding/decoding for text-only user messages, text/reasoning/tagged-raw-image/complete-tool-call assistant messages, singleton-text tool results, and a metadata-aware raw tool-result emitter, preserving safe integers, usage, provenance, replacement ranges, call IDs, raw arguments, `isError`, and quarantined `error`/`meta`; image schema semantics, provider metadata semantics, unsupported surface operations, and other event variants remain external or fail closed.                                                                           |
| `Cordis.SessionOpaqueMetadata`                                 | Lossless quarantine of `tool/result.data.error` and `tool/result.data.meta`: sanitize only those opaque fields, validate the supported session projection, and retain the exact original JSON values in order. Semantics remain external.                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.TextRefinement`                                        | Newline-delimited UTF-8 JSON parsing into exact AST lines, plus proof-carrying composition with stream/session/failure refinement and explicit text/encoding failures.                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.HarnessPersistenceRefinement`                          | Logical Harness JSONL header/storage decoding, lossless text/reasoning/tool packed-row expansion, safe sequence/time reconstruction, and composition with stateful session validation; physical compression and crash repair remain external.                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.HarnessPersistenceBytes`                               | Pure `ByteArray` UTF-8/JSONL ingress retaining source bytes, decoded text, parsed rows, packed expansion, and the final Session/Protocol projection; positive and rejection fixtures run at the executable boundary.                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekHarnessEventArchive`                           | Certificate-gated attachment of a lossless current-Harness event archive plus stateful semantic validation to `ConversationRunner`; opaque/extension events reject restoration, and the tool-message fixture rebuilds a typed request.                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekHarnessEventIgnorableProjection`               | Positional archive projection for explicit `ignorable: true` rows: only opaque ignorable entries are dropped, supported wire certificates and raw positions are retained, and required opaque entries reject. Physical sequence renumbering and local session replay remain separate obligations.                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekHarnessEventIgnorableNormalization`            | Supported-subset continuation of the explicit-ignorable projection: retained rows are renumbered contiguously, supported source-event/surface references are remapped, and `SessionRefinement.validateJsonLog` certifies the local session; duplicate sequences, missing references, malformed rewrites, and semantic failures reject.                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekHarnessEventSimulation`                        | Occurrence-indexed source-to-local replay for a normalized supported log: `DecisionLedger` retains every keep/drop decision, `ReplayStep` carries the exact pre-state refinement, and `SourceReplay` proves protocol erasure and final session projection. Finite supported subset only; no complete deployed-Harness equivalence.                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekHarnessEventArchiveReplay`                     | Archive-aware dependent replay: `ArchiveReplay` pairs the indexed normalized `SourceReplay` with its inductive keep/drop ledger, retains exact archive/kept raw rows, and projects dropped opaque rows and positions. The nine-row tool fixture exercises eight supported transitions plus one explicit opaque no-op.                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekHarnessEventIgnorableRunner`                   | Attaches a normalized validated endpoint to `ConversationRunner`, preserves exact session/step certificates, and rebuilds a typed `ChatRequest`; the tool fixture exercises user/assistant/tool messages after ignorable-row normalization.                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.DeepSeekHarnessEventIgnorableTransport`                | Carries that normalized runner through the existing process-backed complete-response conversation trace, retaining final runner/model/stop evidence in a dependent certificate; the deterministic fixture exercises one no-tool completion.                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.DeepSeekHarnessExtensionArchive`                       | Schema-indexed attachment of a required-extension archive to `ExtensionRunner`; restoration derives the tool-call count, proves exact session equality, and rebuilds a typed request from the same indexed endpoint.                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekHarnessExtensionPersistence`                   | Extension-only persistence composition across JSONL AST, text, UTF-8 bytes, and `DurableIO.Backend`; exact header/raw-row certificates restore the indexed runner and schema-certified request, while core/ignorable rows reject.                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekHarnessMixedPersistence`                       | Schedule-indexed mixed persistence certificate: one lossless archive covers the complete source row stream while independent core and dependent-extension projections retain exact source ASTs and indexed endpoints; no combined arbitrary-schema replay is claimed.                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekHarnessSchemaLift`                             | Arbitrary-schema transport for validated core sessions: dependent core kinds, payloads, intents, surface transitions, headers, sequence proofs, and protocol projections lift into any `ExtensionSchema`; the certificate example exercises a custom schema without claiming extension-row decoding or mixed replay.                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekHarnessMixedReplay`                            | Tagged mixed JSON replay for arbitrary schemas: core rows use the stateful core decoder, custom log-only extension rows interleave with a phantom shadow clock, and exact sequence, surface/header, protocol, and typed rejection witnesses are retained; custom surface/core-kind extension rows are rejected.                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekHarnessTransportContract`                      | Injected transport composition for prepared requests: successful status, one retained response decoder, `acceptValidated` session admission, exact accepted-response/body equations, runner append endpoint, and typed transport/status/decode/session errors; local 200/tool-call and 503 fixtures are executable.                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekHarnessTransportToolRound`                     | Carries that retained single-decoder response through dependent tool execution without reparsing, then certifies the assistant-plus-tool-result runner endpoint, exact sequence growth, and tool-count update; local success and typed 503 fixtures are executable.                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekHarnessEventText`                              | UTF-8/JSONL text and `ByteArray` ingress for the event-archive attachment, retaining exact source/decoded text and archive/session certificates before restoring a `ConversationRunner`; invalid UTF-8 and opaque/extension events fail closed.                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekHarnessEventProcessOutcome`                    | Carries restored text/byte event runners through complete-body rich outcomes and fuel-bounded streamed conversations, retaining prepared request, process/round, tool, endpoint, archive, session, projection, and completion/stop certificates; caller-supplied source and complete-body process boundaries remain explicit.                                                                                                                                                                                                                                                                                          |
| `Cordis.DeepSeekHarnessEventProcessSchema`                     | Composes restored text/byte event runners with the heterogeneous registry-aware process path: the prepared `stream: true` plan, complete body, schema step, dependent runner endpoint, archive/session equality, raw-line equality, and exact projection certificates remain indexed together; the fixture checks the two-tool weather/clock path and `8 -> 11` endpoint; no raw reparse needed.                                                                                                                                                                                                                       |
| `Cordis.LoaderHMR`                                             | Definition 74 entry records, keyed configuration reconciliation, Algorithm 8 fixed-point accepted/declined classification with cycle fallback, declined-boundary stale detection, and Algorithm 10 indexed transactional reload with exact failure rollback; dynamic imports, filesystem watches, real fibers, and deployed loader equivalence remain external.                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekHarnessPayloadText`                            | Composes that text/byte restore with `SessionPayloadArchive.PayloadLog`, retaining exact per-event payload objects, block tags, usage, and tool-result metadata beside the same runner; provider-owned schemas remain raw.                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekHarnessPayloadPersistence`                     | Carries the payload ledger through logical persisted JSONL, pure bytes, and memory/temporary-file reads while tying the expanded events, restored runner, and raw payloads by dependent indices; storage and provider-owned payload semantics remain separate.                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekHarnessOpaqueMetadata`                         | Lossless quarantine of tool-result `error`/`meta` alongside a sanitized `ConversationRunner`; exact metadata order, session equality, and request reconstruction are certified while provider/tool semantics remain uninterpreted.                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekHarnessMetadataArchive`                        | Composes the full current-event envelope archive with the sanitized opaque-metadata runner seam, retaining raw envelopes, one known opaque event, exact metadata order, and a sanitized request projection without dropping the record.                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekHarnessPersistenceIO`                          | Byte-backed UTF-8/JSONL read certificates attach memory- and temporary-file-backed persistence to a DeepSeek `ConversationRunner`, preserving exact session/request equalities and structured invalid-encoding failures without claiming fsync or crash durability.                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekHarnessPersistenceTransportRound`              | Composes a byte-backed restored runner with a complete typed request, one injected response decoder, `acceptValidated`, typed tool execution, and an exact final `ConversationRunner`; the executable fixture proves archive/session/request/assistant/tool endpoint alignment without claiming live or durable deployed behavior.                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekHarnessEndToEnd`                               | Proof-carrying composition of byte-backed restore and retry-aware conversation: `PersistedRetryRun` keeps the restored archive runner in the dependent trace index, while the executable fixture checks archive `nextSeq = 8`, final `nextSeq = 11`, two rounds, one transient failure, model `0`, and typed completion; memory/injected transport only.                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekHarnessPersistenceProcessOutcome`              | Composes byte-backed restore with the actual `IO.Process` outcome path: `PersistedProcessRound` ties the restored runner to a streaming request, complete process body, rich/tool outcome, dependent execution, and exact endpoint; the deterministic shell fixture checks `8 -> 10` and body length `523`. Provider/process trust and deployed equivalence remain external.                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekHarnessPersistenceStreamRetry`                 | Extends byte-backed restore through a real `IO.Process` into a dependent two-round streamed retry trace: the shell fixture emits two tool calls, then terminal text after the first tool result is serialized; executable projections check `8 -> 12`, two rounds, two first-round calls, one attempt, model `0`, and typed completion. Provider/process trust, durability, cancellation, external effects, and deployed equivalence remain external.                                                                                                                                                                  |
| `Cordis.DeepSeekHarnessPersistenceStreamRetryCancellation`     | Adds a pre-round cancellation certificate to that persisted process-backed trace. `runRestoredWithFinish`/`runFixtureWithFinish` carry a caller-supplied certified finisher while the legacy fixture selects multi-tool; the first streamed tool round is retained, cancellation is decided before round one, and executable projections check `8 -> 11`, one round, two first-round calls, timeout reason, preserved model `0`, and exact cancellation. In-flight interruption, cleanup, durability, external effects, and deployed cancellation equivalence remain external.                                         |
| `Cordis.DeepSeekHarnessPersistenceFileStreamRetryCancellation` | Repeats the persisted process-backed cancellation path through an actual temporary-file `DurableIO.FileBackend`, retaining the read certificate beside the exact `8 -> 11` prefix. Its `runRestoredWithFinish`/`runFixtureWithFinish` seam preserves caller finisher choice through the file layer; the default fixture uses multi-tool. The file lifetime is scoped to `withTempFile`; fsync, stable media, crash recovery, in-flight interruption, cleanup, external effects, and deployed equivalence remain external.                                                                                              |
| `Cordis.DeepSeekHarnessEventFileStreamRetryCancellation`       | Writes the supported current-Harness event JSONL fixture to a temporary file, reads and byte-checks it before restoring the event archive/session, then runs the restored runner through a caller-supplied finisher at the process-backed cancellation boundary; the default fixture uses multi-tool and executable projections retain byte equality, `8 -> 11`, one round, two first-round calls, timeout, and model `0`. `withTempFile` cleanup, fsync, stable media, crash recovery, blocked-read interruption, process cleanup, provider authenticity, external effects, and deployed equivalence remain external. |
| `Cordis.DeepSeekHarnessEventFileLocalSseRetryConversation`     | Takes the supported current-Harness event JSONL fixture through a temporary-file restore into two real loopback HTTP/SSE retry rounds; dependent certificates retain event archive/session equality, one typed 503 per round, distinct rebuilt request bodies, `RequestProvenance` for both rounds, and executable `8 -> 10` growth. File durability, provider authenticity, blocked-read interruption, external effects, and deployed equivalence remain external.                                                                                                                                                    |
| `Cordis.DeepSeekHarnessEventFileProcessSchema`                 | Takes the supported current-Harness event JSONL fixture through a temporary-file restore into the heterogeneous weather/clock schema process; the dependent result retains source/read bytes, archive/session equality, the registry-derived streaming plan, complete body, schema step, and executable `8 -> 11` endpoint. Provider obedience, credential authenticity, durable storage, cancellation, external effects, and deployed equivalence remain external.                                                                                                                                                    |
| `Cordis.DeepSeekHarnessPersistenceStreamBytePrefixTimeout`     | Composes memory-backed restore with timed byte-prefix streaming; the fuel fixture checks `8 -> 10`, one accepted round, and explicit exhaustion, while the terminal companion checks `8 -> 11`, two rounds, completion, and model `0`, with exact restored-session equalities. Durable media, crash recovery, blocked-read interruption, provider/process authenticity, cleanup, external effects, and deployed equivalence remain external.                                                                                                                                                                           |
| `Cordis.DeepSeekToolSchema`                                    | Bounded proof-carrying function-tool admission: object parameters, primitive property types, required-name and duplicate-name checks, proof-carrying argument objects, exact source JSON retention, and certified request construction.                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekToolAdmission`                                 | Ties a raw provider `FunctionCall` to one certified tool name and carries its `ValidatedArguments` proof before generic capability execution; provider obedience, call-ID authenticity, and capability correspondence remain external.                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekGenericBridge`                                 | Composes provider-schema admission with an explicit named `SchemaToolBinding` and generic dependent `Config.validate`, returning both certificates and an existentially indexed local call; schema semantic equivalence and execution remain external.                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekSchemaExecution`                               | Consumes the combined provider/generic certificate, applies the existing dependent policy, and dispatches only allowed calls through the committed generic `View`; policy/provider failures are typed and raw compatibility execution remains separate.                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekSchemaHarness`                                 | Reifies successful schema-aware executions as the existing `DeepSeekHarness.ExecutedTool`, retains the provider certificate, and reuses exact tool-result/session/`ConversationRunner` append theorems without re-execution or deployed-semantics claims.                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekSchemaRound`                                   | Bounded complete-body round for one accepted singleton assistant tool call: exact response/tool-call extraction, schema-certified dispatch, typed rejection of zero/multiple calls, and certified runner endpoint.                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekSchemaMultiRound`                              | Bounded complete-body round for a nonempty homogeneous list of calls under one explicit schema/generic binding: sequential dependent execution, exact execution-list length, typed later-call failures, and certified multi-result runner endpoint. Heterogeneous registries and deployed semantics remain external.                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekSchemaRegistry`                                | Bounded heterogeneous registry: dependent name lookup selects an entry-specific schema binding, sequential calls may target different generic operations, and the runner endpoint retains exact execution length/sequence evidence. Live transport and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekScopedRegistry`                                | Nearest-first scoped registry with dependent entries, terminal shadowing restrictions, typed resolve/approval failures, and an approval ticket retained before provider execution; automatic/review/rejection fixtures are executable, while scope construction and deployed Harness semantics remain external.                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekSchemaConversation`                            | Connects registry-derived tool declarations to a typed complete-body transport request and validated response, retaining the wire plan, response certificate, heterogeneous execution batch, and runner endpoint for one round.                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekSchemaConversationBytes`                       | Byte-backed counterpart of the heterogeneous conversation round: exact typed request/UTF-8 bytes, exact response bytes, decoded/validated response, accepted calls, dependent batch, and runner endpoint are retained in one result; invalid UTF-8 and non-2xx responses remain typed.                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekSchemaConversationLoop`                        | Fuel-bounded heterogeneous transport loop with an explicit terminal no-tool response, dependent round history, model/runner endpoint, and distinct exhaustion stop; retries, cancellation, persistence, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekSchemaLocalHttp`                               | Real curl/HTTP loopback instantiation of the heterogeneous schema loop: the fixture validates two declared tools and complete mode, sends a weather/clock tool round followed by a terminal body, and retains request counts, server exit, dependent tool history, final model, and runner endpoint. Remote/provider/persistence/deployed semantics remain external.                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekSchemaTransportRetryCancellation`              | Heterogeneous schema retry/cancellation composition: one validated response feeds terminal or dependent registry execution, retry history and exact endpoints are retained, and timeout-before-send, completion, and exhaustion/cancellation remain distinct; live IO interruption, persistence, and deployed equivalence remain external.                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekSchemaProcessRetryCancellation`                | Process-backed instantiation of the heterogeneous retry/cancellation boundary: a deterministic `sh` fixture emits 503, weather/clock tool calls, and a terminal no-tool body across attempts while the same dependent retry trace retains exact endpoints; network, credentials, shell trust, and deployed semantics remain external.                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekSchemaStreamConversation`                      | Complete-body SSE/rich-stream/session continuation for the heterogeneous registry: a certified `stream: true` request, terminal streamed-body validation, mixed registry dispatch, and a caller-fueled history with distinct completion/exhaustion stops; incremental delivery and deployed semantics remain external.                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekSchemaStreamPrefixConversation`                | Line-oriented process-prefix continuation for the heterogeneous registry: exact accepted prefixes, typed line-budget/cancellation stops, and post-`[DONE]` dependent dispatch into the existing runner; byte framing, blocked-read interruption, and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekSchemaStreamErrors`                            | Heterogeneous streamed provider-failure continuation: dependent failure certificates retain entry/schema/admission/policy/error/model evidence, convert to opt-in `isError` tool results, and prove a later terminal continuation; retry, cancellation, persistence, and deployed error semantics remain external.                                                                                                                                                                                                                                                                                                     |
| `Cordis.HarnessPersistenceIO`                                  | Executable UTF-8 byte/text adapter over memory and filesystem backends: exact read certificates, canonical replacement, validated append-only rows, and structured invalid-encoding/semantic failures; host acknowledgements are not durability proofs.                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekApi`                                           | Typed OpenAI-compatible DeepSeek chat request construction, fail-closed response decoding, dependent parse/decode certificates, and an explicit transport/status/API-error boundary.                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekApiBytes`                                      | Byte-backed request plans and response execution: exact UTF-8 request body bytes, decoded response text, parse/decode certificates, and distinct invalid-UTF-8/non-2xx errors over an injected byte transport; its fixture is executable.                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekRequestMode`                                   | Type-indexed complete/streaming request plans with a proof tying the serialized `stream` flag to the mode; terminal execution accepts only the complete certificate.                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekStream`                                        | Strict UTF-8/SSE framing, typed delta decoding, retained raw data-frame certificates, and explicit terminal/error boundaries.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.DeepSeekStreamFailure`                                 | Raw typed certificate for complete SSE terminal failures (`content_filter` or `insufficient_system_resource`), retaining leading frames, terminal choice/reason, and optional usage without normal rich/session coercion.                                                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekTerminalOutcome`                               | Complete-body dispatcher over provider failures plus text, one-tool, mixed, and finite multi-call rich certificates; the selected dependent outcome and typed rejection remain explicit.                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekCurlStream`                                    | Complete-body process-backed SSE validation with typed process/status/stream errors and a deterministic `sh` fixture; incremental reader semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekCurlOutcome`                                   | Process-backed complete-body terminal-outcome validation: process, status, provider-failure, and rich semantic errors remain distinct while the selected dependent outcome is retained.                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekOutcomeSession`                                | Typed terminal-outcome dispatch: provider failures preserve the unchanged runner, while successful text/tool/mixed/multi outcomes finish and append through the proof-carrying session runner; source-event evidence and failure-message policy remain caller obligations.                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekOutcomeConversation`                           | Process-backed terminal-outcome handoff into `ConversationRunner`: provider failures preserve the conversation, while successful rich assistants append with model/tool-count proofs and route completed `FunctionCall` values through the existing dependent executor, including certified tool-result appends; retry, persistence, cancellation, and provider-ID policy remain caller-controlled.                                                                                                                                                                                                                    |
| `Cordis.DeepSeekOutcomeTransportLoop`                          | Generic-`Transport` complete-body rich-outcome continuation: type-indexed streaming requests, terminal validation, dependent tool execution, updated-runner continuation, typed provider-failure/completion/fuel stops, and a deterministic two-round fixture; incremental IO, retry, cancellation, and deployed equivalence remain external.                                                                                                                                                                                                                                                                          |
| `Cordis.DeepSeekCurlSession`                                   | Complete-body process-backed SSE composition into accepted rich/session terminal values, retaining the wire certificate and runner append invariants; live/deployed session semantics remain external.                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekHarnessProcess`                                | Request-provenance wrapper for the process/session seam: a typed `RequestSource` and exact `RequestPlan` remain indexed into the complete-body response and runner append endpoint, with request and process errors kept separate.                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.DeepSeekHarnessProcessOutcome`                         | Rich process-backed provenance wrapper: a typed streaming request source/plan remains indexed into provider-failure or text/tool/mixed/multi terminal outcomes, dependent execution, and the final `ConversationRunner` endpoint; request, process, and execution errors remain distinct.                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekHarnessProcessSchema`                          | Registry-aware process provenance: the certified heterogeneous tool source and exact `stream: true` plan remain linked to the validated SSE body, schema-dispatched step, and dependent runner endpoint; request, process, and registry-execution errors remain distinct.                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekHarnessProcessSchemaPrefix`                    | Prefix-process provenance: the same registry-certified `stream: true` plan remains indexed into an accepted SSE prefix, typed fuel/cancellation stop, or completed heterogeneous schema step and runner endpoint; byte framing and blocked-read semantics remain external.                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekHarnessProcessSchemaPrefixConversation`        | Fuel-bounded prefix conversation provenance: every completed tool-round witness retains its prepared heterogeneous plan and accepted prefix, and cancellation/round exhaustion retain the attempted plan; blocked-read and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekCurlIncremental`                               | Line-oriented process-backed SSE delivery with callback observations under an explicit read budget, reconstructed-body strict validation, and typed process/status/stream/callback/limit failures; byte-level and live cancellation semantics remain external.                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekCurlPrefix`                                    | Process-backed proof-carrying prefix execution with synchronous line-boundary fuel/cancellation stops, raw-body retention, normalized frame certificates, and child cleanup; blocked-read cancellation and deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekCurlProviderAssemblyIncremental`               | Line-prefix process fold retains parsed rich state, raw/mapped provider chunks, and exact terminal assembly; external IO and deployment remain outside.                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `Cordis.DeepSeekCurlPrefixSession`                             | Completed prefix projection into accepted text/tool/mixed/multi stream semantics and append-only runner proofs, with fuel/cancellation preserved as typed stops rather than response errors.                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekAsyncHarness`                                  | Cooperative `ContextAsync` race over two process-backed complete-body text-prefix jobs, retaining the first typed prefix/session result and a terminal-phase bridge; blocked-read cancellation, fairness, cleanup, and deployed equivalence remain external.                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekAsyncStreamHarness`                            | Cooperative `ContextAsync` race over two complete-body streamed Harness continuations, retaining typed tool execution, round, model, and runner evidence from the winner; synchronous reads, fairness, cleanup, and deployed async equivalence remain external.                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.DeepSeekAsyncStreamHarnessTimeout`                     | Cooperative `ContextAsync` race over timer-backed byte-prefix continuations; successful rounds keep the dependent runner/model trace, and deadline stops keep the accepted prefix and cancelled phase. This remains configured local-process evidence, not arbitrary task cancellation, cleanup, fairness, reconnect, authenticity, or deployed equivalence.                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekAsyncStreamCancellation`                       | Policy-bearing cooperative streamed race with a typed pre-round cancellation result; the executable cancellation branch preserves its unchanged runner/model endpoint and zero dispatched rounds, while process-read interruption and deployed cancellation semantics remain external.                                                                                                                                                                                                                                                                                                                                 |
| `Cordis.DeepSeekAsyncStreamRetryCancellation`                  | Cooperative `ContextAsync.race` over retry-aware streamed jobs; `runWithFinish`/`executeRaceWithFinish` accept a caller-supplied certified finisher while `run`/`executeRace` remain multi-tool wrappers. Each result keeps its dependent retry trace/final endpoint, and text plus multi-tool fixtures cover cancellation-first and delayed-child success-first branches. Blocked-read interruption, fairness, cleanup, reconnect, and deployed async equivalence remain external.                                                                                                                                    |
| `Cordis.DeepSeekRichStream`                                    | Source-honest text-only DeepSeek SSE projection into `RichStream`, retaining wire/projection/intrinsic-trace certificates and typed rejection cases.                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekRichToolStream`                                | Restricted one-tool DeepSeek SSE projection into rich tool-call blocks, preserving raw arguments and retaining wire/projection/intrinsic-trace certificates.                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekRichMixedStream`                               | Composed one-choice text/reasoning/one-tool DeepSeek SSE projection with first-seen block indices, stateful tool metadata, exact rich-trace certificates, and same-frame mixed-kind rejection.                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekRichMultiStream`                               | One-choice text/reasoning/multi-tool DeepSeek SSE projection with provider-indexed call state, first-seen contiguous local blocks, per-call metadata/argument assembly, exact terminal closure, and typed rejection paths.                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.DeepSeekProviderAssembler`                             | Source-shaped post-decoder `BlockAssembler` model with first-seen order, open-block fallback, first-close-wins, latest tool metadata, last metadata wins, max-token tool pruning, unknown-block errors, and proof-carrying validation certificates.                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.DeepSeekAssemblerToolRound`                            | Post-assembly projection to local `FunctionCall`s, dependent tool execution, numeric-ID assistant append, and certified tool-result session append, with an executable counter round.                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `Cordis.DeepSeekProviderStreamAssembly`                        | Strict multi-call SSE-to-provider-assembler composition with retained rich/projection and fold certificates, explicit replay-metadata rejection, and structured failure/abort normalization.                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekStreamToolRound`                               | Wire-backed provider assembly through dependent tool execution and certified assistant/tool-result session append, with an executable model-2-to-5 counter round.                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.DeepSeekScopedStreamToolRound`                         | Scoped/approval-routed companion to the wire-backed round: nearest-first resolution, terminal shadow rejection, typed approval tickets, dependent model-indexed execution, and exact assistant plus tool-result session append for the dual-call fixture.                                                                                                                                                                                                                                                                                                                                                              |
| `Cordis.DeepSeekProcessStreamToolRound`                        | Process-backed complete-body stream adapter retaining status/SSE evidence before reusing provider assembly, dependent execution, and certified session append.                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Cordis.DeepSeekProcessScopedStreamToolRound`                  | Process-backed scoped companion retaining process/status and strict SSE evidence before scoped approval, dependent execution, and exact assistant/tool-result session append for the dual-call fixture; live/deployed semantics remain external.                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.DeepSeekProcessScopedConversation`                     | Finite process-backed scoped conversation indexed by a `Nat → ProcessConfig`: dependent round witnesses retain each body/model/session append, with typed terminal and fuel-exhaustion stops; the local fixture checks both two-step completion and one-step exhaustion.                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekProcessScopedRequestConversation`              | Request-indexed companion that builds each typed streaming request from the current session and feeds that exact `HttpRequest` into an indexed process/SSE/scoped round; the fixture checks distinct round request bodies, terminal completion, and fuel exhaustion.                                                                                                                                                                                                                                                                                                                                                   |
| `Cordis.DeepSeekProcessScopedRequestBytePrefixConversation`    | Request-indexed arbitrary-byte companion retaining raw chunks, pending framing, status, strict SSE completion, scoped execution, and exact session append; the fixture checks two completed rounds with distinct request bodies and a typed prefix-fuel stop.                                                                                                                                                                                                                                                                                                                                                          |
| `Cordis.DeepSeekHarnessLocalSseRequestBytePrefixConversation`  | **Checked/proved/exercised loopback conversation:** a bounded local HTTP server chooses distinct dual-tool/terminal bodies by request index; real curl byte-prefix reads feed the typed request-indexed scoped runner, retaining raw chunks, strict completion, dependent execution, exact session append, request validity, and clean server exit across two rounds plus a prefix-fuel stop.                                                                                                                                                                                                                          |
| `Cordis.DeepSeekSessionBridge`                                 | Terminal rich-view extraction plus proof-carrying append into the local session surface with caller-supplied numeric call IDs and source-event evidence.                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.DeepSeekSessionRunner`                                 | Pure composition of accepted text/one-tool/mixed/multi-call responses into an append-only session runner with exact sequence, message-order, and tool-call-count invariants.                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `Cordis.DeepSeekApiSession`                                    | Fail-closed projection of decoded non-streaming DeepSeek responses into the append-only runner, with singleton-choice/finish/payload guards and local ID/count invariants.                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `Cordis.StreamSession`                                         | Proof-carrying provider-string-ID to numeric-`CallId` assignment and rich assistant insertion into the canonical session surface.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `Cordis.Examples.DependentChoice`                              | Structured non-counter model whose Boolean input selects `Nat` or `String`, with exact-call allow/deny behavior.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `Cordis.Examples.DependentChoiceSession`                       | Non-counter rich-session instantiation: one successful dependent revision call and one exact policy-rejected label call retain a request, surface, records, and structural projection certificate.                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Cordis.Harness`                                               | Counter configuration and dynamic convenience wrapper whose canonical rich session is proved to project to the generic runner's structural log.                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `Cordis.TestSuite`                                             | Executable algebraic, boundary, adversarial, and end-to-end checks.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| `Cordis.NegativeTests`                                         | Guarded compile-failure checks for illegal dependent replies, protocol/policy/lifecycle edges, and forged runner histories.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| `Cordis.AxiomAudit`                                            | `#print axioms` audit for the selected headline theorem declarations, parsed across wrapped diagnostics.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Cordis.Version`                                               | Kernel version exposed to the demo.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |

`Cordis.lean` is the public library umbrella. `Main.lean` builds
`cordis_demo`, and `Tests.lean` builds `cordis_tests`. The executable suite,
static rejection suite, and axiom audit remain separate entry points so
importing the public library does not run them.

## Sources and pins

The interpretation is tied to exact upstream snapshots rather than floating
repository heads:

| Source                                                              | Pinned snapshot                                                                                                                               | Use here                                                                                             |
| ------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------- |
| [CORDIS paper](https://github.com/cordiverse/paper)                 | [`948a07b369c62adb3b12e102458be5c18dfb69b9`](https://github.com/cordiverse/paper/commit/948a07b369c62adb3b12e102458be5c18dfb69b9)             | Effect/coeffect, lifecycle, recovery, and ordering interpretation.                                   |
| [CORDIS implementation](https://github.com/cordiverse/cordis)       | [`8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4`](https://github.com/cordiverse/cordis/commit/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4)            | Concrete context, registry, lifecycle, isolation, and interception reference.                        |
| [DeepSeek Harness](https://github.com/deepseek-ai/deepseek-harness) | [`99f6f02fecdb7dff40c3fbc9470f5907c29f74ca`](https://github.com/deepseek-ai/deepseek-harness/commit/99f6f02fecdb7dff40c3fbc9470f5907c29f74ca) | Current event-sourced session, request reconstruction, surface replacement, tool, and adapter seams. |

The Harness vendor manifest additionally pins CORDIS `v4.0.0-rc.7` and loader
`v1.0.0-rc.5` at
[`56b3d4f725681cf4556c1a8695a709cc3b6eed74`](https://github.com/cordiverse/cordis/commit/56b3d4f725681cf4556c1a8695a709cc3b6eed74).
Compatibility between those snapshots is not inferred. See [SPEC.md](SPEC.md)
for the delivered interpretation and acceptance matrix.

## Trust boundary and credentials

The trusted executable boundary is deliberately small and visible:

- codecs prove only `Lean.Json` AST round-trips;
- all runner, batch, stream, protocol, policy, registry, and lifecycle execution
  in the reviewed baseline and current development slice is finite and in memory;
- `IO`, filesystems, HTTP, subprocesses, signals, wall-clock schedulers, and external persistence,
  remote services, and actual external effects are not proved by the kernel;
- schemas describe expected JSON but cannot force an external producer to obey;
- a modeled inverse cannot undo an irreversible emission outside its state;
- policy at-most-once is local to one explicitly threaded pure trace; and
- runner settlement couples call/result boundaries and records only inside one
  pure immutable state result, not in durable storage or external workers; and
- `DurableSettlement` is a typed crash-prefix/resume certificate over pure effects,
  not a proof that bytes reached a disk or that an external side effect happened once.
- `DurableBytes` parses only its explicitly defined pure binary format over finite Lean byte lists;
  it does not prove JSON text rendering, file reads/writes, flush barriers, or external durability.
- `TextRefinement` parses supported UTF-8 JSONL through Lean's library parser and retains exact
  source/line failures, but does not prove an external logger's schema or transport framing.
- `HarnessPersistenceRefinement` validates only the pinned logical JSONL AST vocabulary and
  expands packed rows before session refinement; it does not prove byte-level rendering,
  Zstandard framing, path/index metadata, torn-tail repair, or filesystem durability.
- `HarnessPersistenceBytes` composes a `ByteArray` UTF-8/JSONL witness with that logical
  validator and preserves the source/decoded/AST/projection fields; it does not prove a
  deployed renderer, compression, file framing, or crash durability.
- `HarnessPersistenceIO` exercises the UTF-8 byte/text and memory/filesystem boundary and refuses
  validated appends to an invalid document, but it does not prove canonical deployed rendering,
  fsync, stable media, torn-tail repair, locking, or crash durability.
- `DurableIO` exercises actual `IO` memory/file adapters and preserves the typed byte-prefix
  recovery boundary, but successful `appendFlush`/`replaceFlush` calls are only host acknowledgements;
  they are not `fsync`, crash atomicity, authenticated storage, multi-process coordination, or
  external-effect exactly-once evidence.

There is no live model or tool API adapter, no network call in the demo, and no
credential-loading path. Do not add API keys or secrets to this repository.

## Publication status

The source is public at [alok/cordis-lean](https://github.com/alok/cordis-lean).
The current reviewed snapshot is pushed to [`main`](https://github.com/alok/cordis-lean/tree/main);
each pushed revision is verified by the repository's hosted Actions workflow, whose exact run is
recorded by GitHub alongside the commit.
The historical review branch remains available at
[`feat/alok-824-proof-carrying-harness`](https://github.com/alok/cordis-lean/tree/feat/alok-824-proof-carrying-harness).
No version tag, package, or GitHub release has been published. The five commands
above and the GitHub Actions run are the reproducibility checks for each reviewed
revision.
