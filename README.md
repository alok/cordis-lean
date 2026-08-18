# CORDIS Lean

[![CI](https://github.com/alok/cordis-lean/actions/workflows/ci.yml/badge.svg?branch=feat%2Falok-824-proof-carrying-harness)](https://github.com/alok/cordis-lean/actions/workflows/ci.yml)

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

The counter wrapper additionally carries a proof that projecting its rich,
payload-bearing session log produces exactly the structural runner log. Rich
surface placement is type-indexed: request headers and chunks cannot carry a
surface mutation, while user, assistant, and tool-result events must. A model
request cannot substitute a history or header assembled independently of that
log.

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

## What is verified

| Guarantee                                                                                                                                          | Lean evidence                                                                                                             | Exact boundary                                                                                                           |
| -------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| Encoded values decode to the original value                                                                                                        | `Codec.decode_encode`                                                                                                     | Starts and ends at the `Lean.Json` AST; byte parsing, rendering, and external schema compliance are excluded.            |
| Sequential modeled effects recover their indexed predecessor in LIFO order                                                                         | `Effect.seq_recovers`, `UndoStack.recover_after`                                                                          | One-sided recovery of the modeled state, not arbitrary external side effects.                                            |
| Distinct dependent-registry updates commute and recover                                                                                            | `Registry.setEffect_commute`, `Registry.setEffect_recovers`                                                               | Requires distinct operation keys; it does not isolate native code.                                                       |
| A committed capability view resolves only declared operations to present providers                                                                 | `View.provider_present` and the `View.resolve` type                                                                       | The view is supplied constructively; arbitrary host/plugin code can bypass it unless separately isolated.                |
| A strongly certified two-call pure batch has the same applied effect and model-ordered outputs in either allowed evaluation order                  | `CertifiedTwoBatch.execute_order_irrelevant`, `execute_outputs_in_model_order`, `execute_recovers`                        | Exactly two pure calls with explicit recovery and result-stability evidence; no tasks, `IO`, or asynchronous execution.  |
| Raw tool calls fail closed before becoming dependent calls                                                                                         | `ToolWire.validate`, `ToolWire.validate_declared`                                                                         | Input is already a `Lean.Json` AST; name resolution, declaration, decoding, contract, and capability checks are covered. |
| Success and failure results round-trip through request-dependent tagged codecs                                                                     | `ToolWire.decode_encoded_result`, `decode_encoded_certified_result`                                                       | Covers the exact typed `Except` result, not transport or storage.                                                        |
| Typed session events cannot produce orphan results or close a step with pending calls                                                              | `Event`, `Event.noOrphanResult`                                                                                           | Applies to the finite indexed protocol model.                                                                            |
| A validated raw event list reconstructs an intrinsic typed trace and replays to its exact terminal state                                           | `ValidatedTrace`, `ValidatedTrace.replays`, `replayRaw_eraseTrace`                                                        | Finite in-memory logs; durable storage integrity is outside the theorem.                                                 |
| A bounded assistant text stream cannot accept post-finish chunks or a second finish, and reconstructs exact concatenated text                      | `Stream.noChunkAfterFinished`, `Stream.replayRaw_eraseTrace`, `Stream.replay_completeTrace`                               | Text chunks only; tool payload parsing and network streaming are excluded.                                               |
| One explicitly threaded exact-subject policy trace dispatches at most once, and a completed trace dispatches exactly once                          | `SubjectPolicyTrace.dispatchCount_le_one`, `dispatchCount_to_completed`                                                   | A pure trace property, not global exactly-once execution across duplicated processes.                                    |
| Lifecycle unload recovers the modeled activation origin and requires the dependency guard                                                          | `Lifecycle.Transition.unload_recovers`, `unload_rejects_relied`                                                           | Finite synchronous lifecycle model; no fairness or hot-module acquisition.                                               |
| Harness records jointly thread model and lease endpoints from the initial model and empty lease pool, and use session-wide IDs `0 .. nextCall - 1` | `Harness.RecordChain`, `length_eq_nextCall`, `ids_eq_range`, `RecordChain.leases_threaded`, `RunnerState.leases_threaded` | The delivered counter runner commits sequentially in model order.                                                        |
| The tool-boundary projection of the log is exactly the records' ordered call/result pairs                                                          | `RecordChain.boundaries_eq_records`, `RunnerState.callBoundaries_eq_records`                                              | Equality concerns finite in-memory lists; it does not prove persistence integrity.                                       |
| A call event, matching result event, record, model endpoint, and lease endpoint appear together in one successful runner settlement                | The private settlement transition, indexed `RecordChain.snoc`, and absence of a public generic emitter                    | Atomic only as one pure immutable `Except` result; not durable or globally exactly-once.                                 |
| The runner's stored protocol state agrees with replaying its complete in-memory log                                                                | `RunnerState.replayProof`, `Harness.replayRaw_append`                                                                     | Persistence and crash recovery are not implemented.                                                                      |
| Catalog, wire, needs, registry, view, model-dependent grants, and exact-call policy cannot drift across the reusable runner                        | `GenericHarness.Config`, `Runner cfg phase`, `DispatchResult`                                                             | Pure sequential execution; external adapters still require refinement evidence.                                          |
| Admission rejection and admitted policy rejection dispatch zero times; a completed exact-call trace dispatches once and restores its lease pool    | `CallEvidence.*dispatchCount*`, `completed_terminal_lease_absent`, `leases_restored`                                      | One explicitly threaded pure runner, not a global cross-worker guarantee.                                                |
| A non-counter Boolean request definitionally selects `Nat` or `String`, and policy rejects the exact string branch before provider execution       | `Examples.DependentChoice.request_selects_exact_output_type` and its allowed/rejected run theorems                        | Deterministic in-memory example over a structured `Workspace`.                                                           |
| Rich surface intent is selected by event visibility; replacement retains a nonempty exact shadow interval with unique earlier covering sources     | `Session.EventIntent`, `SurfaceTransition.replace`, `replacement_exact_shadow`, `replacement_coverage`                    | Intrinsic path plus proof-producing validation after kind-specific payload parsing; byte/JSON parsing remains external.  |
| Rich session sequence numbers are contiguous; surface nodes are unique earlier events; request header and messages are exact log projections       | `ValidLog.*`, `ModelRequest`, `mkRequest`                                                                                 | In-memory typed events; timestamps, JSON bytes, durability, resume, and fork are excluded.                               |
| The counter wrapper's canonical rich session erases exactly to the replay-certified structural protocol log                                        | `RunnerState.protocolProjection_eq_log`, `protocolProjection_replays`                                                     | The rich vocabulary is a finite core subset, not full TypeScript session equivalence.                                    |
| Parsed typed rich events validate into exact append/range/provenance/uniqueness witnesses and finite `ValidLog` suffixes                           | `SessionValidation.validateAppend`, `ValidatedAppend`, `ValidatedSuffix`, `ValidatedLog`                                  | Begins after kind-specific payload parsing; bytes, persistence, and unknown required extension kinds remain external.    |
| Interleaved text, reasoning, and raw tool-call deltas retain first-seen order, exact block-end assembly, terminal discipline, and aligned metadata | `RichStream.Event`, `ValidatedTrace`, `replayRaw_eraseTrace`, `AlignedMetadata`                                           | Images, tool-result blocks, transport, and metadata pruning are deferred.                                                |
| Any finite permutation of a certified commuting pure-effect family denotes the same complete effect and recovery function                          | `Schedule.runEffects_eq_of_perm`, `CertifiedSchedule.*`                                                                   | Semantic sequential reordering only; no tasks, failures, outputs, fairness, or wall-clock overlap.                       |
| A finite dependent coeffect context enforces typed presence/absence, concrete local recovery, decidable satisfaction, and exact notifications      | `Coeffect.Context`, `setEffect_recovers`, `CoeffectAt.lift_recovers`, `activating_iff`, `deactivating_iff`, `neutral_iff` | This module is Definitions 22–26; the next two rows state the separate bounded 27–33 results.                            |
| Isolation resolves logical keys through typed realm stores; interception merges key-indexed metadata; finite unified layers retain LIFO recovery   | `UnifiedContext.IsolatedContext`, `InterceptionContext`, `Layer.record_twice_recovers`, `Layer.liftCoeffect_recovers`     | Definitions 27–31 are direct finite models; Definition 32 is represented only by finite unfoldings, not its fixed point. |
| Related finite contexts have exactly the same domain and key-wise related values, and satisfaction and notifications respect that relation         | `Coeffect.Observational.related_iff`, `contextSetoid`, `satisfies_iff_of_related`, `notify_eq_of_related`                 | Finite-context portion of Definition 33 only; operation-test indistinguishability and Definitions 34–42 remain open.     |
| Supported current-Harness stream JSON refines to an intrinsic validated trace with exact replay, or fails with a structured decode/stream error    | `RuntimeRefinement.validateJsonTrace`, `ValidatedJsonTrace.replay_eq`, exact rejection theorems                           | JSON AST only; unsupported blocks/failures/replay state are rejected, and completeness for Harness is not claimed.       |
| A rich provider assistant view cannot enter a session without one unique numeric `CallId` per ordered provider tool call                           | `StreamSession.CallIdAssignment`, `toSessionToolCalls_length`, `appendAssistant`                                          | Assignment authenticity and provider-ID globalization remain adapter obligations.                                        |

## Module map

| Module                            | Delivered responsibility                                                                                                                                        |
| --------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Cordis.Api`                      | Dependent signatures, providers, registries, restricted committed views, authorized calls, and call-indexed replies.                                            |
| `Cordis.Effect`                   | Exact and observational reversible effects, LIFO composition, accumulators, and indexed undo stacks.                                                            |
| `Cordis.Codec`                    | Proof-carrying `Lean.Json` AST codecs with structured nested decode errors.                                                                                     |
| `Cordis.Tool`                     | Request-indexed tool contracts, capabilities, certified outcomes, catalogs, and policy decisions.                                                               |
| `Cordis.ToolWire`                 | Raw-call admission plus request-dependent success/failure result codecs and certified-result encoding.                                                          |
| `Cordis.Registry`                 | Dependent provider updates, exact recovery, distinct-key commutation, and satisfaction witnesses.                                                               |
| `Cordis.Protocol`                 | Indexed turn/step/pending-call protocol, raw validation, typed trace reconstruction, and replay theorems.                                                       |
| `Cordis.Policy`                   | Single-use lease pools and exact-subject proposed/decided/dispatched/settled traces.                                                                            |
| `Cordis.Batch`                    | Strongly certified, pure, heterogeneous two-call evaluation-order equivalence.                                                                                  |
| `Cordis.Stream`                   | Bounded typed assistant-text streams and raw-chunk replay/reconstruction.                                                                                       |
| `Cordis.Lifecycle`                | Finite synchronous component lifecycle with committed views, recovery stacks, diversion, and withdrawal guards.                                                 |
| `Cordis.Examples.Counter`         | Verified local read/increment contracts and providers over a modeled natural-number counter.                                                                    |
| `Cordis.Examples.CounterWire`     | Counter name resolution, codecs, admission proofs, capabilities, and raw examples.                                                                              |
| `Cordis.GenericHarness`           | Generic phase-indexed dependent runner, exact-call policy rejection/completion evidence, dispatch results, and joint model/lease/ID/log history.                |
| `Cordis.Session`                  | Visibility-indexed rich events, exact append/replacement surface witnesses, contiguous logs, header/message reconstruction, and structural protocol projection. |
| `Cordis.SessionValidation`        | Terminating range location and proof-producing validation from typed untrusted events to `ValidatedAppend`, `ValidatedSuffix`, and `ValidatedLog`.              |
| `Cordis.RichStream`               | Indexed interleaved content blocks, exact raw validation/replay, terminal usage/error/abort discipline, and replay-metadata alignment.                          |
| `Cordis.Schedule`                 | Arbitrary finite `List.Perm` invariance for certified commuting pure effects, including exact successor, undo, and recovery equality.                           |
| `Cordis.Coeffect`                 | Finite dependent contexts, typed get/set/remove and local-operation lift, concrete recovery, specifications, satisfaction, and notifications.                   |
| `Cordis.UnifiedContext`           | In-place/derived realizations, typed realm isolation, metadata interception, and exact finite unfoldings of the unified-context equation.                       |
| `Cordis.ContextualEquivalence`    | Key-wise observational equivalence for finite coeffect contexts, a context `Setoid`, and satisfaction/notification quotient invariance.                         |
| `Cordis.RuntimeRefinement`        | Path-aware current-Harness `StreamChunk` JSON-AST decoding into proof-producing rich-stream validation with explicit unsupported cases.                         |
| `Cordis.StreamSession`            | Proof-carrying provider-string-ID to numeric-`CallId` assignment and rich assistant insertion into the canonical session surface.                               |
| `Cordis.Examples.DependentChoice` | Structured non-counter model whose Boolean input selects `Nat` or `String`, with exact-call allow/deny behavior.                                                |
| `Cordis.Harness`                  | Counter configuration and dynamic convenience wrapper whose canonical rich session is proved to project to the generic runner's structural log.                 |
| `Cordis.TestSuite`                | Executable algebraic, boundary, adversarial, and end-to-end checks.                                                                                             |
| `Cordis.NegativeTests`            | Guarded compile-failure checks for illegal dependent replies, protocol/policy/lifecycle edges, and forged runner histories.                                     |
| `Cordis.AxiomAudit`               | `#print axioms` audit for the selected headline theorem declarations, parsed across wrapped diagnostics.                                                        |
| `Cordis.Version`                  | Kernel version exposed to the demo.                                                                                                                             |

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
- `IO`, filesystems, HTTP, subprocesses, signals, schedulers, persistence,
  remote services, and actual external effects are not proved by the kernel;
- schemas describe expected JSON but cannot force an external producer to obey;
- a modeled inverse cannot undo an irreversible emission outside its state;
- policy at-most-once is local to one explicitly threaded pure trace; and
- runner settlement couples call/result boundaries and records only inside one
  pure immutable state result, not in durable storage or external workers.

There is no live model or tool API adapter, no network call in the demo, and no
credential-loading path. Do not add API keys or secrets to this repository.

## Publication status

The source is public at [alok/cordis-lean](https://github.com/alok/cordis-lean).
This review snapshot is published on
[`feat/alok-824-proof-carrying-harness`](https://github.com/alok/cordis-lean/tree/feat/alok-824-proof-carrying-harness);
`main` remains the bootstrap baseline until review is complete. No version tag,
package, or GitHub release has been published. The five commands above and the
GitHub Actions run are the reproducibility checks for each reviewed revision.
