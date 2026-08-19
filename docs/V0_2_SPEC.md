# CORDIS Lean 0.2: Log-reconstructible generic harness

<!-- markdownlint-disable MD013 MD029 -->

## Status

This specification defines the active implementation slice after the finite `0.1.0` counter
kernel. The generic phase-indexed runner, exact-call allow/reject policy paths, structured
non-counter example, intrinsic rich session/surface kernel, model-request reconstruction, and
the counter wrapper's rich-to-structural log equality are implemented. `SessionValidation`
proof-produces append/replacement and finite-suffix certificates from parsed-but-untrusted typed
events. A current-Harness `StreamChunk` subset is also decoded from `Lean.Json` ASTs into the
intrinsic rich-stream validator. Byte parsing, full `SessionEvent` decoding, and the later
production/refinement layers listed below remain open; this file is therefore an in-progress
contract, not a completed `0.2.0` release claim.

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
- `Cordis.SessionRefinement`, statefully translating a supported source-shaped Harness session
  prefix into joint `Session.ValidatedAppend` and intrinsic `Protocol.ValidatedEvent` witnesses;
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

The bounded algebra/context/global layer now has thirty-two explicit pieces:

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

`Cordis.SessionRefinement` covers a separate stateful subset of current `SessionEvent` JSON:
turn/step boundaries, tool calls, and restricted append-only singleton-text tool results. It
retains source sequence/time values in wire witnesses, derives local zero-based steps and
`turn/end.nextStep` only from the validated prefix, and assigns provider string call IDs to
fresh numeric local IDs with uniqueness proofs. Every admitted event passes both the rich
Session append validator and intrinsic Protocol validator. Unsupported messages, chunks,
headers, replacements, error/meta payloads, extension events, and non-equivalent turn reasons
fail closed.

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
- finite operational tests with heterogeneous outcomes, failed domains, and the formal
  paired-inverse counterexample;
- quotient-effect composition and lifted coeffect context preservation;
- a complete supported current-Harness turn/step/tool session prefix plus stateful rejection
  cases;
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
- durable persistence, flush barriers, crash repair, resume, or fork correctness;
- task/fiber scheduling, fairness, cancellation delivery, or wall-clock concurrency;
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
- native plugin isolation, process confinement, filesystem safety, or remote-service behavior;
- global exactly-once execution across workers; or
- that a model follows supplied schemas or chooses an appropriate tool.

Those remain later proof/refinement layers. The new work is valuable because it makes the pure
kernel's session and request boundary materially closer to the current Harness architecture
while retaining an exact, auditable theorem boundary.
