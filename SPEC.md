# CORDIS Lean: proof-carrying agent-harness specification

Status: implementation target for Linear issue ALOK-824

Repository: `cordis-lean`

Lean toolchain: `leanprover/lean4:v4.33.0`

## 1. Purpose

CORDIS Lean is a small executable kernel for building agent harnesses whose APIs,
capabilities, reversible effects, and event transitions are checked by Lean's type
system. It implements the central ideas of CORDIS and applies them to the current
DeepSeek Harness architecture.

The core design claim is:

> An API is a dependent type signature, not a stringly registry plus a runtime
> convention.

A tool request determines its response type. A component's declared dependency set
determines which operations its context can call. A state transition determines the
only legal successor state. An effect produces both its successor and a recovery
function, together with a proof that recovery returns to the original state.

The implementation must be useful as software as well as as a formal model. It will
include an executable mock agent loop, dynamic JSON validation at the untrusted model
boundary, adversarial tests, and theorem-level checks of the invariants used by the
runner.

## 2. Primary sources and pinned snapshots

The source material is intentionally pinned because all three upstream repositories
describe themselves as active or unstable.

| Source | Snapshot used | Role in this project |
| --- | --- | --- |
| [CORDIS paper](https://github.com/cordiverse/paper) | `948a07b369c62adb3b12e102458be5c18dfb69b9` | Effect/coeffect calculus, component lifecycle, recovery and ordering theorems |
| [CORDIS implementation](https://github.com/cordiverse/cordis) | `8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4` | Concrete `Context`, `Fiber`, registry, lifecycle, isolation, and interception behavior |
| [DeepSeek Harness](https://github.com/deepseek-ai/deepseek-harness) | `47f943859bef60e4160492346772ded9b24f765a` | Tool registry, session log, model/tool loop, ordered results, cancellation, and plugin seams |

The Harness snapshot's vendor manifest pins its production CORDIS dependency more
specifically to CORDIS `v4.0.0-rc.7` / loader `v1.0.0-rc.5` at
`56b3d4f725681cf4556c1a8695a709cc3b6eed74`, plus DeepSeek's CORDIS plugins at
`abb0a307cb1d3b0947f455d590cf5ba922d4caa4`. The newer CORDIS head above is used to
understand the evolving standalone implementation; compatibility is never inferred
between these snapshots.

The paper snapshot is the 88-page draft titled *A Programming Paradigm for
Spatiotemporal Composability*, dated 2026-08-13. The source snapshot was read both as
extracted text and rendered pages; in particular, the tracked-effect recovery diagram,
the lifecycle transition diagram, and the implementation lifecycle algorithm were
checked visually.

Local prior-work search found no CORDIS implementation or target-name collision. Two
nearby projects are references only:

- `~/LeanTool` contains a useful Lean compiler-feedback and property-test loop, but its
  Python/JSON boundary is not a proof-carrying CORDIS API.
- `~/vericoding-posttraining/env/bench/Hilbert` contains untracked DeepSeek-Prover
  plumbing, but its Lean protocol layer consists mainly of opaque `IO String`-style
  signatures.

Both checkouts are dirty and remain untouched.

## 3. Source-to-Lean interpretation

### 3.1 Revertible effects

The paper's witnessed effect returns a successor state, an inverse, and a witness that
the inverse recovers the predecessor. Lean represents that witness directly:

```lean
structure Applied (State : Type u) (before : State) where
  after : State
  undo : State -> State
  undo_after : undo after = before

def Effect (State : Type u) := (before : State) -> Applied State before
```

Sequential composition must install inverses in reverse order. The library must prove:

1. identity is a left and right identity extensionally;
2. sequential composition preserves exact recovery;
3. a folded accumulator recovers the initial state;
4. recovery is LIFO by construction, not by a test or comment.

An observational variant generalizes equality to a `Setoid`. It must require the undo
map to respect observational equivalence and prove recovery up to that equivalence.

The paper's independence condition is stronger than forward commutation. A certificate
must also show that each effect's inverse (and, for iterators, its continuation) is
stable under the other effect's forward and inverse transformations. Arbitrary-removal
and parallel-scheduling theorems may consume only this stronger certificate. Mere
commutativity is sufficient only for typed disjoint-key operations whose inverse-yield
stability is separately proved.

### 3.2 Dependent APIs and coeffects

The API universe is an indexed family:

```lean
structure Signature where
  Op : Type u
  Request : Op -> Type v
  Response : (op : Op) -> Request op -> Type w
```

`Response op request` may itself contain proofs. This is the main strengthening over
the TypeScript harness's `name : string`, `arguments : unknown`, and output JSON schema.
For example, a bounded counter operation may return a value paired with a proof that it
equals the requested transition and remains within the declared limit.

A component never receives an unrestricted context. Given a predicate or finite set
`Needs : sig.Op -> Prop`, it receives a view whose call operation requires a proof of
`Needs op`:

```lean
call : (op : sig.Op) -> Needs op ->
  (request : sig.Request op) -> Exec (sig.Response op request)
```

Therefore an undeclared access is unrepresentable in well-typed component code. Runtime
lookup remains necessary to turn an untrusted or dynamically assembled registry into a
view, but successful resolution returns a value carrying the satisfaction proof.

The coeffect layer must provide:

- heterogeneous provider storage indexed by operation;
- a `Satisfies registry Needs` proposition;
- a committed view whose provider identities cannot drift during one activation;
- reversible install/replace/remove operations;
- proofs that operations on distinct keys commute;
- explicit provider identity rather than merely structural value equality.

### 3.3 Codecs and the untrusted model boundary

DeepSeek model output is dynamic JSON. It cannot be trusted merely because a schema was
shown to the model. Every wire type therefore supplies a proof-carrying codec:

```lean
structure Codec (alpha : Type u) where
  schema : Lean.Json
  encode : alpha -> Lean.Json
  decode : Lean.Json -> Except DecodeError alpha
  roundtrip : forall value, decode (encode value) = .ok value
```

A raw call contains a textual name and raw JSON. Validation resolves the name, decodes
the corresponding request, and returns an existential dependent call:

```lean
structure SomeCall (sig : Signature) where
  op : sig.Op
  request : sig.Request op
```

Only `SomeCall` enters the typed executor. A successful executor result packages the
matching `sig.Response call.op call.request`; it is impossible to attach another tool's
result type to the call. Invalid names, malformed JSON, schema mismatches, duplicate
call identifiers, and results without pending calls are rejected as data at the edge.

### 3.4 Session protocol

The current DeepSeek Harness persists an append-only event log with turn, step,
tool-call, and tool-result boundaries. Its TypeScript implementation validates these
relations dynamically. CORDIS Lean defines them as an indexed transition system:

```lean
inductive SessionState where
  | ready (nextTurn : Nat)
  | turn (turn nextStep : Nat)
  | step (turn step : Nat) (pending : List CallId)

inductive Event : SessionState -> SessionState -> Type
```

Required constructors and invariants:

- `turnStart` uses exactly the next turn number;
- `stepStart` uses exactly the next step number;
- `toolCall` adds a fresh call identifier;
- `toolResult` requires membership in the pending-call set and removes it;
- `stepEnd` requires no pending calls;
- `turnEnd` requires no open step;
- a typed `Trace start finish` composes only matching transitions.

The tool policy layer additionally distinguishes proposed, allowed, dispatched, and
settled calls. Its transition type must rule out execution before allow/approval and
must produce exactly one durable terminal result for every accepted call.

The dynamic validator must reconstruct a typed transition or return a structured error.
The static driver uses only the typed constructors. The project must prove that erasing a
typed trace and replay-validating it succeeds and ends in the erased terminal state.

### 3.5 Component lifecycle

The component layer follows the paper's `Inactive -> Reloading -> Active -> Unloading`
machine. It distinguishes two notions that ordinary plugin APIs often conflate:

1. a provider has stopped accepting new consumers; and
2. its external resources have actually been recovered.

Withdrawal must hide a provider before its inverse is applied, wait until no installed
dependent resolves to it, and only then recover its effects. Activation commits one
dependency view and uses that same view throughout its iterator.

The executable kernel targets a finite registry and synchronous effect steps first. It
must still encode the lifecycle states, committed views, diversion, and dependency guard
explicitly enough to establish:

- well-formedness preservation for every implemented transition;
- activation only when all declared dependencies resolve;
- fixed provider bindings during one active episode;
- recovery of a partially completed activation;
- no provider recovery while an installed dependent still resolves to it.

Async scheduling and hot-module acquisition are adapter concerns. Their completion and
cancellation events may be fed into the same typed state machine, but the Lean kernel
does not claim to prove fairness of an operating-system scheduler.

### 3.6 Harness runner

The reference executable models the DeepSeek turn/step loop:

1. start a turn;
2. start a model step;
3. accept raw assistant tool calls;
4. validate calls against the typed API;
5. schedule calls subject to an explicit independence certificate;
6. execute providers;
7. commit results in original model order;
8. close the step only after every call has a result;
9. either begin another model step or close the turn.

The first backend is deterministic and local. It exercises the complete harness without
credentials or network access. An OpenAI-compatible DeepSeek bridge may be added as an
optional adapter, but it is outside the proof kernel and no API key may be stored in the
repository.

## 4. Trust boundary

The following facts are proven inside Lean:

- composition of accepted effects recovers the modeled state;
- a component can call only declared operations through `View`;
- request and response types correspond to the selected operation;
- encoded values round-trip through their codec;
- accepted protocol transitions preserve the session invariant;
- results correspond to pending calls and all calls settle before step close;
- provider withdrawal obeys the modeled dependency guard;
- the deterministic reference providers satisfy their stated postconditions.

The following remain explicit trusted assumptions or validation boundaries:

- `IO`, HTTP, filesystems, subprocesses, clocks, signals, and model providers may behave
  differently from the modeled state;
- parsing/decoding rejects malformed data, but a schema shown to a language model does
  not force the model to obey it;
- a certificate about an external effect is only as strong as the observation used to
  construct it;
- irreversible emissions outside the controlled state cannot be undone; compensation is
  not exact recovery;
- native plugins can bypass a capability view unless the host also supplies process or
  language-level isolation;
- scheduler fairness, process termination, and remote service availability are not
  logical theorems of the kernel.

Every adapter must name which external facts it trusts. The README and API documentation
must not turn a modeled guarantee into a claim about arbitrary real-world side effects.

## 5. Planned modules

| Module | Responsibility |
| --- | --- |
| `Cordis.Effect` | Exact and observational recovery, composition, accumulators |
| `Cordis.Codec` | Proof-carrying JSON codecs and structured decode errors |
| `Cordis.Api` | Dependent signatures, calls, replies, providers, restricted views |
| `Cordis.Registry` | Heterogeneous coeffect store, satisfaction, committed bindings |
| `Cordis.Protocol` | Indexed session transitions, typed traces, dynamic validation |
| `Cordis.Component` | Declared needs/provisions and lifecycle transitions |
| `Cordis.Harness` | Typed model/tool runner and ordered result commitment |
| `Cordis.Examples.Counter` | Stateful proof-carrying reference tool |
| `Cordis.Examples.MockAgent` | Deterministic end-to-end agent session |
| `Tests` | Executable algebraic, adversarial, codec, protocol, and harness tests |

The public umbrella module is `Cordis`. `Main` runs the demonstrator; `Tests` is a
separate executable used by the build/test gate.

## 6. Proof obligations and acceptance gates

### Effect algebra

- identity recovery;
- sequential recovery;
- associativity up to extensional equality;
- accumulator recovery;
- disjoint-key effects commute;
- certified parallel batches have the same modeled outcome regardless of permitted
  execution order.

### API/coeffect layer

- registry resolution produces a view only when every need is satisfied;
- a committed view resolves each need to the recorded provider identity;
- set/install recovery restores the exact prior registry;
- distinct-key registry updates commute;
- the call/reply dependent pair cannot be mismatched.

### Protocol and lifecycle

- typed transitions preserve structural well-formedness;
- no result without a pending call;
- no duplicate live call identifier;
- no step closes with a pending call;
- erased typed traces validate successfully;
- partial activation recovery returns to the prior modeled state;
- an active component has a satisfaction proof for its committed needs;
- a provider is not recovered while a dependent remains bound to it.

### Runtime validation

- unknown tool names fail closed;
- malformed and schema-invalid JSON fail closed;
- valid codec output decodes to the original value;
- tool implementation failures become typed error results and still settle the call;
- model-order result commitment is stable even when certified executions are evaluated
  in another order;
- replay rejects turn/step numbering errors and orphaned/duplicate results.

### Repository gates

The work is complete only when all of the following pass:

```text
lake build
lake exe cordis_tests
lake exe cordis_demo
```

Additionally:

- every exported theorem used by the guarantee table has its axioms inspected;
- no project Lean file contains `sorry`, `admit`, or a custom `axiom`;
- no credential or local absolute path is committed;
- source claims are mapped in `docs/PAPER_MAP.md`;
- trust boundaries are repeated in `docs/TRUST_BOUNDARY.md`;
- Linear issue ALOK-824 is reconciled with the actual delivered state.

## 7. Claim boundary

This project is a proof-carrying Lean implementation inspired by, and mapped to, the
CORDIS calculus plus DeepSeek Harness. It is not initially a line-by-line mechanization
of every theorem in the paper, a drop-in replacement for every JavaScript plugin, or a
proof that arbitrary external effects are reversible. The finite executable kernel must
fully prove the obligations it advertises. Unimplemented paper results remain listed as
future work rather than being implied by naming or prose.

The intended ambitious endpoint is a foundation on which a production adapter can be
small: dynamic input is decoded once, the rest of the harness operates on dependent
calls and indexed transitions, and every escape back into untyped `IO` is visible.
