# Reconstructing CORDIS Lean by hand

<!-- markdownlint-disable MD013 MD024 MD029 -->

> This guide reconstructs the reviewed `0.1.0` finite kernel. The active
> generic-runner and log-reconstructible-session extension has its own
> [`0.2` specification](V0_2_SPEC.md); do not infer the new declarations or
> current Harness pin from this historical walkthrough.

This guide teaches the implementation of CORDIS Lean `0.1.0` from first
principles. It is written for a developer who wants to rebuild the kernel and
its release glue manually, understand why each index exists, and know exactly
where the proof boundary stops.

The implementation is a finite, pure Lean reference kernel. It is inspired by
the CORDIS paper, the standalone CORDIS implementation, and the DeepSeek
Harness, but it is not a formalization of every paper theorem and it is not a
port or behavioral verification of the TypeScript Harness. The authoritative
claim ledger is [`PAPER_MAP.md`](PAPER_MAP.md), and the external-system
perimeter is [`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md).

The most important lesson is this:

> Do not write an API that returns data and then separately prove that callers
> use the data correctly. Put the relationship into the API's result type, so
> every successful constructor or function call must return both the data and
> the evidence that makes it meaningful.

That principle appears repeatedly:

- an effect result is indexed by the exact state it must recover;
- a response type is selected by both the operation and the exact request;
- a registry binding is indexed by the registry in which it is present;
- a tool outcome is indexed by the invocation whose contract it satisfies;
- an event is indexed by its exact predecessor and successor protocol states;
- a policy result is indexed by the exact subject that was proposed;
- a lifecycle trace is indexed by both endpoint lifecycle states; and
- the harness history is indexed jointly by its initial model, next call ID,
  records, final model, final lease pool, and projected call/result log.

The resulting types are not ornamental documentation. If one of these
relationships is false, the relevant value cannot be constructed without
changing the specification, supplying a false axiom, or exploiting a bug in
Lean's trusted implementation.

## 1. What the upstream sources contribute

Reconstruction should begin with the exact pinned sources, not floating
repository heads.

| Upstream artifact                         | Pinned snapshot                                                                         | What to learn from it                                                                                                                                               | What this repository does not infer                                                                           |
| ----------------------------------------- | --------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------- |
| [CORDIS paper][paper-tree]                | `948a07b369c62adb3b12e102458be5c18dfb69b9`                                              | Witnessed reversible effects, effect and coeffect contexts, dependent stores, component lifecycle, withdrawal, independence, recovery, and system-boundary caveats. | The local modules do not mechanize the paper's whole calculus or all numbered theorems.                       |
| [Standalone CORDIS][cordis-tree]          | `8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4`                                              | Concrete context, fiber, reflection, registry, committed-view, and lifecycle architecture.                                                                          | No theorem equates the TypeScript runtime with the Lean model.                                                |
| [DeepSeek Harness][harness-tree]          | `47f943859bef60e4160492346772ded9b24f765a`                                              | Turn/step/tool-call/tool-result bracketing, model-order result commitment, dynamic tool boundaries, session validation, streaming, cancellation, and adapter seams. | The Lean runner is sequential and counter-specific; it does not verify or replace the TypeScript Harness.     |
| [Harness vendor manifest][harness-vendor] | Harness snapshot above; CORDIS vendor commit `56b3d4f725681cf4556c1a8695a709cc3b6eed74` | The exact CORDIS and plugin versions the Harness vendors and locally modifies.                                                                                      | Compatibility between the vendor commit and the separately studied standalone CORDIS snapshot is not assumed. |

Read the [paper PDF][paper-pdf] with two questions in mind.

1. Which effects are represented in the chosen state, and therefore can be
   discussed by a recovery theorem?
2. Which real effects cross the system boundary and therefore require an
   adapter, compensation, isolation, or an explicit statement that recovery is
   impossible?

The paper's recovery argument does not magically reverse an unmodeled email,
HTTP request, process launch, or observation by another system. CORDIS Lean
preserves that discipline: the model is explicit, and claims are confined to
it.

Read the [Harness architecture document][harness-architecture] for a different
reason. It shows how a production harness decomposes responsibilities across
agent loops, tool registries, policy, sessions, persistence, and provider
adapters. The Lean project chooses a small cross-section of that architecture
whose invariants can be stated precisely:

```text
raw name + Lean.Json AST
        |
        v
checked admission ------ failure is retained and settled
        |
        v
dependent AuthorizedCall
        |
        v
exact-subject policy trace + one local lease
        |
        v
verified pure provider execution
        |
        v
request-indexed encoded result
        |
        v
adjacent call/result log pair + audit record + new model
```

This is intentionally smaller than the upstream runtime. Treat the source pins
as reproducible design evidence, not imported verified artifacts.

## 2. Establish the Lean project and proof discipline

The exact toolchain lives in [`../lean-toolchain`](../lean-toolchain):

```text
leanprover/lean4:v4.33.0
```

The package file [`../lakefile.lean`](../lakefile.lean) enables
`autoImplicit = false` and defines four default targets:

```lean
package «cordis-lean» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Cordis

@[default_target]
lean_lib CordisStaticTests where
  roots := #[`Cordis.NegativeTests]

@[default_target]
lean_exe cordis_demo where
  root := `Main

@[default_target]
lean_exe cordis_tests where
  root := `Tests
```

Keep `autoImplicit` off while reconstructing the project. A misspelled or
forgotten binder should be an elaboration error, not a silently introduced
type variable. This matters especially in declarations with several state
indices.

Create the corresponding entry files as described below, then keep these five
feedback loops green for the rest of the reconstruction:

```bash
lake build
lake lean Cordis/NegativeTests.lean
lake exe cordis_tests
lake exe cordis_demo
lake lean Cordis/AxiomAudit.lean
```

`CordisStaticTests` makes the negative elaboration suite part of the default
build. The focused file command remains useful, and the guarded rejection
fixtures are intentionally kept separate from the native test executable.

The last command is deliberately `lake lean`, not a bare `lean` invocation. It
elaborates the audit with the package's Lake configuration and compiled module
context.

### Reconstruct the root and release glue

The root files are small, but omitting them makes an otherwise correct kernel
impossible to build, run, or audit from a clean checkout. Create them in the
first milestone and evolve them as their imported modules become available.

Start [`../Cordis/Version.lean`](../Cordis/Version.lean) as data rather than a
Git or filesystem lookup:

```lean
namespace Cordis

def version : String := "0.1.0"

end Cordis
```

Initially, [`../Cordis.lean`](../Cordis.lean) can import only `Cordis.Version`.
Append each completed public module until the final umbrella imports `Api`,
`Batch`, `Codec`, `Effect`, both counter example modules, `Harness`,
`Lifecycle`, `Policy`, `Protocol`, `Registry`, `Stream`, `Tool`, `ToolWire`,
and `Version`. Keep executable tests, static rejection fixtures, and the axiom
audit out of this public umbrella because importing the library should not run
or expose release-only checks.

Create minimal executable roots before their real dependencies exist:

```lean
-- Main.lean, during scaffolding
import Cordis.Version

def main : IO Unit :=
  IO.println s!"CORDIS Lean {Cordis.version} scaffold"

-- Tests.lean, during scaffolding
def main : IO Unit :=
  pure ()
```

Replace `Main.main` with the `Harness.demo` reporting loop after the runner is
implemented. Replace `Tests.main` with `Cordis.TestSuite.run` when the executable
suite exists. The final forms are
[`../Main.lean`](../Main.lean) and [`../Tests.lean`](../Tests.lean).

The separate static target also needs a root from the first build. A minimal
[`../Cordis/NegativeTests.lean`](../Cordis/NegativeTests.lean) may begin as an
empty namespace; add anonymous `#guard_msgs` examples only after the APIs they
attack exist. Likewise,
[`../Cordis/AxiomAudit.lean`](../Cordis/AxiomAudit.lean) may begin as an empty
module and should acquire one `#print axioms` line for each selected headline
theorem as that theorem is delivered. An empty audit is acceptable only during
scaffolding: the final CI parser deliberately fails if it sees no audited
declaration.

Two non-Lean files complete the release feedback loop:

- [`.github/workflows/ci.yml`](../.github/workflows/ci.yml) pins checkout and
  Lean actions by commit, verifies the exact toolchain, runs strict and ordinary
  builds, static and runtime tests, the demo, and the selected axiom audit, and
  disables mutable caches;
- [`../scripts/check_lean_hygiene.py`](../scripts/check_lean_hygiene.py) blanks
  nested comments, strings, raw strings, character literals, and quoted
  identifiers before scanning ordinary forbidden Lean tokens. It also rejects
  `sorryAx`, `ofReduceBool`, and `trustCompiler` everywhere—even in prose or
  literals—so an executable expression inside string interpolation cannot hide
  a compiler-trust escape hatch. It self-tests that conservative lexer and
  separately parses the axiom report against the three-principle allow-list.

Implement those files after the named commands exist, then run each workflow
shell gate locally. The checkout and toolchain-installation `uses:` steps remain
GitHub-hosted actions. The checker is trusted release automation, not a Lean
theorem; its self-tests and the kernel audit complement rather than certify one
another.

### A claim vocabulary for the reconstruction

Use the following words consistently in comments and documentation:

- **Proved** means Lean checks a proposition stated by a declaration.
- **Checked** means executable code rejects or accepts a finite input at
  runtime.
- **Trusted** means correctness is supplied by the integrator, toolchain, or
  external boundary rather than established by a local theorem.
- **Not implemented** means the repository neither proves nor executes the
  feature.

Do not turn “checked” into “proved” by prose. For example,
`ToolWire.validate` checks one raw call and returns a proof-carrying value on
success; that does not prove the supplied resolver corresponds to a live
deployment.

### A practical declaration order

For every module, use this order:

1. Define the semantic state or signature.
2. Define legal constructors or proof-carrying records.
3. Define erasure or executable interpretation.
4. Prove local constructor laws.
5. Add adversarial executable tests for the dynamic boundary.
6. Add the headline theorem to the axiom audit.
7. Record the exact external-system boundary in documentation.

Do not begin with tactics. Begin with the type that would make an invalid state
unrepresentable.

## 3. Stage one: proof-carrying reversible effects

Implement [`../Cordis/Effect.lean`](../Cordis/Effect.lean) before the registry,
lifecycle, or batch layers. All three reuse its recovery vocabulary.

### 3.1 Derive `Applied` from the recovery obligation

A tempting first API is:

```lean
structure BadApplied (State : Type) where
  after : State
  undo : State → State
```

It says nothing about what `undo` does. A caller can receive the function, but
the type does not establish that it recovers anything.

Instead, index the result by the predecessor:

```lean
structure Applied (State : Type u) (before : State) where
  after : State
  undo : State → State
  undo_after : undo after = before

def Effect (State : Type u) :=
  (before : State) → Applied State before
```

This is a one-sided, state-dependent inverse. It promises recovery only when
`undo` receives the `after` produced by this exact application. It does not say
that `undo` is injective, a two-sided inverse, or correct on arbitrary states.

The distinction is important. `Effect.replace next` always moves to `next`,
but its inverse closes over a different predecessor on each application. A
global inverse for `replace next` cannot exist; an application-specific
recovery witness can.

### 3.2 Derive sequential composition from LIFO recovery

For effects `first` and `second`, forward execution is:

```text
before --first--> middle --second--> after
```

Recovery must be:

```text
after --undo second--> middle --undo first--> before
```

The definition therefore uses:

```lean
undo := firstApplied.undo ∘ secondApplied.undo
```

The proof follows the same diagram. First rewrite with
`secondApplied.undo_after`, then use `firstApplied.undo_after`. In Lean, the
core step is an equality transported through the older inverse:

```lean
Eq.trans
  (congrArg firstApplied.undo secondApplied.undo_after)
  firstApplied.undo_after
```

This proof is more informative than `simp` alone: it exposes why the order is
forced.

Add `Applied.ext`, comparing `after` and the complete `undo` function. The proof
field then follows by proof irrelevance. Use this extensionality theorem to
prove:

- `Effect.identity_seq`;
- `Effect.seq_identity`; and
- `Effect.seq_assoc`.

Associativity is equality of the proof-carrying applied values, including the
captured inverse behavior, not merely equality of final states.

### 3.3 Make an explicit stack when traces need endpoints

`UndoAccumulator State before after` compiles a recovery function and its law.
`UndoStack State before after` retains the individual applications:

```lean
inductive UndoStack (State : Type u) : State → State → Type u
  | nil (state : State) : UndoStack State state state
  | push
      (prior : UndoStack State before middle)
      (step : Applied State middle) :
      UndoStack State before step.after
```

The middle endpoint is shared by construction. `pushEffect` can only apply its
effect at the stack's current endpoint, and `recover_after` is an induction on
the stack. This becomes the recovery spine of the lifecycle model.

### 3.4 Add observational recovery carefully

Exact equality can be too strong when a model intentionally quotients away
irrelevant details. The `Observational` namespace repeats the design using a
`Setoid State` and a recovery proposition `undo after ≈ before`.

The inverse must respect the supplied equivalence relation. Without that
respectfulness field, the proof for sequential composition cannot transport an
observational equality through the older inverse. This is not boilerplate: it
is the exact additional assumption required by composition.

Do not use the observational variant as a way to hide an inconvenient real
effect. The setoid itself is a trusted modeling choice. An overly coarse
relation can make a vacuous recovery theorem easy to prove.

### 3.5 Effect exercises

Before moving on, implement and check these by hand:

1. `replace next` with an inverse that closes over `before`.
2. Two arithmetic effects whose composition recovers the original natural
   number.
3. A deliberately wrong FIFO composition and a concrete example showing it
   fails.
4. `UndoStack.recover_after` by structural induction.
5. `Effect.seq_assoc` using `Applied.ext` and function extensionality.

The executable suite's `testEffects` covers recovery and explicitly observes
that wrong undo ordering can differ from the correct LIFO result.

## 4. Stage two: make the API itself dependent

The formal center is [`../Cordis/Api.lean`](../Cordis/Api.lean).

### 4.1 Start from the strongest useful signature

A conventional dynamically typed tool API might use:

```text
name : String
request : Json
response : Json
```

Even a simply typed version such as `Op → Request → Response` can lose an
important relationship when different requests to one operation have
different response types.

CORDIS Lean uses:

```lean
structure Signature where
  Op : Type u
  opDecEq : DecidableEq Op
  Request : Op → Type v
  Response : (op : Op) → Request op → Type w
```

Read the last field from left to right:

1. select an operation `op`;
2. select a request of the type belonging to `op`; and
3. obtain the response type belonging to that exact `op` and request.

This is the crux of “API as type signature.” The compiler retains distinctions
that a stringly API would need to recover with casts and runtime checks.

### 4.2 Keep provider and registry types aligned

A provider for `op` handles only requests for `op`:

```lean
structure Provider (sig : Signature) (op : sig.Op) where
  id : ProviderId
  handle :
    (request : sig.Request op) →
    Except String (sig.Response op request)
```

The heterogeneous registry is a dependent function:

```lean
abbrev Registry (sig : Signature) :=
  (op : sig.Op) → Option (Provider sig op)
```

Notice that the value type changes with the key. This prevents installing a
provider for operation `left` at operation `right` unless Lean receives a proof
that the keys are equal and transports the provider along that equality.

`ProviderId` is ordinary nominal data. The type does not prove global
uniqueness, liveness, ownership, or version compatibility.

### 4.3 Replace ambient access with a committed view

Capabilities are represented by a predicate:

```lean
abbrev Needs (sig : Signature) := sig.Op → Prop
```

A binding carries a provider and proof that it occurs in a particular registry
value:

```lean
structure Binding (sig) (registry) (op) where
  provider : Provider sig op
  present : registry op = some provider
```

A `View sig registry needs` resolves an operation only when given
`needs op`. Consequently, a component cannot call an undeclared operation
through that view merely by naming it.

This is a static analogue of a committed dependency view, not OS-level
sandboxing. Host code that is also handed the entire registry, arbitrary I/O,
or another capability channel can bypass the abstraction.

### 4.4 Preserve dependency across dynamic boundaries

`SomeCall sig` existentially packages an operation and its correctly typed
request. `AuthorizedCall sig needs` adds `declared : needs op`. `Reply call`
then contains:

```lean
value : sig.Response call.op call.request
```

The reply is indexed by the exact authorized call. `View.execute` cannot return
a response for another operation or request without violating its result type.

### 4.5 API exercises

1. Define two operations whose request types differ.
2. Make one operation's response type genuinely depend on a request value,
   such as returning a vector whose length is carried by the request.
3. Attempt to construct a reply using another call's response. Keep the
   resulting elaboration failure as a local learning experiment.
4. Define a `Needs` predicate that permits only one operation and observe that
   the other operation's `View.call` requires an unavailable proof.

The learning goal is not a clever proof. It is to see the type checker reject
cross-operation and cross-request confusion before execution.

## 5. Stage three: reversible dependent registries

Build [`../Cordis/Registry.lean`](../Cordis/Registry.lean) after the API and
effect layers.

### 5.1 Implement dependent update using equality transport

`Registry.setAt` receives a target and a value whose provider type is selected
by that target. While evaluating the returned function at an arbitrary `op`,
split on `op = target`:

```lean
if same : op = target then
  same.symm ▸ value
else
  registry op
```

The transport is the dependent-map equivalent of updating an ordinary map.
Prove two local simplification laws first:

- `setAt_same` returns the replacement at the selected key;
- `setAt_other` preserves every distinct key.

Then prove `setAt_restore` by function extensionality and the same key split.
The inverse must remember the overwritten `Option`, not merely delete the new
binding. Otherwise replacement would not recover a pre-existing provider.

### 5.2 Package update as an effect

`setEffect target replacement` captures `registry target` in its inverse and
uses `setAt_restore` for `undo_after`. `installEffect` and `withdrawEffect` are
typed specializations.

For distinct operations, prove:

```lean
Effect.seq (setEffect left leftValue) (setEffect right rightValue) =
Effect.seq (setEffect right rightValue) (setEffect left leftValue)
```

The equality must cover both the final registry and the complete composed undo
function. Commuting only the forward `setAt` operations would be insufficient
for the later reversible-independence story.

### 5.3 Treat satisfaction as constructive data

`Registry.Satisfies` is an alias for `View`, not a Boolean scan. A proof that
needs are satisfied contains the actual bindings and their presence equations.
`satisfiesNone` is vacuous; `satisfiesOne` transports an explicitly present
provider along the declared key equality.

### 5.4 Registry failure modes

- Storing all providers in a nondependent erased box loses operation-specific
  request and response types.
- Defining withdrawal as “set to none” without capturing the old binding makes
  replacement recovery false.
- Proving only final-state commutation says nothing about whether the two
  captured recovery functions agree.
- Calling a finite registry scan a sandbox overstates what the pure function
  proves.

## 6. Stage four: request-indexed tool contracts

Implement [`../Cordis/Tool.lean`](../Cordis/Tool.lean) next.

### 6.1 Separate specification, invocation, outcome, and implementation

`ToolSpec Model Capability` declares:

```lean
name : String
description : String
Input : Type
Output : Input → Type
Failure : Input → Type
pre : Input → Model → Prop
post :
  (input : Input) →
  Model →
  Except (Failure input) (Output input) →
  Model → Prop
required : Input → Capability → Prop
emission : EmissionClass
```

There are three important dependencies:

1. output and failure types may depend on the input;
2. the postcondition observes that exact input and typed result; and
3. required capabilities may depend on the input.

Do not collapse these into a record of unrelated propositions. Preserve them
through the entire call path.

`Invocation spec` packages an input, predecessor model, capability predicate,
precondition proof, and authorization proof. `CertifiedOutcome spec invocation`
packages the exact typed `Except` result, successor model, and postcondition
proof. `VerifiedTool spec` is a pure function from the former to the latter.

This API ensures that a successful implementation returns its proof obligation
with its result. It does not ensure the propositions accurately model an
external system.

### 6.2 Adapt the tool catalog to the generic API

`ToolCatalog` chooses a tool name type and a specification for each tool. Its
`signature` interpretation is:

```lean
Request tool := ToolSpec.Invocation (catalog.spec tool)
Response tool invocation :=
  ToolSpec.CertifiedOutcome (catalog.spec tool) invocation
```

This is the bridge between domain contracts and the generic dependent API. A
verified implementation becomes a provider without erasing the invocation
index.

### 6.3 Keep policy combination monotone

`Decision` has `allow`, `ask`, and `deny`. `tighten` chooses the more restrictive
decision. Exhaustive case proofs establish commutativity, associativity,
idempotence, allow as identity, and deny as absorbing.

These algebraic laws prevent one composed guard from restoring authority after
another guard denies it. They do not implement an approval UI, authenticated
policy source, or asynchronous policy pipeline.

### 6.4 Treat emission classes as labels

`EmissionClass` distinguishes pure, internally reversible, externally
idempotent, compensatable, and irreversible tools. There is no theorem tying a
label to behavior. An integrator must not label an email send “pure” and then
claim the kernel made it reversible.

## 7. Stage five: proof-carrying JSON AST codecs

Implement [`../Cordis/Codec.lean`](../Cordis/Codec.lean) before the dynamic tool
wire.

### 7.1 Put the round-trip theorem in the codec

The central record is:

```lean
structure Codec (α : Type u) where
  schema : Lean.Json
  encode : α → Lean.Json
  decode : Lean.Json → Except DecodeError α
  roundtrip : ∀ value, decode (encode value) = .ok value
```

Every codec constructor must discharge the theorem. This prevents adding an
encoder and decoder pair that immediately disagrees on encoded values.

The theorem starts after parsing, at `Lean.Json`, and ends at `Lean.Json`. It
does not prove:

- byte or text parsing correctness;
- renderer correctness;
- JSON Schema soundness or completeness;
- that `schema` describes `encode` or `decode`;
- canonicalization of arbitrary external JSON; or
- wire compatibility with TypeScript.

### 7.2 Build primitive codecs before combinators

Implement `unit`, `bool`, `string`, and `nat`. The natural codec accepts the
canonical nonnegative, exponent-zero `Lean.JsonNumber` form produced by its
encoder. Do not document it as a theorem about every textual JSON number.

Then implement product and list codecs compositionally:

- a product is a two-element array;
- a list maps each element encoder and decodes recursively;
- nested failures prepend `.index` path segments; and
- the list round trip is an induction using the item codec's `roundtrip`.

Structured `DecodeError` values are executable diagnostic data. They do not
themselves prove that an external schema validator would report the same path.

### 7.3 Codec exercises

1. Write the primitive round-trip proofs without automation.
2. Prove the product codec by destructuring the pair.
3. Prove the list helper `decodeValues_encode` by induction, generalizing the
   current array index.
4. Construct a nested malformed array and check that the error path identifies
   both list and product indices.
5. Try to add an object codec. Decide whether field order, duplicate keys, and
   missing fields belong in the accepted AST language before writing proofs.

## 8. Stage six: cross the dynamic tool boundary once

[`../Cordis/ToolWire.lean`](../Cordis/ToolWire.lean) is the checked-to-proved
handoff.

### 8.1 Keep raw input small and explicitly untrusted

`RawCall` contains only a textual name and `Lean.Json` arguments. The admission
pipeline must proceed in this order:

1. resolve the textual name to a catalog operation;
2. prove the operation is declared by the component's `Needs` predicate;
3. select and run that operation's input codec;
4. ask the proof-producing admission procedure for the precondition and
   capability evidence; and
5. construct `ToolSpec.Invocation` and `AuthorizedCall` only after all checks
   succeed.

Each failure becomes an `AdmissionError`: unknown tool, undeclared tool,
invalid arguments, or rejected contract. Fail closed; never fabricate a
default typed call after a check fails.

The key field is:

```lean
certifyAdmission :
  (tool : catalog.Tool) →
  (input : (catalog.spec tool).Input) →
  (before : Model) →
  (granted : Capability → Prop) →
  ((capability : Capability) → Decidable (granted capability)) →
  Except String
    (AdmissionEvidence (catalog.spec tool) input before granted)
```

The procedure can return `.ok` only by constructing the exact precondition and
authorization propositions selected by the tool and decoded input.

### 8.2 Make result encoding request-indexed

An admitted tool's failure and output types may depend on its input. Therefore
`ToolWire.resultCodec tool input` must select both codecs using the exact
request. It represents the result as:

```text
[false, encoded failure]
[true,  encoded output]
```

The Boolean tag makes the `Except` branch explicit. The composed codec proves
that encoding and decoding either branch returns the exact dependent result.
`encodeCertifiedResult` receives an invocation and certified outcome, so it
cannot accidentally choose another request's codec.

### 8.3 Reconstruct the counter example as the first vertical slice

Use [`../Cordis/Examples/Counter.lean`](../Cordis/Examples/Counter.lean) and
[`../Cordis/Examples/CounterWire.lean`](../Cordis/Examples/CounterWire.lean) as
the first end-to-end exercise.

The counter defines:

- `read`, requiring the read capability and preserving the model;
- `increment`, requiring the write capability and the precondition
  `before + amount ≤ limit`;
- postconditions relating exact results to successor models;
- pure verified implementations;
- a dependent catalog, providers, registry, and committed view;
- input, output, and failure codecs; and
- a proof-producing admission procedure.

`allNeeds` and `allCapabilities` deliberately grant everything in the
credential-free example. They are not production authorization.

Verify these cases before building the harness:

- a valid increment from `2` by `3` under limit `10` reaches `5`;
- an over-limit increment is rejected before an authorized call exists;
- `counter_destroy` is rejected as unknown; and
- a rejected raw call has no request-indexed provider result to encode.

## 9. Stage seven: an indexed session protocol and runtime mirror

Build [`../Cordis/Protocol.lean`](../Cordis/Protocol.lean) in two layers. The
first makes locally generated traces intrinsically legal. The second validates
untrusted runtime data.

### 9.1 Define protocol states and legal edges

The static states are:

```lean
inductive SessionState where
  | ready (nextTurn : Nat)
  | turn (turn nextStep : Nat)
  | step (turn step : Nat) (pending : List CallId)
```

Define `Event : SessionState → SessionState → Type` so each constructor fixes
both endpoints:

- `turnStart` opens exactly the expected turn;
- `stepStart` opens exactly the expected step with no pending calls;
- `toolCall` requires freshness and adds the ID to pending calls;
- `toolResult` requires membership and erases the ID;
- `stepEnd` requires an empty pending list; and
- `turnEnd` increments the turn.

An `Event` is a proof-relevant edge. A `Trace start finish` composes edges only
when the predecessor and successor indices match.

This design makes an orphan typed result and a typed step-end with pending
calls unconstructible. `Event.noOrphanResult` states the property explicitly
for a result-shaped erasure.

### 9.2 Mirror the vocabulary dynamically

Runtime logs cannot carry Lean indices. Define `RuntimeState`, `RuntimeEvent`,
and `ValidationError`, then implement `applyRaw` by exhaustive phase and event
matching. Check turn coordinates, step coordinates, duplicate IDs, orphan
results, and nonempty pending calls.

`replayRaw` folds `applyRaw` from left to right. This is an executable checker,
not yet an intrinsic witness.

### 9.3 Reconstruct witnesses, do not merely return `Bool`

`ValidatedEvent start raw` existentially packages:

```lean
finish : SessionState
event : Event start finish
erase_eq : event.erase = raw
```

`validateEvent` repeats the dynamic checks while refining equalities until it
can construct the relevant typed event. `ValidatedTrace` does the same for a
whole list.

Prove both directions needed by the local bridge:

- every erased typed event or trace is accepted at its statically known
  endpoint; and
- every successfully reconstructed event or trace replays to the endpoint in
  its witness.

Do not claim that all raw logs accepted by some other implementation reconstruct
to this type. The vocabulary contains only six local variants and omits real
Harness payloads, timestamps, surface references, persistence, and extension
merging.

### 9.4 Protocol adversarial tests

Add finite checks for:

- wrong turn;
- wrong step;
- event in the wrong phase;
- duplicate live call ID;
- result for a nonpending call;
- closing a step with pending calls; and
- a valid erased trace reaching its exact expected endpoint.

These tests catch mistakes in `applyRaw`. The universal guarantees come from
the indexed constructors and the erasure/replay theorems.

## 10. Stage eight: bounded text streams

[`../Cordis/Stream.lean`](../Cordis/Stream.lean) applies the same two-layer
pattern to a deliberately small stream language.

The indexed state is either open with a remaining budget and exact accumulator,
or finished with a `Result`. A text `Chunk` requires at least one budget unit,
decrements it, and appends the fragment. A finish chunk exposes the exact
accumulator as the terminal result. There is no constructor whose predecessor
is finished, so `noChunkAfterFinished` follows by constructor impossibility.

The runtime mirror checks:

- budget exhaustion;
- text after finish; and
- double finish.

`textTrace chunks` uses exactly `chunks.length` budget units.
`completeTrace chunks` appends finish, and `replay_completeTrace` proves the
terminal text equals the left-to-right concatenation `assemble chunks`.

Keep the boundary narrow in both code and prose. This model has strings and a
finish marker. It does not model the Harness's richer block, reasoning,
tool-call, usage, byte-decoding, cancellation, backpressure, or persistence
semantics.

## 11. Stage nine: component lifecycle with indexed recovery

Implement [`../Cordis/Lifecycle.lean`](../Cordis/Lifecycle.lean) after effects
and views.

### 11.1 State the local lifecycle explicitly

The lifecycle has four state forms:

- `inactive current outcome`;
- `reloading origin current undo iterator committed`;
- `active origin current undo committed`; and
- `unloading origin current undo committed outcome`.

Retain both `origin` and `current` and index the `UndoStack` by them. This makes
the intended recovery endpoint explicit even during partial reload or unload.

The legal `Transition provider consumers` constructors are:

```text
inactive  --begin-->   reloading
reloading --iterate--> reloading
reloading --finish-->  active
reloading --divert-->  unloading
active    --leave-->   unloading
unloading --unload-->  inactive at origin
```

`iterate` applies an effect exactly at the current model and pushes the applied
effect onto the endpoint-indexed undo stack. `unload` returns to `origin`, not
an unconstrained model.

### 11.2 Make the dependency guard a constructor argument

A `CommittedView Key Fiber` records provider identities selected for keys. A
consumer snapshot records a fiber, installation Boolean, and committed view.
`Withdrawable consumers provider` states that every supplied installed
consumer does not rely on the provider.

The `unload` constructor requires this guard. Therefore
`unload_rejects_relied` is obtained by unpacking the constructor and applying
the guard to contradictory installed-dependent evidence.

The list is supplied data. The type does not prove it is a complete, current
snapshot of a live registry, and the Boolean is not connected to an external
runtime.

### 11.3 Prove only the local facts represented

`unload_recovers` follows from `UndoStack.recover_after` after eliminating the
transition. `active_successor_keeps_view` follows because the only outgoing
active constructor is `leave`, and its successor retains the same committed
view and stack.

These are local constructor theorems. They are not the paper's multi-fiber
preservation, temporal composability, spatial composability, progress, or
confluence results.

## 12. Stage ten: exact-subject policy traces

Build [`../Cordis/Policy.lean`](../Cordis/Policy.lean) before the final runner.

### 12.1 Model a lease pool without pretending it is linear

`LeasePool` stores a list of available `CallId` values plus a `Nodup` proof.
`issue` succeeds only when the ID is absent; `consume` succeeds only when it is
present and returns a duplicate-free remainder.

Prove:

- a consumed ID is absent from the returned pool;
- without reissue, the returned pool cannot consume that ID again; and
- two successive successful consumptions are impossible.

These are properties of one explicitly threaded value. Lean values can be
copied. Two workers given the same pre-consumption pool can each derive a valid
local trace. Do not describe `LeasePool` as globally linear or process-wide
exactly-once state.

### 12.2 Preserve the exact subject through every phase

The simpler `PolicyState` demonstrates the phase machine. The stronger
`SubjectPolicyState Subject Completed Rejected` retains one exact `subject`
through:

```text
proposed -> decided -> dispatched -> settled
```

The terminal result family is also selected by that subject:

```lean
SubjectPolicyResult Completed Rejected subject
```

Dispatch is constructible only from `.decided id subject .allow leases` and
requires evidence that the exact ID was consumed. A non-allow decision can only
take the rejection edge. Settlement after dispatch carries a
`Completed subject` value.

### 12.3 Prove trace properties from phase shape

Give each phase a numerical rank and prove every transition strictly increases
it. Define `SubjectPolicyTrace` as an intrinsically composable sequence and
count dispatch edges.

The phase structure yields:

- no dispatch after the dispatched phase;
- no outgoing transitions after settlement;
- dispatch count at most one for any one trace;
- dispatch count exactly one from proposal to a completed result; and
- dispatch count zero for a trace starting in a denied state.

The proof works because the type has no constructors that move backward or
dispatch twice. It is a path property, not an external execution guarantee.

## 13. Stage eleven: certify exactly two reorderable pure calls

[`../Cordis/Batch.lean`](../Cordis/Batch.lean) is intentionally an exactly-two
call theorem. Preserve that narrowness while rebuilding it.

### 13.1 Strengthen independence beyond final-state commutation

For two reversible effects at `before`, `Effect.IndependentAt` requires:

1. both orders reach the same successor; and
2. both orders produce pointwise equal complete LIFO recovery functions.

The second condition matters. Two orders could happen to reach the same final
state while capturing different undo behavior.

`seq_applied_eq` uses `Applied.ext` to turn those two fields into equality of
the complete proof-carrying applications.

### 13.2 Account for result observations separately

`PureCall` contains both an effect and a result function evaluated at its input
state. If the other effect runs first, the call observes another input. Effect
commutation alone therefore does not establish result equality.

`TwoBatch.IndependentAt` adds:

- stability of the first result when the second effect runs first; and
- stability of the second result when the first effect runs first.

`CertifiedTwoBatch.execute` can now expose model and swapped evaluation orders
while always committing outputs in declared model order. Prove equality of
successors, undo functions, applied effects, ordered outputs, and complete
batch outcomes.

This evaluates pure functions. It launches no tasks, performs no `IO`, models
no cancellation, and says nothing about arbitrary `N`-call schedules.

## 14. Stage twelve: build the joint harness invariant

[`../Cordis/Harness.lean`](../Cordis/Harness.lean) is where independently valid
subsystems become one runner. This is also where weak designs tend to permit
“split-brain” state: a valid protocol log beside unrelated records, or valid
records beside an unrelated lease endpoint.

### 14.1 Retain evidence for both admission branches

`CallEvidence id raw before after leasesBefore leasesAfter` has two
constructors.

The rejected branch stores:

- the `AdmissionError`;
- the exact equation `validateRaw before raw = .error error`;
- unchanged model endpoints; and
- unchanged lease endpoints.

The admitted branch stores:

- the exact dependent `CounterCall`;
- the equation that validation returned it;
- the issued lease pool and issuance equation;
- the exact request-indexed provider completion;
- the equation that `view.execute call` returned that completion; and
- an exact-subject policy trace from proposal to settlement.

Its `after` index is definitionally selected by `completionAfter`. Provider
failure preserves the model; a successful provider reply supplies the
certified modeled successor.

Derive user-facing outcome, optional encoded result, and dispatch count from
the evidence. Rejected admission and provider-level failure have no encoded
typed provider result. A successful provider execution chooses the codec from
the operation and invocation retained by the dependent call.

### 14.2 Package one settled record

`CallRecord` existentially packages the identifiers and endpoints along with
its evidence:

```lean
structure CallRecord where
  id : CallId
  raw : RawCall
  before : Nat
  after : Nat
  leasesBefore : LeasePool
  leasesAfter : LeasePool
  evidence :
    CallEvidence id raw before after leasesBefore leasesAfter
```

This proves the fields of one record agree. It still does not prove records are
contiguous, IDs are ordered, leases thread from one record to the next, or the
log contains the corresponding call/result events. Those are history-level
obligations.

### 14.3 Project only the log boundary needed by the history theorem

Define `CallBoundary` with `call id` and `result id`. Project each
`RuntimeEvent` to an optional boundary and use `filterMap` over the full log.
Define `recordBoundaries` by mapping each record to the adjacent pair:

```text
call record.id, result record.id
```

The projection intentionally erases turn and step coordinates. Protocol replay
still checks those coordinates; the history theorem connects only the ordered
call/result IDs to records. Do not document the boundary equality as a full
payload-preservation theorem.

### 14.4 Derive the six-index `RecordChain`

A history has six pieces that must agree:

1. initial model;
2. next call ID;
3. ordered records;
4. final model;
5. final lease pool; and
6. ordered log-boundary projection.

Put all six in the proposition index:

```lean
inductive RecordChain :
    Nat →
    Nat →
    List CallRecord →
    Nat →
    LeasePool →
    List CallBoundary →
    Prop
```

The empty constructor fixes all base facts at once:

```lean
RecordChain initial 0 [] initial LeasePool.empty []
```

The append-oriented `snoc` constructor receives a prior chain and one record.
It requires:

```lean
record.id.value = nextCall
record.before = current
record.leasesBefore = currentLeases
```

Its result fixes all successor indices:

```lean
RecordChain
  initial
  (nextCall + 1)
  (records ++ [record])
  record.after
  record.leasesAfter
  (boundaries ++ [.call record.id, .result record.id])
```

This constructor is the heart of the joint audit trail. It is impossible to
append a record whose model or lease predecessor disagrees with the prior
history, whose ID skips the next value, or whose boundary contribution is not
one adjacent matching pair.

### 14.5 Prove consequences by induction on the chain

The public history theorems should be easy after the constructor is right:

- `length_eq_nextCall` proves one record per allocated ID;
- `ids_eq_range` proves IDs are exactly `0, ..., nextCall - 1` in order;
- `boundaries_eq_records` proves the boundary index equals the projection of
  the record list; and
- `leases_threaded` proves every record starts from the preceding lease
  endpoint and passes its `leasesAfter` endpoint to the next record, from the
  empty pool to the final pool. It does not by itself prove how either endpoint
  was computed or that every record consumed a lease.

If one of these proofs becomes deeply complicated, reconsider the indices or
constructor. The data type should do most of the work.

### 14.6 Put both history and replay into `RunnerState`

The state contains ordinary runtime data plus two complementary certificates:

```lean
structure RunnerState where
  initialModel : Nat
  model : Nat
  protocol : RuntimeState
  nextCall : Nat
  leases : LeasePool
  log : List RuntimeEvent
  records : List CallRecord
  history :
    RecordChain initialModel nextCall records model leases
      (callBoundaries log)
  replayProof :
    replayRaw (.ready 0) log = .ok protocol
```

`replayProof` alone would allow a replay-valid log unrelated to the records and
model. `history` alone would allow a record chain unrelated to turn/step
coordinates and protocol validity. Together they fix the local protocol
endpoint and the model/ID/record/lease/boundary correspondence.

The certificates still say nothing about durable storage or external tool
effects.

### 14.7 Prevent generic emission from weakening the invariant

A public helper of type “append any runtime event if `applyRaw` accepts it”
would let callers append call boundaries without records. Keep structural
events behind a private `emitNonBoundary` helper that additionally requires:

```lean
RuntimeEvent.callBoundary? event = none
```

That equality lets the history proof remain unchanged when adding turn and
step events.

Call and result events must use a different path that extends the history.

### 14.8 Make settlement one pure state transition

The private `settle` helper receives a fully constructed `CallRecord` plus
proofs that its ID, model predecessor, and lease predecessor match the current
state. It then:

1. constructs the call event;
2. checks it with `applyRaw`;
3. constructs the matching result event;
4. checks it against the pending-call successor;
5. appends both events adjacently;
6. appends the record;
7. updates model, lease pool, and next ID;
8. extends `RecordChain` with `snoc`; and
9. extends `replayProof` using `replayRaw_append`.

It returns one new immutable `RunnerState` or a `RunnerError`. No public state
exists containing only the call event.

This is atomic only in the sense that one pure Lean computation returns one
fully certified value. It is not a database transaction, a write-ahead log, a
crash-safe commit, or global exactly-once tool execution.

### 14.9 Route every dispatch branch through settlement

`dispatch` is available only in an open step. It constructs a `CallId` whose
`value` is `state.nextCall` and runs admission.

For rejection:

- model and leases stay unchanged;
- evidence retains the exact failed validation equation;
- the record has no dispatch trace or encoded provider result; and
- settlement still emits a matching call/result pair so no protocol
  obligation leaks.

For admission:

- issue the exact call-ID lease;
- consume it before dispatch;
- execute the dependent committed view;
- construct an allow/dispatch/settle exact-subject trace;
- determine the successor through `completionAfter`; and
- send the complete record through `settle`.

Provider failure is a completed provider attempt whose abstract model remains
unchanged. A tool-level `Except.error` inside a certified outcome is distinct
from a provider-level failure of `View.execute`.

### 14.10 Add finite turn and step combinators last

Only after single-call settlement works should you add:

- `dispatchAll` for calls in model order;
- `finishStep` and `finishTurn`;
- `runStep`, `runSteps`, and `runTurn`;
- `runTurns` and `runMultiTurn`; and
- the one-turn `runScript` convenience entry point.

These are sequential folds. Their names must not imply asynchronous dispatch
or overlapping tool execution.

### 14.11 Try to forge the state

Two negative elaboration experiments reveal whether the joint index is doing
real work.

First, construct a replay-valid log with call/result ID `99` while retaining a
record chain containing ID `0`. The `history` field should fail because
`callBoundaries log` cannot unify with the chain's boundary index.

Second, quantify over an arbitrary `RunnerState` and try to update only its
`leases` field to `LeasePool.empty` while retaining its dependent `history`
field. The generic update should fail because the history's fifth index is the
original `state.leases`, which is not definitionally equal to `.empty`. This
fixture does not construct a concrete nonempty runner state; the delivered
runner issues and consumes each local lease before settlement, so its recorded
demo endpoints remain empty.

These are finite compile-failure experiments, not runtime tests or universal
proofs. They confirm that those particular forged constructions are rejected;
the general endpoint and boundary claims come from the `RecordChain` theorems.

## 15. Testing the implementation honestly

Executable tests live in
[`../Cordis/TestSuite.lean`](../Cordis/TestSuite.lean), with
[`../Tests.lean`](../Tests.lean) as the executable entry point.
Static rejection tests live separately in
[`../Cordis/NegativeTests.lean`](../Cordis/NegativeTests.lean). They are a
default Lake target, but they are not imported by the native executable.

### 15.1 Separate three kinds of evidence

Use all three, and do not conflate them:

1. **Universal Lean theorems** cover every inhabitant of their stated types.
2. **Executable tests** exercise concrete valid and adversarial cases.
3. **Negative elaboration experiments** show particular invalid values cannot
   type-check.

A test is useful for catching a wrong decoder branch even when a theorem
covers only encode-then-decode. A theorem is useful where finite examples
cannot establish a universal claim. A negative experiment is useful for
checking that the API really excludes an invalid construction.

### 15.2 Reconstruct the test suite in layers

The suite should cover:

- effect recovery and visibly wrong undo order;
- certified two-call successor, recovery, and result-order equality;
- primitive and composite codec round trips;
- nested decode-error paths;
- stream assembly, exhaustion, and terminal rejection;
- registry target update, other-key preservation, recovery, and commutation;
- lifecycle start/iterate/finish/leave/unload with recovery;
- protocol coordinate mismatch, wrong phase, duplicate call, orphan result,
  and pending-call rejection;
- lease issue, duplicate issue, consume, and attempted reuse;
- valid, unknown, and contract-rejected counter admission;
- demo model, protocol, ID order, record count, call/result boundaries, lease
  threading, dispatch counts, and request-indexed result decoding;
- replay and typed reconstruction of the complete demo log; and
- a multi-step, multi-turn run with session-wide IDs.

The static rejection module should cover:

- a request value paired with the wrong request-indexed response type;
- an orphan result and a duplicate pending call at the intrinsic protocol API;
- attempted dispatch from a denied exact-subject policy state;
- withdrawal while an installed consumer relies on the provider;
- a replay-valid log whose call ID disagrees with its certified record chain;
  and
- replacement of a runner's final lease pool without rebuilding its indexed
  history certificate.

Compile those checks directly as well as through the default build:

```bash
lake lean Cordis/NegativeTests.lean
```

The final output is:

```text
CORDIS adversarial and integration tests passed
```

Do not treat that sentence as a theorem about production DeepSeek Harness
interoperability. It reports success of the finite local suite.

### 15.3 Audit proof dependencies explicitly

[`../Cordis/AxiomAudit.lean`](../Cordis/AxiomAudit.lean) runs `#print axioms`
for the headline effect, registry, batch, codec, wire, protocol, stream,
lifecycle, policy, and harness theorems.

Run:

```bash
lake lean Cordis/AxiomAudit.lean
```

Interpret the output narrowly. It reports dependencies of the named
declarations. It does not audit every possible declaration, prove the compiler
correct, or validate an external runtime. Standard principles such as
`propext`, `Classical.choice`, and `Quot.sound` may appear where Lean library
machinery requires them.

Also run the repository's lexical hygiene gate. It ignores comments, strings,
quoted identifiers, and legal `#print axioms` commands while rejecting actual
proof placeholders, project-defined axioms or constants, and unsafe or partial
declarations:

```bash
python3 scripts/check_lean_hygiene.py --self-test .
```

The scan is a source-hygiene check, not a kernel theorem. The CI workflow also
parses the axiom-audit output and fails if a dependency outside `propext`,
`Classical.choice`, and `Quot.sound` appears.

### 15.4 Verify from a clean materialization

Cached build artifacts can hide missing imports or accidental local
dependencies. After local tests pass, commit the exact candidate revision—the
archive command below reads `HEAD`, not unstaged or staged changes—verify the
working tree is clean, and then test that clean archive:

```bash
tmp_dir="$(mktemp -d)"
test -z "$(git status --porcelain)"
git archive HEAD | tar -x -C "$tmp_dir"
(
  cd "$tmp_dir"
  unset LEAN_PATH
  export LAKE_ARTIFACT_CACHE=false
  export LAKE_CACHE_DIR=
  lake clean
  lake --wfail build
  lake build
  lake lean Cordis/NegativeTests.lean
  lake exe cordis_tests
  lake exe cordis_demo
  lake lean Cordis/AxiomAudit.lean
)
```

Disabling the Lean 4.33 system artifact cache here is deliberate. Its cached artifacts need not be
materialized under the archive's `.lake/build` directory, while the subsequent direct `lake lean`
commands load `.olean` files from that directory. `--no-cache` controls remote cache downloads; it
does not replace `LAKE_ARTIFACT_CACHE=false` for this clean-materialization check.

Use an explicit temporary directory as above. Do not point cleanup commands at
the repository root, home directory, or an unresolved variable.

## 16. A manual reconstruction curriculum

The following sequence keeps every milestone executable and makes later proof
obligations depend on already understood code.

### Milestone 1: package and empty public surface

- Pin Lean `v4.33.0`.
- Turn off `autoImplicit`.
- Create the public library, static-rejection library, demo, and runtime-test
  targets.
- Add `Cordis/Version.lean`, the initial public umbrella, minimal `Main.lean`
  and `Tests.lean`, and placeholder `Cordis/NegativeTests.lean` and
  `Cordis/AxiomAudit.lean` roots.
- Run `lake build` before adding semantics.

Exit condition: the empty package builds from a clean checkout.

### Milestone 2: reversible effect algebra

- Implement `Applied`, `Effect`, identity, sequence, and replacement.
- Prove recovery and monoid laws.
- Add accumulator, stack, and observational variant.
- Add a test that distinguishes LIFO from FIFO recovery.

Exit condition: recovery theorems elaborate and arithmetic examples pass.

### Milestone 3: dependent API and registry

- Implement request-indexed `Signature` and call-indexed `Reply`.
- Add providers, dependent registry, needs, bindings, and committed views.
- Implement typed updates and captured-overwrite recovery.
- Prove distinct-key forward and inverse commutation.

Exit condition: a provider for one operation cannot inhabit another key, and a
withdrawn provider is exactly restored.

### Milestone 4: tool contracts and counter

- Implement `ToolSpec`, invocation, outcome, and verified implementation.
- Adapt a catalog to `Signature`.
- Implement read and increment contracts over `Nat`.
- Construct providers, registry, and view.

Exit condition: Lean requires the increment limit proof before an invocation
can be constructed, and the verified implementation proves its postcondition.

### Milestone 5: codecs and wire admission

- Implement primitive and composite codecs with round-trip fields.
- Add structured nested errors.
- Implement raw-name resolution and proof-producing admission.
- Implement request-indexed tagged result codecs.
- Add the counter wire and rejection cases.

Exit condition: valid raw input becomes an `AuthorizedCall`; invalid input does
not; encoded dependent results round-trip.

### Milestone 6: intrinsic and runtime protocols

- Implement indexed session states, events, and traces.
- Add erasure and the runtime validator.
- Reconstruct typed events and traces from accepted raw values.
- Prove erase/replay laws and add adversarial phase tests.
- Repeat the pattern for the bounded text stream.

Exit condition: illegal typed transitions are unconstructible and malformed raw
transitions fail with specific errors.

### Milestone 7: lifecycle, policy, and pure batch

- Reuse `UndoStack` in lifecycle indices.
- Require the withdrawal guard in the unload constructor.
- Implement duplicate-free lease pools and exact-subject policy traces.
- Prove trace dispatch bounds.
- Implement the strong two-call independence certificate.

Exit condition: local lifecycle recovery, policy path bounds, and two-call
order equivalence elaborate without broad external claims.

### Milestone 8: one-call runner

- Define `CallEvidence` and `CallRecord`.
- Settle both rejection and admission with adjacent call/result events.
- Store replay proof in `RunnerState`.

At this temporary milestone, inspect whether records, model, leases, and log can
still diverge. They can unless the next milestone is completed.

### Milestone 9: six-index history repair

- Define call-boundary projections and `LeasesThreaded`.
- Introduce `RecordChain` with all six indices.
- Put the chain at `RunnerState.history`.
- Make structural emission private and boundary-free.
- Make call/result settlement private and history-extending.
- Run the two state-forging experiments.

Exit condition: replay-valid but record-inconsistent states and lease-overwrite
states fail to elaborate.

### Milestone 10: finite scripts and release audit

- Add sequential finite steps and turns.
- Add the deterministic demo.
- Complete adversarial and integration tests.
- Complete the selected axiom audit.
- Verify a clean archive.
- Compare every public claim against `PAPER_MAP.md` and
  `TRUST_BOUNDARY.md`.

Exit condition: all five verified commands pass from a clean materialization,
and documentation says exactly what the types establish.

## 17. Common design failures and their repairs

### Failure: an undo callback with no law

**Symptom:** the effect returns `after` and `undo`, while recovery is tested
only on examples.

**Repair:** index `Applied` by `before` and require `undo after = before` as a
field.

### Failure: composing inverses in forward order

**Symptom:** simple commutative examples pass, but state-dependent effects do
not recover.

**Repair:** derive the diagram and compose newest inverse first.

### Failure: response depends only on an operation

**Symptom:** result decoding requires casts or erased existential packages when
two requests of one operation have different result families.

**Repair:** define `Response : (op) → Request op → Type` and index `Reply` by
the exact call.

### Failure: capability declaration is only metadata

**Symptom:** a view accepts any operation and checks `Needs` after execution.

**Repair:** require `needs op` to obtain the binding, and carry it in
`AuthorizedCall`.

### Failure: registry withdrawal forgets overwritten state

**Symptom:** installing over an existing provider and undoing removes it.

**Repair:** capture `registry target` in the inverse and prove full functional
equality on restoration.

### Failure: schema metadata is described as verified

**Symptom:** `Codec.roundtrip` is cited as proof that arbitrary external JSON
conforms to `schema`.

**Repair:** state the exact AST theorem and add a separate schema-semantics
relation before making schema claims.

### Failure: a runtime validator returns only a Boolean

**Symptom:** downstream typed code must recheck phase facts or trust the
validator informally.

**Repair:** return an existential `ValidatedEvent` or `ValidatedTrace` carrying
the intrinsic transition and erasure equality.

### Failure: final-state commutation is called independence

**Symptom:** both effect orders reach the same model but capture different undo
functions or return different observed results.

**Repair:** require successor equality, pointwise recovery equality, and result
stability.

### Failure: policy at-most-once is called global exactly-once

**Symptom:** a pure lease pool is duplicated and two workers each construct a
valid trace.

**Repair:** retain the local theorem wording. Add atomic persistent lease
acquisition and a refinement theorem before making process-global claims.

### Failure: protocol replay and records are separate certificates

**Symptom:** the log replays and the records form a valid model chain, but their
call IDs differ.

**Repair:** make `callBoundaries log` an index of the same `RecordChain` that
threads records.

### Failure: final leases are stored beside, not in, history

**Symptom:** a caller can overwrite `RunnerState.leases` while retaining a
valid record certificate.

**Repair:** make the final lease pool the fifth `RecordChain` index and
specialize `history` to the state field.

### Failure: a public generic event emitter

**Symptom:** callers can append accepted tool-call events without records.

**Repair:** expose structural operations, keep the generic emitter private,
and require proof that structural events have no call boundary.

### Failure: call and result are committed separately

**Symptom:** an intermediate state contains a pending call but no record or
matching result; a later failure leaks the obligation.

**Repair:** validate and append the adjacent pair, record, model, lease state,
and proof extensions in one private pure settlement function.

### Failure: pure settlement is called durable atomicity

**Symptom:** documentation implies crash safety or external exactly-once
execution.

**Repair:** say “one immutable `Except` result.” Durable atomicity requires a
storage protocol, failure model, and refinement proof not present here.

## 18. The exact trust boundary

The assurance layers can be summarized as follows:

| Layer                            | Local status                                                                                                                                                                                                                                | What remains outside                                                                                                                                                                                            |
| -------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Lean.Json` codecs               | Encode/decode round trips are proved for encoded ASTs.                                                                                                                                                                                      | Text parsing, rendering, schema semantics, and wire compatibility.                                                                                                                                              |
| Tool admission                   | Name, declaration, decode, precondition, and supplied capability checks run before constructing a dependent call.                                                                                                                           | Correctness of the resolver, capability source, model, and correspondence to a live registry.                                                                                                                   |
| Verified tool                    | A pure implementation returns a postcondition proof for its abstract model.                                                                                                                                                                 | Honest correspondence between real I/O and the abstract successor.                                                                                                                                              |
| Effect recovery                  | Captured inverses recover represented predecessors, exactly or modulo a supplied setoid.                                                                                                                                                    | Irreversible or unrepresented external observations and effects.                                                                                                                                                |
| Protocol                         | Six local event variants are indexed, checked, reconstructed, and replayed in memory.                                                                                                                                                       | Full Harness event vocabulary, extension merging, payload fidelity, persistence, and crash recovery.                                                                                                            |
| Stream                           | Finite text chunks respect budget and terminal state and assemble exactly.                                                                                                                                                                  | Provider streams, blocks, usage, tool calls, cancellation, transport, and backpressure.                                                                                                                         |
| Lifecycle                        | A local finite transition carries an undo stack, committed view, and supplied withdrawal guard.                                                                                                                                             | Complete live registry snapshots, races, fairness, reentrancy, and paper-wide multi-fiber metatheory.                                                                                                           |
| Global iterator family           | Oracle-specific reachable partial forwards and actually yielded inverses form exact closures; supplied forward respect gives the effect-relational variant; explicit provenance/membership can discharge temporal per-step commutation.     | Oracle-free or total Definition 60, rule/effect-relation identification, automatic totalization, owner inverse stability, reordering, Theorem 61, and Corollary 62.                                             |
| Global transposition             | `Independent` yields the raw diamond and exact square for two supplied totalized closure-member maps; `ObservationalIndependent` gives the effect square with separate forward-respect obligations; exact phase/code facts remain explicit. | Foreign-phase opacity, fixed landing/program provenance, guard/target stability, actual lifecycle-step transposition, Lemma 71, and mixed-trace reordering.                                                     |
| Foreign-phase frame              | Explicit readable-edit, ordinary-successor, and same-child oracle laws derive compatibility; two compatible independent programs yield an exact framed raw endpoint with retained post-raw lookups.                                         | Lower laws, distinct owners, reaches, executions, post-raw lookups, and typed phases are supplied; no lifecycle phase provenance, fixed episode/program assignment, guards/targets, `Transition`, or Lemma 71.  |
| Landing transposition            | Exact cross-forward yield syntax and fixed-program landings lift the framed raw endpoint to all four common-source L-Iter/L-Finish transition pairs with one exact final state; positive targets are preserved structurally under WF.       | Exact cross-forward law, both phase compatibilities, program-aligned common applicability, distinct owners, and WF are supplied; no Begin pair, trace-step identity, episode assignment, or full Lemma 71.      |
| Activation transposition         | Root-aligned Begin and program-aligned Iter/Finish form all nine exact common-source diamonds; fixed-program endpoint uniqueness reconciles a supplied actual second activation and derives the swapped transition.                         | Partial fixed-oracle Lemma 71(1) analogue under explicit WF, distinct owners, common applicability, provenance, and branch-relevant frame/exact-yield laws; no clause (2), stored-trace rewrite, or confluence. |
| Activation/orchestration         | The literal child condition is kernel-refuted; the corrected theorem reconstructs the early same-template orchestration and moved activation under registration safety and one occurrence frame.                                            | Corrected partial fixed-oracle Lemma 71(2) analogue; registering×Insert is excluded, frames are supplied, and no birth-erasing quotient, stored-trace rewrite, Lemma 72, or confluence is proved.               |
| Exact trace rewrite              | A dependent adjacent window, actual fixed-program occurrence ledger, and assigned corrected swap reconstruct an intrinsic complete trace with the same outer endpoints and reversed rule/actor projections.                                 | Exact stored-trace consequence only; occurrence laws remain supplied, registering×Insert and relation-only endpoints are excluded, and there is no suffix simulation, normalization, deletion, or confluence.   |
| Bounded deletion replay          | Positional keep/drop certificates construct a dependent shadow trace and assignment; finite already-vestigial families admit exact same-template safe foreign-orchestration suffix replay.                                                  | Deletion substrate only; no general lifecycle episode projection, provenance/no-redraw derivation, birth-erased outside relation, Lemma 72, normalization, or confluence.                                       |
| Finite rewrite-chain composition | `GlobalPaperTraceNormalization` connects a finite list of supplied `RelatedAdjacentRewrite` witnesses through dependent trace packages, retaining assignments and proving final birth-erased relatedness plus rule/actor permutations.      | Certificate composition only; no strategy, canonical form, termination, confluence, Lemma 72, or Theorem 73.                                                                                                    |
| Paper-visible relation           | Allocator clock/birth are erased from strict rule observation; full-domain related WF states match orchestration bidirectionally, while a WF source with `VestigialNames` supports directional safe replay.                                 | Finite structural relation slice; no one-sided WF transport, outside/lifecycle bisimulation, name quotient, relation-aware activation swap, Lemma 72, normalization, or confluence.                             |
| Conditional progress             | Fixed-oracle rejection and finite-name exhaustion refute unconditional progress; explicit precedence rank, current landing-or-raise/recovery readiness, and committed-provider soundness prove state-local no-deadlock.                     | Corrected Theorem 66 no-deadlock fragment only; no quantitative bound, target-turn finiteness, maximal termination, trace assignment, fairness, support, or confluence.                                         |
| Corrected support                | A reachable mixed cycle refutes separate acyclicity; combined-order well-founded recursion gives unique support, and state-local totality/failure/parent closure identifies it with active names.                                           | Corrected local Definitions 67/69 and Lemmas 68/70; combined order and parent closure are supplied, totality is state-local, and no trace provenance, deletion, or confluence follows.                          |
| Policy                           | One exact-subject pure trace dispatches at most once; completed traces dispatch exactly once.                                                                                                                                               | Global linearity, worker exclusion, retries, persistence, and idempotency.                                                                                                                                      |
| Batch                            | Two certified pure calls have equal proof-carrying outcomes in either represented order.                                                                                                                                                    | Real parallel execution, arbitrary batch sizes, cancellation, and external effect safety.                                                                                                                       |
| Runner                           | One pure state jointly certifies replay, model/lease/ID history, records, and boundary projection.                                                                                                                                          | TypeScript equivalence, network/model adapters, durable transactions, real tool I/O, and process-wide exactly-once behavior.                                                                                    |

Before extending the project with I/O, write a refinement boundary. For each
external action, identify:

1. the abstract predecessor represented in Lean;
2. the real observation used to construct it;
3. the concrete action corresponding to the abstract transition;
4. the evidence connecting real output to the certified outcome;
5. the compensation or explicit irreversibility policy;
6. retry and idempotency semantics;
7. cancellation and partial-failure semantics; and
8. persistence and restart behavior.

Without those pieces, the pure kernel remains useful as a specification and
reference implementation, but external correctness is trusted.

## 19. Safe extension paths

### 19.1 Generalize beyond the counter

The active `0.2` line now does this in `Cordis.GenericHarness`. When rebuilding
it, parameterize `CallEvidence`, `CallRecord`, and `Runner` by one coherent
configuration containing the catalog, model, capabilities, wire, view, and
policy. Preserve the exact call index in every result and policy trace. Keep
phase errors out of the trusted API by indexing `Runner` by `SessionState`;
retain a dynamic wrapper only at an untrusted boundary.

The rich-session coupling is factored separately in
[`../Cordis/GenericSessionHarness.lean`](../Cordis/GenericSessionHarness.lean).
`GenericSessionHarness.RunnerState` keeps the erased runner phase and the
append-only `Session` together with an exact projection proof. Its transitions
record the request header, user/assistant surface, tool-call/result pair, and
turn/step boundaries before returning the next pure state. The
[`../Cordis/Examples/DependentChoiceSession.lean`](../Cordis/Examples/DependentChoiceSession.lean)
fixture is important evidence: the same bridge carries a dependent non-counter
catalog, retains both an admitted revision call and a policy-rejected label
call, reconstructs a `ModelRequest`, and replays the exact generic log. This
remains an in-memory proof boundary; transport, persistence, external effects,
and deployed TypeScript equivalence are separate work.

### 19.2 Add a real JSON boundary

Keep byte parsing separate from the proof-carrying AST codec. A useful next
theorem would connect a selected parser and renderer to `Lean.Json`, with an
explicit accepted language and normalization policy. A separate semantics can
relate `Codec.schema` to decoder acceptance.

### 19.3 Add durable settlement

The first pure checkpoint is now in
[`../Cordis/DurableSettlement.lean`](../Cordis/DurableSettlement.lean), with the AST edge in
[`../Cordis/DurableCodec.lean`](../Cordis/DurableCodec.lean). `Spec` supplies a
typed effect and injective entry/state encodings; `Log` is indexed by its exact current state,
sequence, and collision-free list transcript; and `CrashPrefix` supplies a retained typed
prefix plus discarded frame suffix. The module proves exact newest-first recovery and typed
resume after the retained prefix. `DurableCodec` proves JSON-AST frame round trips and scans
entry codes, sequence numbers, previous digests, successor codes, and transcript digests before
constructing that typed log; malformed, torn, unknown, and non-contiguous frames fail closed.
[`../Cordis/DurableBytes.lean`](../Cordis/DurableBytes.lean) now adds an explicit pure binary
format over `List UInt8`: unary-length framing, a numeric `RawFrame` payload codec, counted
prefix decoding, and a theorem that carries discarded suffix bytes into the typed scanner. This
is a source-honest binary-prefix model, not a claim about the Harness JSON renderer or bytes
reaching a filesystem.

[`../Cordis/DurableIO.lean`](../Cordis/DurableIO.lean) is now the next, intentionally narrow
stateful boundary. `AppendPlan` carries the exact raw frame and encoded bytes; `MemoryStore` and
`FileBackend` execute append/replace plus host flush calls; and `readAndRecover` returns either a
typed scanned prefix or an operational/semantic error while retaining the discarded byte suffix.
The executable tests cover memory resume, a torn suffix, and a temporary filesystem file.

This does not make host acknowledgement into durable atomicity. The remaining production
obligations are a selected parser/renderer refinement, actual partial-write and crash semantics,
stable-media/fsync policy, checksum or authenticated digest policy, checkpoint selection,
fork/conflict handling, multi-process coordination, and the relationship between external tool
effects and committed entries. Only after those obligations are proved should the project claim
durable atomic settlement or process-wide exactly-once behavior.

### 19.4 Add an `N`-call scheduler

The active `Cordis.Schedule` module now proves that any `List.Perm` of one
finite family carrying pairwise complete-effect commutation denotes the same
pure composite effect. That closes the semantic list-permutation step, but not
the runtime scheduler. The next extension still must distinguish evaluation
order from model-commit and result order, and represent cancellation, drain,
provider failure, and synthetic abort results. A theorem about pure reorderings
does not authorize real parallel I/O without a concrete refinement.

The bounded next slice is now available in
[`../Cordis/ParallelHarness.lean`](../Cordis/ParallelHarness.lean). Its `ParallelWindow`
requires the scheduler-facing obligations as fields: finite task IDs and modes, a complete
effect-commutation certificate, and a result-permutation certificate. `WindowOutcome.execute`
evaluates the supplied schedule and exposes model-order commits; `Plan` adds one explicit
exclusive barrier; `drainOutcome` emits ordered synthetic cancellation reports while leaving the
model unchanged. This is deliberately an executable pure scheduler certificate. It does not
launch `IO` tasks, model promise races or cleanup, or claim equivalence to the TypeScript
`tool-calls.ts` implementation. A production adapter must first prove that its worker, result,
cancellation, and persistence behavior refines these fields.

[`../Cordis/ParallelSchedule.lean`](../Cordis/ParallelSchedule.lean) now composes an arbitrary
finite list of those windows and barriers. `Plan.execute` threads each segment's endpoint and
newest-first recovery, proves equality with the canonical composed effect, emits reports in model
order, and checks global task-ID uniqueness across segment boundaries. This closes the pure
finite-schedule construction step; it still does not launch workers or prove wall-clock overlap,
promise races, fairness, cancellation delivery, cleanup, persistence, or TypeScript refinement.
The next production step is an explicit adapter from those certificate fields to the real
Harness worker/result lifecycle.

[`../Cordis/AsyncHarness.lean`](../Cordis/AsyncHarness.lean) now supplies the next bounded
state-machine layer. `Runtime` stores an indexed phase for every fiber, `Step` makes the
pending/running guards and terminal transitions explicit, and `Trace` retains the exact
completion order. `SuccessfulSchedule` adds a finite drained certificate and proves that the
completion permutation has the canonical pure model endpoint. The concrete example starts two
fibers, completes them in the opposite order, and separately witnesses cancellation without a
model effect. This is still a proof-carrying pure model: do not describe it as launching `IO`,
delivering promise cancellation, proving wall-clock fairness, or refining the TypeScript
scheduler. Those claims require an adapter with explicit worker, cleanup, and persistence
contracts.

[`../Cordis/DeepSeekAsyncHarness.lean`](../Cordis/DeepSeekAsyncHarness.lean) is the first small
adapter over that boundary. Each `ProcessJob` runs the existing complete-body text-prefix session
adapter in its own cooperative `ContextAsync` child, and `executeRace` uses `ContextAsync.race` to
retain the first typed result while requesting cancellation of the other child. The deterministic
fixture runs two real `sh` processes, and `RaceResult.phase` is connected to the pure terminal-phase
certificate. The child still performs a synchronous line-oriented read, so the module does not
prove blocked-read interruption, fairness, arbitrary cleanup, or deployed Harness equivalence.

[`../Cordis/DeepSeekAsyncStreamHarness.lean`](../Cordis/DeepSeekAsyncStreamHarness.lean) lifts
the same adapter over the streamed dependent continuation. A `StreamProcessJob` keeps the request,
configuration, initial model/runner, and source-sequence proofs together; the cooperative race
then preserves the winner's typed tool executions, round witnesses, final model, and runner. The
fixture runs two real `sh` processes through a tool-call round and a later text terminal. This still
does not make synchronous line reads interruptible or prove fairness, cleanup, or deployed async
semantics.

### 19.5 Relate the model to DeepSeek Harness

The active `Cordis.RuntimeRefinement` module begins this work for a supported
current-Harness `StreamChunk` subset. `Cordis.SessionRefinement` adds a stateful
turn/step/tool subset plus text user/assistant surface blocks and complete assistant
tool-call blocks. Accepted events carry rich Session witnesses; runtime events additionally carry intrinsic
Protocol witnesses, while admitted surface IDs/provider metadata remain in the
refinement state and only text enters the smaller local message types. Both start
at `Lean.Json`, decode exact current field/tag shapes, and fail closed outside
their stated language.
`Cordis.SessionArchive` is the adjacent lossless envelope layer: it retains every
envelope-valid record, classifies unsupported required versus explicitly ignorable
extensions, and attaches a `SessionRefinement.WireEvent` certificate when the
semantic decoder succeeds. It must not be used to silently resume through a
required opaque record; extension payload semantics remain a separate task.
`Cordis.TextRefinement` now supplies the preceding executable ingress for local
fixtures and append-only adapters: it parses newline-delimited UTF-8 JSON into
exact AST lines, retains source/line failures, and composes the two validators
without weakening their dependent certificates.
`Cordis.HarnessPersistenceRefinement` supplies the next logical storage ingress:
it splits the pinned JSONL session header from storage rows, expands the exact
text/reasoning/tool packed-row forms with checked safe sequence/time gaps, and
feeds the expanded event AST to `SessionRefinement`. Keep this boundary logical
and fail-closed; compression, file offsets, torn-tail repair, and filesystem
durability belong to a later adapter rather than being smuggled into the proof.
`Cordis.HarnessPersistenceArchive` is the parallel lossless ingress for the same
document when semantic expansion is unavailable: it retains the typed header,
packed row tags/raw ASTs, and ordinary `SessionArchive` envelopes in exact order,
and carries the full document index on malformed envelope errors. It does not
expand packed rows or authorize replay through opaque payloads.
`Cordis.HarnessPersistenceIO` is that deliberately small next adapter. It reads
UTF-8 bytes through the existing memory/filesystem backend, retains the exact
decoded text, parsed rows, logical persistence certificate, and session projection,
and only appends a row after the current document validates. Treat the backend's
write/flush acknowledgement as operational evidence, not as a durability theorem:
fsync, stable media, locking, torn-tail repair, and crash recovery still require
separate contracts.
`Cordis.HarnessPersistenceBytes` is the pure immutable-byte companion: it validates
`ByteArray` UTF-8/JSONL input while retaining the source bytes, decoded text, parsed
rows, packed expansion, and final Session/Protocol projection. Its accepted and
fail-closed fixtures are executable boundary evidence; parser/printer behavior,
compression, filesystem durability, and crash recovery remain separate contracts.
`Cordis.SessionEventArchive` now closes the adjacent wire-vocabulary gap. It recognizes all
thirteen pinned core `SessionEvent` tags, checks object-shaped payloads and forbids surface
metadata on log-only tags, delegates accepted records to `SessionRefinement`, and preserves
unsupported known payloads as raw typed opaque records. It deliberately does not invent payload
types for assistant reasoning/image blocks, provider usage/failure objects, tool-result `error`/
`meta`, or future request configuration.
`Cordis.SessionPayloadArchive` is the next typed raw-payload boundary. It classifies the five
current content-block tags plus unknown block extensions, preserves exact content arrays and
message/chunk source objects, and retains assistant usage/tool-result `error`/`meta` as raw JSON.
Shape failures attach to the already-retained event instead of dropping it. This moves the source
contract inward without claiming provider/tool schema equivalence, replay, or local Session
equivalence.
`Cordis.DeepSeekApi` now supplies the adjacent provider boundary: typed
OpenAI-compatible chat requests become exact POST plans, successful responses
retain parse/decode certificates, and transport, HTTP-status, and API errors
remain separate. `Cordis.DeepSeekCurlTransport` adds a process-backed adapter
that passes request bodies on stdin, URL/headers as direct executable arguments,
and parses a private status trailer; its deterministic `sh` fixture exercises
the real process boundary. Keep it explicit in tests: do not present it as
live HTTP, credential validation, executable trust, or complete provider/schema
compatibility.
`Cordis.DeepSeekRequestMode` is the type-indexed refinement at this seam:
`TypedRequestPlan .complete` and `TypedRequestPlan .streaming` retain an equality
for the serialized `stream` flag, so terminal execution cannot consume the
streaming index. The raw `RequestPlan` remains available as a compatibility
surface, while complete, recoverable, and retry Harness round paths use the
typed complete builder internally.
`Cordis.DeepSeekCurlStream` composes the same process boundary with complete-body strict SSE
validation. It preserves process, HTTP-status, framing, and stream errors before exposing any
frames, while leaving incremental reads, buffering/backpressure, cancellation, reconnects, and
provider-complete assembly as explicit deployment work.
`Cordis.DeepSeekStreamIncremental` supplies the pure prefix contract immediately below that wire
parser: each complete line is parsed into a state retaining the exact accumulated body, frames,
line number, and prefix equation; `finish` invokes the original complete-body validator and refuses
an incomplete `[DONE]` prefix. Its line policy is a proof-carrying stop boundary, not a live-reader
or backpressure/cancellation implementation.
`Cordis.DeepSeekCurlSession` takes the terminal text subset one step further: it retains the
process-backed wire certificate, runs the accepted rich/session projection, and returns the
proof-carrying append-only runner. Source-event evidence, numeric local-ID assignment, and all
live/deployed session behavior remain explicit inputs or external obligations.
`Cordis.DeepSeekStreamHarness` applies the same complete-body boundary to terminal rich tool
streams: it assigns local numeric IDs, sends each streamed call through the generic dependent
admission/policy/provider path, and appends the certified typed results to a reusable
`ConversationRunner`. The one-call entry point and typed
`executeConversationMultiStreamRound` are exercised by deterministic process fixtures, including
a two-call terminal stream. Their output can feed the existing subsequent-request or
fuel-bounded round runner; `runConversationMultiStream` composes those round certificates under
explicit fuel and stops on a text-only terminal response or typed exhaustion. Incremental
delivery, cancellation, backpressure, reconnects,
provider-complete assembly, and deployed equivalence remain outside the adapter.
The streamed builder is deliberately distinct from the non-streaming builder: it calls
`buildStreamingRequestPlan`, whose dependent source/body certificates prove `stream: true`.
The executable fixture consumes stdin and rejects a body without that serialized flag, so the
round test checks the request-mode boundary rather than merely accepting any process output.
`Cordis.DeepSeekStreamHarnessCancellation` adds a typed pre-round cancellation decision over
that streamed loop, preserving the completed streamed prefix and runner/model endpoint while
leaving interruption of an in-flight process read or external tool as an adapter-specific
obligation.
`Cordis.DeepSeekStreamHarnessPrefix` moves that continuation under the existing line-oriented
process prefix: each complete line is retained before the next read, and completion appends the
same certified multi-call tool results while fuel or line cancellation returns the exact prefix.
Byte framing, blocked-read interruption, and deployed stream semantics remain external.
`Cordis.DeepSeekStreamHarnessErrors` is the corresponding complete-body streamed failure seam:
`executeFunctionCallsRecoverable` retains a typed provider failure and model-preservation proof,
then `appendRecoverableToolResults` appends the model-visible `isError` result. The caller must
opt into consuming that result on the next request with `RequestSource.errorToolResults := .include`;
`runConversationMultiStreamRecoverable` retains that failed round and a later streamed text
terminal under explicit fuel. Incremental recovery and deployed provider error behavior remain
outside this adapter.
`Cordis.DeepSeekStreamHarnessRetry` is the adjacent retry seam for a complete-body streamed
round. Its explicit policy retries process and transient-HTTP `SessionClientError`s, retains the
ordered history and retry bound, and then reuses the existing streamed assistant/tool certificates
on success. Stream framing, semantic response, and tool failures remain terminal; backoff,
idempotency, cancellation, persistence, and deployed retry equivalence remain external.
`Cordis.DeepSeekHarnessErrors` makes the provider-failure policy explicit rather than silently
choosing one behavior: `.reject` is the default fail-closed request policy, while `.include`
retains a `ProviderFailedTool` proof and appends its exact provider message as an `isError` tool
result. The recoverable round preserves the model on that branch and can feed a subsequent typed
request; persistence, async scheduling, and deployed error semantics remain external. The separate
`Cordis.DeepSeekHarnessRetry` adapter wraps one fixed `RequestPlan` in an explicit bounded,
immediate retry policy for transport/transient-HTTP failures. Its `RetryHistory` retains every
prior `ClientError`, and the retrying conversation result carries that history into the same typed
runner. This is not provider backoff, idempotency proof, cancellation, or deployed-Harness retry
equivalence.
`Cordis.DeepSeekHarnessCancellation` adds the corresponding pre-round control boundary: the policy
is checked before a complete request round, and a cancellation result carries the unchanged
runner/model endpoint and completed prefix. Keep the boundary honest: interrupting an in-flight
process, HTTP request, stream reader, or external tool needs an adapter-specific token and cleanup
proof that this pure complete-body layer does not provide.
`Cordis.DeepSeekCurlIncremental` changes only the process read shape: a line-oriented callback sees
each body line under an explicit read budget before the private status trailer is consumed, while
the reconstructed body still passes the strict SSE validator. It is not a byte-level reader or a
proof of backpressure, cancellation, reconnect, process trust, or provider-complete assembly.
`Cordis.DeepSeekCurlPrefix` is the typed process counterpart: it advances `PrefixState` before
requesting the next complete line, retains the raw process body separately from the normalized
prefix certificate, and uses the same line policy for synchronous fuel/cancellation stops. Its
cleanup kills and waits for the child, but it cannot interrupt a blocked read or establish
backpressure, reconnect, process trust, or deployed assembler equivalence.
`Cordis.DeepSeekCurlPrefixSession` consumes the completed branch of that result, applies the
existing text/tool/mixed/multi terminal projections, and appends the retained assistant to the
typed session runner with the existing next-sequence/next-call proofs. Fuel and cancellation are
not converted into response errors; they remain explicit stop outcomes.
`Cordis.DeepSeekAsyncHarness` then races two complete-body text-prefix session jobs in separate
cooperative children. The winning `PrefixResult` remains typed and its phase is classified by pure
theorems; the fixture checks the actual process-backed race. Treat the cancellation as a request to
the cooperative context only: the synchronous line reader is not interruptible by this proof, and
fairness, arbitrary cleanup, and deployed asynchronous semantics remain adapter obligations.
`Cordis.DeepSeekAsyncStreamHarness` applies that same cooperative race to the streamed tool/session
continuation. Under explicit fuel, each child can execute dependent tool calls and reach a later text
terminal; the winning typed result preserves its model, runner, and round evidence. The cancellation
is still only a cooperative request around synchronous process reads, not blocked-read interruption,
fairness, cleanup, or deployed asynchronous equivalence.
`Cordis.DeepSeekStream` supplies the next wire boundary: strict in-memory
`data:` / `[DONE]` SSE framing, typed delta choices, retained raw-frame
parse/decode certificates, and explicit invalid-UTF-8/JSON/terminal errors.
It is not a live reader or a stream assembler; buffering, cancellation,
backpressure, provider-complete chunk coverage, and HTTP remain external.
`Cordis.DeepSeekRichStream` then composes the accepted wire certificate with
`RichStream` for one source-honest semantic subset: one assistant choice at
index zero, text-only deltas, terminal usage, and stop/max-token finish. The
validated value retains wire, projection, and intrinsic rich-trace certificates;
reasoning, tool calls, extra choices, unsupported finishes, and missing terminal
fields fail closed rather than being silently normalized.
`Cordis.DeepSeekRichToolStream` is kept separate so tool semantics do not widen
the text-only language implicitly. It accepts one provider-index-zero function
call, preserves raw argument fragments and stable IDs/names, closes the exact
local tool block, and requires a terminal `tool_calls` finish. Multiple calls,
missing identifiers, mixed text/tool deltas, and tool execution remain outside
this proof-carrying projection.
`Cordis.DeepSeekSessionBridge` is the explicit local surface seam after either
rich-stream validator: `finishAssistant` requires the terminal witness, and
`appendFinishedAssistant` requires a caller-supplied numeric `CallIdAssignment`
plus earlier source-event sequence proofs before appending the assistant payload.
The bridge proves the exact resulting message projection, but does not
authenticate provider IDs, persist the append, or establish whole-session
equivalence with the deployed Harness.
`Cordis.DeepSeekSessionRunner` composes `finishText` and `finishTool` into a pure
append-only runner. Its state carries exact physical sequence, turn/step coordinates,
and a proved total tool-call count; each append allocates local IDs by count and
preserves message order. The runner is a proof-carrying composition test, not a live
transport, cancellation, persistence, or external-tool implementation.
`Cordis.DeepSeekApiSession` covers the non-streaming response path with the same
fail-closed policy: singleton index-zero choice, supported finish, and nonempty
content/tool payload are required before the append. Extra choices and unsupported
terminal states are preserved as typed rejection rather than silently dropped.
Continue by defining translations for additional pinned Harness payload fields and tool
definitions and proving only the invariants actually shared by the two representations. Expect to
model more payloads, surface semantics, session
extensions, policy phases, persistence, and cancellation. Similar names and a
one-way supported-subset text/AST decoder are not a whole-runtime equivalence theorem;
Lean's parser and the external logger remain explicit boundaries.

### 19.6 Mechanize more of the paper

Use [`PAPER_MAP.md`](PAPER_MAP.md) as a backlog. Major missing areas include the
effect-context tower, the paper's literal total/quotient Theorem 42 beyond the finite partial
analogue, global trace metatheory,
full preservation, full Theorem 61/Corollary 62 temporal recovery beyond the oracle-specific
finite Definition 60-to-`PerStepCommutes` bridge, spatial composition, progress,
confluence, loader reconciliation, and HMR. The active line now covers finite local coeffects (Definitions 22–26),
direct finite realization/isolation/interception models (27–31), finite
unfoldings of 32, and the finite-context relation/reactive invariance of 33.
It also covers Definition 34 and generator-level Lemma 35, Definitions 36–37,
the finite-composition core of Lemma 38, Definitions 17–19, full total Definition
39, finite partial distinct-key Theorem 40, and Definition 41. Do not present those bounded
results, finite exact Theorem 20/Corollary 21, the orchestration-only global registry, local
`UndoStack`, lifecycle, or batch results as substitutes for the
remaining theorems.

### 19.7 Rebuild the bounded context layer by hand

Implement this layer in paper dependency order.

1. Start with `Coeffect.Context Key Value`, where `Value : Key -> Type` and lookup returns
   `Option (Value key)`. Carry finite support only as a proposition so context equality remains
   extensional in lookup behavior.
2. Make `Present context key` carry both the exact value and its lookup equation. Make `Absent`
   a proposition. The witnessed insertion inverse should remove only the selected key; prove
   `removeAt (setAt context key value) key = context` from absence.
3. Put each key's equivalence, operation-indexed argument/result types, executable domain,
   witnessed local effect, and preservation laws in `CoeffectAt`. Lift an operation by changing
   only that dependent binding.
4. Encode a finite specification as a duplicate-free key list. Define satisfaction by presence,
   then prove the executable notification classifier is exactly activating, deactivating, or
   neutral according to the before/after satisfaction propositions.
5. Keep Definition 27's two realization modes distinct. `InPlace` wraps `Applied`; `Derived`
   indexes a child by an unchanged parent so discard recovery is a projection rather than a
   fabricated mutation.
6. For isolation, use a finite logical-key routing override and a dependent realm store. Require
   the fallback `baseRealm` embedding to be injective, resolve before typing get/set, and prove
   derived routing overrides inherit the store.
7. For interception, define a key-indexed metadata monoid, a total metadata family, and a finite
   table of providers of type `Meta key -> Value key`. Keep component-declared metadata on the
   left and context metadata on the right of the merge.
8. Do not encode `mu Gamma. Gamma x (Gamma -> Gamma) x Sigma` as an ordinary inductive. The
   recursive variable occurs negatively. Define depth-indexed finite unfoldings and state that
   boundary in the module documentation.
9. Lift each key relation through `Option` so absence relates only to absence. Prove this is
   equivalent to equal presence domains plus pointwise-related present values; then package it as
   a `Setoid` and prove satisfaction and notification invariance.
10. Represent a Definition 34 test as a finite word of typed forward operations and concrete
    inverses yielded at enabled seed states. Keep outcomes heterogeneous and make a failed
    forward precondition return an undefined observation.
11. Prove finite-test agreement is an equivalence and the largest relation respected by each
    fixed generator. Do not silently upgrade that result to compare two different inverses
    yielded at related seeds: the checked `PairedGap` model refutes that implication. Name the
    additional paired-inverse coherence law explicitly when a full `CoeffectAt` requires it.
12. Separate Definition 36's quotient-respecting map from pointwise map relatedness. Add
    Definition 37 admissibility to observational effects, prove it is closed under sequential
    composition, and then prove the key-local operation lift preserves whole-context successor,
    inverse-map, and outcome relations.
13. Build Definition 17 as an intrinsic generated-monoid predicate containing identity, every
    forward/yielded-inverse generator, and composition. Prove commutation and inverse stability
    promote from generators, and prove Definition 18 sequencing introduces no transformation
    source outside the joint closure. Keep Definition 19's full cross-monoid commutation and
    yielded-inverse stability separate from adjacent sequence equality.
14. Add operation-specific outcome stability for Definition 39. For partial dependent operations,
    execute explicit finite forward/inverse words and prove distinct keys commute including
    undefinedness and complete yielded data. Encode Definition 41 as a free outcome-indexed
    computation tree and compose its inverse in LIFO order.
15. For Theorem 20, index a paired suffix trace by the target-present and target-omitted states
    and retain every later effect's two application states plus equality of the inverse it yields.
    For Corollary 21, apply the exact retained inverse functions directly, prove they form a
    commuting finite family under pairwise Definition 19 independence, and induct on `List.Perm`.
    Do not reapply or reorder whole effects.

16. Do not compare the individual domains of two partial computations: unit is total while a
    partial computation may be undefined, even though both composite orders agree. Compare the
    composite domains directly and retain conditional yielded-inverse stability as a separate
    field. Kernel-check the old API's failure with partial computation versus unit.
17. Prove the corrected finite whole-run theorem constructively. First preserve complete
    `ForwardData`, including the typed outcome, across an adjacent swap. Then bubble one root
    through every outcome-selected foreign continuation and bubble every left root in turn. Erase
    only `Applied`'s predecessor/recovery proof during structural swapping; reconnect the exact
    successor and complete inverse functions to the original proof-carrying runs before stating
    the theorem.
18. Build the full partial transformation certificate separately. Use Kleisli maps
    `State → Option State`, generate the closure from the adaptive partial forward map and every
    actually yielded totalized inverse, and prove forward/forward, forward/inverse,
    inverse/forward, inverse/inverse, and yield-stability generator laws structurally. Promote
    them through identity/composition closure. Derive whole-run interchange from this certificate,
    and kernel-check that whole-run equality does not imply cross-seed inverse commutation.
19. Descend the exact partial closure through contextual equivalence explicitly. Define related
    partial maps over two related representatives so `none`/`some` disagreement is rejected, and
    require every generator to respect that relation. Prove adaptive computation evaluation
    respects domains, successors, complete inverses, exact heterogeneous outcomes, and selected
    continuations by structural induction. Then show the existing `CoeffectAt` laws discharge
    generator respect and reuse the exact closure theorem. Include a counterexample where an
    exactly commuting map copies hidden representation state into an observed field, demonstrating
    why exact commutation alone cannot supply quotient independence.

The result is the full finite exact and relation-respecting partial/Kleisli analogue of Definitions
17/19 and Theorem 42, not the paper's literal total/quotient setting. The observational theorem
still starts from exact `PairwiseOverlap`, which is stronger than quotient-only operation
independence. Likewise, do not confuse it with exact representative equality: the
universal-equivalence cell counterexample still requires `ExactRepresentativeCoherence` for exact
promotion.

The important review question at each step is whether a theorem describes the paper object
directly, a bounded approximation, or an integrator-supplied obligation. Put that distinction in
the declaration's documentation, not only in release notes.

### 19.8 Rebuild the current JSON refinements by hand

Keep three layers visibly separate:

1. `Lean.Json` wire values mirror supported current TypeScript optionality and tag names.
2. `SupportedChunk.toRaw` performs the named normalization into local `RichStream.RawChunk`.
3. `validateJsonTrace` runs `RichStream.validateTrace` and stores both the exact decoding equation
   and the intrinsic dependent trace witness.

Use path segments for nested decode errors. Accept numeric indices only when their JSON-number
representation is a canonical nonnegative integer no larger than JavaScript's safe-integer
limit. Preserve provider tool IDs and raw argument fragments as strings. Map missing optional
usage counts to zero in one named function so reviewers can see the semantic choice.

Fail closed when the upstream and local types differ. In the current slice that means opaque
replay state, image/tool-result blocks, and error/abort `LlmFailure` values. Add exact rejection
theorems for each unsupported boundary, and keep decode errors separate from semantic stream
errors. The resulting theorem is supported-subset soundness, not assembler completeness.

For session events, use a stateful refiner rather than a context-free codec. Decode and retain
the current `{type, seq, time, data, ignorable?, sourceEventSeqs?, surfaceOp?}` envelope, then:

1. normalize upstream one-based steps to the local zero-based protocol only after rejecting zero;
2. derive `turn/end.nextStep` from the already validated local turn state;
3. assign provider string call IDs to fresh numeric IDs in proof-carrying state;
4. construct one candidate whose rich event projection is definitionally the runtime event;
5. require both `Session.validateAppend` and `Protocol.validateEvent` to accept it; and
6. compose the witnesses and prove the final Session projection equals intrinsic trace erasure.

Keep the subset narrow. The current implementation supports boundary events, tool calls, a
restricted singleton-text tool result, all six pinned turn-end reason tags, and append/replacement
surface operations whose ranges and source coverage are discharged by `Session.validateAppend`.
It rejects identities/payloads the local type cannot preserve, opaque metadata, extensions, and
unsupported turn-end tags. Structured turn-end cancellation/failure facts remain in the
wire/refinement state even when the smaller local type projects them to cancellation or a
failed-string reason. This is stateful supported-subset soundness, not a persisted JSONL or
whole-session equivalence theorem.

### 19.9 Rebuild the first global registry slice by hand

Do not put an effect or iterator function over `GlobalState` inside a fiber stored by that same
`GlobalState`; that repeats the negative recursive occurrence. Define a static signature of opaque
component, iterator, and undo codes first. The state may then contain only codes, finite
declarations, data, and proofs. A later external `Dynamics` record can interpret codes after the
state type exists.

Build the structural slice in this order:

1. Define finite dependency/provision declarations and a total committed view over the declared
   key subtype.
2. Define four code-only phases, private typed fiber tables, retirement, parent, and birth rank.
3. Define a finite name-to-fiber registry and global ambient state.
4. Strengthen well-formedness with `parent_older`; parent presence alone permits cycles. Prove a
   positive parent chain strictly increases birth rank and therefore cannot cycle.
5. Derive active providers/values and target views from the registry. Prove provider/value/target
   uniqueness before defining a chosen active context or target.
6. Make insertion consume an explicit freshness witness and provision-disjointness proof. Keep an
   optional executable `FreshSupply` separate from relational preservation.
7. Encode O-Insert, O-Retire, and O-Remove exactly. O-Remove's retired/inactive/childless premises
   are enough: prior committed-provider-installed well-formedness rules out a surviving installed
   consumer pointing at the inactive removed fiber.
8. Prove every rule and finite orchestration trace preserves the strengthened invariant.
9. Only after `GlobalState` exists, define an external `Dynamics` record interpreting iterator and
   undo codes. Ordinary results must carry exact recovery plus explicit write/read/respect/WF
   laws. Registration admission must carry freshness, owner/parent, provision, and observational
   retirement-recovery evidence.
10. Reconstruct intrinsic ordinary/registration steps from the interpreter and admission oracle.
    Accumulate newest-first undo codes, prove recovery respects the state setoid, and implement a
    total fueled runner whose trace is indexed by the actual continuation code and whose zero-fuel
    result is explicit exhaustion rather than success.
11. Define lifecycle transitions with exact endpoints. A landing must carry its distinct
    registration-error type, admission oracle, dependent `IterationStep`, and the exact equation
    showing `executeOne` returned it. Split L-Divert into abort and land constructors while mapping
    both to one paper rule name; put abort permission in an explicit inertia policy.
12. Make L-Unload the only lifecycle edge that interprets the accumulated recovery list. Until
    temporal composability is proved, require a named `RecoveryAdmission` containing the exact
    recovered owner, inactive endpoint, and WF preservation. Prove deactivation preserves WF from
    the global non-reliance guard, then compose rule preservation over exact finite traces.
13. Exercise Begin/Iter/Finish and Leave/Unload with an explicit orchestration retirement between
    the two trace segments. Prove the landing equations came from `executeOne`, the accumulator
    shape, inactive endpoint, restored observation, and negative target/inertia/raise guards.
14. Wrap orchestration and lifecycle without changing either endpoint. Project to exactly ten rule
    names while retaining the acted-on name for every rule. Keep Equation 51's identity/iterator/
    recovery map separate from insert/retire/remove and phase edit footprints. Prove actual
    installed status changes only at L-Begin/L-Unload, and package a trace whose initial registry
    is explicitly empty.
15. Audit Lemma 54 against the actual recovery API. Prove every non-unload constructor preserves
    pre-existing foreign fibers exactly. For unload, require a step-indexed `RecoveryConfinement`
    covering foreign tables/control and actor static fields; show with a finite countermodel that
    endpoint well-formedness alone does not imply it. Align trace state/step lists and make episode
    boundary exclusion specific to the observed name, so other fibers may begin or unload inside
    its episode. Keep fresh-entry and retirement-write provenance separate for opaque undo codes.
16. Reify Equation 51 state maps independently of their exact endpoints. Iterator-backed maps
    should re-run the captured code/oracle and remain partial off-source. Parameterize temporal
    recovery by an effect-relevant relation distinct from arbitrary `Dynamics.equivalence`; require
    totalization, edit invisibility, relation preservation, per-step recovery commutation, owner
    inversion, and trace reordering explicitly. Derive whole-replay commutation by induction, then
    add the unload bridge. Kernel-check failures of off-source totality, universal-relation
    adequacy, and RecoveryConfinement-as-temporal-independence.
17. Keep the paper's rule and effect observations distinct. Parameterize rule-level context values
    by key-indexed setoids, retain registry domain/control exactly, and include any local proof
    clocks that affect rule applicability. For effect observation, retain ambient state and
    normalized table lookups while deliberately forgetting lifecycle control and treating an
    absent fiber like an empty vestigial table. Prove both relations are setoids and add concrete
    separations in both directions. Require a named undo-respect law before using the effect
    relation in temporal recovery, and name the rule-bisimulation obligation instead of claiming
    Lemma 55 from a relation definition alone.
18. State spatial consequences over one exact master trace. Prove L-Begin dependency satisfaction
    from target-view soundness and well-formedness. Because independently bounded episodes do not
    imply nesting, require an explicit prefix/interior decomposition before deriving strict open
    and close offsets. Propagate an installed consumer's committed provider resolution through a
    sufficiently confined boundary-free interior and use the non-reliance guard to reject provider
    unload. Make provider-table constancy a separate per-record premise; discharge it from
    sufficient confinement only when every actor is foreign. Classify one reloading lifecycle step
    by target equality/diversion/raise without claiming an initial interval, eventual close, or
    recovery theorem.
19. Treat vestigial removal as a commuting-square problem, not as informal invisibility. Package
    retirement, exact successful inactivity, an empty dependent table, and childlessness. Prove
    normalized effect observation equates the state with removal. For orchestration, retain exact
    rule kind, acted name, endpoint deletion, and vestigiality in forward/backward square records.
    Forward insertion must not adopt the vestigial entry as parent. Backward simulation must
    exclude drawing its name, provision overlap, and removal of its parent. Kernel-check every
    exception on well-formed states. The last exception corrects a directional error in pinned
    Lemma 57(2): no child pointing to `n` does not imply `n` has no parent `m`.
20. Prove rule invariance one rule family at a time. For orchestration, extract a peer fiber from
    exact domain/control equality without equating its private table. Reconstruct insert freshness,
    parent presence, and provision disjointness; retire the peer fiber; and transport remove's
    retirement, noninstallation, and childless premises through control fields. Prove ActiveValue
    iff lemmas for all three edits, then use well-formed uniqueness to recover exact per-side
    active-context invariance. Package bidirectional same-kind/name peer steps with exact endpoints,
    endpoint well-formedness, and successor `RuleRelated`. Before extending to lifecycle rules,
    require iterator/read, oracle/landing, recovery, and inertia-respect laws; an ambient-sensitive
    abort-policy countermodel shows these are semantic requirements, not proof conveniences.
21. Before assuming lifecycle execution compatibility, exhaust the observation relation. Match
    active providers by name using context-domain agreement and provision uniqueness, then
    transport dependent target views, committed resolution, reliance, phase patterns, quiescence,
    and each structural guard bidirectionally. Relate matched active tables pointwise rather than
    equating them. Record the activation seam explicitly: a reloading fiber's table is private, so
    L-Finish requires the landing contract to relate the two newly active tables. Keep rule and
    effect relations incomparable with executable examples, and do not let ambient-insensitive
    rule observation stand in for iterator, inertia, or recovery behavior.
22. State external lifecycle compatibility below the rule relation. A landing match must provide a
    real peer landing, equal undo/next codes, related landing endpoints, and related yielded tables
    on the done branch. Add exact raw-error transport, inertia respect, and peer recovery admission
    with related final endpoints; none may mention a transition, step, or bisimulation. Prove
    phase-update context visibility separately for nonactive, activate, and deactivate modes, then
    construct all eight lifecycle cases and combine them with orchestration under well-formedness.
    Add a reloading-table countermodel showing why Finish alone needs the yielded-table premise.
    Keep the result conditional and distinct from the raw no-well-formedness API.
23. Replace opaque equivariance placeholders with an executable structural action. Use a genuine
    name bijection plus bijections on ambient state, each dependent value type, errors, iterator
    codes, and external undo codes; keep keys/components/catalog fixed. Map parent pointers,
    committed providers, retirement undos, phases, tables, and finite registry indices canonically.
    Prove identity, composition, inverse, lookup, and exact state-recovery laws before attempting
    rules. Transport all six well-formedness clauses, prove insert/retire/remove edits commute with
    the action, and build forward/backward orchestration witnesses with renamed actors. Keep catalog
    entry invariance separate for L-Begin. Refute the old record with a noninjective name map that
    satisfies its lone run equation, and defer dynamics/lifecycle action laws explicitly.
24. Extend name action through execution with the smallest noncircular semantic record. Act
    ordinary results, registration requests with inverse-name continuation conjugation, iterator
    results, and both `Except` branches. Require exact run-output action, external-undo commutation,
    dynamics-equivalence invariance, inertia invariance, and fixed catalog entries. From these
    derive undo/recovery, registration admission, a conjugated oracle, proof-carrying iterator
    steps, `executeOne`, Landing, recovery admission, target/reliance action, and all eight lifecycle
    endpoints. Derive inverse assumptions and backward/unified action rather than postulating them.
    Exercise a nonidentity Raise and prove fixed-entry and error-aware-run necessity. Keep source
    well-formedness and fixed component/catalog boundaries explicit.
25. Add iterator-family independence without hiding registration choice or off-source partiality.
    Define a `Program` from one owner, root iterator code, registration-error type, and fixed
    registration oracle. Generate `Reach` only through successful `executeOne` continuations. Let
    the program monoid be the least Kleisli identity/composition closure containing every reachable
    partial forward map and every totalized inverse actually yielded by a reachable execution.
    Define exact yield agreement over inverse map, continuation, and
    ordinary-versus-registration component, then promote generator commutation and yield stability
    to full `Independent`. Index family pairwise independence by occurrences so duplicate programs
    force self-independence, and keep reachability finiteness and continuation bounds as explicit
    certificate types. Build the `EffectEquiv` observational variant separately from the paper's
    rule relation `≃`: require `ProgramRespects` for every reachable forward map, while deriving
    yielded inverse respect from `EffectEquiv.applyUndo_respects`. For the temporal bridge, retain actual inverse provenance in
    `YieldedAccumulator`, require acted-owner equality and closure membership in `StepMapMember`,
    and require every foreign trace step to carry a program, owner/foreign observational independence,
    membership, and an already constructed `TotalStepMap`. Prove only `PerStepCommutes`; do not
    infer totalization, owner inverse stability, mixed-trace reordering, Theorem 61, or Corollary 62. Keep the registration-child, self-independence, whole-run, and totalization counterexamples
    as part of the design explanation.
26. Derive only the transposition facts justified by that independence. Use both yield-stability
    directions to construct the two off-axis raw iterator executions, then use forward-map closure
    commutation to identify their exact raw endpoint. Under `Independent`, package each global
    step's separately supplied `TotalStepMap` with acted-owner `StepMapMember` provenance before
    proving the exact pre-edit map square. Use `ObservationalIndependent` for the `EffectEquiv`
    square, retaining its separately supplied `ProgramRespects`. Because L-Iter/L-Finish store syntax, define a
    separate `LifecycleYieldAgrees` with exact `UndoCode` equality and prove it implies semantic
    `YieldAgrees`. Kernel-check the converse failure with distinct external codes interpreted as the
    same state function. Prove distinct-name `setPhase` updates commute, but keep the future
    foreign-phase contract below `Transition`/`Step`: fixed oracle, reachable code, source lookup,
    exact lifecycle yield, and raw-successor/edit commutation. Construct no inhabitant here and do not
    infer guard/target stability, edited lifecycle endpoints, either Lemma 71 clause, T61/Cor62, or
    confluence.
27. Factor foreign-phase compatibility without hiding which authority is new. First derive owner
    presence from each successful `IterationStep`. Make foreign `setPhase` readable to one program,
    refine `run_read_confined`'s related ordinary successor to an exact frame equation, and require
    the fixed registration oracle to accept the moved request with the same child. Keep all three
    laws program-scoped and reachable-code-limited where appropriate. In the registration proof,
    identify requests from component/continuation equality, derive child/foreign-name inequality
    from freshness, and prove insertion/phase commutation structurally; do not assume the successor
    frame. Derive `ForeignPhaseCompatibility`, package one moved execution, and combine two such
    certificates with the raw independent diamond and `setPhase_commute`. Retain the actual post-raw
    owner lookups in the framed result. Kernel-check three independent gaps: Definition 60
    independence does not imply compatibility, readable ordinary results do not imply exact
    successor framing, and an identical readable registration request does not stabilize a
    state-dependent oracle. Keep caller-supplied phase payloads distinct from lifecycle rule output,
    and do not mention `Transition`, `Step`, guards, targets, or Lemma 71 in the theorem surface.
28. Add the exact representation premise still missing between a common-source landing and its
    off-axis raw execution. Define `LifecycleYieldStable` and package only the two cross-forward
    instances in `ForwardLifecycleIndependent`, retaining semantic `Independent` for endpoint
    commutation. Build `LifecycleForwardDiamond` by identifying the exact-yield witnesses with the
    raw diamond's off-axis steps through their `executeOne` equations. Kernel-check a distinct raw
    forward model where semantic yields agree but syntactic undo codes differ. Next, tie each bare
    landing to the fixed program oracle with `LandingProgramWitness`. Package complete common-source
    Iter/Finish activations whose phases are constructed from the actual landing, not supplied.
    Derive exact foreign source-fiber and positive-target preservation under source WF. Reframe each
    off-axis moved step from the common landing only as a fiber/control template; compose exact
    common-to-off-axis and off-axis-to-phase-framed yields. Finally construct all four Iter/Finish
    orders with one exact final state. Exercise a positive Iter/Finish pair, and kernel-check that a
    provider Finish may enable a previously unavailable consumer Begin and that landings produced by
    different oracles cannot be reassigned across programs. Keep Begin pairs, existing trace-step
    identity, episode provenance, trace rewriting, and full Lemma 71 outside the theorem.
29. Complete the bounded activation-only exchange without inflating Begin branches. Package
    `ProgramActivation` from a root-aligned `BeginGuard` or the existing program-aligned landing;
    derive its exact endpoint, actual transition, foreign lookup frame, and non-active source fact.
    Use source and endpoint well-formedness to preserve only already-valid positive targets, never
    full target equality. Prove fixed-program endpoint/rule determinism from source lookup,
    reloading injectivity, the fixed oracle's exact execution, post-raw lookup, and continuation
    shape. Make `ActivationSwapLaws` branch-indexed: no iterator law for Begin/Begin, only the
    landing program's `ForeignPhaseCompatibility` for a mixed pair, and
    `ForwardLifecycleIndependent` plus both phase certificates for a landing pair. Construct all
    nine common-source diamonds, then accept an actual normal-order second activation and identify
    its endpoint by determinism to derive the swapped actual transition. Kernel-check wrong-root
    attribution and same-owner phase noncommutation; reuse the existing applicability, oracle, and
    exact-yield countermodels. Call this a partial fixed-oracle exact-representative Lemma 71(1)
    analogue, not clause (2), arbitrary trace rewriting, episode assignment, or confluence.
30. Audit activation/orchestration exchange counterexample-first. Kernel-check that a registering
    activation can create a distinct parent needed by a later O-Insert and that opposite legal
    insertions assign different exact birth ranks; show the current rule relation still observes
    the latter. Classify the exact registered child. For O-Insert require no registration; for
    Retire/Remove require only child/actor inequality. Reify the actual normal orchestration as a
    total replay and retain kind, actor, and exact replay template. For a landing require one
    occurrence-specific existential frame with moved fixed-oracle execution, exact lifecycle yield,
    and raw replay square; Begin requires only `True`. Derive the legal early orchestration guards,
    positive activation target, moved landing, and distinct edit/phase commutation, then prove the
    supplied normal final endpoint. Add birth-clock and retirement-sensitive-oracle frame gaps and
    structural/ordinary/registering positive examples. Call this a corrected bounded Lemma 71(2)
    analogue; exclude registering activation/O-Insert, birth erasure, arbitrary trace rewriting,
    Lemma 72, and confluence.
31. Lift the corrected local swaps into exact stored-trace rewrites. Package an indexed
    `StepPair`, an `ExactAdjacentSwap` with reversed rule/actor projections, and an
    `AdjacentOccurrence` whose dependent before/window/after decomposition cannot accept a
    mismatched endpoint. Give actual activation steps supplied `ProgramOccurrence` evidence and
    mirror the trace with an occurrence-indexed `TraceProgramAssignment`; never infer a program or
    oracle from a bare transition. Prove concrete moved-rule coherence from the existing
    transposition constructors, then make both actual-pair adapters return assignments for their
    moved steps. Rebuild the complete rewritten ledger from the retained context assignments and
    prove rule/actor permutations, original selected-record membership, rewritten alignment,
    length, and final well-formedness. Exercise a nonempty prefix. Keep registering
    activation/O-Insert, birth-erased suffix simulation, arbitrary normalization, deletion, Lemma
    72, and confluence outside this exact-state layer.
32. Build deletion as intrinsic replay, never record-list filtering. Define one retained-step
    square carrying an actual replay and assignment transport, then let a relation-indexed
    `DeletionReplay` consume the source trace with positional keep/drop constructors and construct
    the shadow trace. Derive final relation, rule/actor sublists, alignment, length bounds,
    decisions, and output assignment. Counterexample-first, prove that removing an inserted
    parent makes a retained insertion unreplayable and can break well-formedness; retain both clock
    and surviving-birth obstructions plus semantic bare-name redraw. For the positive exact slice,
    compose corrected vestigial squares over a finite already-vestigial family and safe foreign
    orchestration trace, retaining positional edit-template and assignment evidence. Exercise an
    actual `[drop, keep]` filter. Stop before lifecycle episode projection, lifecycle/oracle/recovery
    suffix simulation, a birth-erased outside relation, Lemma 72, normalization, or confluence.
33. Define the paper-visible relation before relation-aware rewriting. Project fiber control to
    component, parent, retirement, and exact dependent phase, deliberately erasing only the
    reference `birth` and `nextBirth` fields relative to current rule observation. Prove full,
    outside-deleted, and combined effect/outside Setoids plus strict-relation bridges and domain
    consequences. Between two independently well-formed full-domain related states, reconstruct
    real O-Insert/O-Retire/O-Remove peers in both directions and derive `RetainedStep` assignment
    transports. Show opposite insertion schedules are related while exact/current-rule equality
    fail. From a well-formed source carrying `VestigialNames`, prove finite erasure satisfies the
    deletion relation and replay safe foreign orchestration traces directionally. Retain
    parent/redraw/provision/parent-removal asymmetry and
    a clock-sensitive unmatched DivertAbort countermodel. Stop before outside/lifecycle
    bisimulation, name quotienting, relation-aware activation swaps, Lemma 72, or normalization.
34. Audit progress before attempting termination. Separate a configured program whose fixed oracle
    rejects from the raw lifecycle relation that can choose another oracle. Kernel-check a stronger
    Boolean freshness-exhaustion state with no possible registration admission or lifecycle rule.
    Define provider-to-consumer `PrecedesAt` and an explicit finite increasing rank. Derive
    program-wide landing-or-raise totality from an explicit oracle-admission law, but make the
    headline theorem consume only exact current reloading witnesses and state-local recovery
    readiness. Name committed-provider provision soundness so a relied provider yields a strict
    precedence edge. Prove state-local no-deadlock by selecting a maximal-rank unloading fiber and
    following any installed consumer to either an applicable rule or a rank contradiction. Stop
    before the `(K + 4)` bound, target-turn finiteness, maximal-execution termination, trace-wide
    program assignment, fairness, support, deletion, or confluence.
35. Audit support order before defining the support set. Build a legal `FromEmpty` trace whose
    provider precedence is well founded and parent relation birth-acyclic but whose union has a
    two-cycle and two Definition 67 solutions. Define `SupportOrder` from combined
    well-foundedness directly. Use an edge-indexed `WellFounded.fix`, prove its unfolding equation,
    and derive solution uniqueness. Add state-local active provision totality, failure exclusion,
    and active-parent closure; prove active names solve the support equations and hence equal the
    unique recursive support at quiescence. Kernel-check active mixed-order nonuniqueness and a
    separate retired-parent/active-child gap under a valid support order. Stop before deriving
    combined order or parent closure from `FromEmpty`, component-wide Definition 69, deletion, or
    confluence.

This reaches a bounded finite Definition 53 relation and an oracle-specific finite partial/Kleisli
Definition 60 analogue. Do not claim Theorem 59 while general unload recovery confinement is still
supplied, or Theorem 61/Corollary 62 while canonical relation identification, per-step
`TotalStepMap`, owner inverse stability, and trace reordering remain supplied. The Definition 60
bridge discharges only `PerStepCommutes`; it does not manufacture those remaining premises. The two
raw/map transposition theorems do not add the foreign-phase, exact-code, guard, or edited-endpoint
facts required for lifecycle Lemma 71. The compatibility record only names that future authority;
`GlobalTransposition` constructs no inhabitant. `GlobalForeignPhase` derives one only from explicit
readability, exact ordinary-frame, and same-child oracle laws, then proves a framed raw—not
lifecycle-rule—diamond. `GlobalLandingTransposition` reaches actual Iter/Finish transitions only
under exact cross-forward syntax, fixed-program provenance, common-source applicability, and WF;
`GlobalActivationTransposition` adds root-aligned Begin and all nine activation-only pairs, then
uses fixed-program endpoint determinism to reconcile a supplied actual second activation.
`GlobalActivationOrchestrationTransposition` then refutes the literal clause-(2) premise and proves
the corrected occurrence-framed exchange while excluding registering activation/O-Insert.
`GlobalTraceRewrite` now identifies actual fixed-program steps in an intrinsic adjacent window,
splices those exact corrected swaps through retained trace context, and reconstructs the moved
assignment ledger. It still neither derives laws for arbitrary occurrences nor transports an exact
suffix from a merely birth-erased endpoint; registering activation/O-Insert, arbitrary
normal-form search, episode programs, and the paper's literal total/quotient Lemma 71 remain
outside the result. `GlobalDeletion` now constructs positional relation-indexed keep/drop replay and exact
multi-vestigial safe orchestration suffixes. Its parent, redraw, clock, and surviving-birth
countermodels expose why general lifecycle episode deletion still needs temporal recovery,
lifecycle/oracle suffix simulation, lifetime-aware no-redraw, corrected support authority, and a
birth-erased outside relation. It proves neither Lemma 72 nor automatic normalization/confluence.
`GlobalPaperTraceSimulation` and `GlobalPaperTraceDeletion` retain the assigned trace/replay
certificates for the birth-erased relation. `GlobalPaperTraceNormalization` now composes a finite
connected list of those supplied adjacent-rewrite certificates and proves endpoint relatedness
plus rule/actor permutations. It is certificate composition only: no rewrite strategy,
canonical form, termination, Lemma 72, or confluence is derived.
`GlobalPaperRelation` now supplies that finite relation: it erases only allocator clock/birth from
current rule control, relates the opposite insertion endpoints, and proves bidirectional
well-formed orchestration replay with assignment transport. From a well-formed source carrying
`VestigialNames`, finite removal and safe foreign orchestration traces satisfy the combined
effect/outside relation directionally. Existing
outside-deletion asymmetry and a clock-sensitive unmatched L-DivertAbort prevent any lifecycle or
reverse-suffix upgrade; relation-aware activation swapping, Lemma 72, and normalization remain
absent as automatic/canonical results.
`GlobalProgress` separately refutes unconditional progress
under configured-oracle rejection and exhausted names, then proves only conditional state-local
no-deadlock from explicit rank/readiness/soundness authorities. It does not prove quantitative or
maximal termination. `GlobalSupport` refutes the printed combined-order inference, then proves
unique support and support-equals-active only from explicit combined well-foundedness, state-local
totality/failure exclusion, and active-parent closure. It does not derive trace provenance or
deletion. The two candidate relations do not themselves prove Lemmas 55–57. The finite spatial
facts do not supply maximal episodes,
same-owner table confinement, or full T63/T64. The corrected vestigial orchestration squares do
not prove lifecycle/iterator invisibility or the paper's literal unqualified clauses.
Unconditional/quantitative progress and confluence remain unproved. The orchestration invariance
certificate is not full Lemma 55.
The lifecycle observation substrate still executes no rule.
The conditional lifecycle certificate does not derive its external contracts from `Dynamics`.
The structural name action does not prove full lifecycle Lemma 56.
The lifecycle name theorem remains conditional on primitive semantic action laws.

## 20. Exact verification and review commands

Run the functional gates:

```bash
lake build
lake lean Cordis/NegativeTests.lean
lake exe cordis_tests
lake exe cordis_demo
lake lean Cordis/AxiomAudit.lean
```

Run source and diff hygiene:

```bash
git diff HEAD --check
uv run scripts/check_lean_hygiene.py --self-test .
```

Run documentation checks when the tools are installed:

```bash
markdownlint README.md SPEC.md docs/*.md
prettier --check README.md SPEC.md docs/*.md
lychee --no-progress README.md SPEC.md docs/*.md
```

For a focused review of the current guide:

```bash
markdownlint docs/IMPLEMENTATION_GUIDE.md
prettier --check docs/IMPLEMENTATION_GUIDE.md
lychee --no-progress docs/IMPLEMENTATION_GUIDE.md
```

Finally, inspect repository state before committing or publishing:

```bash
git status --short --branch
if test -d .jj; then
  jj status
fi
```

The expected implementation result is not merely “the demo prints `5`.” It is
that every data relationship claimed by the finite kernel is either enforced
by a constructor index, proved by a theorem, checked at a named dynamic
boundary, or explicitly recorded as trusted or absent.

[paper-tree]: https://github.com/cordiverse/paper/tree/948a07b369c62adb3b12e102458be5c18dfb69b9
[paper-pdf]: https://raw.githubusercontent.com/cordiverse/paper/948a07b369c62adb3b12e102458be5c18dfb69b9/paper.pdf
[cordis-tree]: https://github.com/cordiverse/cordis/tree/8cc9e33fab69e2d0476d126baaf2acb24e6a6ab4
[harness-tree]: https://github.com/deepseek-ai/deepseek-harness/tree/47f943859bef60e4160492346772ded9b24f765a
[harness-architecture]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/docs/architecture.md
[harness-vendor]: https://github.com/deepseek-ai/deepseek-harness/blob/47f943859bef60e4160492346772ded9b24f765a/vendor/README.md#L9-L49
