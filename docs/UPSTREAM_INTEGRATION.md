# Pinned Harness serializer integration

This milestone connects the Lean request API to the actual DeepSeek Harness
serializer at `99f6f02fecdb7dff40c3fbc9470f5907c29f74ca`, in
`packages/llm/llm-deepseek/src/serialize.ts`.

The generic `DeepSeekApi.ChatRequest` encoder keeps its existing contract. A
separate compatibility adapter accepts a typed request and produces the
Harness wire conventions: streaming with usage reporting, empty assistant text
instead of null, omitted empty tool-call lists, reasoning passback only on
tool-call messages, and `(no output)` for empty tool results. Its transport body
will carry an equality certificate, with source tool preservation checked by Lean.

The integration corpus is a shared semantic request vocabulary. The TypeScript
driver translates it into Harness `GenerateOptions` and calls the upstream
serializer. The Lean driver constructs `ChatRequest` and calls the compatibility
adapter. The runner compares complete JSON values; it does not erase differing
fields, reorder arrays, or normalize away incompatibilities. Each case has a
stable identifier, and failures retain both results. Negative controls must show
that deliberate output drift fails the comparison.

The common fragment includes text, reasoning, tool calls and results, optional
system prompts, raw JSON tool parameters, streaming, high/max effort, thinking
enabled/disabled, and natural-number token budgets. Provider-specific defaults,
low effort, temperature, stop sequences, response formats, tool choice, strict
tool schemas, images, extension blocks, and malformed Harness inputs are outside
this first comparison. Unsupported Lean-only request fields must fail explicitly
at the compatibility boundary rather than silently disappear.

The upstream checkout must match the pin and be clean. CI fetches that exact
revision and run the same command used locally. No model endpoint or credentials
are required. Passing a finite differential corpus is executable compatibility
evidence, not a theorem of TypeScript semantics, provider behavior, session replay,
or deployed equivalence. The TypeScript input translation and Lean input decoder
are reviewed test infrastructure, outside the kernel proof boundary.

## Run the loop

With the repository's Lean toolchain and Bun **1.3.14** installed:

```sh
python3 scripts/check_upstream_integration.py
```

The first run fetches the exact upstream pin into `.lake/upstream/deepseek-harness`.
Subsequent runs reuse it after checking the revision and worktree. To use an
existing clean checkout at that revision:

```sh
python3 scripts/check_upstream_integration.py --upstream /absolute/path/to/deepseek-harness
```

The command builds `cordis_upstream_request`, generates the shared corpus, runs
both implementations, and compares every JSON field. Object member order is
irrelevant; array order, missing versus null fields, strings, and boolean versus
numeric types remain observable. Its six negative controls delete usage reporting,
replace a Boolean with a number, reverse messages, corrupt a tool schema, omit a
case, and duplicate a case ID. Five Lean admission tests reject response format,
tool choice, contradictory thinking/effort, and both values of an explicit strict
tool flag.

The 114 matching cases include 64 seeded generated histories with one to four
tool calls, raw nested parameter ASTs, Unicode and escaped strings, empty tool
results, assistant reasoning with and without calls, system prompts, empty tool
lists, and the supported thinking/effort/token-budget combinations. The seed is
914; generated data contain no user history or credentials.

`.lake/integration/` retains `requests.jsonl`, `upstream.jsonl`, `lean.jsonl`, and
`receipt.json`. A receipt is written only after all gates pass and includes the
upstream revision, serializer and corpus hashes, Lean Git revision, dirty-worktree
flag, runtime version, and case counts. Every invocation removes the previous
receipt before preflight so failure cannot leave an old success marker. CI runs
this on pushes and pull requests and uploads the comparison directory.

## Code and proof boundaries

- `Cordis/DeepSeekHarnessCompatibility.lean`: normalizes the shared typed request,
  rejects unsupported settings, retains a streaming base plan, and certifies the
  exact replacement body. Theorems preserve source tools, URL, and headers.
- `Integration/HarnessRequestDriver.lean`: decodes the shared corpus into the
  existing typed request API and emits the certified transport body.
- `Integration/upstream-request.ts`: converts that same corpus to upstream message
  blocks and calls `serializeRequest` directly. Bun resolves the real pinned LLM,
  Cordis, Cosmokit, Schemastery, and timeout sources; no implementations are mocked
  or copied. The driver does not invoke a model or install the monorepo.
- `Integration/upstream.json`: the upstream and Bun pins.
- `scripts/check_upstream_integration.py`: fetch, build, corpus, comparison,
  rejection gates, and receipt generation using only Python's standard library.

For an upstream update, change the pin deliberately, inspect the serializer and
its dependencies, and run this command. A mismatch is a reviewable behavior change;
resolve it in the compatibility adapter or explicitly revise the supported
fragment. Do not weaken the comparison by dropping differing fields. The loop
pins one implementation revision; it does not continuously track upstream HEAD.

The next milestone is to feed actual upstream event-log replay into this request
boundary. This milestone compares serializer behavior on shared semantic inputs;
it does not compare the upstream session reconstructor or asynchronous scheduler.
