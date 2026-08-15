# CORDIS Lean

CORDIS Lean is a proof-carrying reference kernel for CORDIS-style agent
harnesses. Its central idea is that an API should be a dependent type
signature: a request determines its response type, a component's dependency
proof determines which capabilities it can call, and a transition determines
its legal successor state.

The project is grounded in the
[CORDIS paper](https://github.com/cordiverse/paper), the
[CORDIS implementation](https://github.com/cordiverse/cordis), and the
[DeepSeek Harness](https://github.com/deepseek-ai/deepseek-harness). The exact
source snapshots, theorem obligations, and claim boundary are recorded in
[SPEC.md](SPEC.md).

## Planned commands

```bash
lake build
lake exe cordis_tests
lake exe cordis_demo
```

The first implementation milestone is in progress on Linear issue ALOK-824.
No live model credentials are required by the deterministic reference runner,
and no claim about arbitrary external side effects is included in the pure
recovery theorems.
