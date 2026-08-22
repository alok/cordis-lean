# Global progress assignment bridge

Status: implemented by `Cordis.GlobalProgressAssignment`.

## Purpose

`GlobalProgressRun` proves a finite, proof-carrying lifecycle execution from a
supplied `ProgressAuthority` and `StepPotential`. Its trace is exact, but the
runner alone does not say which fixed iterator/oracle program produced each
lifecycle transition. This module adds the smallest explicit provenance seam:
the caller supplies that evidence for lifecycle transitions, and the module
reconstructs a dependent `TraceProgramAssignment` for the complete trace.

## Implemented API

`AssignedProgressAuthority` extends `ProgressAuthority` with
`stepAssignment`, a `StepProgramAssignment` for every lifecycle transition.
`assignTrace` recursively consumes the intrinsic `GlobalCalculus.Trace`:

- orchestration steps use `StepProgramAssignment.ofOrchestration`;
- lifecycle steps use the authority's supplied assignment;
- the result is indexed by the exact source trace, so no endpoint cast or
  erased list of tags can substitute for the dependent evidence.

`AssignedProgressRunResult` pairs the existing `ProgressRunResult` with that
assignment. `runFuel` and `certifiedRun` preserve the runner's endpoint
well-formedness, trace-length, stop, and initial-potential quiescence proofs.
The `Example` namespace includes a concrete Begin assignment and executable
rule projection.

## Deliberate boundary

The assignment is an authority, not an inference. This module does not derive
fixed programs, roots, registration oracles, continuation reachability, or
program/oracle coherence from a raw `Transition`, `Dynamics`, or `WellFormed`
state. It therefore does not prove the paper's full Definition 60/66
provenance, fairness, maximal-execution, lifecycle bisimulation, deletion,
normalization, or confluence results. Those remain conditional interfaces in
the trace-simulation modules.

## Verification and integration

The module is imported by `Cordis.lean`, `Cordis.TestSuite`, and
`Cordis.AxiomAudit`. The direct checks are:

```text
lake env lean Cordis/GlobalProgressAssignment.lean
lake --wfail build Cordis.GlobalProgressAssignment
lake exe cordis_tests
```

The full repository build and axiom audit remain the release gates.
