---
id: TASK-003
title: Port free-foil-NBE to Lean
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:33'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
  - port
dependencies: []
references:
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249
documentation:
  - free-foil-repos/free-foil-NBE/README.md
  - free-foil-repos/free-foil-NBE/CHANGELOG.md
  - README.md
type: feature
ordinal: 20000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Lean Free Foil provides scope-safe syntax and substitution. The pinned free-foil-NBE submodule adds a reusable normalizer so each object language can supply its own computation rules and share evaluation, readback, and conversion. Use the submodule revision `75e7855a6dc03723ff0198f55774eda50e627249` as the source of behavior and fixtures.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Lean clients can define an object language and run generic evaluation, readback, full normalization, weak-head normalization, and conversion over scope-checked Free Foil syntax.
- [x] #2 The port covers definition unfolding, fragment composition, transparent annotations, and type-directed refinement in the dependent demo.
- [x] #3 Representative examples from the pinned upstream demos agree with the Lean results up to α-equivalence. The existing λΠ and MLTT entry points retain their documented behavior.
- [x] #4 The README shows how to use the Lean NbE API and run its demos and benchmarks. The default `lake build` and `lake test` pass on the pinned Lean toolchain.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Complete the eight subtasks in dependency order, beginning with evaluation and readback, then demos, conversion, definitions, fragments, annotations, the dependent demo, and benchmarks. Review each subtask independently, verify it against the pinned upstream examples and the Lean test suite, and commit only its changes. Close the parent after verifying the entire port and its documentation.

With the eight subtasks completed, verify their combined behavior on the pinned Lean toolchain. Run the default build and test suite, check the README’s NbE examples and benchmark, and smoke-test the documented λΠ and MLTT entry points. Record the evidence for the four parent criteria before closing the task.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Confirmed that all eight subtasks are Done and the upstream checkout matches `75e7855a6dc03723ff0198f55774eda50e627249`.

Ran `lake build` and `lake test` in the Nix shell with Lean 4.35.0 and GCC 16.2.0. The regression driver exercised evaluation and separate readback, full and weak-head normalization, semantic conversion, definition unfolding, fragment composition, transparent annotations, and type-directed refinement. The untyped, mixed, and dependent suites compared normal forms up to α-equivalence with the expected results.

Executed all six Lean examples in the README’s NbE section and all six `nbe` CLI demos. The legacy λΠ compute printed `𝕌`. MLTT produced four `tt` results for the core fixture through both file input and stdin, and five for the module parameters fixture.

Ran `lake exe nbeBench --samples 5` with and without the local lambda-n-ways fixtures. All seven built-in workloads and 201 corpus terms passed the benchmark’s α-equivalence checks.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
The Lean port provides generic evaluation, readback, full and weak-head normalization, and semantic conversion for scope-checked syntax. It includes named definitions, composable reduction rules, transparent annotations, and type-directed refinement in the dependent-types demo.

The parent acceptance review confirmed agreement with representative pinned upstream examples up to α-equivalence and checked the documented λΠ and MLTT entry points. The default build, regression suite, README examples, and native benchmark passed on Lean 4.35.0.
<!-- SECTION:FINAL_SUMMARY:END -->
