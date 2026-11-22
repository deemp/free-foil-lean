---
id: TASK-003
title: Port free-foil-NBE to Lean
status: In Progress
assignee:
  - Codex
created_date: '2026-11-22 15:33'
updated_date: '2026-11-22 15:45'
labels:
  - nbe
  - port
dependencies: []
references:
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249
documentation:
  - free-foil-NBE/README.md
  - free-foil-NBE/CHANGELOG.md
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
- [ ] #1 Lean clients can define an object language and run generic evaluation, readback, full normalization, weak-head normalization, and conversion over scope-checked Free Foil syntax.
- [ ] #2 The port covers definition unfolding, fragment composition, transparent annotations, and type-directed refinement in the dependent demo.
- [ ] #3 Representative examples from the pinned upstream demos agree with the Lean results up to α-equivalence. The existing λΠ and MLTT entry points retain their documented behavior.
- [ ] #4 The README shows how to use the Lean NbE API and run its demos and benchmarks. The default `lake build` and `lake test` pass on the pinned Lean toolchain.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Complete the eight subtasks in dependency order, beginning with evaluation and readback, then demos, conversion, definitions, fragments, annotations, the dependent demo, and benchmarks. Review each subtask independently, verify it against the pinned upstream examples and the Lean test suite, and commit only its changes. Close the parent after verifying the entire port and its documentation.
<!-- SECTION:PLAN:END -->
