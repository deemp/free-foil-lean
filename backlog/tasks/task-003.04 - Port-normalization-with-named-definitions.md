---
id: TASK-003.04
title: Port normalization with named definitions
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
dependencies:
  - TASK-003.01
  - TASK-003.03
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Definitions.hs
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/test/Test/Glue.hs
documentation:
  - free-foil-repos/free-foil-NBE/src/FreeFoil/NbE/Definitions.hs
  - free-foil-repos/free-foil-NBE/test/Test/Definitions.hs
  - free-foil-repos/free-foil-NBE/test/Test/Glue.hs
parent_task_id: TASK-003
type: feature
ordinal: 24000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Clients with global definitions need to compute through a definition while retaining its name in printed results when requested. Generic evaluation provides the client context and conversion provides the value comparison that must account for definitions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Lean clients can extend a scope with nonrecursive definitions whose bodies can refer to earlier definitions. Free names without definitions remain neutral.
- [x] #2 Language eliminations reduce through definitions when their bodies expose a matching constructor. Callers can read normal forms back with definition names folded or bodies unfolded.
- [x] #3 Conversion compares folded values first and can fall back to definitions' bodies. Tests cover a matching folded head, fallback to an unfolded body, and unequal definitions.
- [x] #4 Tests and a documented example cover chained definitions and their use beneath a binder.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Use the pinned upstream definitions and glue tests to add a scope-indexed definition context and suspended definition bodies to the generic NbE evaluator. Integrate folded and unfolded readback, expose definitions to eliminators, and try folded conversion before unfolding. Exercise neutral names, chains, binder freshness, eliminations, and conversion in the Lean test driver, and document a runnable example.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Verified the default build and regression suite with Lean 4.35.0. Executed the README example and confirmed its folded and unfolded terms.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added scope-indexed, nonrecursive definitions with suspended bodies and a reusable elimination helper. Full and weak-head readback support folded and unfolded definitions. Conversion can match folded heads without demanding divergent definitions and falls back to their bodies on a mismatch. Tests cover chained definitions, free neutrals, binder freshness, projections, recursion on naturals, conditionals, and conversion. The default build, test suite, and README example passed.
<!-- SECTION:FINAL_SUMMARY:END -->
