---
id: TASK-001.06.04
title: Check independent MLTT modules in parallel
status: Done
assignee:
  - Codex
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 15:21'
labels:
  - mltt
  - cli
dependencies:
  - TASK-001.06.02
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/src/Language/MLTT/Build.hs
documentation:
  - FreeFoil/Examples/MLTT/Module.lean
  - README.md
modified_files:
  - FreeFoil/Examples/MLTT/Module.lean
  - FreeFoil/Tests/MLTT.lean
  - MLTTMain.lean
  - README.md
parent_task_id: TASK-001.06
type: feature
ordinal: 18000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The multi-file builder supplies the dependency graph and stable name reservations. The existing linker allows modules that share completed dependencies to be checked independently and combined.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 A parallel build mode checks independent modules concurrently and waits for imports before checking a dependent module.
- [x] #2 Sequential and parallel builds produce equivalent checked declarations with the same identifiers and deterministic reported results.
- [x] #3 Failed checks identify the failing module and prevent its dependents from being checked against an incomplete environment.
- [x] #4 Regression coverage exercises a shared-dependency diamond and a failing branch. The README documents how to select parallel mode.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Reuse the existing module planners to validate imports and assign stable identifier ranges for single-file and multi-file builds.
2. Schedule checks when their dependencies are ready and keep command output and failure reporting in sequential plan order. Preserve fresh binder names in rendered output by matching each worker's allocation scope to the sequential prefix. Keep reserved slots for unrelated declarations out of the checked bindings published by each worker.
3. Add and document the opt-in parallel CLI mode. Compare sequential and parallel results and identifiers for a shared-dependency diamond, and verify that a failed branch prevents its clients from being checked.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Review verified that a six-module project exercised multiple Lean worker threads. An independent diamond probe matched the pre-change sequential stdout and failing-branch stderr byte for byte.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added `mltt --parallel` for source projects and single-input module builds. Workers check only after their imported modules succeed. The build preserves sequential declaration identifiers, output, and error ordering, including the generated names displayed for binders.

`lake build` and `lake test` passed. The regressions compare checked artifacts and output for a diamond, exercise failure after declarations in one branch, and cover the multi-file, single-file, and stdin CLI paths.
<!-- SECTION:FINAL_SUMMARY:END -->
