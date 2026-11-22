---
id: TASK-001.06.02
title: Build MLTT modules from multiple source files
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 10:36'
labels:
  - mltt
  - cli
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/src/Language/MLTT/Build.hs
documentation:
  - MLTTMain.lean
  - README.md
modified_files:
  - FreeFoil/Examples/MLTT/Program.lean
  - FreeFoil/Examples/MLTT/Module.lean
  - MLTTMain.lean
  - FreeFoil/Tests/MLTT.lean
  - README.md
  - lakefile.toml
parent_task_id: TASK-001.06
type: feature
ordinal: 11000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The MLTT executable accepts one source at a time. Module projects need a single build that resolves imports across files and assigns reproducible declaration identifiers before caching or parallel checking is added.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 The CLI accepts multiple module source paths and resolves imports across those files in dependency order.
- [x] #2 Permuting the input files for the same set of modules preserves module reservations and declaration identifiers.
- [x] #3 Duplicate modules, missing imports, and import cycles are reported with the relevant module and source names when available.
- [x] #4 Existing one-file and stdin invocations retain their behavior.
- [x] #5 CLI regressions cover cross-file imports and reordered input. The README documents the multi-file invocation.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Parse module source files with their original paths, then resolve telescope declarations across the collected project while retaining module provenance.
2. Extract shared project planning and checking from the single-file module runner. Reserve names by module name for project builds and topologically order modules independently of file order. Keep the existing source-order scheduling for legacy single-file and stdin invocations.
3. Return the checked environment with execution results for downstream build modes. Report duplicate modules, missing imports, and a concrete cycle using source paths when available.
4. Accept several source paths in the CLI. Verify both path orders with the executable, check reservation and declaration ID equality through the Lean API, and document the invocation.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Reviewed project planning and ran the isolated default test driver. It exercised both file orders on the CLI, compared reserved ranges and declaration IDs through the Lean API, and checked standalone files, stdin, duplicates, missing imports and cycles.

Project parsing gathers units from all files before resolving named telescopes and preserves each module's source path. Planning reserves identifier ranges in module-name order and then schedules modules dependency-first. The single-file runner still reserves ranges and breaks scheduling ties in source order.

The default `lake test` driver builds and invokes the MLTT executable. Regressions compare output for reversed path lists, verify the same result from a combined file, preserve standalone and both stdin invocations, and exercise duplicate-module, missing-import, and cycle diagnostics with paths. Lean checks compare reservations and declarations across the input orders and resolve a cross-file telescope. `lake test` and `lake build` passed against an isolated snapshot containing this task’s changes.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Build a project from multiple MLTT paths with telescope declarations shared across files. Plan reservations by module name and check imports before their clients. Duplicate modules, missing imports and cycles identify the relevant modules and paths.

The default test driver verifies stable reservations and identifiers, reordered CLI inputs, and the legacy file and stdin forms. The README documents the project invocation.
<!-- SECTION:FINAL_SUMMARY:END -->
