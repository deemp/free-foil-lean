---
id: TASK-001.06.01
title: Support named telescopes in MLTT
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 10:31'
labels:
  - mltt
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/README.md#named-telescopes-and-include
documentation:
  - FreeFoil/Telescope.lean
  - README.md
modified_files:
  - FreeFoil/Examples/MLTT/Program.lean
  - FreeFoil/Tests/MLTT.lean
  - README.md
parent_task_id: TASK-001.06
type: feature
ordinal: 10000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Dependent parameter blocks are currently repeated in each module header. A named telescope lets several modules share a declaration of those parameters while elaborating the binders in each module’s own scope.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 An MLTT source can declare a named telescope and include it in module headers and in other telescope declarations.
- [x] #2 Included fields appear in declaration order before local fields, and a local field can refer to an earlier included field.
- [x] #3 Each including module gets its own binders, and parameter discharge agrees with the equivalent explicitly written header.
- [x] #4 Missing telescope names, include cycles, and repeated parameter names produce diagnostics.
- [x] #5 Regression coverage exercises nested includes and two includers. The README shows how to declare and include a telescope.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Parse `telescope` declarations and ordered `include` clauses on module and telescope headers, preserving the existing standalone input form and checked `Module` interface.
2. Expand telescope declarations in dependency order before module checking. Resolve forward and nested references, keep included fields before local fields, and report missing names, cycles, duplicate declarations, and repeated parameter labels.
3. Pass expanded raw headers through the existing per-module parameter elaboration and discharge path. Add MLTT regressions for two includers, nested dependent fields, equality with an explicit header, and invalid includes. Document the source form and run Lake checks.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Include resolution memoizes only expanded raw parameter blocks, so module checking still elaborates field types against each module's imports and allocates binders locally. Forward references and multiple ordered includes are accepted. Telescope-only source files validate the telescope declarations without emitting modules.

The focused MLTT suite passed with Lean 4.35.0. Regressions exercise nested and ordered includes, the two includers, per-module import resolution, agreement with an explicit header, and invalid includes. Running the README example through the CLI also succeeded.

Reviewed the expanded parameter headers, per-module checking and diagnostics through the MLTT regression suite. The upstream telescopes program checked all three modules and produced four tt computations.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Named telescope declarations expand ordered includes into raw module headers. Modules still elaborate their own binders, so dependent local fields and parameter discharge follow the same rules as explicit headers.

The README shows nested inclusion and independent users. Regression coverage checks forward references, import scopes, explicit-header agreement, and errors for missing, cyclic and duplicate entries.
<!-- SECTION:FINAL_SUMMARY:END -->
