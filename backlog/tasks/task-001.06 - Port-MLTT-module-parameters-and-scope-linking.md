---
id: TASK-001.06
title: Port MLTT module parameters and scope linking
status: Done
assignee:
  - codex
created_date: '2026-11-21T21:07:51Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies:
  - TASK-001.05
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Foil/Blocks.hs
modified_files:
  - FreeFoil/Examples/MLTT.lean
  - FreeFoil/Examples/MLTT/Module.lean
  - FreeFoil/Examples/MLTT/Program.lean
  - FreeFoil/Tests/MLTT.lean
  - MLTTMain.lean
  - README.md
  - test/fixtures/mltt/parameters.mltt
  - backlog/tasks/task-001.06 - Port-MLTT-module-parameters-and-scope-linking.md
parent_task_id: TASK-001
type: feature
ordinal: 7000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Use telescopes for parameters and reserved name ranges for independently checked modules.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Independently checked parameterized modules with a shared dependency link without renaming declarations.
- [x] #2 Invalid and conflicting allocations are rejected, and `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Extend the MLTT parser and executable to handle multiple named modules with dependent parameters and imports while keeping the standalone program entry point usable. Support explicit `over` assertions on declarations.
2. Check parameter types in an ordered, scope-indexed telescope. Thin the telescope against both the checked declaration type and value, then discharge the retained parameters as Π/λ binders. Reapply exactly these parameters when resolving references to earlier declarations within the same module.
3. Allocate declaration identifiers in checked half-open ranges. Retain scope-indexed environments with module metadata and merge independently checked scopes by inclusion, verifying that shared modules agree and that distinct ranges do not overlap. Keep terms and declarations accessible for artifact revalidation in the next milestone.
4. Test the upstream parameter example, a shared-dependency diamond, stable identifiers, and rejected name allocations and imports. Run lake build and lake test using the pinned Lean 4.35.0 development shell.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Parameter types are checked once in their import context and the telescope is lifted as declarations allocate new global identifiers. Definition discharge uses the combined support of its type and value. Imports expose bare and module-qualified names and diagnose ambiguous aliases when used.

The linked environment keeps numeric declaration names, checks α-equivalent terms and matching metadata for shared modules, and checks the full reservation of each distinct module even when it has no declarations.

Lean 4.35.0: the default build and test driver passed. The unchanged upstream parameter fixture produced five `tt` results from the CLI, and the core fixture still runs via stdin. The tests cover both link orders, stable IDs, missing imports, dependency cycles, ambiguous names, and invalid, exhausted, and overlapping reservations.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added scope-indexed module parameter checking and discharge over the transitive dependencies of the declaration's type and value. Added imports and dependency-ordered execution for files containing several modules. The linking API widens scopes while preserving declaration identifiers and rejects overlapping reservations and conflicting copies of a shared module.

Verified both orders of a shared-dependency diamond, stable declaration identifiers, a client computation through both branches, and rejection of invalid, exhausted, and overlapping ranges. The pinned Lean 4.35.0 build and test suite passed. The upstream core and parameters fixtures produced four and five unit normal forms respectively through both CLI input paths.
<!-- SECTION:FINAL_SUMMARY:END -->
