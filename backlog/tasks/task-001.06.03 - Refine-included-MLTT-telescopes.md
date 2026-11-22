---
id: TASK-001.06.03
title: Refine included MLTT telescopes
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 15:05'
labels:
  - mltt
dependencies:
  - TASK-001.06.01
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/README.md#named-telescopes-and-include
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/examples/theories.mltt
documentation:
  - FreeFoil/Telescope.lean
  - README.md
modified_files:
  - FreeFoil/Named.lean
  - FreeFoil/Examples/MLTT/Program.lean
  - FreeFoil/Examples/MLTT/Module.lean
  - FreeFoil/Tests/MLTT.lean
  - README.md
parent_task_id: TASK-001.06
type: feature
ordinal: 16000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Named telescope inclusion supplies a reusable dependent parameter block. Refinement lets a module specialize some of those fields to concrete values while retaining the remaining fields as parameters.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 A module can fix named fields in an `include` clause, and each supplied value is checked at its field’s specialized type.
- [x] #2 The remaining parameter types incorporate the fixed values, and exported definitions are discharged only over the unfixed parameters they use and their dependencies.
- [x] #3 Unknown or repeated assignments, ill-typed values, and assignments that depend on an unfixed field produce diagnostics.
- [x] #4 Regression coverage includes a partially refined telescope and a fully instantiated one. The README shows both forms.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Parse `/ {field := value, ...}` on telescope includes. Validate assignment targets against the included telescope, reject duplicates and already-fixed fields, and retain the assignments with their original field types in the expanded header.
2. Resolve provided values in the module’s import scope with earlier fixed fields available as scoped terms. Check at the specialized field type and reject dependencies on unfixed parameters. Elaborate local and retained parameter types in declaration order and expand fixed field references without capturing binders.
3. Discharge only the remaining bound fields using the existing telescope thinning path. Keep checked module and artifact representations unchanged. Verify partial and full refinements, dependent field types, import resolution, binder shadowing, and failures through existing tests. Document both forms.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Expanded headers store each assignment with its original field type. Elaboration walks fields in declaration order, checks fixed values with module imports and earlier fixed fields, and inserts ascriptions so checked lambdas remain inferable when used as abbreviations. Earlier unfixed fields continue to shadow imports in dependent types and cannot be referenced by refinement values.

Only unfixed fields enter the telescope used for parameter discharge. The checked module and artifact interfaces remain unchanged. Raw Lean `Parameter` construction has a defaulted `fixedValue` field and positional construction now takes a third argument. The README documents this along with partial and full refinement.

`lake test` and `lake build` passed with Lean 4.35.0 in an isolated snapshot. The CLI also accepted the README example and the local upstream `theories.mltt` example. Regressions cover nested refinement, assignment order, lambda inference, shadowing, discharged parameter sets, and diagnostics for unknown, duplicate, already fixed, ill-typed, and unfixed-dependent assignments.

Independently ran the isolated regression driver and the upstream theories.mltt fixture. Its partial and full refinements checked, including specialized operations, proofs and applications. The deriving changes also pass the isolated default build and regression driver.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Let an include fix telescope fields at checked values. The checker uses each fixed field as a scoped abbreviation and discharges only the eligible remaining parameters. Diagnostics identify unknown or duplicate targets, bad types, and dependencies on unfixed fields.

The README shows partial and full refinement and describes the positional Parameter constructor change. Suite and upstream theory checks passed under Lean 4.35.0.
<!-- SECTION:FINAL_SUMMARY:END -->
