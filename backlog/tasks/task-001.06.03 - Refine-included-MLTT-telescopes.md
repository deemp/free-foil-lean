---
id: TASK-001.06.03
title: Refine included MLTT telescopes
status: To Do
assignee: []
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 10:23'
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
- [ ] #1 A module can fix named fields in an `include` clause, and each supplied value is checked at its field’s specialized type.
- [ ] #2 The remaining parameter types incorporate the fixed values, and exported definitions are discharged only over the unfixed parameters they use and their dependencies.
- [ ] #3 Unknown or repeated assignments, ill-typed values, and assignments that depend on an unfixed field produce diagnostics.
- [ ] #4 Regression coverage includes a partially refined telescope and a fully instantiated one. The README shows both forms.
<!-- AC:END -->
