---
id: TASK-001.06.01
title: Support named telescopes in MLTT
status: To Do
assignee: []
created_date: '2026-11-22 10:22'
labels:
  - mltt
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/README.md#named-telescopes-and-include
documentation:
  - FreeFoil/Telescope.lean
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
- [ ] #1 An MLTT source can declare a named telescope and include it in module headers and in other telescope declarations.
- [ ] #2 Included fields appear in declaration order before local fields, and a local field can refer to an earlier included field.
- [ ] #3 Each including module gets its own binders, and parameter discharge agrees with the equivalent explicitly written header.
- [ ] #4 Missing telescope names, include cycles, and repeated parameter names produce diagnostics.
- [ ] #5 Regression coverage exercises nested includes and two includers. The README shows how to declare and include a telescope.
<!-- AC:END -->
