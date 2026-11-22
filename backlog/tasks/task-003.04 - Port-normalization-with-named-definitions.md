---
id: TASK-003.04
title: Port normalization with named definitions
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:35'
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
  - free-foil-NBE/src/FreeFoil/NbE/Definitions.hs
  - free-foil-NBE/test/Test/Definitions.hs
  - free-foil-NBE/test/Test/Glue.hs
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
- [ ] #1 Lean clients can extend a scope with nonrecursive definitions whose bodies can refer to earlier definitions. Free names without definitions remain neutral.
- [ ] #2 Language eliminations reduce through definitions when their bodies expose a matching constructor. Callers can read normal forms back with definition names folded or bodies unfolded.
- [ ] #3 Conversion compares folded values first and can fall back to definitions' bodies. Tests cover a matching folded head, fallback to an unfolded body, and unequal definitions.
- [ ] #4 Tests and a documented example cover chained definitions and their use beneath a binder.
<!-- AC:END -->
