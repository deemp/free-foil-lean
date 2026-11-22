---
id: TASK-003.07
title: Port the dependent-types NbE demo
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:35'
labels:
  - nbe
dependencies:
  - TASK-002
  - TASK-003.01
  - TASK-003.03
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/demo/DependentTypes.hs
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/demo/DependentTypes
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/test/Test/Refinement.hs
documentation:
  - free-foil-NBE/CHANGELOG.md
  - free-foil-NBE/demo/DependentTypes.hs
  - free-foil-NBE/demo/DependentTypes/Elaborate.hs
  - free-foil-NBE/test/Test/DependentTypes.hs
  - free-foil-NBE/test/Test/Refinement.hs
parent_task_id: TASK-003
type: feature
ordinal: 27000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The dependent-types demo shows how a client can use types in its context and annotations to refine neutral terms. Generic evaluation and semantic conversion supply the shared operations that the demo extends with type information.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 The Lean demo elaborates representative upstream inputs bidirectionally for a universe, dependent functions, dependent pairs, and unit. Elaborated terms carry scope-correct type information, and ill-typed inputs are rejected.
- [ ] #2 Readback and conversion can refine neutrals using context types and node annotations. Refinement respects binder context extension and preserves the head behavior of eliminations.
- [ ] #3 Tests cover η for functions and pairs and the unique inhabitants of unit, Π into a singleton, and Σ of singletons. Representative elaborated normal forms agree with upstream up to α-equivalence.
- [ ] #4 The documentation shows how to run elaboration and normalization on a named example.
<!-- AC:END -->
