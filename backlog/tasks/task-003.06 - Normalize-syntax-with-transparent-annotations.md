---
id: TASK-003.06
title: Normalize syntax with transparent annotations
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:35'
labels:
  - nbe
dependencies:
  - TASK-002
  - TASK-003.05
  - TASK-003.03
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Annotated.hs
documentation:
  - FreeFoil/Annotated.lean
  - free-foil-NBE/src/FreeFoil/NbE/Annotated.hs
  - free-foil-NBE/test/Test/Annotated.hs
parent_task_id: TASK-003
type: feature
ordinal: 26000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Source spans and similar metadata should survive scope checking without affecting an object language's computation. Lean already supports scope-aware annotations. Fragment rules and semantic conversion provide the shared behavior for an annotation-transparent NbE interface.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Annotated ASTs can use the underlying fragment rules. Values and normal forms use the blank annotation behavior of the upstream interface.
- [ ] #2 Conversion gives the same result for terms that differ only in metadata or terms stored as annotations.
- [ ] #3 Tests cover annotations on an elimination and under a binder, and compare readback with normalization of the erased term up to α-equivalence.
- [ ] #4 Documentation demonstrates annotated normalization and describes when a language supplies type-aware rules.
<!-- AC:END -->
