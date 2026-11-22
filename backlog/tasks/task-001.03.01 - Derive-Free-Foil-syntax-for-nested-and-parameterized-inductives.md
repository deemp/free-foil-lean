---
id: TASK-001.03.01
title: Derive Free Foil syntax for nested and parameterized inductives
status: To Do
assignee: []
created_date: '2026-11-22 10:22'
labels:
  - deriving
  - library
dependencies: []
references:
  - 'https://arxiv.org/abs/2405.16384'
documentation:
  - FreeFoil/Derive.lean
  - README.md
parent_task_id: TASK-001.03
type: feature
ordinal: 13000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Syntax authors currently need auxiliary inductives for recursive fields inside common containers and cannot derive directly from parameterized source declarations. Supporting both shapes lets clients keep more of their existing Lean syntax definitions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 `derive_free_foil` accepts recursive fields under `List` and `Option`, including scoped children, while preserving child order and binding scope.
- [ ] #2 Derivation accepts syntax inductives with ordinary type parameters and preserves the parameters in the generated interfaces.
- [ ] #3 Generated conversions round-trip supported declarations and reject malformed input with a child from the wrong category.
- [ ] #4 Unsupported declaration forms receive a targeted diagnostic.
- [ ] #5 Regression coverage exercises nested fields and parameterized syntax. The README documents the supported declaration shapes and parameter constraints.
<!-- AC:END -->
