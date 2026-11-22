---
id: TASK-001.08.01
title: Prove the lexical specification of α-equivalence
status: To Do
assignee: []
created_date: '2026-11-22 10:22'
labels:
  - proof
  - library
dependencies: []
documentation:
  - FreeFoil/Alpha.lean
  - FreeFoil/Lexical.lean
  - FreeFoil/SubstitutionLaws.lean
parent_task_id: TASK-001.08
type: enhancement
ordinal: 15000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The generic α-equivalence checker already accepts terms whose lexical interpretations agree. A converse makes lexical equality a complete specification of the Boolean checker and supports reasoning about canonical forms.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 A public Lean theorem states and proves that `AST.alphaEquiv` returns `true` exactly when lexical interpretations agree for arbitrary supported signatures.
- [ ] #2 The specification covers open terms, shadowing, and patterns with multiple binders while preserving the identity of free names.
- [ ] #3 Checked examples cover binder renaming, distinct free identifiers, and distinct positions in a pattern. Library documentation identifies the theorem and its lexical interpretation.
<!-- AC:END -->
