---
id: TASK-002
title: Support scope-aware syntax annotations
status: To Do
assignee: []
created_date: '2026-11-22 10:22'
labels:
  - annotations
  - library
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Free/Foil/Annotated.hs
documentation:
  - FreeFoil/Syntax.lean
  - README.md
type: feature
ordinal: 12000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Syntax clients need source locations and semantic metadata such as inferred types. A type annotation can itself refer to local binders, so attaching it as ordinary metadata loses the scope guarantees Free Foil gives to terms.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Clients can attach source spans and annotations containing scope-checked terms at syntax nodes.
- [ ] #2 Renaming and substitution update names referenced inside scoped annotations, including below a refreshed binder.
- [ ] #3 Structural α-equivalence ignores annotation data, and an annotation-aware support operation includes names used only by annotations.
- [ ] #4 Regression coverage includes binder collisions and dependencies used only by annotations. Library documentation shows a source span and a scoped type annotation.
<!-- AC:END -->
