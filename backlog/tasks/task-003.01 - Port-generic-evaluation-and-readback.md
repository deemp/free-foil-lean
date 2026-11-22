---
id: TASK-003.01
title: Port generic evaluation and readback
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:35'
labels:
  - nbe
dependencies: []
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE.hs
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Internal/Value.hs
documentation:
  - free-foil-NBE/src/FreeFoil/NbE.hs
  - free-foil-NBE/src/FreeFoil/NbE/Internal/Value.hs
  - free-foil-NBE/test/Test/LambdaPi.hs
  - FreeFoil/Examples/LambdaPi.lean
parent_task_id: TASK-003
type: feature
ordinal: 21000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Free Foil terms already carry scope information. A shared semantic domain lets each object language provide its own elimination rules and reuse evaluation and readback across different binder shapes.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Lean clients can evaluate a scope-checked Free Foil AST to a value, read a value back into syntax, and request `nf` or `whnf` using language-supplied elimination rules.
- [ ] #2 Open terms work with a scope-only context, and callers can supply context information that remains available under binders.
- [ ] #3 `whnf` stops at head form and `nf` reduces under binders. Generic readback performs β and the language's reductions, with η available through language-specific features.
- [ ] #4 Tests exercise stuck eliminations, capture avoidance under a binder, and scope-correct instantiation of a binder that binds two names. A bounded evaluation entry point reports exhaustion on an untyped diverging term.
- [ ] #5 Library documentation includes a runnable λΠ example showing the difference between `nf` and `whnf`.
<!-- AC:END -->
