---
id: TASK-001.04.01
title: Solve the SOAS metavariable pattern fragment
status: To Do
assignee: []
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 10:24'
labels:
  - soas
  - unification
dependencies: []
references:
  - 'https://github.com/fedor-ivn/free-foil-hou'
  - 'https://arxiv.org/abs/2405.16384'
documentation:
  - FreeFoil/Examples/SOAS.lean
  - README.md
parent_task_id: TASK-001.04
type: feature
ordinal: 14000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The SOAS example can apply and validate a supplied metavariable substitution. A solver for the fragment where metavariables are applied to distinct bound variables lets clients obtain substitutions for scoped equations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 The solver produces a well-scoped metavariable substitution for supported solvable equations, including `?F[x] = f(x)` with `f` a rigid unary operator.
- [ ] #2 Rigid mismatches, cyclic assignments, and assignments requiring an out-of-scope bound variable are rejected.
- [ ] #3 Metavariable applications outside the supported pattern fragment receive a distinct outcome.
- [ ] #4 Every returned solution is proved in Lean to satisfy its input equations according to the constraint checker.
- [ ] #5 Regression coverage includes multiple constraints, renamed binders, a cyclic equation, and an out-of-fragment application. The README describes the supported fragment.
<!-- AC:END -->
