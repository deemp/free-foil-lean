---
id: TASK-003.03
title: Port conversion checking on semantic values
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:35'
labels:
  - nbe
dependencies:
  - TASK-003.01
  - TASK-003.02
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Conversion.hs
documentation:
  - free-foil-NBE/src/FreeFoil/NbE/Conversion.hs
  - free-foil-NBE/test/Test/LambdaPi.hs
  - free-foil-NBE/test/Test/Pairs.hs
parent_task_id: TASK-003
type: feature
ordinal: 23000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Type checkers and language tools need to compare terms with internal redexes and terms whose equality depends on the language's η rules. The generic NbE core provides the values and scope-aware evaluation this comparison needs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Lean clients can run conversion directly on values and on terms in a supplied context, including open terms.
- [ ] #2 Conversion respects α-equivalence, β-reduction, and language-supplied eliminations. It distinguishes unequal constructors and unequal neutral terms.
- [ ] #3 Languages can opt introduction forms into η comparison. Regressions cover η for functions and pairs and verify that the default `nf` remains intensional for those examples.
- [ ] #4 API documentation includes an open-term conversion example.
<!-- AC:END -->
