---
id: TASK-003.02
title: Port the untyped NbE demos
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:34'
labels:
  - nbe
dependencies:
  - TASK-003.01
references:
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/demo
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/test
documentation:
  - free-foil-NBE/README.md
  - free-foil-NBE/demo/grammar
  - FreeFoil/Examples/LambdaPi.lean
  - FreeFoil/Examples/LambdaPi/Program.lean
parent_task_id: TASK-003
type: feature
ordinal: 22000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The upstream demos show which reductions belong to the object language and exercise distinct binder shapes. Use the shared normalizer and the expected terms at the pinned revision to demonstrate the same behavior in Lean.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Runnable Lean demos cover λΠ application and reduction under Π binders, Boolean conditionals, and let binding.
- [ ] #2 The pairs demo reduces projections and `split`. The naturals demo reduces primitive recursion at zero and successor. Tests verify the binding order of both names in `split` and the successor branch.
- [ ] #3 Representative open and closed examples from each upstream demo agree up to α-equivalence, including eliminations stuck on a free variable.
- [ ] #4 The demos with upstream grammars accept representative named terms through scope resolution and print their normal forms. Documentation shows how to run them. The existing `lambdaPi` executable still passes its regression tests.
<!-- AC:END -->
