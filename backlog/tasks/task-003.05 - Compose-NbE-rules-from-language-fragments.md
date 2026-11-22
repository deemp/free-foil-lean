---
id: TASK-003.05
title: Compose NbE rules from language fragments
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
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Sum.hs
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/demo/Fragments
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/baselines/Monolith.hs
documentation:
  - free-foil-NBE/src/FreeFoil/NbE/Sum.hs
  - free-foil-NBE/test/Test/Fragments.hs
  - free-foil-NBE/test/Test/Monolith.hs
parent_task_id: TASK-003
type: feature
ordinal: 25000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
An object language assembled from reusable syntax fragments needs the same reduction behavior as a language written in one signature. The generic normalizer and the standalone demos supply the evaluation interface and the function, pair, and natural-number behavior to reuse.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 A fragment can supply rules once for use in any composed signature that contains it. The composed language inherits those rules from its fragments.
- [ ] #2 The Lean example combines functions, pairs, and naturals and reduces mixed-fragment terms under a shared binder vocabulary.
- [ ] #3 The composed demo accepts representative upstream monolith inputs. Tests compare its normal forms with those of a single-signature reference up to α-equivalence.
- [ ] #4 The documentation shows how to add a fragment and evaluate a composed-language term.
<!-- AC:END -->
