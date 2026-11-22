---
id: TASK-003.08
title: Benchmark the Lean NbE port
status: To Do
assignee: []
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:34'
labels:
  - nbe
dependencies:
  - TASK-003.02
  - TASK-003.05
references:
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/bench
documentation:
  - free-foil-NBE/bench/README.md
  - free-foil-NBE/bench/lambda-n-ways/README.md
parent_task_id: TASK-003
type: task
ordinal: 28000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The upstream comparisons measure the overhead of the generic normalizer and of combining language fragments. The Lean demos and composed language give the benchmark harness real library entry points to measure against comparable baselines.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 A reproducible Lean benchmark compares generic λΠ NbE with monomorphic NbE and substitution on shared workloads, including nested lets and Π binders.
- [ ] #2 One benchmark compares composed and single-signature normalization. An opt-in benchmark accepts the pinned lambda-n-ways corpus for the factorial and random-term groups.
- [ ] #3 The harness checks α-equivalence across equivalent implementations and measures complete normal forms on the same inputs.
- [ ] #4 Documentation records commands, workload provenance, and a baseline with toolchain and machine details. The default Lean build and tests run without the optional corpus.
<!-- AC:END -->
