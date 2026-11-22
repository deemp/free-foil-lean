---
id: TASK-003.08
title: Benchmark the Lean NbE port
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
dependencies:
  - TASK-003.02
  - TASK-003.05
references:
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/bench
documentation:
  - free-foil-repos/free-foil-NBE/bench/README.md
  - free-foil-repos/free-foil-NBE/bench/lambda-n-ways/README.md
modified_files:
  - FreeFoil/Benchmarks/NbEBaselines.lean
  - FreeFoil/Benchmarks/NbECorpus.lean
  - NbEBenchMain.lean
  - lakefile.toml
  - README.md
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
- [x] #1 A reproducible Lean benchmark compares generic λΠ NbE with monomorphic NbE and substitution on shared workloads, including nested lets and Π binders.
- [x] #2 One benchmark compares composed and single-signature normalization. An opt-in benchmark accepts the pinned lambda-n-ways corpus for the factorial and random-term groups.
- [x] #3 The harness checks α-equivalence across equivalent implementations and measures complete normal forms on the same inputs.
- [x] #4 Documentation records commands, workload provenance, and a baseline with toolchain and machine details. The default Lean build and tests run without the optional corpus.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Add an on-demand native Lake benchmark executable. Compare the generic λΠ normalizer with a benchmark-only monomorphic closure evaluator and a capture-avoiding substitution baseline over the same scoped AST. Generate Church exponentiation, nested identity redexes, nested lets encoded as β-redexes, and nested Π workloads following the pinned upstream harness. Parse one mixed-language program into both signatures outside timing. Accept the pinned lambda-n-ways factorial and two random groups from a local directory. Check α-equivalence before timing and traverse each complete normal form during each sample. Document commands, upstream revisions, and native results, and verify the built-in and full-corpus runs and default build and tests.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The substitution baseline eagerly rebuilds the children it traverses and reuses substituted arguments. This avoids layering deferred AST children across successive substitutions and keeps the nested-let measurement practical.

Verified lake build, lake test, lake exe nbeBench --samples 1, and lake exe nbeBench --samples 5 --corpus with the three pinned fork fixtures on Lean 4.35.0 and GCC 16.2.0. All seven built-in workloads and the 201 corpus terms agreed up to α-equivalence. README records the measured baseline and the corpus revision.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added an opt-in native benchmark comparing generic λΠ NbE, a monomorphic evaluator, and capture-avoiding substitution over the same scoped ASTs. Built-in workloads include nested lets and Π binders, plus a mixed-language program for composed and single-signature rules.

The harness checks α-equivalence before timing and traverses each full normal form inside every sample. The optional pinned lambda-n-ways run covers factorial and two 100-term random groups. All seven built-in workloads and 201 corpus terms agreed, and checksums matched in the timed runs.

The README records reproduction commands, fixture provenance, toolchain and machine details, and five-sample medians. The default build and test suite passed without a corpus on Lean 4.35.0 with GCC 16.2.0.
<!-- SECTION:FINAL_SUMMARY:END -->
