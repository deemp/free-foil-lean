---
id: TASK-004
title: Port the lambda-n-ways Free Foil benchmark to Lean
status: Done
assignee:
  - '@Codex'
created_date: '2026-11-22 21:56'
updated_date: '2026-11-22 22:14'
labels:
  - benchmark
  - free-foil
dependencies: []
references:
  - >-
    https://github.com/KarinaTyulebaeva/lambda-n-ways/tree/1f507f589ec12366757fdc3ee1fa499855615df3
documentation:
  - free-foil-repos/lambda-n-ways/bench/Main.lhs
  - free-foil-repos/lambda-n-ways/lib/FreeScoped/Eager/Foil.hs
  - free-foil-repos/lambda-n-ways/lib/FreeScoped/Foil.hs
modified_files:
  - FreeFoil/Benchmarks/LambdaNWaysCorpus.lean
  - FreeFoil/Benchmarks/NbECorpus.lean
  - LambdaNWaysBenchMain.lean
  - NbEBenchMain.lean
  - README.md
  - lakefile.toml
type: feature
ordinal: 29000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The NbE benchmark reuses part of the lambda-n-ways corpus. A dedicated port lets contributors measure Lean’s scope-safe Free Foil substitution and α-equivalence on the workloads used by the pinned Haskell benchmark.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 A native Lake executable runs the six active upstream workload groups (`random15`, `random20`, `conv`, `nf`, `aeq`, `aeqs`) against the Free Foil port using the pinned submodule fixtures.
- [x] #2 The Lean port checks both random groups and the Lennart term against upstream reference normal forms up to α-equivalence. The two Lennart α-equivalence groups report success, and malformed input or a failed correctness check exits with an error.
- [x] #3 The benchmark reports per-group sample timings. Parsing and setup take place outside timing, and timed conversion and normalization consume complete results.
- [x] #4 The README identifies the pinned upstream implementation, explains how to reproduce the run, and describes what each group measures. The default `lake build` and `lake test` pass without requiring the corpus.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Share the existing lambda-n-ways parser and corpus loading with the NbE executable, exposing named inputs for conversion timing and reading the pinned reference forms.
2. Add an opt-in native executable for the six active Criterion groups. Reuse the existing eager Free Foil substitution normalizer and AST α-equivalence. Follow the upstream timing boundaries, with complete-result traversal for conversion and reference α-comparison for successful normalization. For `aeq`, compare against a checked copy with shifted binder IDs so the Lean comparator sees different names.
3. Document the command, pinned provenance, group definitions, and timing scope. Verify all six groups against the submodule, bad fixture and CLI errors, and run the existing NbE corpus benchmark, default build, and tests.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The pinned active runner times normalization and reference comparison together. The Lean runner follows that boundary and checks all results within each sample. The freshened α-equivalence group shifts the closed term’s IDs after conversion because Lean’s named conversion assigns canonical binder IDs by depth.

Built and ran both native benchmark executables with Lean 4.35.0 and GCC 16.2.0. One pinned Free Foil sample matched both 100-term groups and Lennart’s reference, traversed 261 converted nodes, and passed both α-equivalence groups. The optional NbE corpus still passed on all 201 terms. `lake build` and `lake test` passed.

A temporary corpus exercised the explicit directory option, malformed input, an unbound name, unequal input and reference counts, and a mismatching reference. The CLI rejected zero samples and reported the missing fixture path. Inspection of the native output confirmed the timed closure runs between the clock reads.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added the native `lambdaNWaysBench` executable for the six active workloads from the pinned Haskell harness. It shares the fixture parser with `nbeBench`, converts the Lennart term to a scope-safe AST, and times eager Free Foil substitution with complete comparisons against the upstream normal forms. The freshened and self-comparison groups exercise Lean’s α-equivalence checker.

A full pinned sample passed all six groups and matched 201 reference normal forms. The existing NbE corpus run, default build, and regression tests passed. Temporary fixtures verified that malformed or unbound input, mismatched counts, incorrect normal forms, missing files, and invalid sample counts fail with diagnostics.
<!-- SECTION:FINAL_SUMMARY:END -->
