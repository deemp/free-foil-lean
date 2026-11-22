---
id: TASK-001
title: Complete the Free Foil Lean port
status: Done
assignee: []
created_date: '2026-11-21T21:05:13Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies: []
references:
  - FreeFoil/Examples/LambdaPi.lean
  - 'https://github.com/fizruk/free-foil/tree/fdfbeef'
  - README.md
type: feature
ordinal: 1000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Complete the Free Foil Lean port in eight subtasks, beginning with the λΠ example and continuing through dependent telescopes, syntax generation, SOAS, and MLTT with checked artifacts. Use upstream revision `fdfbeef` as the behavior and fixture reference. The generic substitution proofs can proceed alongside the example ports.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Lambda and Pi binders support recursive pair patterns. Evaluation checks cover nested pairs, wildcards, and capture avoidance. Name resolution rejects duplicate binders.
- [x] #2 The λΠ executable accepts upstream compute commands from a file or stdin and prints weak-head normal forms. Tests cover α-equivalent parse and print round trips, parse and scope errors, and evaluation fuel exhaustion.
- [x] #3 Scope-indexed telescopes support scope extension, renaming, and α-equivalence. Thinning (A : 𝕌) (x : A) (B : 𝕌) for a term using only x retains A and x in order, drops B, and leaves the retained types and term well scoped.
- [x] #4 Lean syntax generation provides signatures, constructor helpers, and conversions for λΠ and mutually recursive SOAS categories. Generated λΠ syntax preserves binder positions and duplicate-name diagnostics and passes the evaluation tests. Upstream SOAS fixtures cover metavariable substitution, successful matching, and rejected constraints.
- [x] #5 The MLTT evaluator and bidirectional type checker pass upstream examples for inference, checking, and definitional equality. Independently checked parameterized modules with a shared dependency link without renaming their declarations.
- [x] #6 Checked MLTT artifacts survive serialization and loading. Loading revalidates terms and references and rejects missing dependencies and invalid or conflicting name allocations.
- [x] #7 Lean proofs for generic signatures establish the identity and composition laws for substitution up to α-equivalence, including open terms and binders that require refreshing.
- [x] #8 Each milestone passes `lake build` and `lake test` with the toolchain pinned in `lean-toolchain`. Representative upstream λΠ fixtures pass through the executable.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Complete TASK-001.01 through TASK-001.07 in milestone order. TASK-001.08 covers generic substitution laws and can proceed independently.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Split the port into eight subtasks. TASK-001.01 is done and verified, which unblocks TASK-001.02 (dependent telescopes and thinning).

All eight milestones are complete. Final verification ran the default build and test driver with pinned Lean 4.35.0, the three closed upstream λΠ compute commands, and the upstream MLTT core and parameter fixtures through file and stdin. The artifact round trip preserved the upstream core definitions and rejected invalid references, types, and reservations.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Completed all eight Free Foil Lean milestones, including the λΠ and SOAS examples, dependent telescopes and thinning, generated syntax, generic substitution proofs, and MLTT checking, linking, and checked artifacts.

The Lean 4.35.0 build and regression suite pass. The upstream λΠ and MLTT computations produce the expected results, and restored MLTT modules preserve declaration IDs through linking.
<!-- SECTION:FINAL_SUMMARY:END -->
