---
id: TASK-1
title: Complete the Free Foil Lean port
status: In Progress
assignee: []
created_date: '2026-11-21T21:05:13Z'
updated_date: '2026-11-21T21:12:15Z'
labels: []
dependencies: []
references:
  - plan.md
  - FreeFoil/Examples/LambdaPi.lean
  - https://github.com/fizruk/free-foil/tree/fdfbeef
type: feature
ordinal: 1000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The Lean library already checks scopes and provides capture-avoiding substitution, α-equivalence, scope restriction, and named-syntax conversion. Complete the examples and reusable binder machinery in plan.md using upstream revision fdfbeef as the behavior and fixture reference. Follow the milestone order in plan.md and begin with λΠ. The generic substitution proofs can proceed alongside the ports.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Lambda and Pi binders support recursive pair patterns. Evaluation checks cover nested pairs, wildcards, and capture avoidance. Name resolution rejects duplicate binders.
- [x] #2 The λΠ executable accepts upstream compute commands from a file or stdin and prints weak-head normal forms. Tests cover α-equivalent parse and print round trips, parse and scope errors, and evaluation fuel exhaustion.
- [ ] #3 Scope-indexed telescopes support scope extension, renaming, and α-equivalence. Thinning (A : 𝕌) (x : A) (B : 𝕌) for a term using only x retains A and x in order, drops B, and leaves the retained types and term well scoped.
- [ ] #4 Lean syntax generation provides signatures, constructor helpers, and conversions for λΠ and mutually recursive SOAS categories. Generated λΠ syntax preserves binder positions and duplicate-name diagnostics and passes the evaluation tests. Upstream SOAS fixtures cover metavariable substitution, successful matching, and rejected constraints.
- [ ] #5 The MLTT evaluator and bidirectional type checker pass upstream examples for inference, checking, and definitional equality. Independently checked parameterized modules with a shared dependency link without renaming their declarations.
- [ ] #6 Checked MLTT artifacts survive serialization and loading. Loading revalidates terms and references and rejects missing dependencies and invalid or conflicting name allocations.
- [ ] #7 Lean proofs for generic signatures establish the identity and composition laws for substitution up to α-equivalence, including open terms and binders that require refreshing.
- [ ] #8 Each milestone passes `lake build` and `lake test` with the toolchain pinned in `lean-toolchain`. Representative upstream λΠ fixtures pass through the executable.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Complete TASK-1.1 through TASK-1.7 in milestone order. TASK-1.8 covers generic substitution laws and can proceed independently.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Split the port into eight subtasks. TASK-1.1 is done and verified, which unblocks TASK-1.2 (dependent telescopes and thinning).
<!-- SECTION:NOTES:END -->
