---
id: TASK-001.08
title: Prove generic substitution laws
status: Done
assignee:
  - codex
created_date: '2026-11-21T21:07:52Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/test/laws/Control/Monad/Free/Foil/Laws.hs#L411
modified_files:
  - FreeFoil.lean
  - FreeFoil/Alpha.lean
  - FreeFoil/Lexical.lean
  - FreeFoil/Substitution.lean
  - FreeFoil/SubstitutionLaws.lean
  - FreeFoil/Tests/SubstitutionLaws.lean
  - Test.lean
parent_task_id: TASK-001
type: feature
ordinal: 9000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove the substitution laws for arbitrary Free Foil signatures. This task can proceed alongside the example ports.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Identity substitution preserves a term up to α-equivalence.
- [x] #2 Sequential substitution agrees up to α-equivalence with the composed substitution for open terms and under refreshed binders.
- [x] #3 `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Give generic syntax a proof-only lexical interpretation that records bound-variable binding positions and preserves free identifiers, then show agreement implies the existing executable α-comparison.
2. Prove by structural induction that the existing substitution algorithm agrees with simultaneous substitution in that interpretation. Account explicitly for weakening, freshening, and the lifting of substitutions under patterns.
3. Expose composition and derive generic identity and composition theorems for open terms, including explicit refresh. Add a focused proof example for a colliding binder and run the pinned Lake build and test drivers.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The proof interprets names at absolute binding levels. A single induction relates the existing substitution fold to interpretation in an assignment containing its images. This makes composition a pointwise application of that same theorem. The executable α-comparison and substitution choices are unchanged.

The focused regression deliberately collides pattern IDs, compares the different binder names chosen by sequential and composed substitution, and verifies that both preserve the same free ID. A separate explicit identity regression exercises binder refresh after weakening.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Proved substitution identity and composition up to the existing executable α-equivalence for arbitrary signatures with decidable operator and pattern equality. The proofs compare lexical interpretations and include forced refresh on open terms. The regression computes distinct binder allocations for sequential and composed substitution and checks that both preserve the free variable.

Verified with `lake build` and `lake test` on Lean 4.35.0. `#print axioms` reported only standard Lean axioms for the public laws.
<!-- SECTION:FINAL_SUMMARY:END -->
