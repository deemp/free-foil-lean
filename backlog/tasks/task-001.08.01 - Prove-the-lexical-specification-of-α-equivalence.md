---
id: TASK-001.08.01
title: Prove the lexical specification of α-equivalence
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 10:30'
labels:
  - proof
  - library
dependencies: []
documentation:
  - FreeFoil/Alpha.lean
  - FreeFoil/Lexical.lean
  - FreeFoil/SubstitutionLaws.lean
modified_files:
  - FreeFoil/Alpha.lean
  - FreeFoil/Tests/SubstitutionLaws.lean
parent_task_id: TASK-001.08
type: enhancement
ordinal: 15000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The generic α-equivalence checker already accepts terms whose lexical interpretations agree. A converse makes lexical equality a complete specification of the Boolean checker and supports reasoning about canonical forms.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 A public Lean theorem states and proves that `AST.alphaEquiv` returns `true` exactly when lexical interpretations agree for arbitrary supported signatures.
- [x] #2 The specification covers open terms, shadowing, and patterns with multiple binders while preserving the identity of free names.
- [x] #3 Checked examples cover binder renaming, distinct free identifiers, and distinct positions in a pattern. Library documentation identifies the theorem and its lexical interpretation.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Generalize the existing paired-binding-stack proof in FreeFoil/Alpha.lean to an equivalence, proving that variable lookup agrees with lexical binding levels and inducting over ordinary and scoped children. Reuse the existing stack-append invariant and preserve the checker and its current public implication theorem.
2. Export and document AST.alphaEquiv_iff_lexical_eq with the existing lexical interpretation, identifying how free identifiers, shadowing, and positions within a pattern are represented.
3. Add checked examples to FreeFoil/Tests/SubstitutionLaws.lean for open free identifiers, shadowed binder renaming, and differing positions in a multi-binder pattern. Verify using pinned Lean and Lake.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The existing α-comparison and lexical interpreter stayed intact. The proof now works in both directions on raw syntax using the same binding-stack invariant, and the existing implication theorem delegates to the new public equivalence.

Pinned Lean 4.35.0 built FreeFoil.Tests.SubstitutionLaws, including the new shadowing, free identifier, and pattern-position examples. Lean reports only propext, Classical.choice, and Quot.sound as dependencies of the new theorem.

Reviewed the generic statement and compiled the proof examples. The public theorem uses only Lean’s standard propext, Classical.choice and Quot.sound axioms. Both the default build and test driver passed with Lean 4.35.0.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Prove that the existing Boolean α-equivalence checker agrees in both directions with the lexical interpretation, preserving the existing one-way theorem. The proof accounts for name shadowing, binder positions and unchanged free identifiers.

Checked regressions exercise shadowed binder renaming, distinct free identifiers and distinct positions in a pair pattern.
<!-- SECTION:FINAL_SUMMARY:END -->
