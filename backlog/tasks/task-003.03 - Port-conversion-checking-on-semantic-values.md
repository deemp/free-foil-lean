---
id: TASK-003.03
title: Port conversion checking on semantic values
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 16:09'
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
modified_files:
  - FreeFoil.lean
  - FreeFoil/NbE.lean
  - FreeFoil/NbE/Conversion.lean
  - FreeFoil/Examples/LambdaPi/NbE.lean
  - FreeFoil/Examples/NbEDemos/Pairs.lean
  - FreeFoil/Tests/NbEConversion.lean
  - Test.lean
  - README.md
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
- [x] #1 Lean clients can run conversion directly on values and on terms in a supplied context, including open terms.
- [x] #2 Conversion respects α-equivalence, β-reduction, and language-supplied eliminations. It distinguishes unequal constructors and unequal neutral terms.
- [x] #3 Languages can opt introduction forms into η comparison. Regressions cover η for functions and pairs and verify that the default `nf` remains intensional for those examples.
- [x] #4 API documentation includes an open-term conversion example.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Add semantic conversion beside the NbE core, comparing heads and demanded positions left to right, using operator and binder-pattern equality and opening corresponding closures with the same fresh names in the extended client context. Use the refinement hook for ordinary positions and preserve principal heads. Add optional η observers to language rules and use them only in conversion when structural heads do not match. Demonstrate function and pair η in the existing λΠ and pairs rules and exercise direct value and term comparison, short-circuiting, contexts, and intensional normal forms. Add a runnable README example and verify the default build and regression suite.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Comparison walks semantic heads directly. Matching operators demand ordinary positions left to right, then compare bodies opened with the same fresh names and the client’s extended context. The principal-position flag preserves the head when contextual refinement is enabled.

Added opt-in η observers for λΠ variable-pattern functions and for pairs. Both orientations are tested against open neutrals, and default normalization preserves the expanded forms. Tests also cover Boolean results for β and α, distinct neutral heads and constructors, environments with different source scopes, and fuel exhaustion when a diverging argument is demanded. The README example returns `some true`.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added direct conversion for semantic values and scope-checked terms, including terms evaluated under different environments into a common scope. The comparison walks matching positions on demand, aligns binders with shared fresh names, and applies the client’s context and refinement rules. The λΠ and pairs examples opt into function and pair η through observers while ordinary normalization preserves introduction forms. Verified with the pinned Lake build and regression suite, including unequal neutral heads and constructors, and executed the README open-term example.
<!-- SECTION:FINAL_SUMMARY:END -->
