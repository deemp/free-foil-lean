---
id: TASK-003.06
title: Normalize syntax with transparent annotations
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
dependencies:
  - TASK-002
  - TASK-003.05
  - TASK-003.03
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Annotated.hs
documentation:
  - FreeFoil/Annotated.lean
  - free-foil-repos/free-foil-NBE/src/FreeFoil/NbE/Annotated.hs
  - free-foil-repos/free-foil-NBE/test/Test/Annotated.hs
modified_files:
  - FreeFoil.lean
  - FreeFoil/Annotated.lean
  - FreeFoil/NbE/Annotated.lean
  - FreeFoil/Tests/NbEAnnotated.lean
  - README.md
  - Test.lean
parent_task_id: TASK-003
type: feature
ordinal: 26000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Source spans and similar metadata should survive scope checking without affecting an object language's computation. Lean already supports scope-aware annotations. Fragment rules and semantic conversion provide the shared behavior for an annotation-transparent NbE interface.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Annotated ASTs can use the underlying fragment rules. Values and normal forms use the blank annotation behavior of the upstream interface.
- [x] #2 Conversion gives the same result for terms that differ only in metadata or terms stored as annotations.
- [x] #3 Tests cover annotations on an elimination and under a binder, and compare readback with normalization of the erased term up to α-equivalence.
- [x] #4 Documentation demonstrates annotated normalization and describes when a language supplies type-aware rules.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Run fragment rules in the annotated signature by embedding original operators and treating annotation wrappers as transparent at evaluation time. Verify that full readback has blank annotations and weak-head readback keeps source wrappers in frozen bodies. Compare conversion across different metadata and annotation terms without forcing them. Exercise the composed demo and document annotated normalization and the type-aware extension point.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Transparent evaluation uses `.original` operators for blank semantic heads and forces just the subject of an annotation wrapper. Weak-head readback uses the existing binder-freezing path, including readback of captured substitutions needed by stored annotation terms.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
`NbE.Fragment.annotated` runs existing fragment reductions and η rules over scope-aware annotated syntax. Evaluation and conversion ignore source metadata and stored annotation terms. Full readback uses blank annotations, and weak-head readback preserves source wrappers in frozen bodies with their binder references refreshed.

Regressions cover a projection, full normalization versus the erased term, a frozen binder body, divergent annotation payloads, and positive and negative conversion cases. The README demonstrates annotated normalization and points to language-specific rules for type-aware behavior.

Verified with `lake build`, `lake test`, the standalone README example, and a smoke test of annotated definitions in folded and unfolded readback.
<!-- SECTION:FINAL_SUMMARY:END -->
