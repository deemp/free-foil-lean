---
id: TASK-001.03
title: Generate Free Foil syntax from Lean declarations
status: Done
assignee:
  - codex-syntax_generation
created_date: '2026-11-21T21:07:50Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies:
  - TASK-001.02
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Free/Foil/TH/MkFreeFoil.hs
modified_files:
  - FreeFoil/Derive.lean
  - FreeFoil/Examples/LambdaPi.lean
  - FreeFoil/Examples/LambdaPi/Program.lean
  - README.md
  - Test.lean
parent_task_id: TASK-001
type: feature
ordinal: 4000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Replace the handwritten λΠ syntax plumbing with generated signatures, helpers, and conversions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Generation covers binder positions and recursive pair patterns. Generated conversion reports duplicate binders.
- [x] #2 The generated λΠ syntax passes its parser, conversion, and evaluation regressions, and `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Inspect the Lean raw syntax constructors to derive operator tags and arities, distinguishing ordinary term fields from fields wrapped in a binder and its scoped body.
2. Generate `Signature`, named and scope-safe constructor helpers, and bidirectional conversion between the input declaration and `Syntax`. Route name resolution and printing through Free Foil's common operations.
3. Migrate the λΠ parser and evaluator to the generated declarations while preserving its raw helpers. Keep pattern shape and binding-order names in the existing `Binder` representation.
4. Verify binder positions, nested patterns, and duplicate diagnostics with the λΠ regression suite; run the pinned `lake build`, `lake test`, and upstream interpreter fixtures.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Verified in a clean Lean 4.35.0 checkout containing only this task's files. A standalone generator probe exercised a variable-only grammar and a constructor with two scoped fields separated by an ordinary field.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added `derive_free_foil` to generate signatures, constructor helpers, and named conversions from a Lean inductive. The λΠ parser and printer use the generated conversions, and its evaluator uses the generated scope-safe constructors. Generated resolution checks duplicate binders and keeps Π pattern names out of the domain.

`lake build` and `lake test` passed with Lean 4.35.0. Three closed upstream λΠ compute commands produced the expected results.
<!-- SECTION:FINAL_SUMMARY:END -->
