---
id: TASK-001.02
title: Port dependent telescopes and thinning
status: Done
assignee:
  - '@codex'
created_date: '2026-11-21T21:07:50Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies:
  - TASK-001.01
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Foil/Telescope.hs
modified_files:
  - FreeFoil.lean
  - FreeFoil/Alpha.lean
  - FreeFoil/Substitution.lean
  - FreeFoil/Telescope.lean
  - README.md
  - Test.lean
parent_task_id: TASK-001
type: feature
ordinal: 3000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build the reusable context machinery for dependent module parameters and restricting terms to their support.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Telescope payloads can refer to earlier binders. Scope extension, renaming, and α-equivalence account for those dependencies.
- [x] #2 Thinning (A : 𝕌) (x : A) (B : 𝕌) for a term using only x retains A and x in order, drops B, and keeps the term and retained payloads well scoped.
- [x] #3 `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add a labelled, scope-indexed telescope with scope extension and capture-avoiding renaming that carries each binder mapping into later payloads.
2. Reuse the AST alpha comparator under corresponding telescope binders. Close term support from the last entry to the first, then restrict retained payloads and the term to the smaller scopes.
3. Add regression coverage for dependent payloads, renaming into overlapping scopes, and thinning, then run Lake build and tests with Lean 4.35.0.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The implementation uses the pinned Haskell telescope as its reference. It compares payloads under earlier binder correspondences and reuses AST scope checks when rebuilding a reduced telescope. The regressions cover the requested A/x/B fixture, a transitive dependency across a dropped entry, ambient references, and capture avoidance under renaming. `lake build` and `lake test` passed in the Nix development shell with Lean 4.35.0.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added scope-indexed telescopes with scope extension, capture-avoiding renaming, and dependency-aware α-equivalence. Thinning retains parameters in declaration order, closes support over their payloads, and returns the retained telescope and term in the same reduced scope.

The λΠ regression keeps `A` and `x` for a term that references `x` and drops `B`. The default build and regression suite passed on Lean 4.35.0.
<!-- SECTION:FINAL_SUMMARY:END -->
