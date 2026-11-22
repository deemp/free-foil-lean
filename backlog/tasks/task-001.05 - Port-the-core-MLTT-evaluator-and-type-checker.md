---
id: TASK-001.05
title: Port the core MLTT evaluator and type checker
status: Done
assignee:
  - codex-syntax_generation
created_date: '2026-11-21T21:07:51Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies:
  - TASK-001.04
references:
  - 'https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/README.md'
modified_files:
  - FreeFoil/Examples/MLTT.lean
  - FreeFoil/Examples/MLTT/Eval.lean
  - FreeFoil/Examples/MLTT/Program.lean
  - FreeFoil/Examples/MLTT/Syntax.lean
  - FreeFoil/Examples/MLTT/Typecheck.lean
  - FreeFoil/Tests/MLTT.lean
  - MLTTMain.lean
  - README.md
  - Test.lean
  - lakefile.toml
  - test/fixtures/mltt/LICENSE
  - test/fixtures/mltt/core.mltt
parent_task_id: TASK-001
type: feature
ordinal: 6000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run the standalone MLTT core examples using the Lean implementation.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 The evaluator and bidirectional type checker pass upstream core examples for inference, checking, and definitional equality.
- [x] #2 `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Declare the raw MLTT core in Lean and derive its Free Foil signature, helpers, and scoped conversions. Parse the core syntax, desugaring nondependent arrows and products to wildcard binders.
2. Implement scoped, fuel-bounded weak-head and full normalization, including beta, delta, projections, J on refl, lets, annotations, and eta contraction. Compare normal forms up to alpha-equivalence and keep binder openings capture-avoiding.
3. Port the bidirectional type rules over a scope-indexed context with caller-supplied definitions and explicit fresh-ID extension. Expose standalone term parsing and reusable declaration checking and installation.
4. Run sequential definitions, checks and computations through a standalone MLTT executable. Vendor the exact pinned upstream core fixture with its license and cover inference, checking, definitional equality, and scope/error behavior. Run `lake build`, `lake test` and the fixture through CLI file and stdin paths.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The pinned upstream core program and its license are unchanged. The Lean executable ran the program from a file and from stdin. Both paths checked four definitions and two check commands and produced four `tt` normal forms.

Verified on Lean 4.35.0 with `lake build` and `lake test`. The suite covers conversion, dependent patterns, fuel exhaustion, and preservation of free names when a definition unfolds below a binder.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Ported standalone Martin-Löf type theory using generated Free Foil syntax, scope-indexed contexts, fuel-bounded normalization, and a bidirectional checker. The `mltt` executable reads a file or stdin and installs each definition after checking its type and body.

`lake build`, `lake test`, and both CLI entry paths passed with Lean 4.35.0 and the pinned upstream core fixture.
<!-- SECTION:FINAL_SUMMARY:END -->
