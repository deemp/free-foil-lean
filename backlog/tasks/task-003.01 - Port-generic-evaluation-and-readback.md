---
id: TASK-003.01
title: Port generic evaluation and readback
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 15:53'
labels:
  - nbe
dependencies: []
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE.hs
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Internal/Value.hs
documentation:
  - free-foil-NBE/src/FreeFoil/NbE.hs
  - free-foil-NBE/src/FreeFoil/NbE/Internal/Value.hs
  - free-foil-NBE/test/Test/LambdaPi.hs
  - FreeFoil/Examples/LambdaPi.lean
modified_files:
  - FreeFoil.lean
  - FreeFoil/NbE.lean
  - FreeFoil/Examples/LambdaPi/NbE.lean
  - FreeFoil/Tests/NbE.lean
  - Test.lean
  - README.md
  - lakefile.toml
parent_task_id: TASK-003
type: feature
ordinal: 21000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Free Foil terms already carry scope information. A shared semantic domain lets each object language provide its own elimination rules and reuse evaluation and readback across different binder shapes.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Lean clients can evaluate a scope-checked Free Foil AST to a value, read a value back into syntax, and request `nf` or `whnf` using language-supplied elimination rules.
- [x] #2 Open terms work with a scope-only context, and callers can supply context information that remains available under binders.
- [x] #3 `whnf` stops at head form and `nf` reduces under binders. Generic readback performs β and the language's reductions, with η available through language-specific features.
- [x] #4 Tests exercise stuck eliminations, capture avoidance under a binder, and scope-correct instantiation of a binder that binds two names. A bounded evaluation entry point reports exhaustion on an untyped diverging term.
- [x] #5 Library documentation includes a runnable λΠ example showing the difference between `nf` and `whnf`.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Add a scope-indexed semantic domain with neutral names, nodes, and suspended ordinary and scoped children. Evaluate through language-supplied rules that demand only principal children and instantiate closures with arguments in pattern order. Use explicit bounded evaluation throughout. Implement capture-avoiding readback that freshly opens scoped children for full normalization and substitutes their captured environment without reducing the body for weak-head normalization. Give rules scope-indexed client context and a binder extension hook. Add reusable λΠ reduction rules, regression tests for open terms, context, capture, multi-name patterns, demand and exhaustion, and a runnable README example. Verify with the pinned Lake build and test suite.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented demand-based ordinary thunks and scoped semantic closures. Full readback freshly opens closures in the client's extended context. Weak readback preserves the closure body syntax and reads back captured values only where the body uses them. The λΠ rules preserve β/pair semantics and leave principal heads unrefined.

Lake build and lake test passed with Lean 4.35.0 and GCC 16.2. The README example was executed separately and returned the shown weak and full forms. Tests cover open neutrals, capture, pair binding order, with-context refinement, discarded diverging arguments, and exhaustion.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added a generic, bounded evaluator and readback for scope-checked syntax. Language rules demand just the operands they need, instantiate closures in binding order, and may extend the context or refine values at readback. The λΠ rules exercise β-reduction and projections without changing the existing interpreter. Regression tests passed for distinct full and weak readback, stuck open terms, capture avoidance, two-name patterns, context and principal-head handling, and fuel exhaustion. Verified with the pinned Lake build and test suite, and ran the README example.
<!-- SECTION:FINAL_SUMMARY:END -->
