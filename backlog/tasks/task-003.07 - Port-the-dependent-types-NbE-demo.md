---
id: TASK-003.07
title: Port the dependent-types NbE demo
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
dependencies:
  - TASK-002
  - TASK-003.01
  - TASK-003.03
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/demo/DependentTypes.hs
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/demo/DependentTypes
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/test/Test/Refinement.hs
documentation:
  - free-foil-repos/free-foil-NBE/CHANGELOG.md
  - free-foil-repos/free-foil-NBE/demo/DependentTypes.hs
  - free-foil-repos/free-foil-NBE/demo/DependentTypes/Elaborate.hs
  - free-foil-repos/free-foil-NBE/test/Test/DependentTypes.hs
  - free-foil-repos/free-foil-NBE/test/Test/Refinement.hs
modified_files:
  - FreeFoil/NbE.lean
  - FreeFoil/NbE/Conversion.lean
  - FreeFoil/NbE/Definitions.lean
  - FreeFoil/Examples/DependentTypes/Syntax.lean
  - FreeFoil/Examples/DependentTypes/NbE.lean
  - FreeFoil/Examples/DependentTypes/Elaborate.lean
  - FreeFoil/Examples/DependentTypes/Program.lean
  - FreeFoil/Tests/DependentTypes.lean
  - Test.lean
  - README.md
  - lakefile.toml
parent_task_id: TASK-003
type: feature
ordinal: 27000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The dependent-types demo shows how a client can use types in its context and annotations to refine neutral terms. Generic evaluation and semantic conversion supply the shared operations that the demo extends with type information.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 The Lean demo elaborates representative upstream inputs bidirectionally for a universe, dependent functions, dependent pairs, and unit. Elaborated terms carry scope-correct type information, and ill-typed inputs are rejected.
- [x] #2 Readback and conversion can refine neutrals using context types and node annotations. Refinement respects binder context extension and preserves the head behavior of eliminations.
- [x] #3 Tests cover η for functions and pairs and the unique inhabitants of unit, Π into a singleton, and Σ of singletons. Representative elaborated normal forms agree with upstream up to α-equivalence.
- [x] #4 The documentation shows how to run elaboration and normalization on a named example.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Port the upstream named grammar and resolve it with Free Foil. Store a computed type as a scoped operand, including the inferred universe on each dependent type former. Infer and check in a semantic typing context, refreshing raw binders before extending that context. Reuse generic NbE reduction, readback and conversion, with optional rules for ignoring annotation operands in conversion, bounded singleton refinement, and η observers that demand the other term’s type. Refine neutral variables from the context and neutral eliminations from their annotations. Verify pinned upstream normal forms by α-equivalence and cover typing failures, subtyping, singleton conversion after substitution, and shape-directed η. Document a named example and run the default build and tests.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The elaborated signature stores each computed type in the subject’s scope, with fixed types for universes and unit constants. Conversion skips those operands during structural comparison but reads them when refining neutral applications and projections. Typed η observers use bounded evaluation while scope-only observers retain their original interface.

The public scoped elaborator refreshes binders before adding assumptions. The regression exercises a weakened lambda whose old binder identifier collides with a free variable in its type and checks that readback preserves the free type reference.

Verified the dependent-types suite, the README example, and the default lake build and lake test with Lean 4.35.0 and GCC 16.2.0 from the Nix store. The tests compare pinned upstream normal forms up to α-equivalence and cover typing failures, cumulativity, dependent η, and singleton refinement after substitution.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Ported the pinned dependent-types grammar and bidirectional elaboration for cumulative universes, dependent functions, dependent pairs, and Unit. The scoped syntax carries computed types, and elaboration refreshes binders before entering a typing context.

Shared NbE reads types from the context and node annotations to refine singleton neutrals and supplies typed η observers for functions and pairs. Regression tests compare pinned normal forms up to α-equivalence and cover typing errors, weakened binders, singleton refinement, and η in both directions.

Verified the default build, regression suite, and runnable README example on Lean 4.35.0 with GCC 16.2.0.
<!-- SECTION:FINAL_SUMMARY:END -->
