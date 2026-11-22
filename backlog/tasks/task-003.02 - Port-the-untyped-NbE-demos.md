---
id: TASK-003.02
title: Port the untyped NbE demos
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
dependencies:
  - TASK-003.01
references:
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/demo
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/test
documentation:
  - free-foil-repos/free-foil-NBE/README.md
  - free-foil-repos/free-foil-NBE/demo/grammar
  - FreeFoil/Examples/LambdaPi.lean
  - FreeFoil/Examples/LambdaPi/Program.lean
modified_files:
  - FreeFoil/Examples/LambdaPi/Program.lean
  - FreeFoil/Examples/NbEDemos/Booleans.lean
  - FreeFoil/Examples/NbEDemos/LambdaLet.lean
  - FreeFoil/Examples/NbEDemos/Pairs.lean
  - FreeFoil/Examples/NbEDemos/Naturals.lean
  - FreeFoil/Examples/NbEDemos/Program.lean
  - FreeFoil/Examples/TermParser.lean
  - FreeFoil/Tests/NbEDemos.lean
  - NbEMain.lean
  - README.md
  - Test.lean
  - lakefile.toml
parent_task_id: TASK-003
type: feature
ordinal: 22000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The upstream demos show which reductions belong to the object language and exercise distinct binder shapes. Use the shared normalizer and the expected terms at the pinned revision to demonstrate the same behavior in Lean.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Runnable Lean demos cover λΠ application and reduction under Π binders, Boolean conditionals, and let binding.
- [x] #2 The pairs demo reduces projections and `split`. The naturals demo reduces primitive recursion at zero and successor. Tests verify the binding order of both names in `split` and the successor branch.
- [x] #3 Representative open and closed examples from each upstream demo agree up to α-equivalence, including eliminations stuck on a free variable.
- [x] #4 The demos with upstream grammars accept representative named terms through scope resolution and print their normal forms. Documentation shows how to run them. The existing `lambdaPi` executable still passes its regression tests.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Keep the existing λΠ scope-safe syntax and NbE rules. Add standalone signatures and scope-only NbE rules for Booleans, lambda-let, pairs, and naturals. Pass split components and the successor branch’s predecessor and suspended recursive result to a closure in pattern order.
2. Share lexer utilities, open-name resolution, rendering conventions, and a single executable among the demos. Accept upstream syntax for λΠ, lambda-let, pairs, and naturals, and an if/then/else syntax for Booleans. Preserve the existing lambdaPi program commands.
3. Add pinned open and closed examples plus binder-order and parser/printing round-trip regressions to the existing Lake test driver. Document and run the demo CLI, lake build, and lake test.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The standalone demos use the shared evaluator and readback. The λΠ demo reuses its existing rules, while the CLI shares named scope resolution and lexing. Naturals delay the recursive result in the successor branch; pairs and naturals instantiate their two-name patterns in source order.

With pinned Lean 4.35.0 and GCC 16.2, `lake build`, `lake test`, and `git diff --check` passed. The tests compare named open and closed examples up to α-equivalence, round-trip parsed and printed syntax, and verify scope boundaries and multi-name binding order. The upstream standalone pairs syntax has no closed terms. Smoke checks ran all five README commands, a stuck split, an unbound-name diagnostic, and the legacy `lambdaPi` compute input.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added runnable λΠ, Boolean, lambda-let, pairs, and naturals demos using generic NbE. The nbe executable resolves named inputs with an explicit list of free names and prints parseable full normal forms. The regression suite checks upstream results up to α-equivalence, the two binding positions in split and natrec, neutral eliminations, and scope errors. The standalone upstream pairs grammar yields open examples. Verified with the pinned Lake build and test suite, all five README commands, stuck split and natrec output, and a legacy lambdaPi smoke test.
<!-- SECTION:FINAL_SUMMARY:END -->
