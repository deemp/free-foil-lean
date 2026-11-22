---
id: TASK-001.01
title: Finish the λΠ example and interpreter
status: Done
assignee:
  - '@codex'
created_date: '2026-11-21T21:07:50Z'
updated_date: '2026-11-22 16:57'
labels: []
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/lambda-pi/grammar/LambdaPi/Syntax.cf
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/lambda-pi/src/Language/LambdaPi/Impl/FreeFoilTH.hs
parent_task_id: TASK-001
type: feature
ordinal: 2000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Add upstream λΠ pattern and program support to the Lean example. Use the upstream grammar and interpreter at revision `fdfbeef` as the reference.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Lambda and Pi binders support recursive pair patterns. Evaluation checks cover nested pairs, wildcards, and capture avoidance. Name resolution rejects duplicate binders.
- [x] #2 The Lake executable reads upstream compute commands from a file or stdin and prints weak-head normal forms. Tests cover α-equivalent parse and print round trips, parse and scope errors, and fuel exhaustion.
- [x] #3 Representative upstream compute fixtures pass through the executable, and `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Extend λΠ patterns and implement projection-based instantiation for pair binders.
2. Parse and print the upstream λΠ grammar and expose the bounded interpreter through Lake.
3. Check pattern binding, α-equivalent round trips, error handling, and upstream fixtures.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Verified with the Nix development shell on Lean 4.35.0. Both lake build and lake test passed. The executable parsed the unmodified upstream program, printed the three closed compute results, and reported unbound names in the two open compute commands. Stdin checks covered the upstream nested binder example, parse errors, duplicate names, and fuel exhaustion.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added recursive λΠ binder patterns, projection-based substitution, an upstream-style parser and printer, and a Lake executable for bounded weak-head evaluation. File and stdin checks passed. Check commands report that type checking is unimplemented, as in upstream.
<!-- SECTION:FINAL_SUMMARY:END -->
