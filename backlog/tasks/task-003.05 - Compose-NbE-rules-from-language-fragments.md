---
id: TASK-003.05
title: Compose NbE rules from language fragments
status: Done
assignee:
  - Codex
created_date: '2026-11-22 15:34'
updated_date: '2026-11-22 22:14'
labels:
  - nbe
dependencies:
  - TASK-003.01
  - TASK-003.02
references:
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/src/FreeFoil/NbE/Sum.hs
  - >-
    https://github.com/p50000/free-foil-NBE/tree/75e7855a6dc03723ff0198f55774eda50e627249/demo/Fragments
  - >-
    https://github.com/p50000/free-foil-NBE/blob/75e7855a6dc03723ff0198f55774eda50e627249/baselines/Monolith.hs
documentation:
  - free-foil-repos/free-foil-NBE/src/FreeFoil/NbE/Sum.hs
  - free-foil-repos/free-foil-NBE/test/Test/Fragments.hs
  - free-foil-repos/free-foil-NBE/test/Test/Monolith.hs
parent_task_id: TASK-003
type: feature
ordinal: 25000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
An object language assembled from reusable syntax fragments needs the same reduction behavior as a language written in one signature. The generic normalizer and the standalone demos supply the evaluation interface and the function, pair, and natural-number behavior to reuse.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 A fragment can supply rules once for use in any composed signature that contains it. The composed language inherits those rules from its fragments.
- [x] #2 The Lean example combines functions, pairs, and naturals and reduces mixed-fragment terms under a shared binder vocabulary.
- [x] #3 The composed demo accepts representative upstream monolith inputs. Tests compare its normal forms with those of a single-signature reference up to α-equivalence.
- [x] #4 The documentation shows how to add a fragment and evaluate a composed-language term.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
Translate the upstream signature sums and fragment positions into Lean with shape- and arity-preserving embeddings. Use them to dispatch reusable function, pair, and natural elimination rules over a shared binder vocabulary, including defined principals. Add an upstream-style mixed-language demo and compare its normal forms with a flat single-signature reference. Document how to supply a fragment and run the demo.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Verified full and weak-head normal forms against the independently dispatched flat reference and pinned upstream examples. Ran the default build, test driver, and both README examples with Lean 4.35.0.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added arity-preserving operator embeddings and composable NbE fragments. The mixed demo runs function, pair, and natural rules over a shared pattern vocabulary and uses the pinned monolith syntax. Pair and natural rules are shared with their standalone demos. The flat reference dispatches independently. Tests compare normal forms up to α-equivalence and exercise η, weak-head readback, malformed binder arities, and defined principals.
<!-- SECTION:FINAL_SUMMARY:END -->
