---
id: TASK-001.04
title: Port second-order abstract syntax
status: Done
assignee:
  - Codex
created_date: '2026-11-21T21:07:51Z'
updated_date: '2026-11-21 21:53'
labels: []
dependencies:
  - TASK-001.03
references:
  - plan.md
modified_files:
  - FreeFoil/Derive.lean
  - FreeFoil/Examples/SOAS.lean
  - FreeFoil/Tests/SOAS.lean
  - README.md
  - Test.lean
  - lakefile.toml
parent_task_id: TASK-001
type: feature
ordinal: 5000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend the Lean generator to cover SOAS and port the upstream substitution and constraint operations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Generation supports the mutually recursive SOAS term and type categories.
- [x] #2 Upstream fixtures cover metavariable substitution, successful matching, and rejected constraints.
- [x] #3 `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Extend `FreeFoil.Derive` to generate a shared signature, helpers and structurally recursive codecs from a family of ordinary Lean inductives. Classify explicit fields as same-family children, scoped children or nonrecursive payloads, preserve the single-sort λΠ command, and validate categories during reverse conversion.
2. Declare upstream SOAS terms, types, lists and binder-bearing operator arguments in Lean. Preserve the upstream grammar, which connects terms and types through typing judgments, and exercise direct cross-category recursion in a generator regression.
3. Port simultaneous metavariable substitution using the generated operators and `ScopedAST.instantiate`, and check equations with positional α-matching. Verify known metavariable arity before instantiation.
4. Run `lake build` and `lake test` on Lean 4.35.0. Transcribe the upstream nested substitution and true/false equation fixtures, including the two-name positional binder case, and exercise the generated codecs.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The family command reuses the single-inductive generator and emits category-qualified constructors for a shared scope-checked signature. Reverse conversion verifies each declared child category. The upstream SOAS grammar relates term and type syntax in typing judgments. A separate regression exercises direct recursion between two declared categories and rejects a generated tree with a term in a type position.

Matched the upstream fdfbeef SOAS nested substitution and true/false constraint doctests with Lean constructor fixtures. The test driver also checks two-name binding order, rigid operator and metavariable identifiers, duplicate binders, simultaneous insertion behavior, and malformed metavariable arity. `lake test`, `lake build`, and the three closed upstream lambdaPi compute fixtures passed on Lean 4.35.0.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Extended `derive_free_foil` to generate one signature and checked decoders for syntax families. The SOAS port uses the generated term, type, and argument constructors for simultaneous metavariable substitution and α-equivalence-based constraint checking.

The suite ports the upstream substitution and positive and negative matching fixtures. It also checks genuine cross-category recursion and rejects a term used as a type in a generated decoder. `lake build` and `lake test` passed on Lean 4.35.0, and the closed λΠ upstream compute fixtures still passed.
<!-- SECTION:FINAL_SUMMARY:END -->
