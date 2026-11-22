---
id: TASK-001.04.01
title: Solve the SOAS metavariable pattern fragment
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 10:38'
labels:
  - soas
  - unification
dependencies: []
references:
  - 'https://github.com/fedor-ivn/free-foil-hou'
  - 'https://arxiv.org/abs/2405.16384'
documentation:
  - FreeFoil/Examples/SOAS.lean
  - README.md
modified_files:
  - FreeFoil/Examples/SOAS.lean
  - FreeFoil/Tests/SOAS.lean
  - README.md
parent_task_id: TASK-001.04
type: feature
ordinal: 14000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The SOAS example can apply and validate a supplied metavariable substitution. A solver for the fragment where metavariables are applied to distinct bound variables lets clients obtain substitutions for scoped equations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 The solver produces a well-scoped metavariable substitution for supported solvable equations, including `?F[x] = f(x)` with `f` a rigid unary operator.
- [x] #2 Rigid mismatches, cyclic assignments, and assignments requiring an out-of-scope bound variable are rejected.
- [x] #3 Metavariable applications outside the supported pattern fragment receive a distinct outcome.
- [x] #4 Every returned solution is proved in Lean to satisfy its input equations according to the constraint checker.
- [x] #5 Regression coverage includes multiple constraints, renamed binders, a cyclic equation, and an out-of-fragment application. The README describes the supported fragment.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Validate SOAS metavariable applications across the input equations. Accept only distinct variable arguments with a consistent arity per metavariable, and report invalid applications separately from unsatisfiable equations.
2. Solve a shared worklist using scope-safe AST operations. Decompose rigid nodes and open corresponding binders with common fresh names, check cycles and escaping rigid variables, and restrict each assignment body to the metavariable's ordered parameters. Handle flex-flex equations and prune unavailable arguments of flexible occurrences via fresh residual metavariables. Compose assignments for the simultaneous substitution checker.
3. Expose a result containing the substitution and a Lean proof that isSolutionFor returned true for the original equations. Distinguish failure reasons and bound solver work using an explicit optional fuel budget.
4. Add SOAS fixtures for unary solutions, shared constraints, renamed binders, pruning, cycles, escaping variables, rigid mismatches, and invalid applications. Document use and verify the targeted and default Lean build.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented a shared worklist over scope-safe terms. Rigid nodes decompose under freshly aligned binders. Flexible assignments are narrowed to their parameters and composed for simultaneous application. Flexible occurrences may be projected onto available arguments through fresh residual metavariables.

Verified the pinned Lean 4.35.0 build and runtime of FreeFoil.Tests.SOAS against the committed Derive API in an isolated scratch directory. Fixtures cover direct unary assignment, composition across renamed binders, flexible intersections and projections, rigid mismatch, cycles, shadowing-related escaping variables, and non-pattern arguments.

Reviewed the constraint checker proof carried by every success and independently ran the SOAS regression module with Lean 4.35.0. The regression checks passed for the unary example, composed assignments, binder alignment and error outcomes.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Solve SOAS constraints whose metavariables take distinct variables at a fixed arity. The solver aligns binders, checks scope and cycles, and composes simultaneous substitutions. Flexible equations can project away unavailable arguments through fresh metavariables.

A successful result carries Lean evidence that the existing constraint checker accepts the original equations. The README documents the supported applications and fuel budget.
<!-- SECTION:FINAL_SUMMARY:END -->
