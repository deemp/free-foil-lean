---
id: TASK-001.03.01
title: Derive Free Foil syntax for nested and parameterized inductives
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 15:03'
labels:
  - deriving
  - library
dependencies: []
references:
  - 'https://arxiv.org/abs/2405.16384'
documentation:
  - FreeFoil/Derive.lean
  - README.md
modified_files:
  - FreeFoil/Derive.lean
  - FreeFoil/Tests/Derive.lean
  - README.md
  - Test.lean
parent_task_id: TASK-001.03
type: feature
ordinal: 13000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Syntax authors currently need auxiliary inductives for recursive fields inside common containers and cannot derive directly from parameterized source declarations. Supporting both shapes lets clients keep more of their existing Lean syntax definitions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 `derive_free_foil` accepts recursive fields under `List` and `Option`, including scoped children, while preserving child order and binding scope.
- [x] #2 Derivation accepts syntax inductives with ordinary type parameters and preserves the parameters in the generated interfaces.
- [x] #3 Generated conversions round-trip supported declarations and reject malformed input with a child from the wrong category.
- [x] #4 Unsupported declaration forms receive a targeted diagnostic.
- [x] #5 Regression coverage exercises nested fields and parameterized syntax. The README documents the supported declaration shapes and parameter constraints.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Extend declaration analysis to resolve uniform type parameters and recursive field layouts, including nested List and Option positions and scoped leaves. Diagnose indexed, dependent, nonuniform, and unsupported recursive forms.
2. Record container shapes in each operator and compute arities from them. Generate helpers and codecs that preserve container order and flow all recursive children through the ordinary or scoped positions of the shared signature.
3. Preserve current interfaces for existing declarations and extend generated interfaces for parameterized sources. Test nested and parameterized round-trips, binding scope, malformed child categories, and targeted diagnostics, and document supported forms in the README.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Independently compiled and ran the deriving regression module. It checks nested shapes and scoped child order, parameterized payloads and equality, wrong-category rejection in ordinary and scoped containers, and an unsupported recursive field diagnostic.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Derive Free Foil syntax for uniform type parameters and recursive fields nested in lists and options. Generated operators record container shapes, helpers preserve child order, and conversions retain local binder scopes and reject children in the wrong category. Fixed payload types can use the source parameters.

Regressions exercise single and mutual declarations, scoped and ordinary children, parameterized payloads, and unsupported recursive fields. The README describes the generated interfaces and universe constraints.
<!-- SECTION:FINAL_SUMMARY:END -->
