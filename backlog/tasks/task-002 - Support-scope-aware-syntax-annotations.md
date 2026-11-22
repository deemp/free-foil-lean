---
id: TASK-002
title: Support scope-aware syntax annotations
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:22'
updated_date: '2026-11-22 10:31'
labels:
  - annotations
  - library
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Free/Foil/Annotated.hs
documentation:
  - FreeFoil/Syntax.lean
  - README.md
  - FreeFoil/Annotated.lean
modified_files:
  - FreeFoil.lean
  - FreeFoil/Annotated.lean
  - FreeFoil/Tests/Annotated.lean
  - Test.lean
type: feature
ordinal: 12000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Syntax clients need source locations and semantic metadata such as inferred types. A type annotation can itself refer to local binders, so attaching it as ordinary metadata loses the scope guarantees Free Foil gives to terms.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Clients can attach source spans and annotations containing scope-checked terms at syntax nodes.
- [x] #2 Renaming and substitution update names referenced inside scoped annotations, including below a refreshed binder.
- [x] #3 Structural α-equivalence ignores annotation data, and an annotation-aware support operation includes names used only by annotations.
- [x] #4 Regression coverage includes binder collisions and dependencies used only by annotations. Library documentation shows a source span and a scoped type annotation.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add a signature extension for transparent annotation nodes with generic metadata and scope-checked term children. Embed ordinary ASTs and expose annotation construction and inspection in FreeFoil/Annotated.lean.
2. Reuse the existing AST renaming and substitution traversal so annotation terms and their host share the same lifted substitution under each binder. Provide structural erasure and α-equivalence plus annotation-aware support.
3. Document source spans and scoped types in the public module. Add regression coverage for scope dependencies, capture avoidance, and annotation-blind α-equivalence, and run Lake build and tests.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented annotations as an extension of the existing signature. A wrapper holds its subject and annotation terms as children in one scope, so the AST traversal handles binder lifting and capture avoidance for both. Structural α-equivalence erases wrappers before calling the existing checker.

The targeted annotation suite passes and checks source span retention, annotation-only support, alpha-equivalence across metadata types, and binder refresh during both renaming and compound substitution. The public source span and inferred type example also compiles.

Independently ran the documented span/type example and the annotation regressions. Verified that mapped free names stay free while bound names in both the annotation and subject follow the refreshed binder. The default build and test driver passed with Lean 4.35.0.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Expose scope-checked annotations through an annotated signature. Each annotation can carry metadata and terms, and it shares its subject’s scope. Existing renaming, substitution and support operations traverse those terms. Structural α-equivalence compares the erased subjects.

A documented span and inferred type example and regressions for binder refresh and annotation-only support exercise the public API.
<!-- SECTION:FINAL_SUMMARY:END -->
