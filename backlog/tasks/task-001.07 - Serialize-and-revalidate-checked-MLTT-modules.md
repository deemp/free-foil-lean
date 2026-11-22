---
id: TASK-001.07
title: Serialize and revalidate checked MLTT modules
status: Done
assignee:
  - codex
created_date: '2026-11-21T21:07:51Z'
updated_date: '2026-11-22 10:17'
labels: []
dependencies:
  - TASK-001.06
references:
  - plan.md
modified_files:
  - FreeFoil/Examples/MLTT.lean
  - FreeFoil/Examples/MLTT/Artifact.lean
  - FreeFoil/Examples/MLTT/Module.lean
  - FreeFoil/Tests/MLTT.lean
  - README.md
  - backlog/tasks/task-001.07 - Serialize-and-revalidate-checked-MLTT-modules.md
parent_task_id: TASK-001
type: feature
ordinal: 8000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Load previously checked modules while enforcing the scope and dependency invariants at the decoding boundary.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Checked modules survive a serialization and loading round trip.
- [x] #2 Loading revalidates terms and references, and rejects missing dependencies and invalid or conflicting name allocations.
- [x] #3 `lake build` and `lake test` pass.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Encode a checked module's reservation, imports, and ordered declarations using a versioned JSON envelope. Serialize each type and value with lexical levels for bound references and unchanged numeric IDs for free references, so the bytes are independent of incidental binder names.
2. Record checksums for checked imports and their dependency closure. Verify them against the supplied environment when loading, and diagnose missing or changed imports before replaying declarations.
3. Decode terms with explicit operator and pattern arity checks. Reconstruct each declaration in its preceding scope, limiting free references to direct imports and declarations already replayed. Reuse allocation and type checking from source checking, and publish the resulting module only once every declaration is valid.
4. Exercise a parameterized shared-dependency round trip and the linked client, then cover malformed and ill-typed terms, missing and changed dependencies, forbidden references, and invalid or conflicting allocations. Run the Lean 4.35.0 build and test suite.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The version 1 JSON format keeps global declaration identifiers at their original reservations and encodes binding occurrences at lexical levels. A canonical manifest covers the checked contents of direct and transitive imports. Loading verifies the manifest, resolves terms in the prefix environment, and rechecks types and values before publishing the module.

The Lean 4.35.0 default build and test driver passed. The artifact tests restore both independent branches of a diamond, exercise three distinct positions of a nested pair binder, and verify identical bytes when unrelated declarations are in scope. They also cover missing and changed imports, invalid bound or global references, malformed child arity, ill-typed terms, and invalid, duplicate, or overlapping allocations. The core and parameter fixtures produced four and five unit normal forms from both CLI input paths.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added a versioned JSON format for checked MLTT declarations. Artifacts preserve numeric declaration IDs and reservations, use canonical lexical levels for binders, and record checksums for the transitive dependency closure. Loading validates the manifest, syntax tree shape, scope, allocation order, and types before publishing the module.

On Lean 4.35.0, the default build and tests pass. A client computed through both restored branches of a shared-dependency diamond. Independent checks replayed the upstream core artifact and verified rejection of missing imports, forbidden references, malformed scopes, ill-typed values, invalid IDs, and overlapping reservations.
<!-- SECTION:FINAL_SUMMARY:END -->
