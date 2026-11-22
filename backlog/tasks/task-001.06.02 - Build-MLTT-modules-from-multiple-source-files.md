---
id: TASK-001.06.02
title: Build MLTT modules from multiple source files
status: To Do
assignee: []
created_date: '2026-11-22 10:22'
labels:
  - mltt
  - cli
dependencies: []
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/src/Language/MLTT/Build.hs
documentation:
  - MLTTMain.lean
  - README.md
parent_task_id: TASK-001.06
type: feature
ordinal: 11000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The MLTT executable accepts one source at a time. Module projects need a single build that resolves imports across files and assigns reproducible declaration identifiers before caching or parallel checking is added.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 The CLI accepts multiple module source paths and resolves imports across those files in dependency order.
- [ ] #2 Permuting the input files for the same set of modules preserves module reservations and declaration identifiers.
- [ ] #3 Duplicate modules, missing imports, and import cycles are reported with the relevant module and source names when available.
- [ ] #4 Existing one-file and stdin invocations retain their behavior.
- [ ] #5 CLI regressions cover cross-file imports and reordered input. The README documents the multi-file invocation.
<!-- AC:END -->
