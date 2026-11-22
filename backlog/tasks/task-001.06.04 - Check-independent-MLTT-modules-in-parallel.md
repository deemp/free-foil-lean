---
id: TASK-001.06.04
title: Check independent MLTT modules in parallel
status: To Do
assignee: []
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 10:23'
labels:
  - mltt
  - cli
dependencies:
  - TASK-001.06.02
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/src/Language/MLTT/Build.hs
documentation:
  - FreeFoil/Examples/MLTT/Module.lean
  - README.md
parent_task_id: TASK-001.06
type: feature
ordinal: 18000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The multi-file builder supplies the dependency graph and stable name reservations. The existing linker allows modules that share completed dependencies to be checked independently and combined.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 A parallel build mode checks independent modules concurrently and waits for imports before checking a dependent module.
- [ ] #2 Sequential and parallel builds produce equivalent checked declarations with the same identifiers and deterministic reported results.
- [ ] #3 Failed checks identify the failing module and prevent its dependents from being checked against an incomplete environment.
- [ ] #4 Regression coverage exercises a shared-dependency diamond and a failing branch. The README documents how to select parallel mode.
<!-- AC:END -->
