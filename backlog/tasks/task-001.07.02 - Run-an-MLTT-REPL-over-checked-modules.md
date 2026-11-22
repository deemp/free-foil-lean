---
id: TASK-001.07.02
title: Run an MLTT REPL over checked modules
status: To Do
assignee: []
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 10:23'
labels:
  - mltt
  - cli
dependencies:
  - TASK-001.07.01
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/src/Language/MLTT/Build.hs
documentation:
  - MLTTMain.lean
  - FreeFoil/Examples/MLTT/Artifact.lean
  - README.md
parent_task_id: TASK-001.07
type: feature
ordinal: 19000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Batch builds and the artifact cache make checked modules available across commands and sessions. An interactive session lets users import those modules, try queries, and build up local definitions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 The CLI can start an interactive session over a completed MLTT build.
- [ ] #2 The session accepts `def`, `check`, and `compute`, and successful definitions remain available to subsequent commands.
- [ ] #3 An explicit `import` makes a built module visible to the session and can load a cached module with its required dependencies.
- [ ] #4 A rejected command or import produces a diagnostic and preserves the last valid session state.
- [ ] #5 Integration coverage exercises an import followed by a query and recovery after an error. The README documents how to start and use the session.
<!-- AC:END -->
