---
id: TASK-001.07.02
title: Run an MLTT REPL over checked modules
status: Done
assignee:
  - Codex
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 15:29'
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
modified_files:
  - FreeFoil/Examples/MLTT/Program.lean
  - FreeFoil/Examples/MLTT/Module.lean
  - FreeFoil/Examples/MLTT/Cache.lean
  - FreeFoil/Tests/MLTTCache.lean
  - MLTTMain.lean
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
- [x] #1 The CLI can start an interactive session over a completed MLTT build.
- [x] #2 The session accepts `def`, `check`, and `compute`, and successful definitions remain available to subsequent commands.
- [x] #3 An explicit `import` makes a built module visible to the session and can load a cached module with its required dependencies.
- [x] #4 A rejected command or import produces a diagnostic and preserves the last valid session state.
- [x] #5 Integration coverage exercises an import followed by a query and recovery after an error. The README documents how to start and use the session.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add `--repl` to start a session over a successful sequential, parallel, or cached build. Allow a cache-only session to load modules on demand.
2. Reuse the module parser and command checker for one instruction per line. Allocate local definitions above the known module reservations. Expose explicitly imported names, restore missing dependencies under the shared cache lock, and validate all artifacts before publishing the updated session.
3. Add integration coverage for source and cache imports, persistent definitions, and recovery after invalid commands or stale imports. Document invocation and session syntax in the README.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Independent CLI review covered a terminal prompt and EOF, source and parallel startup, and cache-only imports. A live stale-cache probe verified that neither of two restored dependencies entered the session when the requested artifact failed, and that earlier definitions remained usable.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added `mltt --repl` to explore checked builds and caches. A session accepts one `import`, `def`, `check`, or `compute` per line and retains successful definitions. Cache imports restore dependencies in order and check their manifests and reservations. A rejected instruction preserves the current session.

`lake build` and `lake test` passed. Integration tests cover explicit visibility, source and warm cache builds, cached-only dependencies, and recovery from command and import failures.
<!-- SECTION:FINAL_SUMMARY:END -->
