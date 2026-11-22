---
id: TASK-001.07.01
title: Reuse checked artifacts across MLTT builds
status: Done
assignee:
  - codex
created_date: '2026-11-22 10:23'
updated_date: '2026-11-22 15:06'
labels:
  - mltt
  - cli
dependencies:
  - TASK-001.06.02
references:
  - >-
    https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/src/Language/MLTT/Build.hs
documentation:
  - FreeFoil/Examples/MLTT/Artifact.lean
  - README.md
  - FreeFoil/Examples/MLTT/Cache.lean
modified_files:
  - FreeFoil/Examples/MLTT.lean
  - FreeFoil/Examples/MLTT/Cache.lean
  - FreeFoil/Tests/MLTTCache.lean
  - MLTTMain.lean
  - README.md
  - Test.lean
parent_task_id: TASK-001.07
type: feature
ordinal: 17000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The multi-file builder supplies the module graph and deterministic reservations. Users need repeated builds to reuse validated modules from disk and retain stable identifiers as the project grows.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 An optional cache directory stores checked module artifacts and reuses them on a subsequent build with unchanged inputs.
- [x] #2 An edit invalidates the edited module and invalidates dependents when the checked dependency changes. Changes that leave the checked dependency equivalent allow its dependents to be reused.
- [x] #3 Unchanged modules retain their declaration identifiers across incremental builds that add unrelated modules.
- [x] #4 Missing, stale, or invalid cache entries fall back to source checking. Failed checks cannot publish a replacement artifact.
- [x] #5 Regression coverage exercises cold and warm builds, dependency changes, and corrupted cache entries. The README explains cache reuse and whether cached commands are replayed.
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add an optional --cache directory to MLTT module project builds. Use the parsed, expanded module as the source key, including every parameter field, all commands, and the check fuel. Keep normal one-file, stdin, and multi-file invocations on their existing paths.
2. Retain module reservations in a versioned cache index. Preserve adequate reservations, allocate new or grown modules beyond existing ranges, and plan imports using the existing module builder. Serialize concurrent cache users with a directory lock.
3. Load versioned, integrity-checked cache entries only when their source and planned module match. Revalidate artifacts and dependency manifests using the existing loader. Store successful command results with the artifact, and replay them on a hit. Fall back to source on a miss, and publish only after all modules have checked successfully using atomic file replacement.
4. Cover cold and warm CLI builds, semantic and equivalent dependency edits, stable IDs after adding an unrelated module, corrupt entries, and failed checks. Document cache reuse, reservations, and command output replay.
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The cache uses the parsed module after telescope expansion, with exact source JSON compared on a hit. Deriving its parameter encoding covers fixedValue as well as ordinary fields. Source whitespace and comments are ignored. A hit revalidates the stored artifact against the current transitive dependencies and replays recorded command output.

The reservation index is independent of per-module artifact files. It retains adequate ranges across builds, and an exclusive directory lock serializes writers. Updates are written by atomic rename only after source checking succeeds for the whole project.

Verified with the pinned Lean 4.35.0 and GCC 16 environment using lake build and lake test. Regressions cover cold and warm CLI runs, a provider binder rename that reuses its client, dependency payload changes, original IDs after unrelated additions, corrupt entries, failed publication, and expanded or refined telescope fields.

Independently ran the default build and regression driver, including cold and warm reuse, alpha-equivalent and changed dependencies, reserved IDs, corrupted entries, and failed publication. Four concurrent CLI invocations over one fresh cache produced identical output and complete cache entries.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Add an optional filesystem cache for MLTT project builds. Revalidate artifacts against checked dependencies and persist declaration reservations as unrelated modules are added. Rebuild on missing, stale or invalid data and publish replacements after a successful project check.

The README explains the expanded-source cache key and command output replay. Library and CLI checks exercise cold and warm builds, invalidation, corruption and stable IDs.
<!-- SECTION:FINAL_SUMMARY:END -->
