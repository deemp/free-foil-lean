---
id: TASK-001.07.01
title: Reuse checked artifacts across MLTT builds
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
  - FreeFoil/Examples/MLTT/Artifact.lean
  - README.md
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
- [ ] #1 An optional cache directory stores checked module artifacts and reuses them on a subsequent build with unchanged inputs.
- [ ] #2 An edit invalidates the edited module and invalidates dependents when the checked dependency changes. Changes that leave the checked dependency equivalent allow its dependents to be reused.
- [ ] #3 Unchanged modules retain their declaration identifiers across incremental builds that add unrelated modules.
- [ ] #4 Missing, stale, or invalid cache entries fall back to source checking. Failed checks cannot publish a replacement artifact.
- [ ] #5 Regression coverage exercises cold and warm builds, dependency changes, and corrupted cache entries. The README explains cache reuse and whether cached commands are replayed.
<!-- AC:END -->
