---
id: TASK-1.7
title: Serialize and revalidate checked MLTT modules
status: To Do
assignee: []
created_date: '2026-11-21T21:07:51Z'
labels: []
dependencies:
  - TASK-1.6
references:
  - plan.md
parent_task_id: TASK-1
type: feature
ordinal: 8000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Load previously checked modules while enforcing the scope and dependency invariants at the decoding boundary.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Checked modules survive a serialization and loading round trip.
- [ ] #2 Loading revalidates terms and references, and rejects missing dependencies and invalid or conflicting name allocations.
- [ ] #3 `lake build` and `lake test` pass.
<!-- AC:END -->
