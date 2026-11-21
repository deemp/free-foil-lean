---
id: TASK-001.06
title: Port MLTT module parameters and scope linking
status: To Do
assignee: []
created_date: '2026-11-21T21:07:51Z'
labels: []
dependencies:
  - TASK-001.05
references:
  - plan.md
parent_task_id: TASK-001
type: feature
ordinal: 7000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Use telescopes for parameters and reserved name ranges for independently checked modules.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Independently checked parameterized modules with a shared dependency link without renaming declarations.
- [ ] #2 Invalid and conflicting allocations are rejected, and `lake build` and `lake test` pass.
<!-- AC:END -->
