---
id: TASK-1.5
title: Port the core MLTT evaluator and type checker
status: To Do
assignee: []
created_date: '2026-11-21T21:07:51Z'
labels: []
dependencies:
  - TASK-1.4
references:
  - plan.md
parent_task_id: TASK-1
type: feature
ordinal: 6000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run the standalone MLTT core examples using the Lean implementation.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 The evaluator and bidirectional type checker pass upstream core examples for inference, checking, and definitional equality.
- [ ] #2 `lake build` and `lake test` pass.
<!-- AC:END -->
