---
id: TASK-1.4
title: Port second-order abstract syntax
status: To Do
assignee: []
created_date: '2026-11-21T21:07:51Z'
labels: []
dependencies:
  - TASK-1.3
references:
  - plan.md
parent_task_id: TASK-1
type: feature
ordinal: 5000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend the Lean generator to cover SOAS and port the upstream substitution and constraint operations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Generation supports the mutually recursive SOAS term and type categories.
- [ ] #2 Upstream fixtures cover metavariable substitution, successful matching, and rejected constraints.
- [ ] #3 `lake build` and `lake test` pass.
<!-- AC:END -->
