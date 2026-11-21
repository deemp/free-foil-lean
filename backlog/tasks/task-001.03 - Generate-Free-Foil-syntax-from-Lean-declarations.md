---
id: TASK-001.03
title: Generate Free Foil syntax from Lean declarations
status: To Do
assignee: []
created_date: '2026-11-21T21:07:50Z'
labels: []
dependencies:
  - TASK-001.02
references:
  - plan.md
parent_task_id: TASK-001
type: feature
ordinal: 4000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Replace the handwritten λΠ syntax plumbing with generated signatures, helpers, and conversions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Generation covers binder positions and recursive pair patterns. Generated conversion reports duplicate binders.
- [ ] #2 The generated λΠ syntax passes its parser, conversion, and evaluation regressions, and `lake build` and `lake test` pass.
<!-- AC:END -->
