---
id: TASK-001.08
title: Prove generic substitution laws
status: To Do
assignee: []
created_date: '2026-11-21T21:07:52Z'
labels: []
dependencies: []
references:
  - plan.md
parent_task_id: TASK-001
type: feature
ordinal: 9000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove the substitution laws for arbitrary Free Foil signatures. This task can proceed alongside the example ports.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Identity substitution preserves a term up to α-equivalence.
- [ ] #2 Sequential substitution agrees up to α-equivalence with the composed substitution for open terms and under refreshed binders.
- [ ] #3 `lake build` and `lake test` pass.
<!-- AC:END -->
