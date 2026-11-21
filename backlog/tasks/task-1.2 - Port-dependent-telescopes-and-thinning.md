---
id: TASK-1.2
title: Port dependent telescopes and thinning
status: To Do
assignee: []
created_date: '2026-11-21T21:07:50Z'
labels: []
dependencies:
  - TASK-1.1
references:
  - plan.md
parent_task_id: TASK-1
type: feature
ordinal: 3000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build the reusable context machinery for dependent module parameters and restricting terms to their support.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Telescope payloads can refer to earlier binders. Scope extension, renaming, and α-equivalence account for those dependencies.
- [ ] #2 Thinning (A : 𝕌) (x : A) (B : 𝕌) for a term using only x retains A and x in order, drops B, and keeps the term and retained payloads well scoped.
- [ ] #3 `lake build` and `lake test` pass.
<!-- AC:END -->
