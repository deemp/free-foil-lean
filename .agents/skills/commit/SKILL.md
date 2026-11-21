---
name: commit
description: Commit staged Git changes when invoked or when the user requests a commit in this repository.
---

# Commit staged changes

## Check the index

Run `git diff --cached --quiet --` first. If it exits with status 0, tell the
user there are no staged changes, suggest `git add -- <paths>`, and stop. An
exit status of 1 means there are staged changes. Report any other status as
an error and stop. Leave staging to the user.

## Write the commit message

Review `git diff --cached` before drafting the message. Use a concise subject
that names the change and a detailed body that explains what changed, why,
and the key decisions that shaped the implementation. Include relevant
tradeoffs and verification results when they help a reader understand the
change. For a small change, explain the specific choice and its reason.

After a blank line, end every message with these two consecutive lines in
this order.

```text
Harness: <harness>
Model: <model>
```

From the repository root, run `python3 scripts/commit-metadata.py` to get
both lines from the active Codex session. If discovery fails, use other
verified session information and ask for any value you cannot verify. Keep
the `Model:` line last.

## Create the commit

Check that the body matches the staged changes and that both final lines
have the correct values. Run `git commit -F <message-file>` to commit the
index, then report the resulting commit hash and subject. If Git rejects the
commit, report the error.
