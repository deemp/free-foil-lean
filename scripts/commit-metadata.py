#!/usr/bin/env python3
"""Print commit trailers for the active Codex session."""

import json
import os
import sys
from pathlib import Path
from uuid import UUID


def read_session_metadata():
    thread_id = os.environ.get("CODEX_THREAD_ID")
    if not thread_id:
        raise ValueError("CODEX_THREAD_ID is unset")
    thread_id = str(UUID(thread_id))

    codex_home = Path(os.environ.get("CODEX_HOME") or Path.home() / ".codex")
    rollouts = list((codex_home / "sessions").rglob(f"rollout-*-{thread_id}.jsonl"))
    if len(rollouts) != 1:
        raise ValueError(f"expected one rollout for the active thread, found {len(rollouts)}")

    harness = model = None
    with rollouts[0].open(encoding="utf-8") as rollout:
        for line in rollout:
            event = json.loads(line)
            if event.get("type") == "session_meta":
                metadata = event["payload"]
                if metadata.get("id") != thread_id:
                    raise ValueError("the rollout belongs to a different thread")
                harness = metadata.get("originator")
            elif event.get("type") == "turn_context":
                model = event["payload"].get("model")

    for label, value in (("harness", harness), ("model", model)):
        if not isinstance(value, str) or not value.strip() or value.splitlines() != [value]:
            raise ValueError(f"the active rollout has no usable {label}")
    return harness, model


if __name__ == "__main__":
    try:
        harness, model = read_session_metadata()
    except (AttributeError, KeyError):
        sys.exit("commit-metadata: the rollout has an invalid record")
    except (OSError, ValueError) as error:
        sys.exit(f"commit-metadata: {error}")
    print(f"Harness: {harness}\nModel: {model}")
