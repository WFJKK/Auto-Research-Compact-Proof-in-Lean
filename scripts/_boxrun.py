"""Runs one command in the acceptance service's box. Standard library only.

    python3 -I _boxrun.py job.json

job.json: {"policy": {"read": [...], "read_write": [...], "own_proc": true} or null,
           "limits": {"RLIMIT_AS": bytes, "RLIMIT_CPU": seconds, ...}, "cwd": ..., "env": {...}, "cmd": [...]}

It sets the resource limits, takes away its own rights in landlock mode (no new privileges, no sockets,
reading only the policy's paths, writing only its read_write paths; `_harness.py` next to it is a copy of the
pipeline's core/harness.py), then replaces itself with the command. Nothing the command does can undo this.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    with open(sys.argv[1]) as f:
        job = json.load(f)
    sys.path.insert(0, HERE)
    import _harness

    for name, value in (job.get("limits") or {}).items():
        _harness._limit(name, value)
    if job.get("policy"):
        try:
            _harness._lockdown(job["policy"])
        except BaseException as exc:  # fail closed
            sys.stderr.write(f"the box could not be set up: {type(exc).__name__}: {exc}\n")
            os._exit(5)
    os.chdir(job["cwd"])
    cmd = job["cmd"]
    os.execve(cmd[0], cmd, job.get("env") or {})


if __name__ == "__main__":
    main()
