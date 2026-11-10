"""Runs one module inside a check box. Not trusted: it shares its process with the candidate rule.

core.rules_route.box copies this file into the box as _launcher.py, next to a copy of core/harness.py
(_harness.py, for its lockdown) and job.json, and starts it with `python -I -B _launcher.py job.json`:

    {"policy": {...} or null, "limits": {"RLIMIT_AS": bytes, ...}, "sys_path": [...], "cwd": ...,
     "module": "core.rules_route.audit", "argv": [...]}

It sets the resource limits, takes away its own rights in landlock mode (no new privileges, no sockets,
reading only the policy's paths, writing only the box's out/ and tmp/), and runs the module as __main__.
Standard library only; it imports nothing from the core before the lockdown.
"""

import json
import os
import runpy
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
            sys.stderr.write(f"the check box could not be set up: {type(exc).__name__}: {exc}\n")
            os._exit(5)
    sys.path.remove(HERE)
    for p in reversed(job["sys_path"]):
        sys.path.insert(0, p)
    os.chdir(job["cwd"])
    sys.argv = [job["module"]] + list(job["argv"])
    runpy.run_module(job["module"], run_name="__main__", alter_sys=True)


if __name__ == "__main__":
    main()
