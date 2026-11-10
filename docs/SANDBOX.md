# The sandbox

Recipes are code written by an agent, so they run apart from everything trusted: the checker, the model folders, the zoo's weights, the run folder and your API key. The code is in `core/sandbox.py`, `core/runner.py` and `core/harness.py`.

## Modes

| Mode | Where | How it keeps a recipe in |
| --- | --- | --- |
| `container` | Docker or Podman, any OS | No network, read-only root filesystem, only the sandbox folder mounted (its `out/` writable), runs as nobody with no capabilities, memory, CPU and process limits from the runtime. |
| `landlock` | Linux (x86_64 or aarch64), no root needed | Before the recipe is imported, the harness drops its own rights for good: no new privileges; seccomp allows no sockets at all; Landlock allows reading only the Python installation, system libraries and the sandbox folder, writing only the sandbox's `out/` and `tmp/`, and no ptrace or signals outside the sandbox. Of `/proc`, only the process's own entry is readable, so other processes' environments stay hidden. |
| `process` | anywhere | A plain separate process: `python -I -B`, an empty environment, a fresh folder, resource limits. **Weak**: the recipe runs as you and can read and write whatever you can, including the weights of held-out networks and your API key file. |

Every mode also gets: a wall-clock limit enforced from outside, a memory limit, limits on file size and CPU time, and a proof file read back as JSON data only (no links, pipes, NaN or duplicate keys; never executed or unpickled).

The run config's `sandbox` key picks the mode. The default, `auto`, takes the strongest one that works on the machine: `container` if a runtime and the image are present, then `landlock`, then `process`. `hardened` does the same but never falls back to `process`: with neither available, the run refuses to start. The configs for real agent runs use it, so a Docker that stopped while the machine slept makes a resume refuse instead of quietly running recipes in the weak mode.

## The probe

Each `run` and `resume` starts with a probe: a recipe that tries twelve escapes in the chosen mode. It tries to read the checker's source, another network's weights and a file in the run folder; to write into `core/`, the model folder, the run folder and your home folder; to make TCP and UDP connections to a listener on this machine; to read the loop's own environment through `/proc`; to import the checker; and to signal the loop. Escapes are judged only by evidence on the loop's side: bytes that match the real file, files that appear, packets that arrive.

If a hardened mode lets anything critical out, the run refuses to start. In `process` mode the escapes are reported as a warning, and the run goes on. Each probe report is appended to the run's `sandbox.jsonl`.

```bash
python -m core.sandbox info                                  # which modes work here
python -m core.sandbox probe --model models/max2 --mode landlock
```

Results on the build machine (Linux, kernel 6.18, Landlock ABI 7): `container` and `landlock` block all twelve attempts, and `process` lets all twelve out.

## Container image

```bash
python -m core.sandbox build            # docker; or --runtime podman
```

This builds `sandbox/Dockerfile` as `auto-research-compact-proof-sandbox:1`: `python:<your Python version>-slim` with the numpy and CPU-only torch versions pinned in `requirements.txt`. It needs internet access once, to pull the base image and the packages. `--init` is passed to every run, so the recipe is never the container's process 1.

**On a Mac** (no Landlock), install Docker Desktop and build the image; otherwise runs fall back to the weak `process` mode.

## The checker's side

- The checker runs in its own process (`core/check/worker.py`), one per attempt, started with `python -I -B -X pycache_prefix=<empty folder>`. It gets no environment, so no API key. It never reads compiled files lying next to the sources, so a planted `.pyc` (the hole an earlier audit of a similar pipeline found) is never loaded. A test plants one that an ordinary interpreter does run, and checks that the checker ignores it.
- The hashes of the trusted files (the checker, the diagnostics, the model folder, the sandbox code) are recorded when a run starts and checked again before every check. A mismatch halts the run, and `resume` refuses a run whose trusted files changed.
- Before every check, the loop also looks for compiled files written into `core/` or the model folder since it started. The loop itself writes none, so any it finds halts the run.
- The checker loads weights itself, by network id, with hash checks. A proof that names another network is rejected, and proof files have a size limit (`max_proof_mb`).

## Keeping a recipe's processes in

A recipe runs with a wall-clock limit (from outside), a CPU limit, a memory limit, a file-size limit and a process-count ceiling (`RLIMIT_NPROC`, against a fork bomb). A child that calls `setsid()` to leave the harness's process group would escape a plain group-kill, so on Linux the runner makes itself a subreaper and tags every process the recipe starts with a unique id; at teardown it kills everything carrying that id, reparented or not. A test plants a `setsid()` child and checks it does not outlive the sandbox. In `container` mode the PID namespace does this instead, so the whole tree dies with the container.

## The checker cannot be wedged by a proof

The checker is trusted, but it reads an untrusted proof, so a proof must not be able to stall or crash it:

- Every number in a proof is dyadic and bounded, so the exact arithmetic stays cheap (see `docs/RULES.md`); a short string cannot name a huge number.
- `check_proof` rejects a hostile proof as a whole: any error from proof data, including out-of-range or out-of-memory arithmetic, becomes a rejection, never an exception that reaches the run. The checker's own soundness invariants stay fatal.
- The checker process has a memory ceiling, and each proof has a wall-clock limit (`check_timeout_s`, default 600 s). A proof that exceeds it is rejected and the worker is restarted, so one slow proof cannot wedge an unattended run.

## Known limits

- `process` mode protects nothing against a recipe that means harm. Use it only for recipes you trust, such as the baselines and tests.
- In `landlock` mode, recipes can read system folders such as `/etc` and `/sys`, but none of the pipeline's files and no other process's `/proc` entry. Landlock is refused when the Python installation's folders contain the repository, the runs folder or the model folder. A determined `setsid()` escapee is reaped at teardown on Linux, where the subreaper can find it; the surest containment for fully untrusted recipes is `container` mode, whose PID namespace needs no such sweep.
- In `container` mode, the runner can't measure a recipe's peak memory, and a recipe killed by the memory limit is reported as killed by SIGKILL.
- Each hole found later gets its own test in `tests/test_adversarial.py` (recipe sandbox) or `tests/test_hardening.py` (the checker).
