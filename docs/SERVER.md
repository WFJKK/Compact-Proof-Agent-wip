# Running pilots on a server

An open-lane pilot makes a model call at every step, so it only progresses while the machine running it is
online. A laptop that travels or sleeps loses hours to retries and stops after about four hours offline
(`resume` continues it, but nothing happens in between). A small always-on Linux server fixes that, and gives
the service its proper sandbox (Landlock), which a Mac cannot.

## The machine

Any Ubuntu 24.04 VM with 4 or more cores, 16 GB of memory and 60 GB of disk. Lean candidates compile at up to
about 6 GB (the service allows 12 GB of address space per compile), and Mathlib's prebuilt files take about
10 GB of disk. No GPU. For attention networks take 32 GB (Hetzner's CPX62: 16 cores, 32 GB): there the
kernel's memory is the limit (models/attn-min2/config.yaml: at vocabulary size 64 and width 8, one pass over
the 512-entry embedding takes 2.1 GB, and the general single rule on one input did not fit in 7 GB). Cloud providers such as Hetzner bill a machine like this by the hour, up to a monthly
cap, until it is deleted (check the provider's current price); delete it when the series is done, after copying
the run folders home.

## Setup, once

Log in over ssh as a user with `sudo`, then

    curl -fsSL https://raw.githubusercontent.com/WFJKK/Compact-Proof-Agent-wip/main/scripts/server_setup.sh | bash

The script (idempotent: run it again if interrupted) installs the system packages, Lean through elan, the Lean
project at the commit the pipeline was tested with (e79a9a0; `LEAN_COMMIT=<commit>` before the command takes
another) with Mathlib's prebuilt cache and every module of its library but the tutorial (the rule on proofs
asks Lean about all of them), `compactcheck`, `acceptcheck` and the tactic modules the agents' proofs import,
the pipeline (Compact-Proof-Agent-wip) in a virtual environment with its pinned packages, tmux, and the Claude
Code CLI. It clones both repositories to the paths the pilot configs name on the Mac
(`~/Desktop/VerifiedMechanisms/...`), so nothing in a config needs editing and every command in
docs/OPEN_LANE.md is the same. About five minutes on an 8-core machine, most of it Lean.

Then sign in to Claude Code: run `claude` and choose a login. On a headless server it prints a link to open on
any device (the laptop, the phone) and asks for the code shown there. `claude auth status` must then report a
login; the loop checks it before every run, and never passes an API key to the CLI (its environment has them
removed), so the login is what pays.

- "Anthropic Console account": the API, billed per token to the Console organisation. Set a spend limit on
  the workspace first. Each session's dollar figure is in its `response_meta.json` (`api_equivalent_usd`, the
  CLI's own figure); `cost_usd` stays 0 there.
- An API key, with no sign-in at all: `export CPL_ANTHROPIC_KEY=sk-ant-...` (never `ANTHROPIC_API_KEY`) and start
  the run with `--auth api_key --budget-usd <dollars>`. The run checks the key before it starts and stops itself
  when the budget is spent (docs/BACKENDS.md). Several runs may use one key at once: they share the
  organisation's rate limits and bill, each run keeps its own budget.
- The subscription: no per-call bill; the runs count against its usage limits, and the loop waits when it hits
  one (docs/BACKENDS.md, including the note on Anthropic's terms).

## Running

Always inside tmux, so the run survives the ssh session:

    tmux new -s pilot
    cd ~/Desktop/VerifiedMechanisms/CompactProofsAgent/Compact-Proof-Agent-wip && source .venv/bin/activate
    python3 -m pytest tests/test_open_lane.py      # the pair works together: a few minutes
    python3 -m core.loop run --config config/pilot/attn-min2-quick.yaml

`--set` changes a setting for this run only, without editing the config (a run with a model backend starts
only from a clean commit, so an edited config on the server would be refused); the run folder records it.
Detach with Ctrl-B then D; the run keeps going. Later, from anywhere:

    ssh <server>
    tmux attach -t pilot                           # watch it
    python3 -m core.loop status --run ~/auto-research-compact-proof-runs/<run_id>

Runs one after another, not at the same time: they share the login's limits, and two at once only wait
twice. If the machine reboots, `python3 -m core.loop resume --run ~/auto-research-compact-proof-runs/<run_id>`
continues the run from its last finished round.

## Updating

Pull both repositories and rebuild the Lean targets (the script's commands, or run the script again). A run
refuses to resume if the Lean project changed under it (`lean-checker.lock`), so update between runs, not
during one.

## Bringing results home

    scp -r <server>:auto-research-compact-proof-runs/<run_id> ~/auto-research-compact-proof-runs/

The run folder holds the archive, every receipt, the agent's notes and tool logs; `python3 -m core.report` and
`python3 -m core.rescore` work on the copy.
