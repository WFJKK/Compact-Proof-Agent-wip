# Running pilots on a server

An open-lane pilot makes a model call at every step, so it only progresses while the machine running it is
online. A laptop that travels or sleeps loses hours to retries and stops after about four hours offline
(`resume` continues it, but nothing happens in between). A small always-on Linux server fixes that, and gives
the service its proper sandbox (Landlock), which a Mac cannot.

## The machine

Any Ubuntu 24.04 VM with 4 or more cores, 16 GB of memory and 60 GB of disk. Lean candidates compile at up to
about 6 GB (the service allows 12 GB of address space per compile), and Mathlib's prebuilt files take about
10 GB of disk. No GPU. Cloud providers such as Hetzner bill a machine like this by the hour, up to a monthly
cap, until it is deleted (check the provider's current price); delete it when the series is done, after copying
the run folders home.

## Setup, once

Log in over ssh as a user with `sudo`, then

    curl -fsSL https://raw.githubusercontent.com/WFJKK/auto-research-compact-proof/main/scripts/server_setup.sh | bash

The script (idempotent: run it again if interrupted) installs the system packages, Lean through elan, the Lean
project with Mathlib's prebuilt cache and the targets the service needs (`lake build CompactCheck.Soundness
CompactCheck.CountedOps CompactCheck.CountedGeneralSound compactcheck acceptcheck`, plus the tactic modules the
agents' proofs import), the pipeline in a virtual environment with its pinned packages, tmux, and the Claude
Code CLI. It clones both repositories to the paths the pilot configs name on the Mac
(`~/Desktop/VerifiedMechanisms/...`), so nothing in a config needs editing and every command in
docs/OPEN_LANE.md is the same. About five minutes on an 8-core machine, most of it Lean.

Then sign in to Claude Code with the subscription: run `claude`, choose the subscription login; on a headless
server it prints a link to open on any device (the laptop, the phone) and asks for the code shown there. `claude
auth status` must then report a login; the loop checks it before every run. Nothing per call is billed: the
runs count against the subscription's usage limits, and the loop waits when it hits one (docs/BACKENDS.md,
including the note on Anthropic's terms).

## Running

Always inside tmux, so the run survives the ssh session:

    tmux new -s pilot
    cd ~/Desktop/VerifiedMechanisms/CompactProofsAgent/Auto-Research-Compact-Proof && source .venv/bin/activate
    python3 -m pytest tests/test_open_lane.py      # the pair works together: about two minutes
    python3 -m core.loop run --config config/open-lane-pilot-attn-max2-tiny.yaml --set rounds_max=5

`--set` changes a setting for this run only, without editing the config (a run with a model backend starts
only from a clean commit, so an edited config on the server would be refused); the run folder records it.
Detach with Ctrl-B then D; the run keeps going. Later, from anywhere:

    ssh <server>
    tmux attach -t pilot                           # watch it
    python3 -m core.loop status --run ~/auto-research-compact-proof-runs/<run_id>

Runs one after another, not at the same time: they share the subscription's limit, and two at once only wait
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
