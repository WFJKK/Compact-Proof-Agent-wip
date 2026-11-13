#!/usr/bin/env bash
# Set up a fresh Ubuntu 24.04 server for unattended open-lane pilots (docs/SERVER.md).
#
#     curl -fsSL https://raw.githubusercontent.com/WFJKK/Compact-Proof-Agent-wip/main/scripts/server_setup.sh | bash
#
# or copy the file over and run `bash server_setup.sh`. Idempotent: run it again after an interruption.
# It installs system packages, Lean (elan) and the Lean project at the commit the pipeline was tested with,
# with Mathlib's prebuilt cache, the pipeline with its Python packages, tmux, and the Claude Code CLI. It puts
# both repositories at the paths the pilot configs name on the Mac, so the configs and the commands of
# docs/OPEN_LANE.md work unchanged:
#
#     ~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck
#     ~/Desktop/VerifiedMechanisms/CompactProofsAgent/Compact-Proof-Agent-wip
#
# What it does not do: sign in to Claude Code (run `claude` once and sign in, with the Anthropic Console
# account for a run billed to the API or with the subscription; a headless server shows a link to open on
# any device), and start a run (docs/SERVER.md).
set -euo pipefail

LEAN_DIR=~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck
PIPE_DIR=~/Desktop/VerifiedMechanisms/CompactProofsAgent/Compact-Proof-Agent-wip
LEAN_REPO=https://github.com/WFJKK/Compact-Proof-Checker
PIPE_REPO=https://github.com/WFJKK/Compact-Proof-Agent-wip
# The Lean project's commit the pipeline was tested with (a run records the one it starts on).
LEAN_COMMIT=${LEAN_COMMIT:-e79a9a0}

echo "== system packages"
sudo apt-get update -qq
sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -qq git curl build-essential tmux python3 python3-venv python3-pip \
  libgmp-dev zstd ca-certificates > /dev/null

echo "== Lean toolchain (elan)"
if ! command -v elan > /dev/null; then
  curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi
# shellcheck disable=SC1090
source ~/.elan/env

echo "== the Lean project at $LEAN_COMMIT"
mkdir -p "$(dirname "$LEAN_DIR")"
if [ ! -d "$LEAN_DIR/.git" ]; then
  git clone "$LEAN_REPO" "$LEAN_DIR"
fi
cd "$LEAN_DIR"
git fetch -q origin
git checkout -q --detach "$LEAN_COMMIT"
elan toolchain install "$(cat lean-toolchain)" 2> /dev/null || true
lake exe cache get          # Mathlib's prebuilt files: minutes instead of hours
# Every module of the library (the rule on proofs asks Lean about all of them), except the tutorial and the
# placeholder Basic, which nothing imports; then the service's two programs and the tactics proofs use.
mapfile -t MODULES < <(ls CompactCheck/*.lean | sed 's#/#.#; s#\.lean$##' | grep -v -e '^CompactCheck\.Tutorial$' -e '^CompactCheck\.Basic$')
lake build "${MODULES[@]}" compactcheck acceptcheck
lake build Mathlib.Tactic.IntervalCases Mathlib.Tactic.Linarith Mathlib.Tactic.Ring

echo "== the pipeline"
mkdir -p "$(dirname "$PIPE_DIR")"
if [ ! -d "$PIPE_DIR/.git" ]; then
  git clone "$PIPE_REPO" "$PIPE_DIR"
fi
cd "$PIPE_DIR"
git pull --ff-only
if [ ! -d .venv ]; then
  python3 -m venv .venv
fi
# shellcheck disable=SC1091
source .venv/bin/activate
pip install -q --upgrade pip
pip install -q --index-url https://download.pytorch.org/whl/cpu torch 2> /dev/null || pip install -q torch
pip install -q -r requirements.txt

echo "== Claude Code"
if ! command -v node > /dev/null; then
  curl -fsSL https://deb.nodesource.com/setup_22.x | sudo -E bash - > /dev/null
  sudo apt-get install -y -qq nodejs > /dev/null
fi
if ! command -v claude > /dev/null; then
  sudo npm install -g @anthropic-ai/claude-code > /dev/null
fi

echo "== checks"
cd "$PIPE_DIR"
python3 -c "import torch, numpy, yaml, psutil, matplotlib, anthropic; print('python packages ok')"
ls "$LEAN_DIR/.lake/build/bin/acceptcheck" > /dev/null && echo "acceptcheck built"
echo "Lean project at $(git -C "$LEAN_DIR" rev-parse --short HEAD)"
python3 -c "from core.sandbox import landlock_abi; print('landlock abi', landlock_abi())"
claude --version

cat <<EOF

Done. Next, by hand:
  1. claude            (sign in: "Anthropic Console account" for the API, or the subscription;
                        then /exit)
     or, with an API key and no sign-in: export CPL_ANTHROPIC_KEY=sk-ant-...  and start the run
     with --auth api_key --budget-usd <dollars> (docs/BACKENDS.md)
  2. claude auth status   (not needed with an API key)
  3. tmux new -s pilot
     cd $PIPE_DIR && source .venv/bin/activate
     python3 -m pytest tests/test_open_lane.py        (a few minutes: the pair works together)
     python3 -m core.loop run --config config/pilot/<pilot>.yaml
     (detach with Ctrl-B then D; later: tmux attach -t pilot)
EOF
