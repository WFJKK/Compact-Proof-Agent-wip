#!/usr/bin/env bash
# Set up a fresh Ubuntu 24.04 server for unattended open-lane pilots (docs/SERVER.md).
#
#     curl -fsSL https://raw.githubusercontent.com/WFJKK/auto-research-compact-proof/main/scripts/server_setup.sh | bash
#
# or copy the file over and run `bash server_setup.sh`. Idempotent: run it again after an interruption.
# It installs system packages, Lean (elan) and the Lean project with Mathlib's prebuilt cache, the pipeline
# with its Python packages, tmux, and the Claude Code CLI. It puts both repositories at the same paths the
# pilot configs name on the Mac, so the configs and the commands of docs/OPEN_LANE.md work unchanged:
#
#     ~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck
#     ~/Desktop/VerifiedMechanisms/CompactProofsAgent/Auto-Research-Compact-Proof
#
# What it does not do: sign in to Claude Code (run `claude` once and sign in with the subscription; a
# headless server shows a link to open on any device), and start a run (docs/SERVER.md).
set -euo pipefail

LEAN_DIR=~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck
PIPE_DIR=~/Desktop/VerifiedMechanisms/CompactProofsAgent/Auto-Research-Compact-Proof
LEAN_REPO=https://github.com/WFJKK/Compact-Proof-Checker
PIPE_REPO=https://github.com/WFJKK/Compact-Proof-Agent

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

echo "== the Lean project"
mkdir -p "$(dirname "$LEAN_DIR")"
if [ ! -d "$LEAN_DIR/.git" ]; then
  git clone "$LEAN_REPO" "$LEAN_DIR"
fi
cd "$LEAN_DIR"
git pull --ff-only
elan toolchain install "$(cat lean-toolchain)" 2> /dev/null || true
lake exe cache get          # Mathlib's prebuilt files: minutes instead of hours
lake build CompactCheck.Soundness CompactCheck.CountedOps CompactCheck.CountedGeneralSound compactcheck acceptcheck
lake build Mathlib.Tactic.IntervalCases Mathlib.Tactic.Linarith Mathlib.Tactic.Ring   # tactics the agents' proofs use

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
python3 -c "from core.sandbox import landlock_abi; print('landlock abi', landlock_abi())"
claude --version

cat <<EOF

Done. Next, by hand:
  1. claude            (sign in with the subscription; then Ctrl-C or /exit)
  2. claude auth status
  3. tmux new -s pilot
     cd $PIPE_DIR && source .venv/bin/activate
     python3 -m pytest tests/test_open_lane.py        (about 2 minutes: the pair works together)
     python3 -m core.loop run --config config/<pilot>.yaml
     (detach with Ctrl-B then D; later: tmux attach -t pilot)
EOF
