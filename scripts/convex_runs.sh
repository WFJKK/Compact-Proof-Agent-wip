#!/bin/bash
# The agent with token_convex version 2 on max and min of 4 (README section 4.3), unattended: the smoke test,
# a check of its results, then the two four-round runs. Meant for a tmux session, from the repository:
#
#     tmux new -s convex 'bash scripts/convex_runs.sh; exec bash'
#
# Needs the key file of the README (~/.config/auto-research-compact-proof/env), Docker running with the
# sandbox image built (python -m core.sandbox build), and a Python with the packages of requirements.txt
# (PYTHON=/path/to/python, or the first one found below). Running it again continues where it stopped: a run
# whose folder exists is resumed, which never pays again for an answer already saved. caffeinate keeps the
# Mac awake while a run is going; closing the lid on battery still sends it to sleep.
#
# With 10 GB or more for Docker, max of 4 and min of 4 run side by side (a second tmux window, min4);
# otherwise one after the other. Expect about $2 for the smoke test and $7.50 for each run.
set -u
cd "$(dirname "$0")/.." || exit 1
REPO=$(pwd)
RUNS=~/auto-research-compact-proof-runs
MODE=${1:-all}

for c in "${PYTHON:-}" ~/auto-research-compact-proof/.venv/bin/python ~/auto-research-compact-proof/venv/bin/python \
         "$REPO/.venv/bin/python" python3 python; do
  if [ -n "$c" ] && command -v "$c" >/dev/null 2>&1 && "$c" -c "import torch, numpy, yaml" 2>/dev/null; then
    PY=$c
    break
  fi
done
[ -n "${PY:-}" ] || { echo "No Python with torch, numpy and yaml found; run again with PYTHON=/path/to/python"; exit 1; }
echo "Python: $PY"
[ -f ~/.config/auto-research-compact-proof/env ] || { echo "No key file at ~/.config/auto-research-compact-proof/env (README: Running with your own API key)"; exit 1; }
set -a
. ~/.config/auto-research-compact-proof/env
set +a
docker info >/dev/null 2>&1 || { echo "Docker is not running: start Docker Desktop, then run this again"; exit 1; }

run_or_resume() {  # run_id: the config of that name, or the run's folder if it exists
  if [ -d "$RUNS/$1" ]; then
    caffeinate -i "$PY" -m core.loop resume --run "$RUNS/$1"
  else
    caffeinate -i "$PY" -m core.loop run --config "config/$1.yaml"
  fi
}

if [ "$MODE" = min4 ]; then
  run_or_resume attn-min4-q-api-convex
  exit
fi

# 1. The smoke test: one round on one v16 and one v24 network.
run_or_resume attn-max4-convex-smoke || { echo "The smoke test stopped with an error (above); not starting the runs"; exit 1; }
"$PY" -m core.loop status --run "$RUNS/attn-max4-convex-smoke" --diagnostics
"$PY" - "$RUNS/attn-max4-convex-smoke" <<'EOF' || { echo "Not starting the runs: the smoke test's recipes hit a limit or never ran"; exit 1; }
import json
import sys

rs = [json.loads(line) for line in open(sys.argv[1] + "/archive.jsonl") if line.strip()]
r1 = [r for r in rs if r.get("round") == 1]
killed = [r for r in r1 if r.get("status") == "crash"
          and any(w in (r.get("error") or "") for w in ("SIGKILL", "time limit", "timed out"))]
ok = sum(r.get("status") == "ok" for r in r1)
print(f"smoke test, round 1: {len(r1)} results, {ok} ok, {len(killed)} killed by a memory or time limit")
sys.exit(1 if killed or not r1 else 0)
EOF

# 2. The two runs.
MEM=$(docker info --format '{{.MemTotal}}' 2>/dev/null)
if [ "${MEM:-0}" -ge 10000000000 ] 2>/dev/null && [ -n "${TMUX:-}" ]; then
  echo "Docker has $((MEM / 1000000000)) GB: min of 4 runs in the tmux window min4, max of 4 here"
  tmux new-window -d -n min4 "PYTHON='$PY' bash '$REPO/scripts/convex_runs.sh' min4; exec bash"
  run_or_resume attn-max4-q-api-convex
else
  echo "Running max of 4, then min of 4"
  run_or_resume attn-max4-q-api-convex
  run_or_resume attn-min4-q-api-convex
fi
