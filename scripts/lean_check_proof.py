#!/usr/bin/env python3
"""Check one proof file of a model folder's network with the Lean checker (core.lean's `lean_check` command).

    python3 scripts/lean_check_proof.py <proof.json> <weights.npz>

A model folder opts in with, in its config.yaml,

    lean_check: [python3, ../../scripts/lean_check_proof.py, "{proof}", "{weights}"]

(the path relative to the model folder, where core.lean runs the command). The Lean project is the folder in
COMPACT_PROOF_LEAN, or the pilots' default path, and must have `lake build compactcheck`. The network id and
the model folder come from the weights file's place in the zoo (<model>/zoo/<network id>.npz); the network
is exported once into the Lean project's work folder and reused. The last line of output is the Lean
checker's JSON: {"certified": n}, or {"certified": 0, "status": "rejected", "reason": ...}.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

DEFAULT_LEAN = Path("~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck").expanduser()
REPO = Path(__file__).resolve().parent.parent


def main() -> int:
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    proof, weights = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    lean = Path(os.environ.get("COMPACT_PROOF_LEAN", str(DEFAULT_LEAN))).expanduser().resolve()
    checker = lean / ".lake" / "build" / "bin" / "compactcheck"
    if not checker.is_file():
        sys.exit(f"no Lean checker at {checker}: build it with `lake build compactcheck` in {lean}")
    network_id = weights.stem
    model_dir = weights.parent.parent
    try:
        model = str(model_dir.relative_to(REPO))
    except ValueError:
        sys.exit(f"{weights} is not in a model folder of {REPO}")
    work = lean / ".lake" / "work" / "networks"
    work.mkdir(parents=True, exist_ok=True)
    net_json = work / f"{network_id}.json"
    if not net_json.is_file():
        r = subprocess.run([sys.executable, "-B", str(lean / "scripts" / "export_network.py"), str(REPO), model, network_id,
                            str(net_json)], capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"export failed: {r.stderr[-1000:]}")
    r = subprocess.run([str(checker), str(net_json), str(proof)], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"compactcheck failed: {r.stderr[-1000:]}")
    last = r.stdout.strip().splitlines()[-1]
    json.loads(last)  # it is JSON, or we fail here rather than hand the loop a line it cannot read
    print(last)
    return 0


if __name__ == "__main__":
    sys.exit(main())
