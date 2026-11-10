"""Audit the zoo's correct-input counts against the checker, and record the checker's own.

    python -m core.check.exact_counts models/<name>

For every network of a model's zoo (held-out ones included: this is maintenance, not the agent), checks the
brute-force proof file with the Python checker and writes its count into the manifest as `checked_correct`,
with `checked_semantics` "exact" for linear networks (exact rational arithmetic, the same count the Lean
specification defines) or "enclosure" for general ones (interval bounds on exp: a lower bound of the real
count). The zoo's `real_correct` comes from the float forward pass and only approximates the real-semantics
count; any network where the two differ is reported. The loop halts a run on a count above `checked_correct`
when it is exact (core/rounds.py, core/open_lane/records.py).
"""

from __future__ import annotations

import argparse

from ..model_folder import load_model_folder
from ..zoo import read_manifest, write_manifest
from .checker import brute_force_proof, build_any, check_proof
from .cost import VERSION


def fill_exact_counts(folder, log=print) -> dict:
    manifest = read_manifest(folder)
    mismatches = []
    for entry in manifest["networks"]:
        nid = entry["id"]
        general = bool(getattr(build_any(folder.build(entry["setting"])), "general", False))
        result = check_proof(brute_force_proof(folder, nid), folder, nid, rule_set=("single",), allow_held_out=True)
        if result["status"] != "ok":
            raise RuntimeError(f"{nid}: the checker rejected the brute-force proof: {result['reason']}")
        entry["checked_correct"] = int(result["certified"])
        entry["checked_semantics"] = "enclosure" if general else "exact"
        entry["checked_cost_model"] = VERSION
        same = entry.get("real_correct") == entry["checked_correct"]
        log(f"{nid}: checker {entry['checked_correct']} ({entry['checked_semantics']}), float {entry.get('real_correct')}"
            + ("" if same else "  <- differs"))
        if not same:
            mismatches.append(nid)
    write_manifest(folder, manifest)
    if mismatches:
        log(f"the float count differs from the checker's on {len(mismatches)} networks: {', '.join(mismatches)}")
    else:
        log("the float count equals the checker's on every network")
    return manifest


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("model_folder")
    args = ap.parse_args(argv)
    fill_exact_counts(load_model_folder(args.model_folder))


if __name__ == "__main__":
    main()
