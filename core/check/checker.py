"""Check one proof file for one network.

    python -m core.check.checker models/<name> <network id> proof.json

The checker loads the network's weights itself (hash-checked) and builds the
network from the model folder's model.py. Nothing the proof claims is trusted:
every bound is recomputed exactly. A malformed proof is rejected as a whole;
a leaf whose bound fails simply certifies nothing.

With detail=True the result also holds the certified mask and every leaf's
outcome, for diagnostics (core.diagnostics). Nothing in it changes the score.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

import numpy as np

from .. import inputs
from ..model_folder import ModelFolder, load_model_folder
from ..zoo import load_weights, network_entry
from .approx import Approximation, ApproximationError
from .cost import VERSION as COST_VERSION
from .cost import Counter, count_scalars
from .evaluate import CheckError
from .proof import SCHEMA, TOP_KEYS, certified_mask, full_tree, sorted_orbit_count, walk
from .rules import GENERIC_RULES, adopted_rules, leaf_rules
from .trace import UnsupportedOp, build_any, make_program

MAX_REJECTED_REPORTED = 50


def limits(n_inputs: int) -> dict:
    return {"max_scalars": 50 * n_inputs + 10**6, "max_nodes": 4 * n_inputs + 10**4}


def _fraction_str(f: Fraction) -> str:
    return f"{f.numerator}/{f.denominator}"


def _safe_float(x) -> float:
    """float(x) for a Fraction or int, without raising on an out-of-range value."""
    try:
        return float(x)
    except (OverflowError, ValueError):
        return float("inf") if x > 0 else float("-inf")


def _rejected(reason: str, nid: str, n: int, counter: Counter) -> dict:
    return {
        "status": "rejected",
        "reason": reason,
        "network": nid,
        "n_inputs": n,
        "certified": 0,
        "certified_accuracy": "0/1",
        "certified_accuracy_float": 0.0,
        "length": counter.total,
        "length_by_rule": counter.as_dict(),
        "leaves": {"total": 0, "accepted": 0, "rejected": 0, "skipped": 0},
        "rejected_pieces": [],
        "cost_model": COST_VERSION,
    }


def check_proof(
    proof,
    folder: ModelFolder,
    network_id: str,
    rule_set=GENERIC_RULES,
    allow_held_out: bool = False,
    want_mask: bool = False,
    detail: bool = False,
) -> dict:
    rule_set = tuple(rule_set)
    want_mask = want_mask or detail
    entry = network_entry(folder, network_id)
    setting = entry["setting"]
    sizes = folder.sizes(setting)
    space = folder.input_space(setting)
    n = inputs.n_inputs(space)
    lim = limits(n)
    counter = Counter()
    try:
        # read: the file's size is capped, not charged; the numbers it supplies are charged where they are
        # read, in the approximations (cost-v4) ---------------------------------------------------------
        if not isinstance(proof, dict):
            raise CheckError("a proof file is a JSON object")
        n_scalars = count_scalars(proof, limit=lim["max_scalars"])
        if n_scalars > lim["max_scalars"]:
            raise CheckError(f"the proof file has more than {lim['max_scalars']} numbers and strings")
        extra = set(proof) - TOP_KEYS
        if extra:
            raise CheckError(f"unknown top-level keys {sorted(extra)}")
        if proof.get("schema") != SCHEMA:
            raise CheckError(f"schema must be {SCHEMA!r}")
        if proof.get("network") != network_id:
            raise CheckError(f"the proof names network {proof.get('network')!r}, not {network_id!r}")
        if "tree" not in proof:
            raise CheckError("the proof has no tree")

        # network -------------------------------------------------------------
        weights = load_weights(folder, network_id, allow_held_out=allow_held_out)
        graph = build_any(folder.build(setting))
        prog = make_program(graph, weights, counter, space)

        # global rules --------------------------------------------------------
        symmetry = proof.get("symmetry", False)
        if not isinstance(symmetry, bool):
            raise CheckError("symmetry must be true or false")
        if symmetry:
            if "symmetry" not in rule_set:
                raise CheckError("the symmetry rule is not allowed in this run")
            if not graph.summed_over_positions_first():
                raise CheckError("symmetry does not hold: the input is not used only through a sum over positions")
            if getattr(folder.task, "LABEL_SYMMETRIC", False) is not True:
                raise CheckError("symmetry does not hold: the task does not declare that reordering keeps the label")
        contractions = proof.get("contract", [])
        if contractions and "contract" not in rule_set:
            raise CheckError("the contract rule is not allowed in this run")
        if not isinstance(contractions, list):
            raise CheckError("contract must be a list")
        for c in contractions:
            if not isinstance(c, dict) or set(c) != {"name", "chain"}:
                raise CheckError('each contraction is {"name": ..., "chain": [...]}')
            prog.contract(c["name"], c["chain"], counter)
        approximations = {}
        approx_specs = proof.get("approximate", [])
        if approx_specs and "approximate" not in rule_set:
            raise CheckError("the approximate rule is not allowed in this run")
        if not isinstance(approx_specs, list):
            raise CheckError("approximate must be a list")
        for a in approx_specs:
            if not isinstance(a, dict) or not isinstance(a.get("name"), str) or not isinstance(a.get("of"), str):
                raise CheckError('each approximation has a "name" and an "of"')
            if a["name"] in approximations:
                raise CheckError(f"approximation {a['name']!r} is defined twice")
            try:
                lin = prog.linear(a["of"])
            except KeyError:
                raise CheckError(f"approximation of unknown linear map {a['of']!r}") from None
            spec = {k: v for k, v in a.items() if k not in ("name", "of")}
            try:
                approximations[a["name"]] = Approximation(a["name"], a["of"], spec, lin.W, counter)
            except ApproximationError as exc:
                raise CheckError(f"approximation {a['name']!r}: {exc}") from exc

        # tree: walked for free (cost-v4), its size capped by walk ------------------------------------
        leaves, _ = walk(proof["tree"], space, lim["max_nodes"])
        allowed_leaves = leaf_rules()
        plugins = adopted_rules()
        for leaf in leaves:
            if leaf.rule not in allowed_leaves or leaf.rule not in rule_set + ("skip",):
                raise CheckError(f"{leaf.path}: rule {leaf.rule!r} is not allowed in this run")
            if leaf.rule in plugins and plugins[leaf.rule].applies_to == "general" and not getattr(graph, "general", False):
                raise CheckError(f"{leaf.path}: rule {leaf.rule!r} is only for networks beyond linear maps")
            if leaf.approx is not None and leaf.approx not in approximations:
                raise CheckError(f"{leaf.path}: unknown approximation {leaf.approx!r}")

        # leaves ----------------------------------------------------------------
        # Each leaf's outcome: accepted, rejected (with reason and shortfall) or skipped.
        accepted, rejected, skipped = [], [], 0
        outcomes = [] if detail else None

        def outcome(l, accepted_, reason=None, margin=None, label=None, worst_output=None):
            if outcomes is not None:
                outcomes.append(
                    {
                        "ranges": l.ranges,
                        "rule": l.rule,
                        "accepted": accepted_,
                        "reason": reason,
                        "margin": margin,
                        "label": label,
                        "worst_output": worst_output,
                    }
                )

        singles = [l for l in leaves if l.rule == "single"]
        for l in singles:
            if not l.is_single():
                raise CheckError(f"{l.path}: a single leaf must hold exactly one input")
        if singles:
            tokens = np.array([[lo for lo, _ in l.ranges] for l in singles], dtype=np.int64)
            labels = np.asarray(folder.task.label(tokens, sizes), dtype=np.int64)
            ok, margins = prog.run_singles(tokens, labels, counter)
            for l, good, m, lab in zip(singles, ok, margins, labels):
                if good:
                    accepted.append(l)
                    outcome(l, True, margin=float(m), label=int(lab))
                else:
                    rejected.append(
                        {
                            "path": l.path,
                            "rule": "single",
                            "ranges": l.ranges,
                            "reason": "margin not positive",
                            "label": int(lab),
                            "worst_margin": float(m),
                            "shortfall": -float(m),
                        }
                    )
                    outcome(l, False, "margin not positive", float(m), int(lab))
        for l in leaves:
            if l.rule == "skip":
                skipped += 1
                outcome(l, False, "skipped")
            elif l.rule in ("interval", "token_interval") or l.rule in plugins:
                label = folder.task.constant_label(l.ranges, sizes)
                if label is None:
                    rejected.append({"path": l.path, "rule": l.rule, "ranges": l.ranges, "reason": "label not constant"})
                    outcome(l, False, "label not constant")
                    continue
                if l.rule == "interval":
                    good, worst, j = prog.run_interval(l.ranges, int(label), counter, approximations.get(l.approx))
                elif l.rule == "token_interval":
                    good, worst, j = prog.run_token_interval(l.ranges, int(label), counter)
                else:
                    good, worst, j = plugins[l.rule].check_leaf(prog, l.ranges, int(label), counter)
                    if isinstance(worst, bool) or not isinstance(worst, (int, Fraction)):
                        raise TypeError(f"rule {l.rule!r} returned a bound that is not an exact rational")
                    worst = Fraction(worst)
                    good = bool(good) and worst > 0  # the rule's verdict must agree with its own bound
                if good:
                    accepted.append(l)
                    outcome(l, True, margin=_safe_float(worst), label=int(label), worst_output=int(j))
                else:
                    rejected.append(
                        {
                            "path": l.path,
                            "rule": l.rule,
                            "ranges": l.ranges,
                            "reason": "margin bound not positive",
                            "label": int(label),
                            "worst_output": int(j),
                            "worst_margin": _safe_float(worst),
                            "shortfall": -_safe_float(worst),
                        }
                    )
                    outcome(l, False, "margin bound not positive", _safe_float(worst), int(label), int(j))

        # count -------------------------------------------------------------------
        if symmetry:
            certified = sum(sorted_orbit_count(l.ranges) for l in accepted)  # counting is free (cost-v4)
        else:
            certified = sum(l.size for l in accepted)
        mask = None
        if want_mask:
            mask = certified_mask(space, [l.ranges for l in accepted], symmetry)
            if int(mask.sum()) != certified:
                raise RuntimeError("internal error: certified count and mask disagree")
        if certified > n:
            raise RuntimeError("internal error: more inputs certified than exist")
    except (CheckError, UnsupportedOp) as exc:
        return _rejected(str(exc), network_id, n, counter)
    except (ArithmeticError, ValueError, TypeError, RecursionError, MemoryError) as exc:
        return _rejected(f"the proof made the checker fail: {type(exc).__name__}: {str(exc)[:200]}", network_id, n, counter)

    acc = Fraction(certified, n)
    rejected.sort(key=lambda r: r.get("worst_margin", float("-inf")))
    result = {
        "status": "ok",
        "reason": None,
        "network": network_id,
        "n_inputs": n,
        "certified": int(certified),
        "certified_accuracy": _fraction_str(acc),
        "certified_accuracy_float": float(acc),
        "length": counter.total,
        "length_by_rule": counter.as_dict(),
        "leaves": {"total": len(leaves), "accepted": len(accepted), "rejected": len(rejected), "skipped": skipped},
        "rejected_pieces": rejected[:MAX_REJECTED_REPORTED],
        "cost_model": COST_VERSION,
        "symmetry": symmetry,
    }
    if want_mask:
        result["mask"] = mask
    if detail:
        result["outcomes"] = outcomes
    return result


def brute_force_proof(folder: ModelFolder, network_id: str) -> dict:
    space = folder.input_space(network_entry(folder, network_id)["setting"])
    return {"schema": SCHEMA, "network": network_id, "tree": full_tree(space)}


def extraction_and_brute_force_costs(folder: ModelFolder, network_id: str) -> tuple[int, int]:
    """E and B under the cost model, computed without running brute force.

    Both depend only on the network's shapes, never on its weights, so this
    uses the module's own initial weights and loads nothing from the zoo (held-
    out networks included). A test checks that B is the length the checker
    reports for brute_force_proof.
    """
    entry = network_entry(folder, network_id)
    space = folder.input_space(entry["setting"])
    n = inputs.n_inputs(space)
    module = folder.build(entry["setting"])
    weights = {k: v.detach().numpy() for k, v in module.state_dict().items()}
    counter = Counter()
    prog = make_program(build_any(module), weights, counter, space)
    E = counter.total
    one = Counter()
    tok = np.zeros((1, len(space)), dtype=np.int64)
    lab = np.asarray(folder.task.label(tok, folder.sizes(entry["setting"])), dtype=np.int64)
    prog.run_singles(tok, lab, one)
    # the tree and the file's strings are free (cost-v4): E and one forward pass per input
    B = E + n * one.total
    return E, B


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("model_folder")
    ap.add_argument("network")
    ap.add_argument("proof")
    args = ap.parse_args(argv)
    folder = load_model_folder(args.model_folder)
    with open(args.proof) as f:
        proof = json.load(f)
    res = check_proof(proof, folder, args.network)
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
