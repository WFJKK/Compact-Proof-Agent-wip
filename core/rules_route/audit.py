"""The route's audit: a leaf rule's bounds against brute force, on networks it was never tuned on.

    python -m core.rules_route.audit <rule folder> [--level small|full] [--out report.json]
                                     [--counterexamples cases.json]

For each model folder whose network goes beyond linear maps, it takes
trained development networks, random-weight networks at several scales (sharp softmaxes included), and trained
networks with their weights perturbed, and on each it samples leaves with a constant label: one varying
position, several with the last position fixed, several with every position free, boxes that hold the
label token at one position, and boxes whose positions in a set hold one token while all the others lie below
it (or all above). Per leaf it runs the rule and brute force in float64 on every input:

- a bound above the leaf's smallest float64 margin (beyond float rounding) is a violation: the rule is unsound;
- a certified leaf must have every input certified by the exact single rule too, else a violation;
- the rule's verdict must agree with its bound, the bound must be an exact rational, and its charges must be
  non-negative integers.

Counterexamples (the adversarial reviewer's, say) are checked the same way: a JSON list of
{"folder": ..., "setting": ..., "network": "zoo:<id>" | "random:<seed>:<scale>" | "perturbed:<id>:<seed>:<relative>"
| "file:<path to an .npz of weights>", "ranges": [[lo, hi], ...], "label": optional}, or with "weights":
{parameter: nested lists} in place of "network", or with "leaves": [{"ranges": ..., "label": optional,
"rule": optional "token_interval"}, ...] in place of "ranges": a sequence run in order on one program, so that
bugs in what the rule keeps across leaves show (a "token_interval" leaf only shares the memo).

Every audit also runs the cases in tests/rule_route/regressions.json (bugs found before, as sequences of leaves
on one program). A leaf where the rule raises an arithmetic or similar error is recorded as a crash: the
checker would reject the whole proof there, which is not unsound, so it is reported but does not fail the
audit. The report lists every violation with what reproduces it. The exit code is 1 if there is any, 2 if the
rule could not be loaded. Nothing here trusts the rule: it runs in this process, so the route runs the audit
inside the sandbox.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np

from ..check.cost import Counter
from ..check.evaluate import CheckError
from ..check.plugins import PluginError, drop_candidates, use_candidate
from ..check.trace import UnsupportedOp, build_any, make_program
from ..model_folder import load_model_folder
from ..util import REPO_ROOT
from ..zoo import load_weights, networks

REGRESSIONS = REPO_ROOT / "tests" / "rule_route" / "regressions.json"  # cases every audit runs: past bugs
TOLERANCE_ABS = 1e-7
TOLERANCE_REL = 1e-9
LEVELS = {
    # networks per kind per folder, leaves per network, largest leaf (inputs), exact singles per audit
    "small": {"trained": 1, "random": 1, "perturbed": 1, "leaves": 12, "max_inputs": 600, "singles": 4000},
    "full": {"trained": 2, "random": 3, "perturbed": 2, "leaves": 40, "max_inputs": 2500, "singles": 60000},
}
SCALES = (1.0, 4.0, 16.0)
RELATIVE = (0.01, 0.1, 0.5)


@dataclass
class Net:
    folder: object
    setting: str
    spec: str
    weights: dict


def general_folders(names=None) -> list:
    """(folder, smallest setting) for every model folder beyond linear maps: the real ones in models/, and the
    synthetic ones in tests/ (no trained zoo; random weights only), which use operations the real ones do not."""
    out = []
    for root in (REPO_ROOT / "models", REPO_ROOT / "tests"):
        for path in sorted(p for p in root.iterdir() if p.is_dir()):
            if not ((path / "model.py").is_file() and (path / "config.yaml").is_file()) or (names and path.name not in names):
                continue
            folder = load_model_folder(path)
            setting = min(folder.setting_names(), key=lambda s: folder.n_inputs(s))
            if getattr(build_any(folder.build(setting)), "general", False):
                out.append((folder, setting))
    return out


def _module(folder, setting, weights):
    import torch

    m = folder.build(setting).double()
    m.load_state_dict({k: torch.tensor(np.asarray(v), dtype=torch.float64) for k, v in weights.items()})
    m.eval()
    return m


def random_weights(folder, setting, seed: int, scale: float) -> dict:
    import torch

    torch.manual_seed(seed)
    m = folder.build(setting)
    rng = np.random.default_rng(seed)
    out = {}
    for k, v in m.state_dict().items():
        a = v.detach().numpy().astype(np.float64)
        spread = float(np.abs(a).max()) or 0.5
        out[k] = (rng.uniform(-1, 1, size=a.shape) * spread * scale).astype(np.float32)
    return out


def perturbed_weights(base: dict, seed: int, relative: float) -> dict:
    rng = np.random.default_rng(seed)
    out = {}
    for k, v in base.items():
        a = np.asarray(v, dtype=np.float64)
        s = float(a.std()) or 1.0
        out[k] = (a + rng.normal(size=a.shape) * s * relative).astype(np.float32)
    return out


def network(folder, setting, spec: str) -> Net:
    kind, _, rest = spec.partition(":")
    if kind == "zoo":
        return Net(folder, setting, spec, load_weights(folder, rest))
    if kind == "random":
        seed, scale = rest.split(":")
        return Net(folder, setting, spec, random_weights(folder, setting, int(seed), float(scale)))
    if kind == "perturbed":
        nid, seed, rel = rest.rsplit(":", 2)
        return Net(folder, setting, spec, perturbed_weights(load_weights(folder, nid), int(seed), float(rel)))
    if kind == "file":
        with np.load(rest) as f:
            return Net(folder, setting, spec, {k: np.asarray(f[k], dtype=np.float32) for k in f.files})
    raise ValueError(f"unknown network spec {spec!r}")


def label_set_ranges(space, rng):
    """A box whose positions in a random nonempty set S hold one token M and whose other positions all lie below M
    (or all above it), each from M - 1 down to 0 or to a random token (up to M + 1 .. the last): the shape of
    proofs that split each position at the largest token. None if M leaves no room."""
    P = len(space)
    M = int(rng.integers(0, min(space)))
    S = [p for p in range(P) if rng.random() < 0.35] or [int(rng.integers(0, P))]
    below = rng.random() < 0.5
    ranges = []
    for p in range(P):
        if p in S:
            ranges.append((M, M))
        elif below:
            if M == 0:
                return None
            ranges.append((0 if rng.random() < 0.5 else int(rng.integers(0, M)), M - 1))
        else:
            if M == space[p] - 1:
                return None
            ranges.append((M + 1, space[p] - 1 if rng.random() < 0.5 else int(rng.integers(M + 1, space[p]))))
    return ranges


def sample_leaves(folder, setting, rng, n: int, max_inputs: int) -> list:
    """Leaves with a constant label, of five kinds, none larger than max_inputs."""
    sizes = folder.sizes(setting)
    space = folder.input_space(setting)
    P = len(space)
    out, tries = [], 0
    while len(out) < n and tries < 200 * n:
        tries += 1
        kind = ("one", "fixed_last", "free", "label_token", "label_set")[len(out) % 5]
        ranges = []
        free = int(rng.integers(0, P))
        for p in range(P):
            V = space[p]
            lo = int(rng.integers(0, V))
            if kind == "one":
                w = int(rng.integers(1, max(2, V))) if p == free else 0
            elif kind == "fixed_last" and p == P - 1:
                w = 0
            else:
                w = int(rng.integers(0, max(1, V // 2)))
            ranges.append((lo, min(V - 1, lo + w)))
        if kind == "label_token":  # one position holds the largest (or smallest) allowed token
            top = max(hi for _, hi in ranges)
            bottom = min(lo for lo, _ in ranges)
            p = int(rng.integers(0, P))
            ranges[p] = (top, top) if rng.random() < 0.5 else (bottom, bottom)
        if kind == "label_set":
            ranges = label_set_ranges(space, rng)
            if ranges is None:
                continue
        size = int(np.prod([hi - lo + 1 for lo, hi in ranges]))
        label = folder.task.constant_label(ranges, sizes)
        if label is None or size > max_inputs:
            continue
        out.append({"kind": kind, "ranges": ranges, "label": int(label)})
    return out


def leaf_inputs(ranges) -> np.ndarray:
    return np.array(list(itertools.product(*[range(lo, hi + 1) for lo, hi in ranges])), dtype=np.int64)


def float_min_margin(net: Net, module, ranges, label) -> float:
    import torch

    toks = leaf_inputs(ranges)
    with torch.no_grad():
        z = module(net.folder.encode(toks, net.setting).double()).numpy()
    return float((z[:, label] - np.delete(z, label, axis=1).max(axis=1)).min())


def check_case(rule, net: Net, ranges, label, singles_left: list) -> dict:
    """One leaf: the rule's verdict and bound against brute force. Returns a record with "violation" set if wrong."""
    folder, setting = net.folder, net.setting
    space = folder.input_space(setting)
    prog = net.prog
    rec = {"folder": folder.name, "setting": setting, "network": net.spec, "ranges": [list(r) for r in ranges], "label": label}
    counter = Counter()
    t0 = time.monotonic()
    try:
        ok, bound, j = rule.check_leaf(prog, [tuple(r) for r in ranges], label, counter)
    except (UnsupportedOp, CheckError) as exc:
        rec.update(outcome="refused", reason=str(exc)[:200])
        return rec
    except (ArithmeticError, ValueError, TypeError, IndexError, KeyError, RecursionError, MemoryError) as exc:
        # the checker would reject the whole proof here: not unsound, but recorded, never fatal to the audit
        rec.update(outcome="crash", reason=f"{type(exc).__name__}: {str(exc)[:200]}")
        return rec
    rec["seconds"] = round(time.monotonic() - t0, 3)
    if isinstance(bound, bool) or not isinstance(bound, (int, Fraction)):
        rec.update(outcome="violation", violation=f"the bound is a {type(bound).__name__}, not an exact rational")
        return rec
    bound = Fraction(bound)
    charges = counter.as_dict()
    if any((not isinstance(v, int)) or v < 0 for v in charges.values()):
        rec.update(outcome="violation", violation=f"bad charges {charges}")
        return rec
    true = float_min_margin(net, net.module, ranges, label)
    rec.update(certified=bool(ok), bound=float(bound), float_min_margin=true, length=sum(charges.values()))
    if bool(ok) != (bound > 0):
        rec.update(outcome="violation", violation="the verdict disagrees with the bound")
        return rec
    if float(bound) > true + TOLERANCE_ABS + TOLERANCE_REL * abs(true):
        rec.update(outcome="violation", violation="the bound exceeds the smallest float64 margin of the leaf")
        return rec
    if ok:
        toks = leaf_inputs(ranges)
        if len(toks) <= singles_left[0]:
            singles_left[0] -= len(toks)
            labels = np.full(len(toks), label, dtype=np.int64)
            good, margins = prog.run_singles(toks, labels, Counter())
            rec["exact_singles"] = int(len(toks))
            if not bool(np.all(good)):
                bad = toks[~good][0].tolist()
                rec.update(outcome="violation", violation=f"certified, but the single rule does not certify input {bad}")
                return rec
    rec["outcome"] = "ok"
    return rec


def _attach(net: Net) -> Net:
    space = net.folder.input_space(net.setting)
    net.prog = make_program(build_any(net.folder.build(net.setting)), net.weights, Counter(), space)
    net.module = _module(net.folder, net.setting, net.weights)
    return net


def audit(rule_dir: Path, level: str = "full", folders=None, seed: int = 0, counterexamples=None, log=print) -> dict:
    cfg = LEVELS[level]
    try:
        rule = use_candidate(Path(rule_dir))
    except PluginError as exc:
        return {"rule": Path(rule_dir).name, "loaded": False, "problems": str(exc), "violations": [], "passed": False}
    rng = np.random.default_rng(seed)
    records = []
    singles_left = [cfg["singles"]]
    try:
        for folder, setting in general_folders(folders):
            dev = [e["id"] for e in networks(folder, setting=setting)] if folder.zoo_dir().is_dir() else []
            specs = [f"zoo:{nid}" for nid in dev[: cfg["trained"]]]
            n_random = cfg["random"] if dev else cfg["random"] + cfg["trained"] + cfg["perturbed"]  # no zoo: random only
            specs += [f"random:{seed + i}:{SCALES[i % len(SCALES)]}" for i in range(n_random)]
            if dev:
                specs += [f"perturbed:{dev[i % len(dev)]}:{seed + i}:{RELATIVE[i % len(RELATIVE)]}" for i in range(cfg["perturbed"])]
            for spec in specs:
                net = _attach(network(folder, setting, spec))
                for leaf in sample_leaves(folder, setting, rng, cfg["leaves"], cfg["max_inputs"]):
                    if rng.random() < 0.5:  # token_interval leaves share the program's memo: interleave some
                        try:
                            net.prog.run_token_interval([tuple(r) for r in leaf["ranges"]], leaf["label"], Counter())
                        except (UnsupportedOp, CheckError, ArithmeticError, ValueError, TypeError):
                            pass
                    rec = check_case(rule, net, leaf["ranges"], leaf["label"], singles_left)
                    rec["kind"] = leaf["kind"]
                    records.append(rec)
                log(f"  {folder.name} {spec}: {sum(1 for r in records if r['network'] == spec and r['folder'] == folder.name)} leaves")
        fixed = json.loads(REGRESSIONS.read_text()) if REGRESSIONS.is_file() else []
        for case in fixed + list(counterexamples or []):
            try:
                name = str(case.get("folder", ""))
                paths = [REPO_ROOT / root / name for root in ("models", "tests")]
                path = next((p for p in paths if name and "/" not in name and (p / "model.py").is_file()), None)
                if path is None:
                    raise ValueError(f"no model folder named {name!r} in models/ or tests/")
                folder = load_model_folder(path)
                setting = case.get("setting") or min(folder.setting_names(), key=lambda s: folder.n_inputs(s))
                if "weights" in case:  # a network the reviewer constructed
                    expected = {k: tuple(v.shape) for k, v in folder.build(setting).state_dict().items()}
                    w = {k: np.asarray(v, dtype=np.float32) for k, v in case["weights"].items()}
                    if {k: v.shape for k, v in w.items()} != expected:
                        raise ValueError(f"weights must have exactly the parameters {expected}")
                    if not all(np.isfinite(v).all() for v in w.values()):
                        raise ValueError("weights must be finite")
                    net = _attach(Net(folder, setting, "inline", w))
                else:
                    net = _attach(network(folder, setting, case["network"]))
                # one leaf ("ranges"), or a sequence ("leaves") run in order on one program, sharing its memo
                seq = case["leaves"] if "leaves" in case else [{"ranges": case["ranges"], "label": case.get("label")}]
                leaves = []
                for lf in seq:
                    ranges = [tuple(int(x) for x in r) for r in lf["ranges"]]
                    label = lf.get("label")
                    label = int(folder.task.constant_label(ranges, folder.sizes(setting))) if label is None else int(label)
                    if len(leaf_inputs(ranges)) > 200000:
                        raise ValueError("a leaf is too large to brute-force")
                    leaves.append((ranges, label, lf.get("rule", "rule")))
            except Exception as exc:  # a malformed case is reported, not fatal
                records.append({"kind": "counterexample", "outcome": "malformed", "case": case, "reason": f"{type(exc).__name__}: {exc}"[:300]})
                continue
            for ranges, label, which in leaves:
                if which == "token_interval":  # a leaf of the other rule, only for its effect on the memo
                    try:
                        net.prog.run_token_interval(ranges, label, Counter())
                    except (UnsupportedOp, CheckError, ArithmeticError, ValueError, TypeError):
                        pass
                    continue
                rec = check_case(rule, net, ranges, label, singles_left)
                rec["kind"] = "regression" if case in fixed else "counterexample"
                records.append(rec)
    finally:
        drop_candidates()
    violations = [r for r in records if r.get("outcome") == "violation"]
    ok = [r for r in records if r.get("outcome") == "ok"]
    slack = [r["float_min_margin"] - r["bound"] for r in ok]
    report = {
        "rule": Path(rule_dir).name,
        "loaded": True,
        "level": level,
        "seed": seed,
        "leaves": len(records),
        "by_outcome": {k: sum(1 for r in records if r.get("outcome") == k) for k in ("ok", "refused", "crash", "violation", "malformed")},
        "crashes": [r for r in records if r.get("outcome") == "crash"][:10],
        "certified": sum(1 for r in ok if r["certified"]),
        "exact_singles": sum(r.get("exact_singles", 0) for r in records),
        "by_kind": {k: sum(1 for r in records if r.get("kind") == k) for k in sorted({r.get("kind") for r in records})},
        "smallest_slack": min(slack) if slack else None,
        "violations": violations,
        "passed": not violations,
        "records": records,
    }
    return report


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("rule_dir")
    ap.add_argument("--level", choices=sorted(LEVELS), default="full")
    ap.add_argument("--folders", nargs="*", default=None)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--counterexamples", default=None)
    ap.add_argument("--only-counterexamples", action="store_true", help="skip the sampled networks and leaves")
    ap.add_argument("--out", default=None)
    args = ap.parse_args(argv)
    cases = json.loads(Path(args.counterexamples).read_text()) if args.counterexamples else None
    folders = ["(none)"] if args.only_counterexamples else args.folders
    report = audit(Path(args.rule_dir), args.level, folders, args.seed, cases, log=lambda m: print(m, file=sys.stderr))
    text = json.dumps(report, indent=1)
    if args.out:
        Path(args.out).write_text(text)
    summary = {k: report[k] for k in report if k != "records"}
    summary["violations"] = report["violations"][:5]
    print(json.dumps(summary, indent=1))
    if not report["loaded"]:
        return 2
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
