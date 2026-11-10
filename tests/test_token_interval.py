"""The token_interval rule (core/check/tokens.py) on the four attention model folders: its bounds are
sound against the float network on random leaves, exact up to rounding when one position varies, far
tighter than interval leaves, and its token-only rows are charged once per proof. Linear networks refuse
it, and a hand-written proof built from it certifies a whole network well below brute force."""

import itertools
from pathlib import Path

import numpy as np
import pytest
import torch

from core.check.checker import check_proof
from core.check.cost import Counter
from core.check.proof import SCHEMA
from core.check.trace import build_any, make_program
from core.model_folder import load_model_folder
from core.zoo import load_module, load_weights, networks

REPO = Path(__file__).resolve().parent.parent
FOLDERS = ["attn-max4", "attn-min4", "attn-max2", "attn-min2"]
RULES = ("single", "interval", "token_interval", "skip")


def setup(name, setting=None):
    folder = load_model_folder(REPO / "models" / name)
    e = next(x for x in networks(folder) if setting is None or x["setting"] == setting)
    space = folder.input_space(e["setting"])
    prog = make_program(build_any(folder.build(e["setting"])), load_weights(folder, e["id"]), Counter(), space)
    return folder, e, prog, load_module(folder, e["id"])


def true_margin(folder, e, module, ranges, label):
    toks = np.array(list(itertools.product(*[range(lo, hi + 1) for lo, hi in ranges])))
    with torch.no_grad():
        z = module(folder.encode(toks, e["setting"]).to(next(module.parameters()).dtype)).numpy()
    return float((z[:, label] - np.delete(z, label, axis=1).max(axis=1)).min())


def random_leaves(folder, e, rng, n, one_varying):
    sizes = folder.sizes(e["setting"])
    V, P = sizes["d_vocab"], sizes["n_ctx"]
    out = []
    while len(out) < n:
        ranges = []
        free = int(rng.integers(0, P))
        for p in range(P):
            lo = int(rng.integers(0, V))
            width = int(rng.integers(0, V // 2)) if (p == free or not one_varying) else 0
            if not one_varying:
                width = int(rng.integers(0, 4))
            ranges.append((lo, min(V - 1, lo + width)))
        label = folder.task.constant_label(ranges, sizes)
        if label is not None:
            out.append((ranges, int(label)))
    return out


@pytest.mark.parametrize("name", FOLDERS)
def test_bounds_are_sound_and_exact_when_one_position_varies(name):
    folder, e, prog, module = setup(name)
    rng = np.random.default_rng(7)
    for ranges, label in random_leaves(folder, e, rng, 25, one_varying=True):
        ok, bound, _ = prog.run_token_interval(ranges, label, Counter())
        true = true_margin(folder, e, module, ranges, label)
        assert float(bound) <= true + 1e-4  # sound
        assert float(bound) >= true - 1e-3  # and tight: the smallest margin over the leaf's inputs
        assert ok == (float(bound) > 0)


@pytest.mark.parametrize("name", ["attn-max4", "attn-min4"])
def test_bounds_are_sound_when_several_positions_vary(name):
    folder, e, prog, module = setup(name)
    rng = np.random.default_rng(8)
    for ranges, label in random_leaves(folder, e, rng, 25, one_varying=False):
        ok, bound, _ = prog.run_token_interval(ranges, label, Counter())
        assert float(bound) <= true_margin(folder, e, module, ranges, label) + 1e-4


def test_far_tighter_than_interval_and_cheaper_than_singles():
    folder, e, prog, module = setup("attn-max2", "v64")
    ranges, label = [(0, 30), (40, 40)], 40
    c_tok, c_int = Counter(), Counter()
    tok = prog.run_token_interval(ranges, label, c_tok)
    box = prog.run_interval(ranges, label, c_int)
    assert tok[0] and not box[0] and float(box[1]) < 0
    per_single = (e["B"] - e["E"]) // folder.n_inputs(e["setting"])
    # the strip's 31 inputs for well under their singles; the token rows (tables) are shared by the whole proof
    assert c_tok.by_rule["token_interval"] < 31 * per_single / 5


def test_token_rows_are_charged_once_per_proof():
    folder, e, prog, module = setup("attn-max2", "v64")
    first, again = Counter(), Counter()
    prog.run_token_interval([(0, 20), (30, 30)], 30, first)
    prog.run_token_interval([(0, 20), (30, 30)], 30, again)
    assert first.by_rule["tables"] > 0 and again.by_rule.get("tables", 0) == 0
    assert again.by_rule["token_interval"] == first.by_rule["token_interval"]  # the per-leaf work is paid every time


def test_linear_networks_refuse_the_rule():
    folder = load_model_folder(REPO / "models" / "max2")
    e = networks(folder)[0]
    space = folder.input_space(e["setting"])
    V = space[0]
    leaf = {"split": {"position": 1, "cuts": [1]}, "children": [{"leaf": "token_interval"}, {"leaf": "skip"}]}
    tree = {"split": {"position": 0, "cuts": [1]}, "children": [leaf, {"leaf": "skip"}]}
    r = check_proof({"schema": SCHEMA, "network": e["id"], "tree": tree}, folder, e["id"], rule_set=RULES)
    assert V > 1 and r["status"] == "rejected" and "beyond linear maps" in r["reason"]


def test_the_rule_must_be_allowed_in_the_run():
    folder, e, prog, module = setup("attn-max2", "v64")
    proof = {"schema": SCHEMA, "network": e["id"], "tree": {"leaf": "token_interval"}}
    r = check_proof(proof, folder, e["id"], rule_set=("single", "interval", "skip"))
    assert r["status"] == "rejected" and "not allowed" in r["reason"]


def strip_proof(nid, V):
    """Per token a at position 0: the inputs (a, b) with b <= a share the label a, one token_interval leaf;
    the rest (b > a) are token_interval leaves of one input each."""
    children = []
    for a in range(V):
        if a == V - 1:
            children.append({"leaf": "token_interval"})
            continue
        kids = [{"leaf": "token_interval"}] + [{"leaf": "token_interval"} for _ in range(a + 1, V)]
        children.append({"split": {"position": 1, "cuts": list(range(a + 1, V))}, "children": kids})
    tree = {"split": {"position": 0, "cuts": list(range(1, V))}, "children": children}
    return {"schema": SCHEMA, "network": nid, "tree": tree}


def test_a_hand_written_strip_proof_certifies_a_network_well_below_brute_force():
    folder = load_model_folder(REPO / "models" / "attn-max2")
    e = next(x for x in networks(folder) if x["setting"] == "v64")
    V = folder.sizes("v64")["d_vocab"]
    r = check_proof(strip_proof(e["id"], V), folder, e["id"], rule_set=RULES)
    assert r["status"] == "ok" and r["certified"] == e["real_correct"]
    assert r["length"] < e["B"] / 5


def test_a_linear_layer_with_a_bias_keeps_its_bias():
    """Regression (19 October 2026): an nn.Linear with a bias multiplies and adds at one node, and the bias rows
    were kept under the product's memo key, so the bias was dropped and bounds could exceed the true margin."""
    import torch as t

    class Net(t.nn.Module):
        def __init__(self):
            super().__init__()
            self.inp = t.nn.Linear(4, 3, bias=True)
            self.out = t.nn.Linear(3, 4, bias=False)

        def forward(self, x):
            h = self.inp(x)
            w = t.softmax(t.sum(h, dim=2), dim=1)
            return self.out(t.sum(w.unsqueeze(2) * h, dim=1))

    t.manual_seed(0)
    m = Net()
    with t.no_grad():
        m.inp.bias.copy_(t.tensor([5.0, -7.0, 3.0]))
    weights = {k: v.detach().numpy().astype(np.float32) for k, v in m.state_dict().items()}
    prog = make_program(build_any(m), weights, Counter(), [4, 4])
    for ranges in ([(0, 3), (1, 1)], [(0, 3), (0, 3)], [(2, 2), (0, 2)]):
        toks = np.array(list(itertools.product(*[range(lo, hi + 1) for lo, hi in ranges])))
        z = m.double()(t.nn.functional.one_hot(t.tensor(toks), 4).double()).detach().numpy()
        for label in range(4):
            true = float((z[:, label] - np.delete(z, label, axis=1).max(axis=1)).min())
            _, bound, _ = prog.run_token_interval(ranges, label, Counter())
            assert float(bound) <= true + 1e-9


def test_two_terms_with_one_origin_keep_their_own_rows():
    """Regression (19 October 2026, found by the rule route's adversarial review): head @ A + head @ B and
    h + h @ W put two terms with the same origin and position into one Mix; their rows were kept under
    (node, origin, position) at the next product, so the second read the first's and leaves were certified
    with bound 1.0 where the true margin was -9. Rows are now kept under the term's whole chain."""
    import torch as t

    folder = load_model_folder(REPO / "tests" / "stub_twopaths")
    setting = folder.setting_names()[0]
    module = folder.build(setting)
    rng = np.random.default_rng(3)
    for scale in (1.0, 6.0):
        weights = {k: (rng.uniform(-1, 1, size=v.shape) * scale).astype(np.float32) for k, v in module.state_dict().items()}
        module.load_state_dict({k: t.tensor(v) for k, v in weights.items()})
        prog = make_program(build_any(folder.build(setting)), weights, Counter(), folder.input_space(setting))
        V = folder.sizes(setting)["d_vocab"]
        for ranges in ([(0, V - 1), (0, V - 1), (V - 1, V - 1)], [(1, 1), (2, 2), (V - 1, V - 1)], [(0, 2), (3, 3), (1, 2)]):
            label = folder.task.constant_label(ranges, folder.sizes(setting))
            toks = np.array(list(itertools.product(*[range(lo, hi + 1) for lo, hi in ranges])))
            with t.no_grad():
                z = module.double()(folder.encode(toks, setting).double()).numpy()
            true = float((z[:, label] - np.delete(z, label, axis=1).max(axis=1)).min())
            _, bound, _ = prog.run_token_interval(ranges, int(label), Counter())
            assert float(bound) <= true + 1e-9
        module = folder.build(setting)


def test_a_mix_of_scalar_rows_becomes_its_exact_value():
    """A sum over the positions of scores (rows that are scalars) is a Mix whose terms hold scalar rows; when every
    term has one row, leaving the token rules makes it its exact value. This used to fail on the scalar rows
    (found with tests/stub_query, 19 October 2026)."""
    folder = load_model_folder(Path(__file__).resolve().parent / "stub_query")
    setting = folder.setting_names()[0]
    rng = np.random.default_rng(3)
    template = {k: v.detach().numpy() for k, v in folder.build(setting).state_dict().items()}
    w = {k: (rng.uniform(-1, 1, size=v.shape) * max(1e-3, float(np.abs(v).max()))).astype(np.float32) for k, v in template.items()}
    prog = make_program(build_any(folder.build(setting)), w, Counter(), folder.input_space(setting))
    module = folder.build(setting).double()
    module.load_state_dict({k: torch.tensor(v, dtype=torch.float64) for k, v in w.items()})
    e = {"setting": setting}
    for ranges in ([(2, 2), (4, 4), (5, 5)], [(5, 5), (1, 1), (0, 0)], [(0, 3), (4, 4), (2, 2)], [(1, 1), (5, 5), (0, 4)]):
        label = folder.task.constant_label(ranges, folder.sizes(setting))
        _, bound, _ = prog.run_token_interval(ranges, label, Counter())
        true = true_margin(folder, e, module, ranges, label)
        assert float(bound) <= true + 1e-9 * max(1.0, abs(true))
        assert float(bound) >= true - 1e-6 * max(1.0, abs(true))  # one varying position: per input, exact
