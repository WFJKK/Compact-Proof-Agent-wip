"""Regression tests for the review findings: a hostile proof is rejected, never a hang or a run-halt.

The two independent reviews found no way to certify a wrong input or double-count;
these cover the robustness and cost gaps they did find.
"""

import gzip
import json
import sys
import time
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "core"))
import helpers  # noqa: E402  (the sandbox copy of core/helpers.py)

from core.check.arith import ProofNumberError, parse_number  # noqa: E402
from core.check.checker import brute_force_proof, check_proof  # noqa: E402
from core.check.worker import CheckerProcess  # noqa: E402
from core.model_folder import load_model_folder  # noqa: E402
from core.versions import trusted  # noqa: E402

REPO = Path(__file__).resolve().parent.parent


@pytest.fixture(scope="module")
def max2():
    return load_model_folder(REPO / "models" / "max2")


# number parsing ------------------------------------------------------------------------
def test_exponent_strings_are_refused_instantly():
    # The bomb was an 11-character string whose value has hundreds of millions of bits.
    for s in ("1e-99999999", "1e-10000000", "1E500", "1.0e9", "nan", "inf", "-inf", "0x10"):
        t = time.monotonic()
        with pytest.raises(ProofNumberError):
            parse_number(s)
        assert time.monotonic() - t < 0.1, s


def test_numbers_must_be_dyadic_and_bounded():
    for s in ("-3/4", "1.25", "5", "0.5", "-7", "3/8", "-0.0"):
        parse_number(s)  # dyadic: accepted
    for s in ("1/3", "7/5", "0.1", "2/6"):
        with pytest.raises(ProofNumberError, match="dyadic"):
            parse_number(s)
    with pytest.raises(ProofNumberError, match="too large"):
        parse_number("1" + "0" * 60)  # ~200-bit integer
    with pytest.raises(ProofNumberError, match="too large"):
        parse_number(str(2**200) + "/4")  # dyadic but a 198-bit numerator
    assert parse_number("2") == 2
    with pytest.raises(ProofNumberError):
        parse_number(True)


# hostile proofs through the checker ----------------------------------------------------
def _contract_approx(folder, nid, approx_spec, leaf):
    w = {k: v.detach().numpy() for k, v in folder.build("v64").state_dict().items()}
    V = folder.input_space("v64")[0]
    return w, V, {
        "schema": "split-tree-v1",
        "network": nid,
        "contract": [{"name": "M", "chain": ["embedding", "linear", "unembedding"]}],
        "approximate": [{"name": "A", "of": "M", **approx_spec}],
        "tree": helpers.split_values(1, 0, V - 1, lambda v: leaf if v == 0 else helpers.leaf("skip")),
        "symmetry": True,
    }


def test_unhashable_contraction_chain_is_rejected_not_crashed(max2):
    proof = {
        "schema": "split-tree-v1",
        "network": "max2-v64-s0",
        "contract": [{"name": "M", "chain": [["embedding"], "linear"]}],
        "tree": helpers.full_tree(max2.input_space("v64")),
    }
    res = check_proof(proof, max2, "max2-v64-s0")
    assert res["status"] == "rejected" and "chain" in res["reason"]


def test_huge_interval_margin_does_not_overflow(max2):
    M = _product(max2, "max2-v64-s0")
    dense = [[helpers.fraction(M[i, j]) for j in range(64)] for i in range(64)]
    dense[0][0] = 1.5e308  # a value that would overflow float() of the resulting margin pre-fix
    _, _, proof = _contract_approx(max2, "max2-v64-s0", {"form": "dense", "values": dense}, helpers.leaf("interval", approx="A"))
    res = check_proof(proof, max2, "max2-v64-s0")
    assert res["status"] == "rejected" and "too large" in res["reason"]  # the entry is refused before any float()


def test_low_rank_rank_is_capped(max2):
    big = [[helpers.fraction(0.0) for _ in range(5000)] for _ in range(64)]
    right = [[helpers.fraction(0.0) for _ in range(64)] for _ in range(5000)]
    _, _, proof = _contract_approx(max2, "max2-v64-s0", {"form": "low_rank", "left": big, "right": right}, helpers.leaf("skip"))
    res = check_proof(proof, max2, "max2-v64-s0")
    assert res["status"] == "rejected" and "inner dimension" in res["reason"]


def test_non_dyadic_approximation_values_are_rejected(max2):
    M = _product(max2, "max2-v64-s0")
    dense = [[helpers.fraction(M[i, j]) for j in range(64)] for i in range(64)]
    dense[1][1] = "1/3"
    _, _, proof = _contract_approx(max2, "max2-v64-s0", {"form": "dense", "values": dense}, helpers.leaf("interval", approx="A"))
    res = check_proof(proof, max2, "max2-v64-s0")
    assert res["status"] == "rejected" and "dyadic" in res["reason"]


def _product(folder, nid):
    w = {k: v.detach().numpy() for k, v in folder.build("v64").state_dict().items()}
    E, W, U = (np.asarray(w[k], float) for k in ("embedding.weight", "linear.weight", "unembedding.weight"))
    return U @ W @ E


def test_check_proof_never_raises_on_structured_garbage(max2):
    garbage = [
        {"schema": "split-tree-v1", "network": "max2-v64-s0", "contract": "notalist", "tree": helpers.leaf("skip")},
        {"schema": "split-tree-v1", "network": "max2-v64-s0", "approximate": [{"name": "A", "of": "nope", "form": "dense", "values": [[1]]}], "tree": helpers.leaf("skip")},
        {"schema": "split-tree-v1", "network": "max2-v64-s0", "tree": {"split": {"position": 0, "cuts": [1.5]}, "children": [helpers.leaf("skip")] * 2}},
        {"schema": "split-tree-v1", "network": "max2-v64-s0", "tree": {"leaf": "single", "approx": {"x": 1}}},
    ]
    for proof in garbage:
        res = check_proof(proof, max2, "max2-v64-s0")  # must return, never raise
        assert res["status"] == "rejected"


# the checker worker: a slow proof is rejected, and the run goes on --------------------
def test_worker_times_out_one_proof_and_recovers(max2, tmp_path):
    gz = tmp_path / "bf.json.gz"
    gz.write_bytes(gzip.compress(json.dumps(brute_force_proof(max2, "max2-v64-s0")).encode()))
    rules = ["single", "interval", "skip", "contract", "symmetry", "approximate"]
    with CheckerProcess(max2.path, trusted(max2), timeout_s=0.001) as cp:
        res, diag = cp.check("max2-v64-s0", gz, rules)
        assert res["status"] == "rejected" and "time limit" in res["reason"] and diag is None
        cp.timeout_s = 120  # the worker was killed and restarted; it still works
        res, diag = cp.check("max2-v64-s0", gz, rules)
        assert res["status"] == "ok" and res["certified"] == 4095 and diag is not None


def test_worker_rejects_an_oversized_or_broken_proof_file(max2, tmp_path):
    bad = tmp_path / "bad.json.gz"
    bad.write_bytes(gzip.compress(b'{"schema": "split-tree-v1", "network": "max2-v64-s0", "tree": {"leaf": "nope"}}'))
    with CheckerProcess(max2.path, trusted(max2), timeout_s=60) as cp:
        res, diag = cp.check("max2-v64-s0", bad, ["single", "skip"])
        assert res["status"] == "rejected"


def test_the_sandbox_image_uses_the_installed_numpy_and_torch(monkeypatch):
    from importlib import metadata

    from core import sandbox

    real = metadata.version
    monkeypatch.setattr(metadata, "version", lambda n: {"numpy": "2.2.6", "torch": "2.8.0+cpu"}.get(n) or real(n))
    v = sandbox.image_versions()
    assert v["numpy"] == "2.2.6" and v["torch"] == "2.8.0"


def test_the_sandbox_image_falls_back_to_the_pins(monkeypatch):
    from importlib import metadata

    from core import sandbox

    def missing(name):
        raise metadata.PackageNotFoundError(name)

    monkeypatch.setattr(metadata, "version", missing)
    assert sandbox.image_versions() == sandbox.requirement_versions()


def test_an_image_that_inspect_misses_is_found_in_the_image_list(monkeypatch):
    import subprocess

    from core import sandbox

    def fake(cmd, **kw):
        if cmd[1:3] == ["image", "inspect"]:
            return subprocess.CompletedProcess(cmd, 1, "", "No such image")
        return subprocess.CompletedProcess(cmd, 0, "sha256:abc\n", "")

    monkeypatch.setattr(sandbox.subprocess, "run", fake)
    assert sandbox.image_id("docker", "img:1") == "sha256:abc"


def test_the_hardened_error_says_whether_the_runtime_or_the_image_is_missing(monkeypatch):
    from core import sandbox

    monkeypatch.setattr(sandbox, "landlock_available", lambda: False)
    monkeypatch.setattr(sandbox, "container_runtime", lambda *a: "docker")
    monkeypatch.setattr(sandbox, "image_id", lambda *a: None)
    with pytest.raises(sandbox.SandboxError, match="docker is running but the image"):
        sandbox.choose({"sandbox": "hardened"})
    monkeypatch.setattr(sandbox, "container_runtime", lambda *a: None)
    with pytest.raises(sandbox.SandboxError, match="no docker or podman answered"):
        sandbox.choose({"sandbox": "hardened"})
