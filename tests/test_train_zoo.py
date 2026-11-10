import numpy as np
import pytest

from core.model_folder import load_model_folder
from core.train import train_zoo
from core.zoo import ZooError, load_module, load_weights, networks, read_manifest, split_assignment


def _quiet(*a, **k):
    pass


def test_split_is_deterministic_and_sized(stub):
    a, b = split_assignment(stub), split_assignment(stub)
    assert a == b
    held = [k for k, v in a.items() if v == "held_out"]
    assert len(held) == stub.config["split"]["held_out_per_setting"] * len(stub.setting_names())


def test_train_zoo_writes_manifest_and_refuses_held_out(stub):
    manifest = train_zoo(stub, log=_quiet)
    assert len(manifest["networks"]) == len(stub.config["seeds"])
    for n in manifest["networks"]:
        assert 0.0 <= n["real_accuracy"] <= 1.0
        assert n["n_inputs"] == 25
    dev = networks(stub, "dev")
    held = networks(stub, "held_out")
    assert len(held) == 1 and len(dev) == 2
    w = load_weights(stub, dev[0]["id"])
    assert set(w) == {"inp.weight", "inp.bias", "out.weight", "out.bias"}
    assert all(v.dtype == np.float32 for v in w.values())
    with pytest.raises(ZooError, match="held out"):
        load_weights(stub, held[0]["id"])
    assert load_weights(stub, held[0]["id"], allow_held_out=True)
    load_module(stub, dev[0]["id"])


def test_tampered_weights_are_refused(stub):
    train_zoo(stub, log=_quiet)
    nid = networks(stub, "dev")[0]["id"]
    path = stub.zoo_dir() / f"{nid}.npz"
    w = load_weights(stub, nid)
    w["out.bias"] = w["out.bias"] + 1
    np.savez(path, **w)
    with pytest.raises(ZooError, match="hash"):
        load_weights(stub, nid)


def test_retraining_is_skipped_until_config_changes(stub_path):
    folder = load_model_folder(stub_path)
    train_zoo(folder, log=_quiet)
    first = {n["id"]: n["sha256"] for n in read_manifest(folder)["networks"]}
    msgs = []
    train_zoo(folder, log=msgs.append)
    assert all(m.endswith("up to date") for m in msgs if not m.startswith("    "))
    # Changing a size in config.yaml retrains, with no code change.
    cfg = (stub_path / "config.yaml").read_text().replace("d_hidden: 5", "d_hidden: 6")
    (stub_path / "config.yaml").write_text(cfg)
    folder = load_model_folder(stub_path)
    train_zoo(folder, log=_quiet)
    second = {n["id"]: n["sha256"] for n in read_manifest(folder)["networks"]}
    assert set(first) == set(second) and all(first[k] != second[k] for k in first)
    w = load_weights(folder, networks(folder, "dev")[0]["id"])
    assert w["inp.weight"].shape == (6, 5)
