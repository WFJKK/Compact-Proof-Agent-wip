
import pytest

from core.model_folder import ModelFolderError, load_model_folder


def test_stub_loads(stub):
    assert stub.module_class.__name__ == "Tiny"
    assert stub.setting_names() == ["tiny"]
    assert stub.input_space("tiny") == [5, 5]
    assert stub.n_inputs("tiny") == 25
    assert stub.network_id("tiny", 2) == f"{stub.name}-tiny-s2"
    assert "class Tiny" in stub.source()
    assert len(stub.folder_hash()) == 64


def test_folder_hash_changes_with_content(stub_path):
    h1 = load_model_folder(stub_path).folder_hash()
    (stub_path / "task.py").write_text((stub_path / "task.py").read_text() + "\n# changed\n")
    assert load_model_folder(stub_path).folder_hash() != h1


def test_missing_file_is_refused(stub_path):
    (stub_path / "task.py").unlink()
    with pytest.raises(ModelFolderError, match="missing task.py"):
        load_model_folder(stub_path)


def test_two_modules_are_refused(stub_path):
    src = (stub_path / "model.py").read_text()
    (stub_path / "model.py").write_text(src + "\n\nclass Other(torch.nn.Module):\n    pass\n")
    with pytest.raises(ModelFolderError, match="exactly one nn.Module"):
        load_model_folder(stub_path)


def test_incomplete_config_is_refused(stub_path):
    text = (stub_path / "config.yaml").read_text().replace("zoo_path: zoo\n", "")
    (stub_path / "config.yaml").write_text(text)
    with pytest.raises(ModelFolderError, match="zoo_path"):
        load_model_folder(stub_path)


def test_incomplete_task_is_refused(stub_path):
    text = (stub_path / "task.py").read_text().replace("def constant_label", "def not_constant_label")
    (stub_path / "task.py").write_text(text)
    with pytest.raises(ModelFolderError, match="constant_label"):
        load_model_folder(stub_path)


def test_bad_held_out_count_is_refused(stub_path):
    text = (stub_path / "config.yaml").read_text().replace("held_out_per_setting: 1", "held_out_per_setting: 3")
    (stub_path / "config.yaml").write_text(text)
    with pytest.raises(ModelFolderError, match="held_out_per_setting"):
        load_model_folder(stub_path)


def test_a_named_split_holds_out_exactly_the_seeds_it_names(stub_path):
    """split.held_out_seeds names a size setting's held-out seeds instead of drawing them (for a folder that
    takes over networks other runs have developed on); it must name held_out_per_setting seeds of the folder."""
    from core.zoo import split_assignment

    base = (stub_path / "config.yaml").read_text()
    drawn = split_assignment(load_model_folder(stub_path))
    for held in (0, 1, 2):
        (stub_path / "config.yaml").write_text(base.replace("  seed: 7\n", f"  seed: 7\n  held_out_seeds:\n    tiny: [{held}]\n"))
        split = split_assignment(load_model_folder(stub_path))
        assert {seed for (setting, seed), v in split.items() if v == "held_out"} == {held} and len(split) == len(drawn)
    for bad in ("tiny: [0, 1]", "tiny: [5]", "tiny: 0", "huge: [0]"):
        (stub_path / "config.yaml").write_text(base.replace("  seed: 7\n", f"  seed: 7\n  held_out_seeds:\n    {bad}\n"))
        with pytest.raises(ModelFolderError, match="held_out_seeds"):
            load_model_folder(stub_path)


def test_the_linear_ladder_has_three_vocabulary_sizes_too_large_for_a_copy_of_the_weights():
    """tests/max2_ladder (10 November 2026): the linear max-of-2 network at 24, 32 and 48 tokens, hidden width 8,
    four seeds each, two for development (all at full accuracy) and two held out, with cost-v4's B (E plus one
    forward pass per input). The sizes are chosen so that a checker cannot carry a copy of a network's weights:
    the least a copy holds, each weight's sign and significant bits (the Lean service's weight_bits, in its
    scripts/accept.py), is over the service's default description budget (policy v11: 8192 + 4 E, or half of
    weight_bits where that is more, at most 16,384), by 8% at vocabulary size 24. On the tiny networks it is
    not, which is why the linear ladder does not start there."""
    from fractions import Fraction
    from pathlib import Path

    import numpy as np

    from core.zoo import load_weights, networks

    def weight_bits(folder, entry) -> int:
        held = 0
        for tensor in load_weights(folder, entry["id"], allow_held_out=True).values():  # maintenance, not the agent
            for v in np.asarray(tensor, dtype=np.float64).reshape(-1):
                m = abs(Fraction(float(v)).numerator)
                held += 1 + (m >> ((m & -m).bit_length() - 1)).bit_length() if m else 1
        return held

    def budget(folder, entry) -> int:  # the service's size_budget, policy v11
        return max(8192 + 4 * entry["E"], min(weight_bits(folder, entry) // 2, 16384))

    root = Path(__file__).resolve().parent
    ladder = load_model_folder(root / "max2_ladder")
    sizes = [ladder.sizes(s) for s in ladder.setting_names()]
    assert [(z["n_ctx"], z["d_vocab"], z["d_model"]) for z in sizes] == [(2, 24, 8), (2, 32, 8), (2, 48, 8)]
    nets = networks(ladder, None)  # both splits
    assert len(nets) == 12 and all(n["cost_model"] == "cost-v4" and n["checked_correct"] == n["real_correct"] for n in nets)
    for setting in ladder.setting_names():
        mine = [n for n in nets if n["setting"] == setting]
        assert sorted(n["split"] for n in mine) == ["dev", "dev", "held_out", "held_out"]
        assert all((n["B"] - n["E"]) % n["n_inputs"] == 0 for n in mine)  # no plan in B
    assert all(n["real_correct"] == n["n_inputs"] for n in nets if n["split"] == "dev")
    assert all(n["real_correct"] >= n["n_inputs"] - 1 for n in nets)
    for n in nets:
        assert weight_bits(ladder, n) > budget(ladder, n), n["id"]
    tiny = load_model_folder(root / "max2_tiny")
    assert all(weight_bits(tiny, n) < budget(tiny, n) for n in networks(tiny, None))


def test_size_setting_that_does_not_build_is_refused(stub_path):
    text = (stub_path / "config.yaml").read_text().replace("d_hidden: 5", "d_hiddn: 5")
    (stub_path / "config.yaml").write_text(text)
    with pytest.raises(ModelFolderError, match="does not build"):
        load_model_folder(stub_path)
