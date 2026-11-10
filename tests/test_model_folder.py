
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


def test_size_setting_that_does_not_build_is_refused(stub_path):
    text = (stub_path / "config.yaml").read_text().replace("d_hidden: 5", "d_hiddn: 5")
    (stub_path / "config.yaml").write_text(text)
    with pytest.raises(ModelFolderError, match="does not build"):
        load_model_folder(stub_path)
