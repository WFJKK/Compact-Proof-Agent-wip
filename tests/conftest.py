import shutil
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
STUB = Path(__file__).resolve().parent / "stub_model"


@pytest.fixture
def stub_path(tmp_path) -> Path:
    """A fresh copy of the stub model folder, so tests can write its zoo."""
    dst = tmp_path / "stub"
    shutil.copytree(STUB, dst, ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    return dst


@pytest.fixture
def stub(stub_path):
    from core.model_folder import load_model_folder

    return load_model_folder(stub_path)


def _quiet(*a, **k):
    pass


@pytest.fixture(scope="session")
def trained_stub(tmp_path_factory) -> Path:
    """A copy of the stub model folder with a trained zoo and E and B filled in."""
    from core.check.costs import fill_costs
    from core.model_folder import load_model_folder
    from core.train import train_zoo

    dst = tmp_path_factory.mktemp("model") / "stub"
    shutil.copytree(STUB, dst, ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    folder = load_model_folder(dst)
    train_zoo(folder, log=_quiet)
    fill_costs(folder, log=_quiet)
    return dst


def sandbox_modes(hardened_only: bool = False) -> list[str]:
    """The sandbox modes that work on this machine. CPL_TEST_SANDBOX_IMAGE names the container image to test with."""
    import os

    from core.sandbox import DEFAULT_IMAGE, container_runtime, image_id, landlock_available

    modes = [] if hardened_only else ["process"]
    if landlock_available():
        modes.append("landlock")
    rt = container_runtime()
    if rt and image_id(rt, os.environ.get("CPL_TEST_SANDBOX_IMAGE", DEFAULT_IMAGE)):
        modes.append("container")
    return modes


def make_sandbox(mode: str, protected=()):
    import os

    from core.sandbox import DEFAULT_IMAGE, Sandbox, container_runtime, image_id

    if mode == "container":
        rt = container_runtime()
        image = os.environ.get("CPL_TEST_SANDBOX_IMAGE", DEFAULT_IMAGE)
        return Sandbox("container", runtime=rt, image=image, image_id=image_id(rt, image), protected=tuple(protected))
    return Sandbox(mode, protected=tuple(protected))
