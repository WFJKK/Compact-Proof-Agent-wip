"""The sandbox runner: what comes back from a recipe, and what never does."""

import json
import os
from pathlib import Path

import numpy as np
import pytest

from core.runner import BadOutput, Limits, parse_proof_bytes, read_regular, run_recipe

from tests.conftest import make_sandbox, sandbox_modes

LIMITS = Limits(time_s=10, memory_mb=1024, max_proof_bytes=1 << 16)
MODES = sandbox_modes()


@pytest.fixture(params=MODES)
def mode(request):
    return request.param


@pytest.fixture(scope="module")
def setup():
    from core.model_folder import load_model_folder

    folder = load_model_folder(Path(__file__).resolve().parent / "stub_model")
    setting = folder.setting_names()[0]
    weights = {k: v.detach().numpy() for k, v in folder.build(setting).state_dict().items()}
    info = {"sizes": folder.sizes(setting), "input_space": folder.input_space(setting)}
    return folder, weights, info


def run(setup, source, limits=LIMITS, knob=0.5, root=None, mode="process"):
    folder, weights, info = setup
    sb = make_sandbox(mode, (str(folder.path),))
    return run_recipe(source, folder.source(), weights, info, knob, limits, sandbox_root=root, sandbox=sb)


def test_a_proof_comes_back(setup, tmp_path, mode):
    src = (
        "import helpers\n"
        "def make_proof(weights, info, knob):\n"
        "    return helpers.proof(helpers.full_tree(info['input_space']), notes=str(knob))\n"
    )
    ex = run(setup, src, root=tmp_path, mode=mode)
    assert ex.status == "ok" and ex.error is None and ex.mode == mode
    assert ex.proof["schema"] == "split-tree-v1" and ex.proof["notes"] == "0.5"
    assert ex.proof_bytes == len(json.dumps(ex.proof, separators=(",", ":")).encode())
    assert list(tmp_path.iterdir()) == []  # the sandbox folder is gone


def test_the_recipe_sees_exactly_its_inputs(setup, mode):
    folder, weights, info = setup
    src = (
        "import os, json, numpy as np\n"
        "def can_write(path):\n"
        "    try:\n"
        "        with open(path, 'a'):\n"
        "            return True\n"
        "    except OSError:\n"
        "        return False\n"
        "def make_proof(weights, info, knob):\n"
        "    here = os.path.dirname(os.path.abspath(__file__))\n"
        "    return {'files': sorted(os.listdir(here)), 'env': sorted(os.environ),\n"
        "            'weights': {k: np.asarray(v).tolist() for k, v in weights.items()},\n"
        "            'dtypes': sorted({str(v.dtype) for v in weights.values()}), 'info': info, 'knob': knob,\n"
        "            'writable': can_write(os.path.join(here, 'helpers.py')) or can_write(os.path.join(here, 'new.txt'))}\n"
    )
    ex = run(setup, src, limits=Limits(time_s=10, memory_mb=1024, max_proof_bytes=1 << 20), mode=mode)
    assert ex.status == "ok", ex.error
    p = ex.proof
    assert p["files"] == ["harness.py", "helpers.py", "input.json", "model.py", "out", "recipe.py", "tmp", "weights.npz"]
    assert "ANTHROPIC_API_KEY" not in p["env"] and "CPL_ANTHROPIC_KEY" not in p["env"]
    assert p["info"] == info and p["knob"] == 0.5 and p["dtypes"] == ["float32"]
    for k, v in weights.items():
        assert np.array_equal(np.asarray(p["weights"][k], dtype=np.float32), v)
    # Not real protection in process mode (the recipe owns these files), but no accidental writes.
    if os.geteuid() != 0 or mode != "process":
        assert p["writable"] is False


def test_numpy_values_become_json(setup):
    ex = run(setup, "import numpy as np\ndef make_proof(w, i, k):\n    return {'a': np.int64(3), 'b': np.arange(3), 'c': np.float32(0.5), 'd': np.bool_(True)}\n")
    assert ex.status == "ok" and ex.proof == {"a": 3, "b": [0, 1, 2], "c": 0.5, "d": True}


@pytest.mark.parametrize(
    "source, status, message",
    [
        ("def make_proof(w, i, k):\n    raise ValueError('deliberate')\n", "crash", "ValueError: deliberate"),
        ("raise ImportError('at import time')\ndef make_proof(w, i, k):\n    return {}\n", "crash", "at import time"),
        ("import sys\ndef make_proof(w, i, k):\n    sys.exit(0)\n", "crash", "SystemExit"),
        ("def make_proof(w, i, k):\n    return [1, 2]\n", "bad_output", "returned a list"),
        ("def make_proof(w, i, k):\n    return {'x': float('nan')}\n", "bad_output", "not valid JSON data"),
        ("def make_proof(w, i, k):\n    return {'x': {1, 2}}\n", "bad_output", "not JSON-serialisable"),
        ("def make_proof(w, i, k):\n    return {'x': 'y' * 100000}\n", "bad_output", "above the limit"),
        ("import os\ndef make_proof(w, i, k):\n    os._exit(0)\n", "bad_output", "wrote no proof file"),
        ("import os, signal\ndef make_proof(w, i, k):\n    os.kill(os.getpid(), signal.SIGKILL)\n", "crash", "SIGKILL"),
        ("import os\ndef make_proof(w, i, k):\n    os._exit(7)\n", "crash", "exited with code 7"),
    ],
)
def test_failures_get_their_status(setup, source, status, message, mode):
    ex = run(setup, source, mode=mode)
    assert ex.status == status and message in ex.error, ex.error
    assert ex.proof is None


def _write_out(body: str) -> str:
    """A recipe that writes out/proof.json itself and exits without the harness."""
    return (
        "import os\n"
        "def make_proof(w, i, k):\n"
        "    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'proof.json')\n"
        f"{body}"
        "    os._exit(0)\n"
    )


@pytest.mark.parametrize(
    "body, message",
    [
        ("    open(out, 'w').write('{\"schema\": ')\n", "not valid JSON"),
        ("    open(out, 'w').write('{\"a\": 1, \"a\": 2}')\n", "duplicate key"),
        ("    open(out, 'w').write('{\"a\": NaN}')\n", "NaN is not a JSON number"),
        ("    open(out, 'w').write('[1, 2]')\n", "not an object"),
        ("    open(out, 'wb').write(b'\\xff\\xfe')\n", "not UTF-8"),
        ("    open(out, 'w').write('[' * 50000 + ']' * 50000)\n", "nested too deeply"),
        ("    os.symlink('/etc/passwd', out)\n", "links are refused"),
        ("    os.mkfifo(out)\n", "not a regular file"),
        ("    open(out, 'w').write('{\"a\": \"' + 'x' * 200000 + '\"}')\n", "above the limit"),
    ],
)
def test_output_written_behind_the_harness_is_only_ever_data(setup, body, message, mode):
    ex = run(setup, _write_out(body), limits=Limits(time_s=10, memory_mb=1024, max_proof_bytes=1 << 17), mode=mode)
    if mode == "landlock" and ("symlink" in body or "mkfifo" in body):
        assert ex.status == "crash" and "PermissionError" in ex.error  # the sandbox stops it even earlier
    else:
        assert ex.status == "bad_output" and message in ex.error, ex.error


def test_time_limit(setup, mode):
    limits = Limits(time_s=1.5, memory_mb=1024, max_proof_bytes=1 << 16)
    ex = run(setup, "def make_proof(w, i, k):\n    while True:\n        pass\n", limits=limits, mode=mode)
    assert ex.status == "timeout" and 1.5 <= ex.runtime_s < 12


def test_children_are_killed_with_the_recipe(setup, tmp_path):
    import time

    flag = tmp_path / "survived"
    child = f"import time; time.sleep(3); open({str(flag)!r}, 'w').write('x')"
    src = (
        "import subprocess, sys\n"
        "def make_proof(w, i, k):\n"
        f"    subprocess.Popen([sys.executable, '-c', {child!r}])\n"
        "    while True:\n"
        "        pass\n"
    )
    ex = run(setup, src, limits=Limits(time_s=1, memory_mb=1024, max_proof_bytes=1 << 16))
    assert ex.status == "timeout", ex.error
    time.sleep(3.5)
    assert not flag.exists()


def test_memory_limit(setup, mode):
    src = "import numpy as np\ndef make_proof(w, i, k):\n    keep = [np.ones(25_000_000) for _ in range(8)]\n    return {}\n"
    ex = run(setup, src, limits=Limits(time_s=20, memory_mb=400, max_proof_bytes=1 << 16), mode=mode)
    assert ex.status == "crash" and ("memory limit" in ex.error or "MemoryError" in ex.error), ex.error


def test_parse_proof_bytes_and_read_regular(tmp_path):
    assert parse_proof_bytes(b'{"a": [1, "2/3"]}', 100) == {"a": [1, "2/3"]}
    for bad in (b"{", b'{"a": Infinity}', b'"text"', b'{"a": -NaN}'):
        with pytest.raises(BadOutput):
            parse_proof_bytes(bad, 100)
    with pytest.raises(BadOutput, match="above the limit"):
        parse_proof_bytes(b'{"a": 1}', 3)
    f = tmp_path / "f"
    assert read_regular(f, 10) is None
    f.write_bytes(b"12345")
    assert read_regular(f, 10) == b"12345"
    with pytest.raises(BadOutput, match="above the limit"):
        read_regular(f, 4)
