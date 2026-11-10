"""Adversarial tests (Step 6 of the spec): every attack must fail safely, for every model.

Recipe attacks run in each hardened sandbox mode that works on this machine:
landlock on Linux, and container when a runtime and an image are present
(CPL_TEST_SANDBOX_IMAGE names the image; the default is the one
`python -m core.sandbox build` makes). The weak process mode is tested for what
it can promise: limits, proof files that are only ever data, and planted
bytecode that the checker never loads and the loop detects.

Each hole found later gets its own test here.
"""

import importlib.util
import json
import marshal
import os
import sys
import socket
import threading
import time
from pathlib import Path

import pytest
import yaml

from core import loop
from core.check.worker import CheckerProcess
from core.model_folder import load_model_folder
from core.runner import Limits, run_recipe
from core.sandbox import SandboxError, check_probe, landlock_policy, probe, protected_paths
from core.util import REPO_ROOT
from core.versions import trusted
from core.zoo import load_weights, networks, read_manifest

from tests.conftest import make_sandbox, sandbox_modes

HARDENED = sandbox_modes(hardened_only=True)
LIMITS = Limits(time_s=60, memory_mb=1024, max_proof_bytes=1 << 20)
pytestmark = pytest.mark.skipif(not HARDENED, reason="no hardened sandbox mode works on this machine")


@pytest.fixture(params=["stub", "max2"])
def model(request, trained_stub):
    return load_model_folder(trained_stub if request.param == "stub" else REPO_ROOT / "models" / "max2")


@pytest.fixture(params=HARDENED)
def sandbox(request, model, tmp_path):
    return make_sandbox(request.param, protected_paths({"runs_dir": str(tmp_path)}, model, tmp_path))


def attack(sandbox, model, body: str, payload: dict, limits=LIMITS):
    """Run a recipe whose make_proof returns {"result": <body's result>} with PAYLOAD available to it."""
    nid = networks(model, "dev")[0]["id"]
    entry = next(e for e in read_manifest(model)["networks"] if e["id"] == nid)
    source = f"import json, os, socket, sys\nPAYLOAD = json.loads({json.dumps(payload)!r})\n\n{body}"
    return run_recipe(
        source,
        model.source(),
        load_weights(model, nid),
        {"sizes": model.sizes(entry["setting"]), "input_space": model.input_space(entry["setting"])},
        0.0,
        limits,
        sandbox=sandbox,
    )


def _head(path) -> str:
    with open(path, "rb") as f:
        return f.read(32).hex()


def test_writes_into_trusted_folders_fail(sandbox, model):
    marker = f"attack-{os.urandom(4).hex()}"
    targets = [
        REPO_ROOT / "core" / "check" / "__pycache__" / f"checker.{marker}.pyc",
        REPO_ROOT / "core" / f"{marker}.py",
        model.path / f"{marker}.txt",
        model.zoo_dir() / f"{marker}.npz",
        REPO_ROOT / f"{marker}.txt",
    ]
    body = (
        "def make_proof(weights, info, knob):\n"
        "    out = {}\n"
        "    for t in PAYLOAD['targets']:\n"
        "        try:\n"
        "            os.makedirs(os.path.dirname(t), exist_ok=True)\n"
        "            with open(t, 'wb') as f:\n"
        "                f.write(b'planted')\n"
        "            out[t] = 'written'\n"
        "        except Exception as e:\n"
        "            out[t] = type(e).__name__\n"
        "    return {'result': out}\n"
    )
    try:
        ex = attack(sandbox, model, body, {"targets": [str(t) for t in targets]})
        assert ex.status == "ok", ex.error
        if sandbox.mode == "landlock":  # same paths inside and out; a container's /tmp is its own scratch space
            assert "written" not in ex.proof["result"].values()
    finally:
        found = [t for t in targets if t.exists()]
        for t in found:
            t.unlink()
    assert not found  # judged on this side: nothing landed


def test_reads_of_weights_not_given_fail(sandbox, model):
    given = networks(model, "dev")[0]["id"]
    others = [model.zoo_dir() / e["weights"] for e in read_manifest(model)["networks"] if e["id"] != given]
    targets = others + [model.manifest_path(), REPO_ROOT / "core" / "check" / "checker.py", model.path / "task.py"]
    body = (
        "def make_proof(weights, info, knob):\n"
        "    out = {}\n"
        "    for t in PAYLOAD['targets']:\n"
        "        try:\n"
        "            with open(t, 'rb') as f:\n"
        "                out[t] = f.read(32).hex()\n"
        "        except Exception as e:\n"
        "            out[t] = type(e).__name__\n"
        "    return {'result': out}\n"
    )
    ex = attack(sandbox, model, body, {"targets": [str(t) for t in targets]})
    assert ex.status == "ok", ex.error
    assert any(e["split"] == "held_out" for e in read_manifest(model)["networks"])
    for t in targets:
        assert ex.proof["result"][str(t)] != _head(t), f"read {t}"


def test_network_connections_fail(sandbox, model):
    tcp = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    tcp.bind(("127.0.0.1", 0))
    tcp.listen(1)
    tcp.settimeout(0.2)
    udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    udp.bind(("127.0.0.1", 0))
    udp.settimeout(0.2)
    got, stop = [], threading.Event()

    def listen():
        while not stop.is_set():
            for s in (tcp, udp):
                try:
                    got.append(s.accept() if s is tcp else s.recvfrom(64))
                except OSError:
                    pass

    th = threading.Thread(target=listen, daemon=True)
    th.start()
    body = (
        "def make_proof(weights, info, knob):\n"
        "    out = {}\n"
        "    def tcp():\n"
        "        socket.create_connection(('127.0.0.1', PAYLOAD['tcp']), timeout=2).sendall(b'x')\n"
        "    def udp():\n"
        "        socket.socket(socket.AF_INET, socket.SOCK_DGRAM).sendto(b'x', ('127.0.0.1', PAYLOAD['udp']))\n"
        "    def dns():\n"
        "        socket.getaddrinfo('example.com', 443)\n"
        "    def unix():\n"
        "        socket.socket(socket.AF_UNIX, socket.SOCK_STREAM).connect('/var/run/docker.sock')\n"
        "    for name, fn in (('tcp', tcp), ('udp', udp), ('dns', dns), ('unix', unix)):\n"
        "        try:\n"
        "            fn()\n"
        "            out[name] = 'ok'\n"
        "        except Exception as e:\n"
        "            out[name] = type(e).__name__\n"
        "    return {'result': out}\n"
    )
    try:
        ex = attack(sandbox, model, body, {"tcp": tcp.getsockname()[1], "udp": udp.getsockname()[1]})
        time.sleep(0.5)
    finally:
        stop.set()
        th.join(timeout=2)
        tcp.close()
        udp.close()
    assert ex.status == "ok", ex.error
    assert not got
    r = ex.proof["result"]
    assert r["tcp"] != "ok" and r["dns"] != "ok" and r["unix"] != "ok"
    if sandbox.mode == "landlock":
        assert r["udp"] != "ok"  # in a container, UDP goes to the container's own loopback and nowhere else


def test_checker_and_cost_model_cannot_be_imported(sandbox, model):
    body = (
        "def make_proof(weights, info, knob):\n"
        "    sys.path.insert(0, PAYLOAD['repo'])\n"
        "    out = {}\n"
        "    for name in ('core.check.checker', 'core.check.cost', 'core'):\n"
        "        try:\n"
        "            __import__(name)\n"
        "            out[name] = 'imported'\n"
        "        except Exception as e:\n"
        "            out[name] = type(e).__name__\n"
        "    return {'result': out}\n"
    )
    ex = attack(sandbox, model, body, {"repo": str(REPO_ROOT)})
    assert ex.status == "ok", ex.error
    assert "imported" not in ex.proof["result"].values()


def test_time_and_memory_limits(sandbox, model):
    forever = "def make_proof(weights, info, knob):\n    while True:\n        pass\n"
    ex = attack(sandbox, model, forever, {}, Limits(time_s=3, memory_mb=1024, max_proof_bytes=1 << 16))
    assert ex.status == "timeout"
    hog = (
        "import numpy as np\n"
        "def make_proof(weights, info, knob):\n"
        "    keep = [np.ones(25_000_000) for _ in range(12)]\n"
        "    return {}\n"
    )
    ex = attack(sandbox, model, hog, {}, Limits(time_s=60, memory_mb=400, max_proof_bytes=1 << 16))
    assert ex.status == "crash" and ("memory" in ex.error.lower()), ex.error


def test_the_api_key_never_reaches_a_recipe(sandbox, model, monkeypatch):
    canary = "sk-ant-canary-" + os.urandom(8).hex()
    monkeypatch.setenv("CPL_ANTHROPIC_KEY", canary)
    body = (
        "def make_proof(weights, info, knob):\n"
        "    seen = json.dumps(dict(os.environ))\n"
        "    for pid in {os.getppid(), 1, PAYLOAD['driver']}:\n"
        "        try:\n"
        "            seen += open('/proc/%d/environ' % pid, 'rb').read().decode('latin-1')\n"
        "        except Exception:\n"
        "            pass\n"
        "    return {'result': seen}\n"
    )
    ex = attack(sandbox, model, body, {"driver": os.getpid()})
    assert ex.status == "ok", ex.error
    assert canary not in ex.proof["result"]


# proof-file attacks, through the whole loop ---------------------------------------------
PROOF_ATTACKS = {
    "false_claim": ("ok", "tree = helpers.split_values(0, 0, V - 1, lambda v: helpers.leaf('interval'))\n    return helpers.proof(tree)"),
    "overlapping_pieces": ("bad_output", "return helpers.proof({'split': {'position': 0, 'cuts': [2, 1]}, 'children': [helpers.leaf('skip')] * 3})"),
    "outside_the_input_space": ("bad_output", "return helpers.proof({'split': {'position': 0, 'cuts': [V + 3]}, 'children': [helpers.leaf('skip')] * 2})"),
    "missing_position": ("bad_output", "return helpers.proof({'split': {'position': 7, 'cuts': [1]}, 'children': [helpers.leaf('skip')] * 2})"),
    "rule_not_allowed": ("bad_output", "return helpers.proof(helpers.full_tree(info['input_space']), symmetry=True)"),
    "unknown_rule": ("bad_output", "return helpers.proof(helpers.full_tree(info['input_space'], rule='trust_me'))"),
    "another_networks_name": ("bad_output", "p = helpers.proof(helpers.full_tree(info['input_space']))\n    p['network'] = 'someone-else'\n    return p"),
    "malformed_json": ("bad_output", "p = helpers.proof(helpers.full_tree(info['input_space']))\n    p['notes'] = float('inf')\n    return p"),
    "oversized_body": ("bad_output", "return helpers.proof(helpers.full_tree(info['input_space']), notes='x' * 200000)"),
}


def _response(name: str, code: str) -> str:
    return (
        f"CLAIM: attack {name}.\n\nWHY IT HELPS: it does not.\n\nPREDICTION: rejected.\n\nKNOB: unused.\n\n"
        f"RECIPE:\n```python\nimport helpers\n\n\ndef make_proof(weights, info, knob):\n    V = info['input_space'][0]\n    {code}\n```\n\n"
        f"NOTES: attack {name}.\n"
    )


def test_proof_file_attacks_through_the_loop(model, tmp_path):
    responses = tmp_path / "responses"
    responses.mkdir()
    names = list(PROOF_ATTACKS)
    for i, name in enumerate(names):
        (responses / f"{i:02d}_{name}.md").write_text(_response(name, PROOF_ATTACKS[name][1]))
    first = [next(e["id"] for e in networks(model, "dev") if e["setting"] == s) for s in model.setting_names()]
    cfg = {
        "run_id": "attacks",
        "model": str(model.path),
        "runs_dir": str(tmp_path / "runs"),
        "networks": first[:1],
        "knob_values": [0],
        "screen": False,
        "baselines": False,
        "fake_responses": [str(responses)],
        "rounds_max": len(names),
        "rule_set": ["single", "interval", "skip", "contract", "approximate"],  # no symmetry
        "max_proof_mb": 0.1,
        "time_limit_s": 60,
    }
    path = tmp_path / "attacks.yaml"
    path.write_text(yaml.safe_dump(cfg))
    ctx = loop.start(path, log=lambda *a: None)
    assert ctx.sandbox.hardened
    loop.drive(ctx)
    records = ctx.run.read_archive()
    for k, name in enumerate(names, start=1):
        rs = [r for r in records if r["round"] == k]
        assert rs and {r["status"] for r in rs} == {PROOF_ATTACKS[name][0]}, (name, [(r["status"], r["error"]) for r in rs])
        for r in rs:
            if r["status"] == "ok":
                assert r["certified"] <= r["real_correct"] and r["rejected_summary"]["count"] > 0


# what the weak process mode still guarantees -------------------------------------------
def _plant(target: Path, code_source: str) -> tuple[Path, bytes | None]:
    """Write a compiled file for target that CPython would load in place of the source; returns it and any file it replaced."""
    pyc = Path(importlib.util.cache_from_source(str(target)))
    pyc.parent.mkdir(exist_ok=True)
    old = pyc.read_bytes() if pyc.exists() else None
    st = target.stat()
    header = importlib.util.MAGIC_NUMBER + (0).to_bytes(4, "little")
    header += (int(st.st_mtime) & 0xFFFFFFFF).to_bytes(4, "little") + (st.st_size & 0xFFFFFFFF).to_bytes(4, "little")
    pyc.write_bytes(header + marshal.dumps(compile(code_source, str(target), "exec")))
    return pyc, old


def _unplant(pyc: Path, old: bytes | None) -> None:
    if old is None:
        pyc.unlink(missing_ok=True)
    else:
        pyc.write_bytes(old)


def test_planted_bytecode_is_never_loaded_by_the_checker(tmp_path):
    import subprocess
    import sys

    target = REPO_ROOT / "core" / "check" / "cost.py"
    pyc, old = _plant(target, "raise RuntimeError('PLANTED BYTECODE RAN')\n")
    try:
        # An ordinary interpreter would run the planted file ...
        naive = subprocess.run(
            [sys.executable, "-c", "import sys; sys.path.insert(0, %r); import core.check.cost" % str(REPO_ROOT)],
            capture_output=True,
            text=True,
            cwd=tmp_path,
        )
        assert "PLANTED BYTECODE RAN" in naive.stderr
        # ... but the checker process never reads compiled files next to the sources.
        folder = load_model_folder(REPO_ROOT / "models" / "max2")
        with CheckerProcess(folder.path, trusted(folder)) as cp:
            assert cp.proc.poll() is None
    finally:
        _unplant(pyc, old)


def test_the_loop_halts_when_compiled_files_appear(trained_stub, tmp_path):
    cfg = {
        "run_id": "halt",
        "model": str(trained_stub),
        "runs_dir": str(tmp_path / "runs"),
        "sandbox": "process",
        "fake_responses": [],
        "rounds_max": 1,
    }
    path = tmp_path / "halt.yaml"
    path.write_text(yaml.safe_dump(cfg))
    ctx = loop.start(path, log=lambda *a: None)
    ctx.verify_trusted()
    tag = sys.implementation.cache_tag
    planted = REPO_ROOT / "core" / "__pycache__" / f"planted-{os.urandom(4).hex()}.{tag}.pyc"
    planted.parent.mkdir(exist_ok=True)
    planted.write_bytes(b"not really bytecode")
    try:
        with pytest.raises(loop.RoundError, match="compiled files appeared"):
            ctx.verify_trusted()
    finally:
        planted.unlink()
    # Bytecode outside __pycache__ counts whatever its name.
    loose = REPO_ROOT / "core" / f"planted-{os.urandom(4).hex()}.pyc"
    loose.write_bytes(b"not really bytecode")
    try:
        with pytest.raises(loop.RoundError, match="compiled files appeared"):
            ctx.verify_trusted()
    finally:
        loose.unlink()


def test_another_pythons_bytecode_does_not_halt_the_loop(trained_stub, tmp_path):
    """A second run started from a different interpreter writes files this run never loads."""
    cfg = {
        "run_id": "other-python",
        "model": str(trained_stub),
        "runs_dir": str(tmp_path / "runs"),
        "sandbox": "process",
        "fake_responses": [],
        "rounds_max": 1,
    }
    path = tmp_path / "other.yaml"
    path.write_text(yaml.safe_dump(cfg))
    ctx = loop.start(path, log=lambda *a: None)
    other = "cpython-399" if sys.implementation.cache_tag != "cpython-399" else "cpython-398"
    planted = REPO_ROOT / "core" / "__pycache__" / f"loop.{other}.pyc"
    planted.parent.mkdir(exist_ok=True)
    planted.write_bytes(b"another interpreter's cache")
    try:
        ctx.verify_trusted()
    finally:
        planted.unlink()


def test_starting_the_loop_writes_no_bytecode_into_the_core(tmp_path):
    """Whatever the shell sets, importing the loop compiles nothing into core/ but core/__init__ itself."""
    import subprocess

    env = {k: v for k, v in os.environ.items() if k != "PYTHONDONTWRITEBYTECODE"}
    prefix = tmp_path / "pycache"
    subprocess.run(
        [sys.executable, "-X", f"pycache_prefix={prefix}", "-c", "import core.loop, core.report, core.final"],
        cwd=REPO_ROOT, env=env, check=True,
    )
    core_dir = str((REPO_ROOT / "core").resolve()).lstrip("/")
    written = [p for p in prefix.rglob("*.pyc") if core_dir in str(p)]
    assert [p.name.split(".")[0] for p in written] in ([], ["__init__"]), written


def test_process_mode_is_reported_as_weak(trained_stub, tmp_path):
    folder = load_model_folder(trained_stub)
    sb = make_sandbox("process")
    report = probe(sb, folder, networks(folder, "dev")[0]["id"], tmp_path / "run")
    assert "read_other_weights" in report["critical_escapes"] and "write_trusted_folder" in report["critical_escapes"]
    check_probe(sb, report)  # reported, not refused
    logs = []
    cfg = {"run_id": "weak", "model": str(trained_stub), "runs_dir": str(tmp_path / "runs"), "sandbox": "process", "rounds_max": 1}
    path = tmp_path / "weak.yaml"
    path.write_text(yaml.safe_dump(cfg))
    loop.start(path, log=logs.append)
    assert any("weak" in line for line in logs)


def test_a_hardened_mode_that_leaks_is_refused():
    sb = make_sandbox(HARDENED[0])
    with pytest.raises(SandboxError, match="not keeping recipes in"):
        check_probe(sb, {"critical_escapes": ["read_other_weights"], "minor_escapes": [], "attempts": {}})


def test_landlock_policy_never_exposes_protected_folders(tmp_path):
    with pytest.raises(SandboxError, match="contains"):
        landlock_policy(tmp_path / "box", protected=("/usr/share/somewhere",))
    pol = landlock_policy(tmp_path / "box", protected_paths({"runs_dir": str(tmp_path)}))
    for p in pol["read"] + pol["read_write"]:
        assert not Path(p).resolve() == REPO_ROOT and REPO_ROOT.resolve() not in Path(p).resolve().parents or str(tmp_path) in p


def test_probe_blocks_everything_in_hardened_modes(trained_stub, tmp_path):
    folder = load_model_folder(trained_stub)
    for mode in HARDENED:
        sb = make_sandbox(mode, protected_paths({"runs_dir": str(tmp_path)}, folder, tmp_path / "run"))
        report = probe(sb, folder, networks(folder, "dev")[0]["id"], tmp_path / "run")
        assert report["critical_escapes"] == [] and report["minor_escapes"] == [], (mode, report)
        assert len(report["attempts"]) == 12


def _run(model, sb, source, limits):
    nid = networks(model, "dev")[0]["id"]
    entry = next(e for e in read_manifest(model)["networks"] if e["id"] == nid)
    return run_recipe(
        source, model.source(), load_weights(model, nid),
        {"sizes": model.sizes(entry["setting"]), "input_space": model.input_space(entry["setting"])},
        0.0, limits, sandbox=sb,
    )


def test_a_setsid_child_does_not_outlive_the_sandbox(model, tmp_path):
    """A recipe child that re-sessions to escape the process-group kill is still reaped at teardown."""
    import sys
    import time

    modes = sandbox_modes()  # process, landlock, and container where present
    if not sys.platform.startswith("linux"):
        modes = [m for m in modes if m == "container"]  # the reaping sweep needs Linux's subreaper
        if not modes:
            pytest.skip("setsid reaping is guaranteed only on Linux or in container mode")
    for mode in modes:
        flag = tmp_path / f"escaped_{mode}.txt"
        flag.unlink(missing_ok=True)
        sb = make_sandbox(mode, (str(model.path),))
        source = (
            "import os, time\n"
            "def make_proof(weights, info, knob):\n"
            "    if os.fork() == 0:\n"
            "        os.setsid()\n"
            "        time.sleep(1.5)\n"
            f"        open({str(flag)!r}, 'w').write('escaped')\n"
            "        time.sleep(30)\n"
            "        os._exit(0)\n"
            "    while True:\n"
            "        time.sleep(0.01)\n"
        )
        ex = _run(model, sb, source, Limits(time_s=1.0, memory_mb=800, max_proof_bytes=1 << 16))
        assert ex.status == "timeout"
        time.sleep(2.5)  # an un-reaped escapee would have written the flag by now
        survived = flag.exists()
        flag.unlink(missing_ok=True)
        assert not survived, f"a setsid child outlived teardown in {mode} mode"


def test_the_recipe_has_a_finite_process_limit(model):
    """A ceiling against a fork bomb: RLIMIT_NPROC is set for the recipe (container uses its own pids-limit)."""
    from core.runner import MAX_RECIPE_PROCESSES

    source = (
        "import resource\n"
        "def make_proof(weights, info, knob):\n"
        "    soft, hard = resource.getrlimit(resource.RLIMIT_NPROC)\n"
        "    return {'result': [soft, hard]}\n"
    )
    for mode in [m for m in sandbox_modes() if m != "container"]:
        ex = _run(model, make_sandbox(mode, (str(model.path),)), source, LIMITS)
        assert ex.status == "ok", ex.error
        soft = ex.proof["result"][0]
        assert 0 < soft <= MAX_RECIPE_PROCESSES, (mode, soft)


def test_hardened_mode_never_falls_back_to_process(monkeypatch):
    """A stopped Docker must make an unattended resume refuse, not run recipes in the weak mode."""
    from core import sandbox as sbx

    monkeypatch.setattr(sbx, "container_runtime", lambda: None)
    monkeypatch.setattr(sbx, "landlock_available", lambda: False)
    with pytest.raises(sbx.SandboxError, match="refuses to fall back"):
        sbx.choose({"sandbox": "hardened"})
    assert sbx.choose({"sandbox": "auto"}).mode == "process"  # auto still falls back, with a warning
