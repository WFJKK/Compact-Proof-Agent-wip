"""The seatbelt sandbox mode (macOS's sandbox-exec, ported from the level-1 pipeline). Its profile is tested here
as text, on any machine; on a Mac, tests/test_adversarial.py runs every escape attempt and the probe in seatbelt
mode too (tests/conftest.py adds it to the modes there), which is the profile's real test."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

from core import runner, sandbox
from core.run_config import merge
from core.sandbox import Sandbox, SandboxError, choose, protected_paths, python_paths, seatbelt_command, seatbelt_profile


def test_the_profile_takes_away_the_home_folder_the_protected_folders_the_network_and_other_programs(tmp_path):
    box = tmp_path / "box"
    protected = protected_paths({"runs_dir": str(tmp_path / "runs")})
    text = seatbelt_profile(box, protected, "/opt/python/bin/python3")
    lines = text.splitlines()
    assert lines[:2] == ["(version 1)", "(allow default)"]
    assert "(deny network*)" in lines and "(deny process-fork)" in lines and "(deny process-exec)" in lines
    assert '(allow process-exec (literal "/opt/python/bin/python3"))' in lines
    assert "(deny signal)" in lines and "(allow signal (target self))" in lines
    # writing: nowhere but the box's out/ and tmp/; a later rule wins, so the allow comes after the deny
    write = next(l for l in lines if l.startswith("(allow file-write*"))
    assert f'(subpath "{box / "out"}")' in write and f'(subpath "{box / "tmp"}")' in write and '(literal "/dev/null")' in write
    assert lines.index("(deny file-write*)") < lines.index(write)
    # reading: the home folder and every protected folder refused, then Python and the box allowed again
    deny = next(l for l in lines if l.startswith("(deny file-read*"))
    allow = next(l for l in lines if l.startswith("(allow file-read*"))
    assert f'(subpath "{Path.home().resolve()}")' in deny and all(f'(subpath "{p}")' in deny for p in protected)
    assert f'(subpath "{box}")' in allow and all(f'(subpath "{p}")' in allow for p in python_paths())
    assert lines.index(deny) < lines.index(allow) and lines[-1] == "(allow file-read-metadata)"
    assert not any(f'"{p}"' in allow for p in protected)
    # a readable folder that holds a protected one is refused
    with pytest.raises(SandboxError, match="contains"):
        seatbelt_profile(box, (str(Path(sys.prefix) / "lib" / "something"),))
    # quotes in a path cannot end the string early
    assert sandbox._sb('/a "b') == '"/a \\"b"'


def test_on_a_framework_python_the_interpreter_inside_python_app_may_run_too(tmp_path, monkeypatch):
    # python.org's and Homebrew's builds: bin/python3.x replaces itself with Resources/Python.app/.../Python
    app = tmp_path / "Versions" / "3.12" / "Resources" / "Python.app" / "Contents" / "MacOS" / "Python"
    app.parent.mkdir(parents=True)
    app.write_text("")
    monkeypatch.setattr(sandbox.sys, "platform", "darwin")
    monkeypatch.setattr(sandbox.sys, "base_prefix", str(tmp_path / "Versions" / "3.12"))
    monkeypatch.setattr(sandbox.sysconfig, "get_config_var", lambda name: "Python" if name == "PYTHONFRAMEWORK" else None)
    text = seatbelt_profile(tmp_path / "box", (), "/opt/python/bin/python3.12")
    rule = next(l for l in text.splitlines() if l.startswith("(allow process-exec"))
    assert '(literal "/opt/python/bin/python3.12")' in rule and f'(literal "{app}")' in rule
    # not a framework build (Linux, pyenv, uv, conda): the launcher alone
    monkeypatch.setattr(sandbox.sysconfig, "get_config_var", lambda name: "" if name == "PYTHONFRAMEWORK" else None)
    rule = next(l for l in seatbelt_profile(tmp_path / "box", (), "/opt/python/bin/python3.12").splitlines()
                if l.startswith("(allow process-exec"))
    assert rule == '(allow process-exec (literal "/opt/python/bin/python3.12"))'


def test_the_harness_starts_under_sandbox_exec_in_seatbelt_mode(tmp_path, monkeypatch):
    seen = []

    class Stop(Exception):
        pass

    def popen(argv, **kw):
        seen.append(argv)
        raise Stop()

    monkeypatch.setattr(runner.subprocess, "Popen", popen)
    limits = runner.Limits.from_config({"time_limit_s": 1, "memory_limit_mb": 100, "max_proof_mb": 1, "threads_per_recipe": 1})
    for sb in (Sandbox("seatbelt", protected=("/p",)), Sandbox("process")):
        with pytest.raises(Stop):
            runner._wait_process(tmp_path, limits, None, None, "id", sb)
    assert seen[0][:2] == [sandbox.SEATBELT, "-p"] and seen[0][3:] == [sys.executable, "-I", "-B", str(tmp_path / "harness.py")]
    assert seen[0][2] == seatbelt_profile(tmp_path, ("/p",), sys.executable)
    assert seen[1] == [sys.executable, "-I", "-B", str(tmp_path / "harness.py")]
    assert seatbelt_command(tmp_path, (), ["python3", "x"])[3:] == ["python3", "x"]


def test_seatbelt_is_used_only_when_asked_for_and_only_on_a_mac(monkeypatch):
    assert Sandbox("seatbelt").hardened
    monkeypatch.setattr(sandbox, "seatbelt_available", lambda: False)
    with pytest.raises(SandboxError, match="needs macOS with sandbox-exec"):
        choose({"sandbox": "seatbelt"})
    monkeypatch.setattr(sandbox, "seatbelt_available", lambda: True)
    monkeypatch.setattr(sandbox, "container_runtime", lambda: None)
    monkeypatch.setattr(sandbox, "landlock_available", lambda: False)
    assert choose({"sandbox": "seatbelt"}).mode == "seatbelt"
    assert choose({"sandbox": "auto"}).mode == "process"  # auto does not pick it yet: not until it has passed a Mac's probe
    with pytest.raises(SandboxError, match="refuses to fall back"):
        choose({"sandbox": "hardened"})
    assert merge({"run_id": "x", "model": "tests/max2_tiny", "backend": "fake", "rule_set": ["single"], "sandbox": "seatbelt"})["sandbox"] == "seatbelt"
