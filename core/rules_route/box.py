"""The check box: where the route runs a candidate rule's tests and audit, which execute code an agent wrote.

A box is a fresh folder holding a copy of the repository's code and model folders (repo/, with the candidate
at repo/rules/<name>/), the launcher and a job. Three modes, strongest first, as for recipes (core/sandbox.py):

    container  docker or podman with the checks image (python -m core.rules_route build-image): no network, a
               read-only root, the box mounted read-only with out/ and tmp/ writable, nobody, no capabilities.
    landlock   Linux: no new privileges, seccomp with no sockets, Landlock allowing reads of the Python
               installation, system libraries and the box, writes only to the box's out/ and tmp/.
    process    a plain separate process with resource limits and an empty environment. Weak.

`hardened` takes container or landlock and refuses to fall back to process; `auto` falls back. The environment
never carries an API key. What a candidate can see is a copy: the box's repo/ is thrown away afterwards.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import uuid
from dataclasses import dataclass
from pathlib import Path

from ..sandbox import CONTAINER_PIDS, CONTAINER_TMP_MB, NOBODY, SYSTEM_READ, DEVICE_READ, DEVICE_READ_WRITE, PROC_READ
from ..sandbox import container_runtime, image_id, landlock_available, python_paths
from ..util import REPO_ROOT

CHECKS_IMAGE = "auto-research-compact-proof-checks:1"
CHECKS_DOCKERFILE = REPO_ROOT / "sandbox" / "Dockerfile.checks"
COPIED = ("core", "models", "tests", "pyproject.toml", "config")
MODES = ("container", "landlock", "process")


class BoxError(RuntimeError):
    pass


@dataclass
class BoxResult:
    returncode: int
    stdout: str
    stderr: str
    mode: str
    timed_out: bool = False


def choose_mode(want: str = "hardened") -> tuple[str, str | None]:
    """(mode, container runtime or None) for 'hardened', 'auto' or a mode name."""
    if want not in ("auto", "hardened") + MODES:
        raise BoxError(f"checks_sandbox must be auto, hardened or one of {MODES}, not {want!r}")
    if want in ("auto", "hardened", "container"):
        rt = container_runtime()
        if rt and image_id(rt, CHECKS_IMAGE):
            return "container", rt
        if want == "container":
            raise BoxError(f"container mode needs docker or podman with {CHECKS_IMAGE}: python -m core.rules_route build-image")
    if want in ("auto", "hardened", "landlock") and landlock_available():
        return "landlock", None
    if want in ("hardened", "landlock", "container"):
        raise BoxError(
            "no hardened check box is available here: on Linux, Landlock; elsewhere, Docker or Podman with the checks "
            "image (python -m core.rules_route build-image). Set checks_sandbox: process only for rules you trust."
        )
    return "process", None


def _ignore(dirpath, names):
    return [n for n in names if n in ("__pycache__", ".pytest_cache") or n.endswith((".pyc", ".pyo"))]


def make_box(candidate: Path, root: Path | None = None) -> Path:
    """A fresh box with the repository's code, the model folders and the candidate at repo/rules/<name>/."""
    box = Path(tempfile.mkdtemp(prefix="rulebox-", dir=root))
    repo = box / "repo"
    repo.mkdir()
    for name in COPIED:
        src = REPO_ROOT / name
        if src.is_dir():
            shutil.copytree(src, repo / name, ignore=_ignore)
        elif src.is_file():
            shutil.copy2(src, repo / name)
    (repo / "rules").mkdir()
    shutil.copytree(candidate, repo / "rules" / Path(candidate).name, ignore=_ignore)
    shutil.copy2(Path(__file__).with_name("launcher.py"), box / "_launcher.py")
    shutil.copy2(REPO_ROOT / "core" / "harness.py", box / "_harness.py")
    for d in ("out", "tmp"):
        (box / d).mkdir()
    return box


def run(box: Path, module: str, argv: list, mode: str, runtime: str | None = None, timeout_s: float = 3600,
        memory_mb: int = 4096, threads: int = 1) -> BoxResult:
    """Run `python -m module argv` in the box. Paths in argv may use {box} for the box as the module sees it."""
    inside = Path("/box") if mode == "container" else box
    argv = [str(a).replace("{box}", str(inside)) for a in argv]
    job = {
        "policy": None,
        "limits": {"RLIMIT_CPU": int(timeout_s) + 60},
        "sys_path": [str(inside / "repo")],
        "cwd": str(inside / "repo"),
        "module": module,
        "argv": argv,
    }
    if mode != "container":
        job["limits"]["RLIMIT_AS"] = int(memory_mb) << 20
    if mode == "landlock":
        read = python_paths() + [p for p in SYSTEM_READ + DEVICE_READ + PROC_READ if os.path.exists(p)] + [str(box)]
        job["policy"] = {"read": read, "read_write": [str(box / "out"), str(box / "tmp")] + list(DEVICE_READ_WRITE), "own_proc": True}
    (box / "job.json").write_text(json.dumps(job))
    t = str(threads)
    env = {"PATH": "/usr/bin:/bin", "HOME": str(inside / "tmp"), "TMPDIR": str(inside / "tmp"), "LANG": "C.UTF-8",
           "PYTHONDONTWRITEBYTECODE": "1", "OMP_NUM_THREADS": t, "MKL_NUM_THREADS": t, "OPENBLAS_NUM_THREADS": t}
    if mode == "container":
        name = f"rulebox-{uuid.uuid4().hex[:12]}"
        cmd = [runtime, "run", "--rm", "--init", "--name", name, "--network", "none", "--read-only",
               "--tmpfs", f"/tmp:rw,size={CONTAINER_TMP_MB}m,mode=1777", "--memory", f"{int(memory_mb)}m",
               "--memory-swap", f"{int(memory_mb)}m", "--cpus", t, "--pids-limit", str(CONTAINER_PIDS),
               "--user", NOBODY, "--cap-drop", "ALL", "--security-opt", "no-new-privileges"]
        for k, v in env.items():
            cmd += ["-e", f"{k}={v}"]
        os.chmod(box / "out", 0o777)
        os.chmod(box / "tmp", 0o777)
        cmd += ["-v", f"{box}:/box:ro", "-v", f"{box / 'out'}:/box/out:rw", "-v", f"{box / 'tmp'}:/box/tmp:rw", "-w", "/box"]
        cmd += [CHECKS_IMAGE, "python", "-I", "-B", "/box/_launcher.py", "/box/job.json"]
        run_env = None
    else:
        cmd = [sys.executable, "-I", "-B", str(box / "_launcher.py"), str(box / "job.json")]
        run_env = env
    try:
        p = subprocess.run(cmd, env=run_env, capture_output=True, text=True, timeout=timeout_s, cwd=str(box))
    except subprocess.TimeoutExpired as exc:
        if mode == "container":
            subprocess.run([runtime, "kill", name], capture_output=True)
        return BoxResult(-9, (exc.stdout or b"").decode(errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or ""),
                         "timed out", mode, timed_out=True)
    return BoxResult(p.returncode, p.stdout, p.stderr, mode)


def discard(box: Path) -> None:
    shutil.rmtree(box, ignore_errors=True)


def build_image(runtime: str | None = None, log=print) -> str:
    """Build the checks image: the sandbox image's Python, numpy and torch, plus pyyaml and pytest."""
    from ..sandbox import image_versions

    rt = runtime or container_runtime()
    if not rt:
        raise BoxError("no docker or podman is running")
    v = image_versions()
    py = f"{sys.version_info.major}.{sys.version_info.minor}"
    cmd = [rt, "build", "-t", CHECKS_IMAGE, "-f", str(CHECKS_DOCKERFILE), "--build-arg", f"PYTHON_VERSION={py}"]
    for arg, key in (("NUMPY_VERSION", "numpy"), ("TORCH_VERSION", "torch"), ("PYYAML_VERSION", "pyyaml"), ("PYTEST_VERSION", "pytest")):
        cmd += ["--build-arg", f"{arg}={v[key]}"]
    cmd.append(str(CHECKS_DOCKERFILE.parent))
    log(" ".join(cmd))
    if subprocess.run(cmd).returncode != 0:
        raise BoxError("the checks image build failed")
    return CHECKS_IMAGE
