"""The checker in its own clean process.

The loop starts one worker per attempt (core.check.worker.CheckerProcess):

    python -I -B -X pycache_prefix=<empty folder> -c <bootstrap> <model folder> <hashes>

-I ignores the environment and the user's site folder, -B writes no bytecode,
and the empty pycache prefix means compiled files lying next to the sources,
planted or not, are never read: every module is compiled from its source. The
worker gets no API key and no other environment. It first checks that the
trusted files have the hashes the run started with, then answers one request
per line on stdin,

    {"network": id, "proof": "<path to a .json.gz>", "rule_set": [...]}

A worker started with held_out=True (by core.final, and nothing else) may load
held-out networks; any other worker refuses them.

with one JSON line on stdout: {"result": ..., "diagnosis": ...} or
{"error": ...}. It hashes the trusted files again before every check, and an
error stops the run. When a proof has leaves of a rule adopted through the rule
route (core/check/plugins.py), every accepted one is compared with the float
margins of its inputs, and a bound above them is such an error.
"""

from __future__ import annotations

import gzip
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
MAX_PROOF_BYTES = 1 << 30
STDERR_TAIL = 4000
DEFAULT_CHECK_TIMEOUT_S = 600
# A generous backstop on the worker's data memory; the arithmetic itself is
# kept small by the dyadic, bounded proof numbers (core.check.arith).
WORKER_MEMORY_MB = 4096


class CheckerError(RuntimeError):
    """The checker could not be used (it stopped, or its trusted files changed); the run halts."""


class CheckRejected(Exception):
    """One proof was too expensive to check (it timed out); that proof is rejected, the run goes on."""


# the worker side ------------------------------------------------------------------------
def _limit_memory(mb: int) -> None:
    try:
        import resource

        _, hard = resource.getrlimit(resource.RLIMIT_DATA)
        cap = mb << 20
        if hard != resource.RLIM_INFINITY:
            cap = min(cap, hard)
        resource.setrlimit(resource.RLIMIT_DATA, (cap, hard))
    except (ImportError, ValueError, OSError):
        pass


def serve(folder_path: str, expected: dict, held_out: bool = False) -> None:
    # Keep stdout for the protocol; anything else printed goes to stderr.
    proto = os.fdopen(os.dup(1), "w", buffering=1)
    os.dup2(2, 1)
    sys.dont_write_bytecode = True
    _limit_memory(WORKER_MEMORY_MB)  # a backstop; an out-of-memory check becomes a rejection, not a crash

    from ..diagnostics import diagnose, float_margins
    from ..model_folder import load_model_folder
    from ..versions import changed
    from ..zoo import correct_mask, network_entry
    from .checker import check_proof
    from .plugins import adopted, runtime_audit

    folder = load_model_folder(folder_path)
    float_view: dict = {}

    def verify():
        bad = changed(expected, folder)
        if bad:
            raise CheckerError(f"trusted files changed since the run started: {', '.join(bad)}")

    try:
        verify()
    except CheckerError as exc:
        proto.write(json.dumps({"error": str(exc)}) + "\n")
        return
    proto.write(json.dumps({"ready": True}) + "\n")
    for line in sys.stdin:
        try:
            req = json.loads(line)
            verify()
            with gzip.open(req["proof"], "rb") as f:
                data = f.read(MAX_PROOF_BYTES + 1)
            if len(data) > MAX_PROOF_BYTES:
                raise CheckerError("the proof file is too large")
            nid = req["network"]
            result = check_proof(
                json.loads(data), folder, nid, rule_set=tuple(req["rule_set"]), allow_held_out=held_out, detail=True
            )
            diagnosis = None
            if result["status"] == "ok":
                if nid not in float_view:
                    float_view[nid] = (
                        float_margins(folder, nid, allow_held_out=held_out),
                        correct_mask(folder, nid, allow_held_out=held_out),
                    )
                entry = network_entry(folder, nid)
                bad = runtime_audit(result["outcomes"], float_view[nid][0], folder.input_space(entry["setting"]), adopted())
                if bad:  # an adopted rule claimed more than the network's own margins allow: the rule is wrong
                    raise CheckerError(f"adopted rule {bad[0]['rule']!r} claimed a margin above the float margin "
                                       f"of an input in its leaf ({bad[0]}); {len(bad)} such leaves")
                diagnosis = diagnose(folder, entry, result, *float_view[nid])
            result.pop("mask", None)
            result.pop("outcomes", None)
            reply = {"result": result, "diagnosis": diagnosis}
        except Exception as exc:  # reported to the driver, which halts the run
            reply = {"error": f"{type(exc).__name__}: {exc}"}
        proto.write(json.dumps(reply) + "\n")


def main() -> None:
    serve(sys.argv[1], json.loads(sys.argv[2]), held_out=len(sys.argv) > 3 and sys.argv[3] == "held-out")


# the driver side ------------------------------------------------------------------------
class CheckerProcess:
    """A checker worker for one model folder, started from read-only code with a clean slate."""

    def __init__(self, folder_path: str | Path, expected: dict, held_out: bool = False, timeout_s: float = DEFAULT_CHECK_TIMEOUT_S):
        self.pycache = tempfile.mkdtemp(prefix="cpl-no-pycache-")
        self.timeout_s = float(timeout_s)
        bootstrap = f"import sys; sys.path.insert(0, {str(REPO_ROOT)!r}); from core.check.worker import main; main()"
        self._cmd = [sys.executable, "-I", "-B", "-X", f"pycache_prefix={self.pycache}", "-c", bootstrap]
        self._cmd += [str(folder_path), json.dumps(expected)] + (["held-out"] if held_out else [])
        self._env = {
            "PATH": os.defpath,
            "LANG": "C.UTF-8",
            "PYTHONDONTWRITEBYTECODE": "1",
            "OMP_NUM_THREADS": "1",
            "MKL_NUM_THREADS": "1",
            "OPENBLAS_NUM_THREADS": "1",
        }
        self.proc = None
        self.log = None
        self._start()

    def _start(self) -> None:
        self.log = tempfile.TemporaryFile()
        self.proc = subprocess.Popen(
            self._cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.log, env=self._env,
            text=True, cwd=self.pycache, start_new_session=True,
        )
        hello = self._reply()  # the worker checks the trusted hashes before it says it is ready
        if not hello.get("ready"):
            msg = hello.get("error", "the checker did not start")
            self._kill()
            raise CheckerError(msg)

    def _stderr(self) -> str:
        try:
            self.log.seek(0)
            return self.log.read().decode("utf-8", errors="replace")[-STDERR_TAIL:]
        except (OSError, AttributeError):
            return ""

    def _kill(self) -> None:
        if self.proc is not None:
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError, OSError):
                pass
            try:
                self.proc.wait(timeout=30)
            except (OSError, subprocess.TimeoutExpired):
                pass
        if self.log is not None:
            self.log.close()
            self.log = None

    def _reply(self, timeout: float | None = None) -> dict:
        """One reply line, within `timeout` seconds. Times out -> CheckRejected; worker stopped -> CheckerError."""
        box: dict = {}
        reader = threading.Thread(target=lambda: box.__setitem__("line", self.proc.stdout.readline()), daemon=True)
        reader.start()
        reader.join(timeout)
        if reader.is_alive():
            raise CheckRejected(f"the checker exceeded its time limit of {timeout:g} s on this proof")
        line = box.get("line")
        if not line:
            try:
                self.proc.wait(timeout=30)
            except subprocess.TimeoutExpired:
                pass
            raise CheckerError(f"the checker process stopped (exit code {self.proc.returncode}): {self._stderr()}")
        return json.loads(line)

    def check(self, network_id: str, proof_path: str | Path, rule_set) -> tuple[dict, dict | None]:
        """Check one proof. A proof that times out is rejected (status 'rejected') and the worker is restarted."""
        self.proc.stdin.write(json.dumps({"network": network_id, "proof": str(proof_path), "rule_set": list(rule_set)}) + "\n")
        self.proc.stdin.flush()
        try:
            reply = self._reply(self.timeout_s)
        except CheckRejected as exc:
            self._kill()
            self._start()  # a fresh worker for the proofs that follow
            return {"status": "rejected", "reason": str(exc)}, None
        if "error" in reply:
            raise CheckerError(reply["error"])
        return reply["result"], reply["diagnosis"]

    def close(self) -> None:
        try:
            if self.proc is not None and self.proc.stdin and not self.proc.stdin.closed:
                self.proc.stdin.close()
                self.proc.wait(timeout=60)
        except (OSError, subprocess.TimeoutExpired):
            self._kill()
        finally:
            if self.log is not None:
                self.log.close()
            shutil.rmtree(self.pycache, ignore_errors=True)

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()
