"""The loop driver.

    python -m core.loop run --config config/<run>.yaml [--run-id <id>] [--set rounds_max=5 ...]
    python -m core.loop resume --run <runs_dir>/<run_id>
    python -m core.loop status --run <runs_dir>/<run_id>

Round 0 replays the baselines the run config selects (all of the model
folder's, none, or named ones such as brute force only, so the agent has to
discover the rest); rounds 1 to rounds_max ask the run's backend for
recipes_per_round responses each. A
run can stop at any point and resume: completed rounds are kept, and an
incomplete round reuses any response it already saved. A run refuses to go on
if the checker, the sandbox code or the model folder changed since it started.

Recipes run in the sandbox the run config asks for (core.sandbox). Each start
and resume first runs the sandbox probe; a hardened mode that lets anything
critical out is refused, and the weak process mode is reported.

A run stops at rounds_max, after `patience` agent rounds in a row without a
gain in the agent-facing metric, after max_consecutive_refusals refused
attempts in a row, when the fake backend runs out of responses, or when the API
reports something waiting cannot fix (a spend limit, say); `resume` continues.
A run with the api or claude_code backend starts only from a clean commit.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .agent.backends import BackendError
from .agent.backends.api import ApiBackend, StopRun
from .agent.backends.claude_code import ClaudeCodeBackend
from .agent.backends.fake import FakeBackend
from .agent.backends.manual import ManualBackend
from .agent.build_prompt import Prompt, PromptError, build_prompt
from .diagnostics import render_attempt
from .lean import LeanError, lean_command, spot_check
from .archive import RunDir
from .check.cost import VERSION as COST_VERSION
from .model_folder import load_model_folder
from .rounds import Context, RoundError, now, run_round
from .run_config import METRIC_KEYS, RunConfigError, load_run_config, parse_overrides, resolve
from .runner import Limits
from .sandbox import SandboxError, check_probe, choose, probe, protected_paths
from .scoring import frontier, summarize
from .util import REPO_ROOT, git_state, read_json, write_json
from .versions import changed, collect
from .zoo import networks


class LoopError(RuntimeError):
    pass


class _NoResponses:
    name = "none"

    def available(self, index):
        return False


def select_networks(folder, cfg) -> list[dict]:
    dev = networks(folder, "dev")
    order = {s: i for i, s in enumerate(folder.setting_names())}
    dev.sort(key=lambda e: (order.get(e["setting"], len(order)), e["seed"]))
    if cfg["networks"] == "all":
        chosen = dev
    else:
        by_id = {e["id"]: e for e in dev}
        unknown = [n for n in cfg["networks"] if n not in by_id]
        if unknown:
            raise LoopError(f"not development networks of {folder.name}: {unknown}")
        chosen = [by_id[n] for n in cfg["networks"]]
    if not chosen:
        raise LoopError(f"{folder.name} has no development networks; train its zoo first")
    missing = [e["id"] for e in chosen if e.get("E") is None or e.get("B") is None]
    if missing:
        raise LoopError(f"E and B are missing for {missing}; run python -m core.check.costs on the model folder")
    stale = sorted({e.get("cost_model") for e in chosen if e.get("cost_model") != COST_VERSION})
    if stale:
        raise LoopError(
            f"E and B in the manifest were computed under {', '.join(map(str, stale))} but the checker is {COST_VERSION}; "
            "run python -m core.check.costs on the model folder"
        )
    return chosen


def baseline_files(folder, selection) -> list:
    """The baseline responses round 0 replays: all of the model folder's, none, or the named ones.

    A name matches a file stem exactly ("01_brute_force") or without its numeric prefix ("brute_force").
    Whatever is left out never reaches the agent, so it has to discover that strategy itself.
    """
    available = sorted((folder.path / "baselines").glob("*.md")) if (folder.path / "baselines").is_dir() else []
    if selection is True:
        return available
    if selection is False:
        return []

    def stems(p):
        stem = p.stem
        bare = stem.split("_", 1)[1] if stem[:1].isdigit() and "_" in stem else stem
        return {stem, bare}

    chosen = []
    for name in selection:
        hits = [p for p in available if name in stems(p)]
        if not hits:
            raise LoopError(f"no baseline named {name!r} in {folder.path / 'baselines'}; available: {[p.stem for p in available]}")
        chosen += [h for h in hits if h not in chosen]
    return chosen


def make_backend(cfg, log=print):
    if cfg.get("open_lane", {}).get("enabled"):
        from .open_lane.backends import ClaudeCodeToolBackend, FakeToolBackend

        if cfg["backend"] == "fake":
            return FakeToolBackend([resolve(p) for p in cfg["open_lane"]["fake_scripts"]])
        if cfg["backend"] == "claude_code":
            return ClaudeCodeToolBackend(cfg, log=log)
        raise LoopError(f"the open lane has no {cfg['backend']} backend")
    if cfg["backend"] == "fake":
        return FakeBackend([resolve(p) for p in cfg["fake_responses"]])
    if cfg["backend"] == "manual":
        return ManualBackend(log=log)
    if cfg["backend"] == "api":
        return ApiBackend(cfg, log=log)
    if cfg["backend"] == "claude_code":
        return ClaudeCodeBackend(cfg, log=log)
    raise LoopError(f"unknown backend {cfg['backend']!r}")


def metric_by_setting(records: list[dict], entries: list[dict], metric: str, budget_ratio: float | None = None) -> dict:
    key = METRIC_KEYS[metric]
    return {s: v[key] for s, v in summarize(records, entries, budget_ratio).items()}


def rounds_without_gain(run: RunDir, entries: list[dict], metric: str, budget_ratio: float | None = None) -> int:
    """Agent rounds in a row, counting back from the last, that raised the metric in no size setting."""
    records = run.read_archive()
    done = [k for k in run.done_rounds() if k > 0]
    best = metric_by_setting([r for r in records if r["round"] == 0], entries, metric, budget_ratio)
    since = 0
    for k in done:
        now_ = metric_by_setting([r for r in records if r["round"] <= k], entries, metric, budget_ratio)
        if any(now_[s] > best.get(s, 0.0) + 1e-12 for s in now_):
            since = 0
        else:
            since += 1
        best = {s: max(best.get(s, 0.0), v) for s, v in now_.items()}
    return since


def claim_identity(record: dict) -> tuple | None:
    """What an accepted open-lane record established, as the service saw it: a scored proof is its network,
    count and length; a verified proof its network and count; a lemma its network and statement. Not the
    files (a changed comment is not progress) and not the theorem's name (a name is the author's): the
    same claim proved twice is one artifact, a new count, length or statement is a new one; a verified
    proof of a count that already has a scored or verified proof is not new either."""
    status = record.get("status")
    if status == "ok":
        return ("ok", record.get("network"), record.get("certified"), record.get("length"))
    if status == "verified":
        return ("verified", record.get("network"), record.get("certified"))
    if status == "lemma":
        statement = " ".join(str(record.get("statement") or "").split())
        return ("lemma", record.get("network"), statement)
    return None


def rounds_without_new_artifact(run: RunDir, entries: list[dict] | None = None, metric: str | None = None,
                                budget_ratio: float | None = None) -> int:
    """For the open lane: agent rounds in a row, counting back from the last, that accepted nothing new. An
    accepted submission (scored, verified or a lemma) counts only if its claim (claim_identity) differs
    from every earlier accepted one, so resubmitting a lemma, or a proof with a comment changed, does not
    keep the loop alive, while a new statement, count or length does. Under the metric Q_above a scored
    proof counts only if it raised the metric in its size setting (a new count and length at or below the
    brute-force line, or worse than an earlier proof, is not progress); lemmas and verified proofs count as
    before. The hard budgets (rounds, the session's calls and clock) are unchanged."""
    records = run.read_archive()
    done = [k for k in run.done_rounds() if k > 0]
    seen: set = set()  # identities
    counts: set = set()  # (network, count) with a scored or verified proof: a verified proof of it is not new
    by_gain = metric == "Q_above" and entries is not None
    best = metric_by_setting([r for r in records if r["round"] == 0], entries, metric, budget_ratio) if by_gain else {}
    since = 0
    for k in done:
        new = False
        for r in records:
            if r["round"] != k or r.get("lane") != "open":
                continue
            identity = claim_identity(r)
            if identity is None or identity in seen:
                continue
            if identity[0] == "verified" and (identity[1], identity[2]) in counts:
                continue
            seen.add(identity)
            if identity[0] in ("ok", "verified"):
                counts.add((identity[1], identity[2]))
            if identity[0] == "ok" and by_gain:
                continue  # judged by the metric below
            new = True
        if by_gain:
            now_ = metric_by_setting([r for r in records if r["round"] <= k], entries, metric, budget_ratio)
            if any(now_[s] > best.get(s, 0.0) + 1e-12 for s in now_):
                new = True
            best = {s: max(best.get(s, 0.0), v) for s, v in now_.items()}
        since = 0 if new else since + 1
    return since


def consecutive_refusals(run: RunDir) -> int:
    n = 0
    for k in reversed([k for k in run.done_rounds() if k > 0]):
        metas = []
        j = 0
        while (run.round_path(k) / f"attempt_{j}").is_dir():
            metas.append(run.read(k, f"attempt_{j}/response_meta.json") or {})
            j += 1
        for m in reversed(metas):
            if m.get("stop_reason") != "refusal":
                return n
            n += 1
    return n


def round_prompt(ctx: Context, k: int) -> Prompt:
    """The prompt round k sent, if it has one already; otherwise a new one from the archive."""
    saved = ctx.run.read(k, "prompt.json")
    if saved is not None:
        return Prompt.from_json(saved)
    if ctx.cfg.get("open_lane", {}).get("enabled"):
        from .open_lane.prompt import build_open_lane_prompt

        p = build_open_lane_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, k)
    else:
        p = build_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, k)
    ctx.log(f"  prompt: about {p.stats['tokens_estimate']:,} tokens" + (f"; trimmed {', '.join(p.stats['trimmed'])}" if p.stats["trimmed"] else ""))
    return p


def prepare_sandbox(cfg: dict, folder, run: RunDir, entries: list[dict], log=print):
    """Choose the run's sandbox and probe it; returns the sandbox and the probe's report."""
    sb = choose(cfg, protected_paths(cfg, folder, run.path))
    report = probe(sb, folder, entries[0]["id"], run.path / "probe", Limits.from_config(cfg))
    check_probe(sb, report)
    if sb.hardened:
        log(f"sandbox: {sb.mode}; the probe's {len(report['attempts'])} escape attempts were all blocked")
    else:
        log(
            f"warning: sandbox mode process is weak; recipes can read and write what you can "
            f"(the probe got out with {', '.join(report['critical_escapes'])}). Use container or landlock mode "
            "for recipes you do not trust."
        )
    return sb, report


def open_context(run: RunDir, cfg: dict, log=print) -> Context:
    sys.dont_write_bytecode = True  # so compiled files that appear in trusted folders can only come from elsewhere
    folder = load_model_folder(resolve(cfg["model"]))
    started = read_json(run.path / "versions.json")
    bad = changed(started, folder)
    if bad:
        raise LoopError(
            f"{', '.join(bad)} changed since run {run.run_id} started; results would not be comparable. "
            "Start a new run instead."
        )
    if cfg.get("open_lane", {}).get("enabled"):
        check_lean_checker(cfg, started, run.run_id)
    entries = select_networks(folder, cfg)
    sb, report = prepare_sandbox(cfg, folder, run, entries, log)
    with open(run.path / "sandbox.jsonl", "a") as f:
        f.write(json.dumps({"at": now(), **sb.describe(), "probe": report}) + "\n")
    return Context(
        cfg=cfg,
        folder=folder,
        run=run,
        entries=entries,
        versions=started,
        limits=Limits.from_config(cfg),
        sandbox=sb,
        log=log,
    )


def preflight(cfg: dict, folder) -> None:
    """Checks that must pass before a run folder is made."""
    select_networks(folder, cfg)
    baseline_files(folder, cfg["baselines"])  # a misspelt baseline name fails here
    if cfg["lean_spot_check"] and lean_command(folder) is None:
        raise LoopError(f"lean_spot_check is on, but {folder.name} has no Lean checker (lean_check in its config.yaml)")
    if cfg.get("open_lane", {}).get("enabled"):
        project = resolve(cfg["open_lane"]["lean_project"])
        binary = project / ".lake" / "build" / "bin" / "acceptcheck"
        if not binary.is_file():
            raise LoopError(f"the Lean project at {project} has no built acceptcheck (lake build acceptcheck there first)")
        check_lean_lock(project)
    if cfg["backend"] in ("api", "claude_code"):
        g = git_state()
        if g["commit"] is None or g["dirty"]:
            raise LoopError(f"a run with the {cfg['backend']} backend starts only from a clean commit; commit or stash your changes first")
        make_backend(cfg)  # fails here, before the run exists, if the key is missing or the CLI is not logged in


LEAN_LOCK = REPO_ROOT / "lean-checker.lock"
LEAN_IDENTITY_KEYS = ("commit", "toolchain", "lean_project", "policy", "acceptcheck")


def lean_identity(project: Path, knowledge: str = "minimal") -> dict:
    """What the Lean service is, as it reports itself (`accept.py identity`): the project's commit, the
    digests every receipt carries (toolchain, trusted sources, policy with its environment hooks) and the
    acceptcheck binary. A run records it when it starts and checks it when it resumes and on every
    receipt, so one frontier never mixes two services."""
    import subprocess

    cmd = [sys.executable, "-B", str(project / "scripts" / "accept.py"), "identity", "--knowledge", knowledge]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise LoopError(f"cannot ask the Lean service at {project} what it is: {exc}")
    return parse_identity(r.returncode, r.stdout, r.stderr, project)


def parse_identity(returncode: int, stdout: str, stderr: str, project) -> dict:
    """The identity command's answer, accepted only when it succeeded and reported every field."""
    if returncode != 0:
        raise LoopError(f"the Lean service at {project} could not report its identity (exit {returncode}): {(stderr or stdout)[-800:]}")
    try:
        ident = json.loads(stdout)
    except ValueError:
        raise LoopError(f"the Lean service at {project} did not report its identity: {(stderr or stdout)[-800:]}")
    if not isinstance(ident, dict):
        raise LoopError(f"the Lean service at {project} reported an identity of the wrong shape")
    missing = [k for k in LEAN_IDENTITY_KEYS if not ident.get(k)]
    if missing:
        raise LoopError(f"the Lean service at {project} reported an incomplete identity (no {', '.join(missing)})")
    if ident.get("dirty"):
        raise LoopError(f"the Lean project at {project} has uncommitted changes to tracked files; a run needs a clean checker")
    return {k: ident[k] for k in LEAN_IDENTITY_KEYS}


def lean_checker_changed(started: dict, now: dict) -> list[str]:
    """The parts of the Lean service's identity that differ from what the run recorded."""
    return [k for k in LEAN_IDENTITY_KEYS if started.get(k) != now.get(k)]


def check_lean_checker(cfg: dict, started: dict, run_id: str) -> None:
    """On resume: the Lean service must be the one the run started with, whatever today's lock says. A run
    keeps its checker; a new checker is a new run."""
    recorded = started.get("lean_checker")
    if not recorded:
        raise LoopError(f"run {run_id} recorded no Lean checker identity (it started before that was recorded); start a new run")
    project = resolve(cfg["open_lane"]["lean_project"])
    lock = read_json(LEAN_LOCK)
    if lock["commit"] != recorded.get("commit"):
        raise LoopError(
            f"lean-checker.lock moved since run {run_id} started ({recorded.get('commit', '')[:12]} to {lock['commit'][:12]}); "
            "a run keeps the checker it started with, so this pipeline version cannot resume it: start a new run"
        )
    bad = lean_checker_changed(recorded, lean_identity(project, knowledge=cfg["open_lane"]["knowledge"]))
    if bad:
        raise LoopError(
            f"the Lean checker's {', '.join(bad)} changed since run {run_id} started; its receipts would mean "
            "something else. Check out the commit the run started with and rebuild, or start a new run"
        )


def check_lean_lock(project: Path) -> dict:
    """The Lean project must be at the commit lean-checker.lock names: a run's receipts mean what this pipeline
    version expects only then. Returns the lock."""
    lock = read_json(LEAN_LOCK)
    import subprocess

    try:
        head = subprocess.run(["git", "-C", str(project), "rev-parse", "HEAD"], capture_output=True, text=True, timeout=60).stdout.strip()
        dirty = subprocess.run(["git", "-C", str(project), "status", "--porcelain", "--untracked-files=no"], capture_output=True, text=True, timeout=60).stdout.strip()
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise LoopError(f"cannot read the Lean project's git state at {project}: {exc}")
    if head != lock["commit"]:
        raise LoopError(
            f"the Lean project at {project} is at commit {head[:12]}, but lean-checker.lock expects {lock['commit'][:12]}: "
            "check out that commit, or update the lock in a commit of this repository if the new checker is meant"
        )
    if dirty:
        raise LoopError(f"the Lean project at {project} has uncommitted changes to tracked files; a run needs a clean checker")
    return lock


def start(config_path: str | Path, log=print, run_id: str | None = None, overrides: dict | None = None) -> Context:
    cfg = load_run_config(config_path, run_id=run_id, overrides=overrides)
    folder = load_model_folder(resolve(cfg["model"]))
    preflight(cfg, folder)
    run = RunDir(resolve(cfg["runs_dir"]), cfg["run_id"])
    run.create(cfg)
    config_sha = (run.path / "config.sha256").read_text().strip()
    versions = collect(folder, cfg, config_sha)
    if cfg.get("open_lane", {}).get("enabled"):
        versions["lean_checker"] = lean_identity(resolve(cfg["open_lane"]["lean_project"]), knowledge=cfg["open_lane"]["knowledge"])
    write_json(run.path / "versions.json", {**versions, "git": git_state(), "created": now(),
                                            "config_file": str(config_path), "set_on_command_line": overrides or {}})
    log(f"run {cfg['run_id']} at {run.path}")
    if overrides:
        log("set on the command line: " + ", ".join(f"{k}={v}" for k, v in overrides.items()))
    return open_context(run, run.config(), log)


def resume(run_path: str | Path, log=print) -> Context:
    run_path = Path(run_path).expanduser().resolve()
    run = RunDir(run_path.parent, run_path.name)
    if not run.exists():
        raise LoopError(f"no run at {run_path}")
    return open_context(run, run.config(), log)


def drive(ctx: Context) -> None:
    cfg, run, folder = ctx.cfg, ctx.run, ctx.folder
    if not run.round_done(0):
        files = baseline_files(folder, cfg["baselines"])
        if files:
            fake = FakeBackend(files)
            run_round(ctx, 0, fake, 0, len(fake), "baseline")
        else:
            run_round(ctx, 0, _NoResponses(), 0, 0, "baseline")
    backend = make_backend(cfg, ctx.log)
    if hasattr(backend, "bind"):
        backend.bind(cfg, cfg["model"], ctx.entries, run.path)
    per_round = cfg["recipes_per_round"]
    k = max(run.next_round(), 1)
    while k <= cfg["rounds_max"]:
        first = (k - 1) * per_round
        fresh = not run.round_done(k) and run.read(k, "attempt_0/response.md") is None
        if fresh:
            if cfg.get("open_lane", {}).get("enabled"):
                stale = rounds_without_new_artifact(run, ctx.entries, cfg["metric"], cfg.get("budget_ratio"))
                what = "no new accepted submission" + (" and no gain in Q_above" if cfg["metric"] == "Q_above" else "")
            else:
                stale = rounds_without_gain(run, ctx.entries, cfg["metric"], cfg.get("budget_ratio"))
                what = "no gain"
            if stale >= cfg["patience"]:
                ctx.log(f"{what} in {stale} rounds (patience {cfg['patience']}); stopping after round {k - 1}")
                break
            refused = consecutive_refusals(run)
            if refused >= cfg["max_consecutive_refusals"]:
                ctx.log(f"the model declined {refused} attempts in a row; stopping after round {k - 1}")
                break
            if not backend.available(first):
                ctx.log(f"the {backend.name} backend has no more responses; stopping after round {k - 1}")
                break
        before = {p["record_id"] for pts in frontier(run.read_archive()).values() for p in pts}
        run_round(ctx, k, backend, first, per_round, "agent", prompt=round_prompt(ctx, k))
        if cfg["lean_spot_check"]:
            entered = [r for r in run.read_archive() if r["round"] == k and r["record_id"] not in before]
            new_points = {p["record_id"] for pts in frontier(run.read_archive()).values() for p in pts}
            spot_check(ctx, k, [r for r in entered if r["record_id"] in new_points])
        k += 1


# status ------------------------------------------------------------------------
def status_text(run: RunDir, diagnostics: bool = False) -> str:
    cfg = run.config()
    lines = [f"run {run.run_id}: model {cfg['model']}, backend {cfg['backend']}, rounds done {run.done_rounds()}"]
    records = run.read_archive()
    try:
        grouping = load_model_folder(resolve(cfg["model"])).group_label()
    except Exception:
        grouping = "group"
    for k in sorted({r["round"] for r in records}):
        for j in sorted({r["attempt"] for r in records if r["round"] == k}):
            rs = [r for r in records if r["round"] == k and r["attempt"] == j]
            meta = run.read(k, f"attempt_{j}/response_meta.json") or {}
            counts: dict[str, int] = {}
            for r in rs:
                counts[r["status"]] = counts.get(r["status"], 0) + 1
            text = ", ".join(f"{s} {c}" for s, c in sorted(counts.items()))
            errs = sorted({(r["error"] or "").splitlines()[-1][:100] for r in rs if r["error"]})
            lines.append(f"  round {k} attempt {j} ({rs[0]['source']}, {meta.get('source', '')}): {text}")
            if diagnostics:
                lines += ["      " + ln for ln in render_attempt(rs, grouping).splitlines()]
            else:
                lines += [f"      {e}" for e in errs[:2]]
    try:
        folder = load_model_folder(resolve(cfg["model"]))
        entries = select_networks(folder, cfg)
    except Exception as exc:  # status should still print what it can
        lines.append(f"(no metrics: {exc})")
        return "\n".join(lines)
    checkers = sorted({str(r.get("checked_by") or "python") for r in records if r.get("status") == "ok"}) or ["python"]
    lines.append(f"frontier metrics (checked by {', '.join(checkers)}):")
    for setting, s in summarize(records, entries, cfg.get("budget_ratio")).items():
        lines.append(
            f"  {setting}: Q median {s['Q_median']:.4f}, worst {s['Q_worst']:.4f}; Q_grid median {s['Q_grid_median']:.4f}; Q_exact mean {s['Q_exact_mean']:.4f}; "
            f"Q_above mean {s['Q_above_mean']:.4f}; cost of finishing median {s['cost_of_finishing_median']:.2f}"
        )
        for nid, m in s["networks"].items():
            full = f"{m['shortest_full']:,} (B/{m['B'] / m['shortest_full']:.1f})" if m["shortest_full"] else "none"
            real = f"{m['real_accuracy']:.5f}" if m["real_accuracy"] is not None else "?"
            lines.append(
                f"    {nid}: Q {m['Q']:.4f}, Q_above {m['Q_above']:.4f} ({m['points_above_line']} of {m['points']} frontier proofs above "
                f"the brute-force line), best certified accuracy {m['best_accuracy']:.5f} of {real}, "
                f"shortest full-accuracy proof {full}"
            )
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p_run = sub.add_parser("run", help="start a run from a run config")
    p_run.add_argument("--config", required=True)
    p_run.add_argument("--run-id", help="use this run id instead of the config's, e.g. to repeat a run")
    p_run.add_argument("--set", dest="settings", action="append", default=[], metavar="KEY=VALUE",
                       help="set a value for this run on top of the config, e.g. --set rounds_max=5 or "
                            "--set open_lane.worker_seconds=3600 (repeatable; the run folder's config.yaml records it)")
    for name in ("resume", "status"):
        p = sub.add_parser(name)
        p.add_argument("--run", required=True, help="the run's folder, <runs_dir>/<run_id>")
    sub.choices["status"].add_argument("--diagnostics", action="store_true", help="show each attempt's diagnostics")
    args = ap.parse_args(argv)
    try:
        if args.cmd == "status":
            path = Path(args.run).expanduser().resolve()
            print(status_text(RunDir(path.parent, path.name), diagnostics=args.diagnostics))
            return 0
        if args.cmd == "run":
            ctx = start(args.config, run_id=args.run_id, overrides=parse_overrides(args.settings))
        else:
            ctx = resume(args.run)
        drive(ctx)
        print(status_text(ctx.run))
        return 0
    except StopRun as exc:
        print(f"stopped: {exc}\nFix the cause, then continue with: python -m core.loop resume --run <the run's folder>", file=sys.stderr)
        return 3
    except (LoopError, RoundError, BackendError, SandboxError, PromptError, LeanError, RunConfigError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
