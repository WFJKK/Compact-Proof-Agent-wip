"""Run configs: one YAML file per run, merged over config/defaults.yaml.

A run config must name `run_id` and `model` (the model folder) and may override
any default. Unknown keys are refused, so a typo never silently falls back to
a default. Relative paths are relative to the repository root.

A run may also set values when it starts (`python -m core.loop run ... --set
rounds_max=5`): they go on top of the run config before the merge, under the
same checks, and the run folder's config.yaml records the result.

A run config may build on another: `extends: <file>` (a path next to it) takes
that file's settings and puts its own on top, so what several runs share is
written once and a run on another model is a file of a few lines.

What an open-lane run takes from the Lean project for one architecture (the
worked example, further sources, notes for the agent) belongs to the model: a
model folder's config.yaml may carry them under `open_lane`, and they apply
unless the run config sets the same entry itself.
"""

from __future__ import annotations

import re
from pathlib import Path

import yaml

from .check.rules import generic_rules
from .util import REPO_ROOT, read_yaml

DEFAULTS_PATH = REPO_ROOT / "config" / "defaults.yaml"
REQUIRED = ("run_id", "model")
BACKENDS = ("fake", "manual", "api", "claude_code")
METRICS = ("Q", "Q_grid", "Q_exact", "Q_above", "cost_of_finishing")
METRIC_KEYS = {"Q": "Q_median", "Q_grid": "Q_grid_median", "Q_exact": "Q_exact_mean", "Q_above": "Q_above_mean",
               "cost_of_finishing": "cost_of_finishing_geomean"}
SANDBOX_MODES = ("auto", "hardened", "container", "landlock", "process")
THINKING_TYPES = ("adaptive", "enabled", "disabled")
EFFORTS = ("low", "medium", "high", "xhigh", "max")
FORBIDDEN_KEY_VARIABLES = ("ANTHROPIC_API_KEY",)


class RunConfigError(ValueError):
    pass


def resolve(path: str | Path) -> Path:
    """A path from a run config: absolute, home-relative, or relative to the repository."""
    p = Path(str(path)).expanduser()
    return p if p.is_absolute() else REPO_ROOT / p


def defaults() -> dict:
    return dict(read_yaml(DEFAULTS_PATH))


def read_run_config_file(path: str | Path, _seen: tuple = ()) -> dict:
    """A run config file as written, with the file it extends underneath (`extends: <file>`, a path relative
    to the file's own folder; a chain is followed). A setting that is a mapping in both (open_lane,
    api_retries) is merged entry by entry; anything else the extending file replaces."""
    path = Path(path)
    raw = read_yaml(path)
    if not isinstance(raw, dict):
        raise RunConfigError(f"{path}: a run config is a mapping")
    raw = dict(raw)
    parent = raw.pop("extends", None)
    if parent is None:
        return raw
    if not isinstance(parent, str) or not parent:
        raise RunConfigError(f"{path}: extends must be the path of another run config")
    parent_path = (path.parent / Path(parent).expanduser()).resolve()
    if parent_path in _seen or parent_path == path.resolve():
        raise RunConfigError(f"{path}: extends leads back to {parent_path.name}")
    if not parent_path.is_file():
        raise RunConfigError(f"{path}: extends {parent!r}, which is not a file")
    base = read_run_config_file(parent_path, (*_seen, path.resolve()))
    out = dict(base)
    for key, value in raw.items():
        out[key] = {**base[key], **value} if isinstance(value, dict) and isinstance(base.get(key), dict) else value
    return out


MODEL_OPEN_LANE_KEYS = ("example", "extra_sources", "notes")


def model_open_lane(model: object) -> dict:
    """The open-lane facts a model folder carries in its config.yaml (`open_lane`: the worked example and
    further sources in the Lean project, notes for the agent); empty without them. The folder's own loader
    checks their form (core.model_folder)."""
    if not isinstance(model, str):
        return {}
    path = resolve(model) / "config.yaml"
    if not path.is_file():
        return {}
    block = (read_yaml(path) or {}).get("open_lane")
    return {k: v for k, v in block.items() if k in MODEL_OPEN_LANE_KEYS} if isinstance(block, dict) else {}


def load_run_config(path: str | Path, run_id: str | None = None, overrides: dict | None = None) -> dict:
    raw = read_run_config_file(path)
    if run_id is not None:
        raw = {**raw, "run_id": run_id}
    if overrides:
        raw = apply_overrides(raw, overrides)
    return merge(raw, source=str(path))


def parse_overrides(items: list[str]) -> dict:
    """Command-line settings, KEY=VALUE each, as {KEY: value}. VALUE is read as YAML: 5, true, high, [single, skip]."""
    out = {}
    for item in items:
        key, sep, text = item.partition("=")
        key = key.strip()
        if not sep or not key:
            raise RunConfigError(f"--set {item!r}: write KEY=VALUE, for example rounds_max=5")
        try:
            out[key] = yaml.safe_load(text)
        except yaml.YAMLError as exc:
            raise RunConfigError(f"--set {item!r}: the value is not YAML ({exc})") from exc
    return out


def apply_overrides(raw: dict, overrides: dict) -> dict:
    """The run config with the command-line settings on top.

    A key names a setting (rounds_max) or one entry of a setting that is a mapping
    (open_lane.worker_seconds, api_retries.tries); the rest of that mapping stays
    as the run config or the defaults have it. The merge's checks then apply as to
    any run config: an unknown key or a wrong type is refused.
    """
    out = dict(raw)
    base = defaults()
    for key, value in overrides.items():
        head, _, entry = key.partition(".")
        if head == "run_id":
            raise RunConfigError("--set run_id: use --run-id")
        if not entry:
            out[head] = value
            continue
        current = out.get(head, base.get(head))
        if "." in entry or not isinstance(current, dict):
            raise RunConfigError(f"--set {key}: write a setting, or <setting>.<entry> for a setting that is a mapping")
        if head == "open_lane" and head not in out:
            current = {}  # the merge lays open_lane over the defaults and the model folder's entries itself
        out[head] = {**current, entry: value}
    return out


def merge(raw: dict, source: str = "run config") -> dict:
    base = defaults()
    unknown = sorted(set(raw) - set(base) - set(REQUIRED))
    if unknown:
        raise RunConfigError(f"{source}: unknown keys {unknown}")
    missing = [k for k in REQUIRED if k not in raw]
    if missing:
        raise RunConfigError(f"{source}: missing {missing}")
    cfg = {**base, **raw}
    if isinstance(raw.get("open_lane", {}), dict):
        # the defaults, then what the model folder says about itself, then the run config
        cfg["open_lane"] = {**base["open_lane"], **model_open_lane(raw.get("model")), **raw.get("open_lane", {})}
    validate(cfg, source)
    if cfg["open_lane"]["enabled"] and "rule_set" not in raw:
        raise RunConfigError(f"{source}: with the open lane on, rule_set must be written in the run config (no implicit default)")
    return cfg


def _number(cfg, key, errors, integer=False, minimum=None, positive=False):
    v = cfg.get(key)
    if isinstance(v, bool) or not isinstance(v, int if integer else (int, float)):
        errors.append(f"{key} must be {'an integer' if integer else 'a number'}")
    elif positive and v <= 0:
        errors.append(f"{key} must be positive")
    elif minimum is not None and v < minimum:
        errors.append(f"{key} must be at least {minimum}")


def validate(cfg: dict, source: str = "run config") -> None:
    errors = []
    if not isinstance(cfg["run_id"], str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", cfg["run_id"]):
        errors.append("run_id must be letters, digits, '.', '_' or '-'")
    if not isinstance(cfg["model"], str) or not (resolve(cfg["model"]) / "model.py").is_file():
        errors.append(f"model {cfg['model']!r} is not a model folder")
    knobs = cfg["knob_values"]
    if (
        not isinstance(knobs, list)
        or not knobs
        or not all(isinstance(k, (int, float)) and not isinstance(k, bool) and 0 <= k <= 1 for k in knobs)
        or len(set(float(k) for k in knobs)) != len(knobs)
    ):
        errors.append("knob_values must be a non-empty list of distinct numbers in [0, 1]")
    for key in ("time_limit_s", "memory_limit_mb", "max_proof_mb", "check_timeout_s"):
        _number(cfg, key, errors, positive=True)
    for key in ("threads_per_recipe", "workers", "recipes_per_round", "rounds_max", "patience", "prompt_budget_tokens"):
        _number(cfg, key, errors, integer=True, minimum=1)
    for key in ("shown_top_recipes", "shown_last_attempts", "seed"):
        _number(cfg, key, errors, integer=True, minimum=0)
    for key in ("screen", "lean_spot_check"):
        if not isinstance(cfg[key], bool):
            errors.append(f"{key} must be true or false")
    b = cfg["baselines"]
    if not (isinstance(b, bool) or (isinstance(b, list) and b and all(isinstance(x, str) for x in b))):
        errors.append("baselines must be true (all), false (none) or a list of baseline names")
    if cfg["backend"] not in BACKENDS:
        errors.append(f"backend must be one of {BACKENDS}")
    if not isinstance(cfg["fake_responses"], list) or not all(isinstance(p, str) for p in cfg["fake_responses"]):
        errors.append("fake_responses must be a list of paths")
    if not isinstance(cfg["claude_code_command"], str) or not cfg["claude_code_command"]:
        errors.append("claude_code_command must name the Claude Code executable")
    if not isinstance(cfg["api_key_env"], str) or not cfg["api_key_env"]:
        errors.append("api_key_env must name an environment variable")
    elif cfg["api_key_env"] in FORBIDDEN_KEY_VARIABLES:
        errors.append(f"api_key_env must not be {cfg['api_key_env']}: Claude Code would bill its own work to that key")
    ws = cfg.get("api_workspace_env")
    if not isinstance(ws, str) or not ws or ws in FORBIDDEN_KEY_VARIABLES:
        errors.append("api_workspace_env must name an environment variable")
    rules = cfg["rule_set"]
    allowed = generic_rules()  # the generic rules and those adopted through the rule route (rules/)
    if not isinstance(rules, list) or not rules or not set(rules) <= set(allowed):
        errors.append(f"rule_set must be a non-empty list drawn from {list(allowed)}")
    if not isinstance(cfg["prompt_template"], str) or not (REPO_ROOT / "core" / "agent" / "prompts" / f"{cfg['prompt_template']}.md").is_file():
        errors.append(f"prompt_template {cfg['prompt_template']!r} is not in core/agent/prompts")
    thinking = cfg["thinking"]
    if thinking is not None and (not isinstance(thinking, dict) or thinking.get("type") not in THINKING_TYPES):
        errors.append(f"thinking must be null or a mapping whose type is one of {THINKING_TYPES}")
    if cfg["effort"] is not None and cfg["effort"] not in EFFORTS:
        errors.append(f"effort must be null or one of {EFFORTS}")
    if cfg["max_output_tokens"] is not None:
        _number(cfg, "max_output_tokens", errors, integer=True, minimum=1)
    retries = cfg["api_retries"]
    if not isinstance(retries, dict) or set(retries) != {"tries", "first_wait_s", "max_wait_s", "timeout_s"}:
        errors.append("api_retries must give tries, first_wait_s, max_wait_s and timeout_s")
    else:
        for key in retries:
            _number(retries, key, errors, positive=True)
    _number(cfg, "max_consecutive_refusals", errors, integer=True, minimum=1)
    if cfg["metric"] not in METRICS:
        errors.append(f"metric must be one of {METRICS}")
    ratio = cfg.get("budget_ratio")
    if isinstance(ratio, bool) or not isinstance(ratio, (int, float)) or ratio <= 1:
        errors.append("budget_ratio must be a number above 1 (each fixed budget is the previous one divided by it)")
    if cfg["metric"] == "Q_grid" and not (isinstance(cfg.get("open_lane"), dict) and cfg["open_lane"].get("enabled") is True):
        # the fixed rules lane's prompt tells the recipe its budget; an open-lane prompt states the grid itself
        tpl = REPO_ROOT / "core" / "agent" / "prompts" / f"{cfg['prompt_template']}.md"
        if tpl.is_file() and "{KNOB}" not in tpl.read_text():
            errors.append(f"metric Q_grid needs a prompt template with a {{KNOB}} placeholder (v2 or later), not {cfg['prompt_template']!r}")
    nets = cfg["networks"]
    if nets != "all" and (not isinstance(nets, list) or not nets or not all(isinstance(n, str) for n in nets)):
        errors.append('networks must be "all" or a list of network ids')
    if cfg["sandbox_dir"] is not None and not isinstance(cfg["sandbox_dir"], str):
        errors.append("sandbox_dir must be a path or null")
    if cfg["sandbox"] not in SANDBOX_MODES:
        errors.append(f"sandbox must be one of {SANDBOX_MODES}")
    if not isinstance(cfg["sandbox_image"], str) or not cfg["sandbox_image"]:
        errors.append("sandbox_image must name a container image")
    errors += open_lane_errors(cfg)
    if errors:
        raise RunConfigError(f"{source}: " + "; ".join(errors))


OPEN_LANE_KEYS = {"enabled", "lean_project", "work_dir", "python", "compile_calls", "python_calls", "submissions", "max_turns",
                  "worker_seconds", "notes_reserve_seconds", "python_workspace_mb", "python_workspace_files", "stall_rounds", "fake_scripts", "example", "extra_sources", "knowledge", "second_example", "notes",
                  "seed_check", "scaling", "split_example"}
KNOWLEDGE_CONDITIONS = ("minimal", "maximum")


def open_lane_errors(cfg: dict) -> list[str]:
    ol = cfg.get("open_lane")
    if not isinstance(ol, dict):
        return ["open_lane must be a mapping"]
    unknown = sorted(set(ol) - OPEN_LANE_KEYS)
    if unknown:
        return [f"open_lane: unknown keys {unknown}"]
    errors = []
    if not isinstance(ol.get("enabled"), bool):
        errors.append("open_lane.enabled must be true or false")
    for key in ("compile_calls", "python_calls", "submissions", "max_turns", "stall_rounds"):
        _number(ol, key, errors, integer=True, minimum=1)
    _number(ol, "worker_seconds", errors, positive=True)
    _number(ol, "notes_reserve_seconds", errors, minimum=0)
    _number(ol, "python_workspace_mb", errors, positive=True)
    _number(ol, "python_workspace_files", errors, positive=True, integer=True)
    reserve, clock = ol.get("notes_reserve_seconds"), ol.get("worker_seconds")
    if all(isinstance(v, (int, float)) and not isinstance(v, bool) for v in (reserve, clock)) and reserve >= clock:
        errors.append("open_lane.notes_reserve_seconds must be less than open_lane.worker_seconds")
    if not isinstance(ol.get("fake_scripts"), list) or not all(isinstance(p, str) for p in ol["fake_scripts"]):
        errors.append("open_lane.fake_scripts must be a list of paths")
    for key in ("lean_project", "work_dir", "python"):
        if ol.get(key) is not None and not isinstance(ol[key], str):
            errors.append(f"open_lane.{key} must be a path or null")
    if not isinstance(ol.get("example"), str) or not ol["example"]:
        errors.append("open_lane.example must be a path in the Lean project")
    if not isinstance(ol.get("extra_sources"), list) or not all(isinstance(p, str) for p in ol["extra_sources"]):
        errors.append("open_lane.extra_sources must be a list of paths in the Lean project")
    second = ol.get("second_example")
    if second is not None and (not isinstance(second, str) or not second.startswith("examples/") or ".." in second):
        errors.append("open_lane.second_example must be null or a path under examples/ in the Lean project")
    split = ol.get("split_example")
    if split is not None and (not isinstance(split, str) or not split.startswith("examples/") or ".." in split):
        errors.append("open_lane.split_example must be null or a path under examples/ in the Lean project")
    if not isinstance(ol.get("notes", ""), str):
        errors.append("open_lane.notes must be text")
    check = ol.get("seed_check")
    if check is not None and not (isinstance(check, dict) and set(check) == {"network"} and isinstance(check["network"], str)):
        errors.append("open_lane.seed_check must be null or {network: <a development network of the model>}")
    if not isinstance(ol.get("scaling", False), bool):
        errors.append("open_lane.scaling must be true or false")
    if ol.get("knowledge") not in KNOWLEDGE_CONDITIONS:
        errors.append(f"open_lane.knowledge must be one of {', '.join(KNOWLEDGE_CONDITIONS)}")
    errors = [f"open_lane: {e}" if not e.startswith("open_lane") else e for e in errors]
    if ol.get("enabled") is True and not errors:
        project = ol.get("lean_project")
        if not project or not (Path(project).expanduser() / "scripts" / "accept.py").is_file():
            errors.append("open_lane.lean_project must be the Lean project (with scripts/accept.py)")
        else:
            for rel in [ol["example"], *ol["extra_sources"], *([second] if second else []), *([split] if split else [])]:
                if not (Path(project).expanduser() / rel).is_file():
                    errors.append(f"the Lean project has no {rel} (open_lane.example, open_lane.extra_sources, open_lane.second_example)")
        if cfg["backend"] not in ("fake", "claude_code"):
            errors.append("the open lane runs with backend fake or claude_code")
        tpl = REPO_ROOT / "core" / "agent" / "prompts" / f"{cfg['prompt_template']}.md"
        if tpl.is_file() and "{COUNTED}" not in tpl.read_text():
            errors.append(f"the open lane needs an open-lane prompt template (open_lane_v1), not {cfg['prompt_template']!r}")
    return errors
