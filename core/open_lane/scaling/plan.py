"""Which sessions the scaling proofs have, and what each is called.

open_lane.scaling_steps (the run's, or config/defaults.yaml's for a run made before the setting existed) is a
list of {parameter, minutes, usd}. A parameter is:

- `general`: the session that writes the checker with its sizes as parameters and proves its exact cost;
- `sizes`: one session for every size of the network that the list does not name itself, in the sizes' order;
- the symbol of one size: the session for that size, with settings of its own.

Which sizes a network has is not known here (core.open_lane.scaling.sizes): the list is expanded against them
when a run's sessions are planned. A session's record (a "step") has the parameter `general` or a size's symbol.
"""

from __future__ import annotations

import copy

import yaml

from ...run_config import DEFAULTS_PATH, SCALING_GENERAL, SCALING_SIZES, scaling_steps_errors
from . import sizes as network_sizes


class ScalingError(ValueError):
    pass


def default_steps() -> list[dict]:
    return [dict(s) for s in yaml.safe_load(DEFAULTS_PATH.read_text())["open_lane"]["scaling_steps"]]


def configured_steps(cfg: dict) -> list[dict]:
    """open_lane.scaling_steps as written: the run's, or config/defaults.yaml's."""
    steps = (cfg.get("open_lane") or {}).get("scaling_steps")
    if steps is None:
        steps = default_steps()
    errors = scaling_steps_errors(steps)
    if errors:
        raise ScalingError("; ".join(errors))
    return [dict(s) for s in steps]


def expand(steps: list[dict], sizes: list[dict], where: str = "open_lane.scaling_steps") -> list[dict]:
    """The sessions a list of steps stands for on a network with these sizes, in order: `sizes` becomes one
    session for each size the list does not name; a symbol must be one of the network's."""
    symbols = [s["symbol"] for s in sizes]
    named = [s["parameter"] for s in steps if s["parameter"] not in (SCALING_GENERAL, SCALING_SIZES)]
    unknown = [p for p in named if p not in symbols]
    if unknown:
        raise ScalingError(f"{where} names {network_sizes.listed(unknown)}, which is no size of this network: its sizes are "
                           + ", ".join(network_sizes.text(s) for s in sizes))
    out = []
    for s in steps:
        if s["parameter"] == SCALING_SIZES:
            out += [{**s, "parameter": symbol} for symbol in symbols if symbol not in named]
        else:
            out.append(dict(s))
    return out


def planned(cfg: dict, sizes: list[dict]) -> list[dict]:
    """The sessions of a run on a network with these sizes: {parameter, minutes, usd}, in order."""
    return expand(configured_steps(cfg), sizes)


def settings(cfg: dict, sizes: list[dict]) -> dict:
    """For `general` and each size's symbol, the minutes and dollars a session for it gets: the run's steps',
    else config/defaults.yaml's."""
    out = {}
    for steps in (default_steps(), configured_steps(cfg)):
        both = {s["parameter"]: s for s in steps}
        for name in [SCALING_GENERAL] + [s["symbol"] for s in sizes]:
            found = both.get(name) or (both.get(SCALING_SIZES) if name != SCALING_GENERAL else None)
            if found:
                out[name] = {"minutes": found["minutes"], "usd": found["usd"]}
    return out


def wanted(names: list[str], cfg: dict, sizes: list[dict]) -> list[str]:
    """`--again`'s names as sessions, in the sessions' order: `general`, `sizes` (every size) or sizes' symbols;
    none named: every session the run's steps stand for."""
    symbols = [s["symbol"] for s in sizes]
    known = [SCALING_GENERAL] + symbols
    unknown = [n for n in names if n not in known and n != SCALING_SIZES]
    if unknown:
        raise ScalingError(f"--again takes some of {', '.join(known)} (or `{SCALING_SIZES}` for every size), not "
                           + ", ".join(map(str, unknown)))
    if not names:
        return [s["parameter"] for s in planned(cfg, sizes)]
    chosen = set(names) | (set(symbols) if SCALING_SIZES in names else set())
    return [p for p in known if p in chosen]


def step_config(cfg: dict, step: dict) -> dict:
    """The run's config for one session: its session time and its own dollar cap."""
    out = copy.deepcopy(cfg)
    out["open_lane"]["worker_seconds"] = int(round(float(step["minutes"]) * 60))
    if isinstance(out.get("api_budget"), dict):
        out["api_budget"]["round_usd"] = float(step["usd"])
    return out


# what a session is called ------------------------------------------------------------------
def is_general(step: dict) -> bool:
    return step["parameter"] == SCALING_GENERAL


def kind(step: dict) -> str:
    """`general`, or `size` for the session of one size: which text the session gets (core.open_lane.scaling.prompt)."""
    return SCALING_GENERAL if is_general(step) else "size"


def size_of(step: dict, sizes: list[dict]) -> dict:
    found = next((s for s in sizes if s["symbol"] == step["parameter"]), None)
    if found is None:
        raise ScalingError(f"the session of round {step.get('round', '?')} is for {step['parameter']}, which is no size of this "
                           "run's network as its scaling proofs recorded them")
    return found


def name(step: dict) -> str:
    """A session as the log, the status and the report call it."""
    return ("scaling, the general checker" if is_general(step) else f"scaling in {step['parameter']}") + (
        ", a further session" if step.get("again") else "")


GENERAL_WORDS = "the checker with its sizes as parameters"


def words(step: dict, sizes: list[dict]) -> str:
    """A session as a prompt calls it."""
    return (GENERAL_WORDS if is_general(step) else network_sizes.phrase(size_of(step, sizes))) + (" again" if step.get("again") else "")
