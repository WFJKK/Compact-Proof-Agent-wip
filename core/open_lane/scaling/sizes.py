"""The sizes of a network, for the scaling proofs.

They are the whole-number entries of the network's size setting in its model folder, whatever they are called
there. A model folder declares nothing for the scaling proofs, so they can follow a run on any network, and
nothing a run's identity rests on changes with them. open_lane.scaling_names (the run's, or
config/defaults.yaml's for a run made before the setting existed) gives the names it lists a symbol and words
for the prompts and the report, puts them first, in its order, and joins names that are one size where they
have the same value on the network (a width and a head width that are equal), under the symbol of the one
listed first. A name it does not list is a size under its own name.

A size here is {symbol, words, names, value}: `names` are the size setting's entries that vary with it.
"""

from __future__ import annotations

import re

import yaml

from ...run_config import DEFAULTS_PATH, SCALING_GENERAL, SCALING_SIZES, scaling_names_errors

OWN_WORDS = "the size"  # of a size that open_lane.scaling_names does not name


class SizesError(ValueError):
    pass


def naming(cfg: dict) -> dict:
    """open_lane.scaling_names: the run's, or config/defaults.yaml's."""
    block = (cfg.get("open_lane") or {}).get("scaling_names")
    if block is None:
        block = yaml.safe_load(DEFAULTS_PATH.read_text())["open_lane"]["scaling_names"]
    errors = scaling_names_errors(block)
    if errors:
        raise SizesError("; ".join(errors))
    return block


def of_network(cfg: dict, folder, entry: dict) -> list[dict]:
    """The sizes of a network, in the order the sessions take them."""
    values = {name: v for name, v in folder.sizes(entry["setting"]).items() if isinstance(v, int) and not isinstance(v, bool)}
    if not values:
        raise SizesError(f"the size setting {entry['setting']!r} of {entry['id']} has no whole-number entry: no size to vary")
    block = naming(cfg)
    names, groups = {e["name"]: e for e in block.get("names") or []}, block.get("together") or []
    out, used = [], set()
    for name in [n for n in names if n in values] + [n for n in values if n not in names]:
        if name in used:
            continue
        group = next((g for g in groups if name in g), [name])
        members = [name] + [m for m in group if m != name and m in values and m not in used and values[m] == values[name]]
        used.update(members)
        named = names.get(name)
        symbol = named["symbol"] if named else re.sub(r"[^A-Za-z0-9_]", "_", name)
        out.append({"symbol": symbol, "words": named["words"] if named else OWN_WORDS, "names": members, "value": values[name]})
    symbols = [s["symbol"] for s in out]
    clash = sorted({s for s in symbols if symbols.count(s) > 1 or s in (SCALING_GENERAL, SCALING_SIZES) or not re.match(r"[A-Za-z]", s)})
    if clash:
        raise SizesError(f"the sizes of {entry['id']} cannot be told apart or named as steps ({', '.join(clash)}): give them symbols in "
                         "open_lane.scaling_names")
    return out


def stored(sp: dict, cfg: dict) -> list[dict]:
    """The sizes a run's scaling proofs were begun with, as a list. (The first ones, of 24 November 2026, kept
    {symbol: {names, value}} for the symbols V, n and d: their words are read from the naming.)"""
    sizes = sp["sizes"]
    if isinstance(sizes, list):
        return sizes
    words = {e["symbol"]: e["words"] for e in naming(cfg).get("names") or []}
    return [{"symbol": symbol, "words": words.get(symbol, OWN_WORDS), "names": list(s["names"]), "value": s["value"]}
            for symbol, s in sizes.items()]


def text(size: dict) -> str:
    """`<symbol> = <value> (<its name in the size setting>)`; several names vary together; a size called by its
    own name is not named twice."""
    names = size["names"]
    if names == [size["symbol"]]:
        return f"{size['symbol']} = {size['value']}"
    return f"{size['symbol']} = {size['value']} ({' and '.join(names)}" + (", varied together)" if len(names) > 1 else ")")


def phrase(size: dict) -> str:
    """`the number of token values V`."""
    return f"{size['words']} {size['symbol']}"


def listed(symbols: list[str]) -> str:
    """`V, n and d`."""
    return symbols[0] if len(symbols) == 1 else ", ".join(symbols[:-1]) + " and " + symbols[-1]
