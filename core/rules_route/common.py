"""What the route's steps share: prompts, response sections, backends and the checker context."""

from __future__ import annotations

import re
from pathlib import Path

from ..agent.backends import BackendError
from ..agent.build_prompt import Prompt
from ..agent.parse import code_blocks
from ..util import REPO_ROOT, read_yaml

PROMPTS = Path(__file__).resolve().parent / "prompts"
PART1, PART2 = "=== PART 1 ===", "=== PART 2 ==="
CONTEXT_FILES = (
    "core/check/plugins.py",
    "core/check/cost.py",
    "core/check/interval.py",
    "core/check/tokens.py",
    "core/check/general.py",
    "core/check/rules.py",
    "docs/RULES.md",
)
RULE_FILES = ("rule.py", "SOUNDNESS.md", "test_rule.py")
_FENCE = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})")
_CLOSE = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})[ \t]*$")


def template(name: str) -> tuple[str, str]:
    text = (PROMPTS / f"{name}.md").read_text()
    head, part2 = text.split(PART2, 1)
    return head.replace(PART1, "", 1).strip() + "\n", part2.strip() + "\n"


def fill(text: str, values: dict) -> str:
    for k, v in values.items():
        text = text.replace("{" + k + "}", v)
    return text


def file_block(path: str, text: str) -> str:
    return f"\n----- {path} -----\n{text.rstrip()}\n----- end of {path} -----\n"


def checker_context(rules_dir: Path | None = None, exclude: str | None = None) -> str:
    """The checker's code and every adopted rule's files (the worked examples)."""
    from ..check.plugins import RULES_DIR, adopted

    out = []
    for rel in CONTEXT_FILES:
        p = REPO_ROOT / rel
        if p.is_file():
            out.append(file_block(rel, p.read_text()))
    seen = set()
    for path in model_sources():  # each distinct architecture the rule may meet, once
        text = path.read_text()
        if text not in seen:
            seen.add(text)
            out.append(file_block(path.relative_to(REPO_ROOT).as_posix(), text))
    for name, rule in sorted(adopted(rules_dir or RULES_DIR).items()):
        if name == exclude:
            continue
        for f in RULE_FILES:
            p = rule.path / f
            if p.is_file():
                out.append(file_block(f"rules/{name}/{f}", p.read_text()))
    return "".join(out)


def model_sources() -> list:
    """The model.py of every model folder whose network goes beyond linear maps."""
    from ..check.trace import build_any
    from ..model_folder import load_model_folder

    out = []
    for path in sorted((REPO_ROOT / "models").iterdir()):
        if (path / "model.py").is_file():
            folder = load_model_folder(path)
            if getattr(build_any(folder.build(folder.setting_names()[0])), "general", False):
                out.append(path / "model.py")
    return out


def models_summary() -> str:
    from ..check.trace import build_any
    from ..model_folder import load_model_folder
    from ..zoo import networks

    lines = []
    for root in (REPO_ROOT / "models", REPO_ROOT / "tests"):
        for path in sorted(p for p in root.iterdir() if p.is_dir()):
            if not ((path / "model.py").is_file() and (path / "config.yaml").is_file()):
                continue
            folder = load_model_folder(path)
            for setting in folder.setting_names():
                if not getattr(build_any(folder.build(setting)), "general", False):
                    break
                ids = [e["id"] for e in networks(folder, setting=setting)] if folder.zoo_dir().is_dir() else []
                params = {k: list(v.shape) for k, v in folder.build(setting).state_dict().items()}
                where = path.relative_to(REPO_ROOT).as_posix()
                lines.append(f"- {folder.name} ({where}), setting {setting} (sizes {folder.sizes(setting)}; parameters {params}): "
                             f"{', '.join(ids) if ids else 'no trained networks'}")
    return "\n".join(lines)


def split_sections(text: str, names: tuple) -> dict:
    """Section name -> its text, for headings like 'NAME: ...', '## Name' or '**NAME:**' outside code fences.
    The first copy of a heading counts; later copies are ordinary text."""
    alt = "|".join(re.escape(n) for n in sorted(names, key=len, reverse=True))
    pats = [
        re.compile(rf"^[ \t]*({alt})[ \t]*:(.*)$"),
        re.compile(rf"^[ \t]*({alt})[ \t]*$"),
        re.compile(rf"^[ \t]*#{{1,6}}[ \t]+(?:\*\*)?[ \t]*({alt})[ \t]*:?[ \t]*(?:\*\*)?[ \t]*:?(.*)$", re.IGNORECASE),
        re.compile(rf"^[ \t]*\*\*[ \t]*({alt})[ \t]*:?[ \t]*\*\*[ \t]*:?(.*)$", re.IGNORECASE),
    ]
    out, current, fence = {}, None, None
    for line in text.splitlines():
        if fence is None:
            heading = None
            for pat in pats:
                m = pat.match(line)
                if m:
                    rest = (m.group(2) if m.lastindex and m.lastindex >= 2 else "") or ""
                    heading = (m.group(1).upper(), rest.strip())
                    break
            if heading is not None and heading[0] not in out:
                current = heading[0]
                out[current] = [heading[1]] if heading[1] else []
                continue
            m = _FENCE.match(line)
            if m:
                fence = m.group(1)
        else:
            m = _CLOSE.match(line)
            if m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence):
                fence = None
        if current is not None:
            out[current].append(line)
    return {k: "\n".join(v).strip() for k, v in out.items()}


def one_code_block(text: str, what: str) -> str:
    blocks, unclosed = code_blocks(text.splitlines())
    if unclosed:
        raise ValueError(f"{what}: a code block is not closed")
    if len(blocks) != 1:
        raise ValueError(f"{what}: expected exactly one code block, found {len(blocks)}")
    return blocks[0][1]


def backend_config(role: dict, cfg: dict) -> dict:
    """The keys core.agent.backends.api.ApiBackend reads, from a role's settings and the route config."""
    defaults = read_yaml(REPO_ROOT / "config" / "defaults.yaml") or {}
    out = {
        "api_key_env": cfg.get("api_key_env", defaults.get("api_key_env", "CPL_ANTHROPIC_KEY")),
        "api_workspace_env": cfg.get("api_workspace_env", defaults.get("api_workspace_env")),
        "agent_model": role.get("agent_model", defaults.get("agent_model")),
        "max_output_tokens": role.get("max_output_tokens", 64000),
        "thinking": role.get("thinking", defaults.get("thinking")),
        "effort": role.get("effort", defaults.get("effort")),
        "api_retries": defaults.get("api_retries"),
    }
    return out


def make_backend(role: dict, cfg: dict, log=print):
    kind = role.get("backend", "fake")
    if kind == "fake":
        from ..agent.backends.fake import FakeBackend

        src = role.get("responses")
        if not src:
            raise BackendError("a fake backend needs responses: a file or a folder of them")
        return FakeBackend([REPO_ROOT / src if not Path(src).is_absolute() else src])
    if kind == "manual":
        from ..agent.backends.manual import ManualBackend

        return ManualBackend(log=log)
    if kind == "api":
        from ..agent.backends.api import ApiBackend

        return ApiBackend(backend_config(role, cfg), log=log)
    raise BackendError(f"unknown backend {kind!r} (fake, manual or api)")


def prompt(part1: str, part2: str) -> Prompt:
    return Prompt(part1, part2)
