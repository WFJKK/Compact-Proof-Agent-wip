"""The prompt builder, information hygiene and the manual backend."""

import inspect
import threading
import time
from pathlib import Path

import pytest
import yaml

from core import loop
from core.agent.build_prompt import REMOVED, Prompt, PromptError, build_prompt, fill, load_template, placeholders
from core.check import cost
from core.check.rules import RULES
from core.model_folder import load_model_folder
from core.zoo import networks

TESTS = Path(__file__).resolve().parent
RECIPE = '''```python
import helpers


def make_proof(weights, info, knob):
    return helpers.proof(helpers.full_tree(info["input_space"]))
```'''


def response(claim="It checks every input.", notes="Brute force first.") -> str:
    return (
        f"CLAIM: {claim}\n\nWHY IT HELPS: It does not.\n\nPREDICTION: Full accuracy at B.\n\nKNOB: Unused.\n\n"
        f"RECIPE:\n{RECIPE}\n\nNOTES: {notes}\n"
    )


def start(tmp_path, model, responses, **over):
    cfg = {
        "run_id": "prompt-test",
        "model": str(model),
        "runs_dir": str(tmp_path / "runs"),
        "knob_values": [0, 1],
        "sandbox": "process",  # trusted recipes only; keeps these tests quick
        "fake_responses": [str(p) for p in responses],
        "rounds_max": 5,
    }
    cfg.update(over)
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    return loop.start(path, log=lambda *a: None)


def write_responses(tmp_path, texts) -> list[Path]:
    folder = tmp_path / "responses"
    folder.mkdir(exist_ok=True)
    out = []
    for i, t in enumerate(texts):
        p = folder / f"{i:02d}.md"
        p.write_text(t)
        out.append(p)
    return out


def test_template_has_two_parts_and_every_placeholder_gets_a_value():
    part1, part2 = load_template("v1")
    assert "PART 1" not in part1 and "PART 2" not in part2
    assert part2.startswith("ROUND {k} OF {K}")
    assert placeholders(part1) | placeholders(part2) == {
        "MODEL_SOURCE", "TASK_DESCRIPTION", "SIZE_SETTINGS", "INFO", "TEMPLATE", "RULES_SPEC", "COST_MODEL",
        "METRIC", "TIME_LIMIT", "k", "K", "FRONTIER", "TOP_RECIPES", "m", "DIAGNOSTICS", "GROUPING", "NOTES",
    }
    assert fill("a {X} b {Y}", {"X": "{Y}", "Y": "2"}) == "a {Y} b 2"  # values are never filled again
    with pytest.raises(PromptError, match="no value"):
        fill("{X}", {})


def test_round_one_prompt_comes_from_the_model_folder_and_round_zero(trained_stub, tmp_path):
    ctx = start(tmp_path, trained_stub, [])
    loop.drive(ctx)  # round 0 only: the fake backend has no responses
    folder = ctx.folder
    p = build_prompt(ctx.cfg, folder, ctx.entries, ctx.run, 1)
    text = p.text
    assert folder.source().strip() in text  # the module's source, verbatim
    assert folder.task.DESCRIPTION in text and folder.task.GROUPING in text
    assert "d_hidden=5" in text and "25 inputs" in text
    for name in ctx.cfg["rule_set"]:
        assert RULES[name] in text
    assert inspect.getdoc(cost).strip() in text
    e = ctx.entries[0]
    assert f"E {e['E']:,}, B {e['B']:,}" in text
    assert "ROUND 1 OF 5" in text and "None yet: this is your first round." in text
    assert "baseline 01_brute_force" in text and "baseline 02_symmetry" in text
    assert "def make_proof" in p.part2  # the best recipes come with their code
    assert p.stats["tokens_estimate"] == p.stats["chars"] // 4 and p.stats["removed"] == 0


def test_hygiene_never_lets_forbidden_strings_or_held_out_ids_through(trained_stub, tmp_path):
    folder = load_model_folder(trained_stub)
    held = networks(folder, "held_out")[0]["id"]
    secret = folder.hygiene_terms()[0]
    texts = [response(claim=f"It uses {secret}.", notes=f"Compare with {held}; remember {secret}.")]
    ctx = start(tmp_path, trained_stub, write_responses(tmp_path, texts), rounds_max=2)
    loop.drive(ctx)
    p = build_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, 2)
    assert secret not in p.text and held not in p.text
    assert REMOVED in p.part2 and p.stats["removed"] >= 3
    assert "round 1:" in p.part2  # the attempt itself is still shown
    # Every prompt the loop saved is clean too.
    for path in ctx.run.path.glob("round_*/prompt.md"):
        assert secret not in path.read_text() and held not in path.read_text()


def test_a_model_folder_that_leaks_into_part_one_is_an_error(trained_stub, tmp_path):
    model = tmp_path / "leaky"
    import shutil

    shutil.copytree(trained_stub, model, ignore=shutil.ignore_patterns("__pycache__"))
    task = model / "task.py"
    task.write_text(task.read_text().replace('DESCRIPTION = "', 'DESCRIPTION = "SECRET-HINT: '))
    ctx = start(tmp_path, model, [])
    loop.drive(ctx)
    with pytest.raises(PromptError, match="forbidden"):
        build_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, 1)


def test_the_budget_drops_code_first(trained_stub, tmp_path):
    ctx = start(tmp_path, trained_stub, [])
    loop.drive(ctx)
    full = build_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, 1)
    cfg = {**ctx.cfg, "prompt_budget_tokens": (full.stats["chars"] - 100) // 4}
    small = build_prompt(cfg, ctx.folder, ctx.entries, ctx.run, 1)
    assert small.stats["trimmed"] and small.stats["trimmed"][0].startswith("code of best recipe")
    assert small.stats["chars"] < full.stats["chars"]
    tiny = build_prompt({**ctx.cfg, "prompt_budget_tokens": 1}, ctx.folder, ctx.entries, ctx.run, 1)
    assert tiny.stats["trimmed"][-1] == "still over budget" and "code left out" in tiny.part2


def test_a_resumed_round_sends_the_prompt_it_saved(trained_stub, tmp_path):
    ctx = start(tmp_path, trained_stub, write_responses(tmp_path, [response(), response()]), rounds_max=2)
    loop.drive(ctx)
    saved = ctx.run.read(2, "prompt.json")
    assert Prompt.from_json(saved).text == ctx.run.read(2, "prompt.md")
    for name in ("DONE", "meta.json", "attempt_0/results.json"):
        (ctx.run.round_path(2) / name).unlink()
    ctx2 = loop.resume(ctx.run.path, log=lambda *a: None)
    assert loop.round_prompt(ctx2, 2).as_json() == saved
    loop.drive(ctx2)
    assert ctx2.run.round_done(2) and ctx2.run.read(2, "prompt.json") == saved
    assert ctx2.run.read(2, "meta.json")["prompt"] == saved["stats"]


def test_one_manual_round_end_to_end(trained_stub, tmp_path):
    ctx = start(tmp_path, trained_stub, [], backend="manual", rounds_max=1)
    import core.agent.backends.manual as manual

    done = threading.Event()
    errors = []

    def run():
        try:
            loop.drive(ctx)
        except Exception as exc:  # surfaced below
            errors.append(exc)
        finally:
            done.set()

    original = loop.make_backend
    loop.make_backend = lambda cfg, log=print: manual.ManualBackend(log=log, poll_s=0.1, settle_s=0.2)
    try:
        th = threading.Thread(target=run, daemon=True)
        th.start()
        prompt = ctx.run.round_path(1) / "prompt.md"
        deadline = time.time() + 120
        while not prompt.exists() and time.time() < deadline:
            time.sleep(0.1)
        assert prompt.exists() and "ROUND 1 OF 1" in prompt.read_text()
        assert not done.is_set()  # waiting for a person
        (ctx.run.round_path(1) / "attempt_0" / "response.md").write_text(response())
        assert done.wait(timeout=300)
    finally:
        loop.make_backend = original
    assert not errors, errors
    recs = [r for r in ctx.run.read_archive() if r["round"] == 1]
    assert recs and {r["status"] for r in recs} == {"ok"}
    assert ctx.run.read(1, "attempt_0/response_meta.json")["backend"] == "manual"


def test_template_v3_ends_with_the_aim_and_the_score_as_it_stands(trained_stub, tmp_path):
    part1, part2 = load_template("v3")
    assert placeholders(part2) - placeholders(load_template("v2")[1]) == {"AIM"}
    assert part2.rstrip().endswith("{AIM}") and "AIM" not in placeholders(part1)
    from core.run_config import METRICS

    names = {"Q": "Q", "Q_grid": "Q_grid", "Q_exact": "Q_exact", "Q_above": "Q_above", "cost_of_finishing": "cost of finishing"}
    assert set(METRICS) == set(names), "a metric without a prompt test"
    for metric, name in names.items():
        (tmp_path / metric).mkdir()
        ctx = start(tmp_path / metric, trained_stub, [], prompt_template="v3", metric=metric)
        loop.drive(ctx)
        text = build_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, 1).part2
        aim = text.split("YOUR AIM THIS ROUND", 1)[1]
        assert f"Raise your score, {name}. It stands at:" in aim and "consider several approaches" in aim
        assert all(e["setting"] in aim for e in ctx.entries)
        # the score as the run takes it: the mean over networks for Q_exact, the median otherwise
        mean = metric in ("Q_exact", "Q_above")
        assert (" mean " in aim) == mean and (" median " in aim) == (not mean)


@pytest.mark.parametrize("model", ["max2", "attn-max2", "attn-max4", "attn-min2", "attn-min4", "xorformer-majority"])
def test_the_default_prompt_never_names_the_paper(model):
    from core.agent.build_prompt import static_values
    from core.run_config import merge

    repo = Path(__file__).resolve().parent.parent
    folder = load_model_folder(repo / "models" / model)
    cfg = merge({"run_id": "x", "model": f"models/{model}"})
    entries = [e for e in networks(folder) if e["split"] == "dev"]
    part1, part2 = load_template(cfg["prompt_template"])
    text = fill(part1, static_values(cfg, folder, entries)) + part2
    assert "Gross" not in text and "Compact Proofs of Model Performance" not in text
    assert {"Gross", "Compact Proofs of Model Performance"} <= set(folder.hygiene_terms())  # and part 2 is scrubbed
