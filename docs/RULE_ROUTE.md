# The rule route: from an agent's rule idea to a rule the checker uses

The agent that writes proofs often asks for a rule the checker does not have (its NEW RULE IDEA section). The route turns such an idea into an adopted rule without a person in between, while the agent being scored never writes checker code:

1. **Propose.** The scored agent describes the idea. `python -m core.rules_route proposals <run folder>` lists a run's ideas, with the attempts that gave them.
2. **Implement.** A separate implementer agent, not scored on anything, writes `rule.py`, `SOUNDNESS.md` and `test_rule.py` against a fixed contract (`core/check/plugins.py`). Its prompt (`core/rules_route/prompts/implement.md`) gives the contract, the hard constraints, the checker's code and the adopted rules as worked examples, and treats the proposal as data.
3. **Check**, in a check box (below):
   - the static guard on `rule.py`;
   - the candidate's own tests;
   - the audit (`core/rules_route/audit.py`): the rule's bound on every sampled leaf against brute force, on trained development networks, on random-weight networks at three scales (very sharp softmaxes included), on trained networks with perturbed weights, and on synthetic model folders in `tests/` that use operations the trained ones do not. Leaves of token_interval are interleaved on the same program, so whatever the rules keep across leaves is shared, and the cases in `tests/rule_route/regressions.json` (bugs found before, as sequences of leaves) run every time. A bound above a leaf's smallest float64 margin is a violation, and every input of every certified leaf is rechecked with the exact single rule. A leaf where the rule crashes is reported (the checker would reject that proof), not counted as unsound.
4. **Review.** An adversarial reviewer agent (`prompts/review.md`) tries to break the rule and the argument, and returns a verdict (SOUND, UNSOUND or UNSURE) and counterexamples. The audit runs the counterexamples; one confirmed violation rejects the rule, whatever the verdict.
5. **Adopt.** A candidate that passes everything, with every verdict in `adopt_on` (SOUND by default), is copied to `rules/<name>/`. Its `status.json` records the tier (`python-checked`), where the idea and the code came from, the checks it passed, and the SHA-256 of its files. If a check fails, the implementer gets the reasons and tries again, up to `revisions` times.

Nothing is committed or pushed by the route; commit `rules/<name>/` to keep it.

## Running it

A route is one YAML file (`config/rule-route-token-convex.yaml` is the first):

```yaml
route_id: my-rule-2026-10-20
name: my_rule                       # the rule's name and folder
proposal:
  run: ~/auto-research-compact-proof-runs/attn-max4-q-api-tokens   # or file: ..., or text: ...
  pick: latest                      # or the index from `proposals`
implementer: {backend: api, agent_model: claude-fable-5-1, effort: high, max_output_tokens: 64000}
reviewer: {backend: api, agent_model: claude-opus-5-5, effort: high}
reviewers: 1
revisions: 1
audit_level: full
checks_sandbox: hardened
adopt_on: [SOUND]
```

```text
python -m core.rules_route run config/<route>.yaml
python -m core.rules_route status config/<route>.yaml
```

Each step writes into `work_dir/<route_id>/` (by default `~/auto-research-compact-proof-runs/rule-route/`) and is skipped once done, so a route stopped by a crash or a lost connection resumes without repeating a paid call (responses are saved before they are parsed). Backends are the loop's: `fake` replays files, `manual` waits for a person (or another agent) to write `answer/response.md` next to the prompt, `api` calls the model with the key in `api_key_env`. A route costs two calls per attempt (implementer and reviewer), each with a prompt of roughly 50,000 tokens (the checker's code and the adopted rules), plus the audit's CPU time (about 15 minutes at `full` on two cores).

On the Mac, the check box needs Docker and the checks image, built once:

```text
python -m core.rules_route build-image
```

## The check box

The candidate's tests and audit run code an agent wrote, so they run in a box (`core/rules_route/box.py`): a fresh folder with a copy of the code and the model folders, run in one of three modes:

- `container`: Docker or Podman with the checks image, no network, a read-only root, nobody, no capabilities;
- `landlock` (Linux): no new privileges, no sockets, reading only Python, system libraries and the box, writing only the box's `out/` and `tmp/`;
- `process`: a plain process with resource limits.

`hardened` (the default) takes one of the first two and refuses to fall back. The environment never carries an API key, and the box's copy is thrown away afterwards. A probe in landlock mode confirmed that a candidate there cannot open a socket, read the real repository or write outside the box.

## Trust

An adopted rule runs inside the checker, so it extends the trusted code. What stands behind it:

- **The static guard** (`core/check/plugins.py`): imports from an allowlist only, no names or attributes that reach files, processes or the network, no dynamic code. It keeps accidents out; it is not a security boundary.
- **The audit**, in the box, against brute force on networks the rule was not written for.
- **The adversarial review** and its audited counterexamples.
- **Hash pinning**: the checker uses an adopted rule only while its files match the hashes in `status.json`; any edit takes it out of use until the route adopts it again. The rule's files are part of the checker hash that every result records.
- **The runtime audit**: in every run that uses an adopted rule, the checker worker compares each accepted leaf's bound with the float margins of its inputs, and any excess halts the run. So an unsound rule cannot quietly inflate a frontier.
- **Labels**: results with adopted-rule leaves are Python-checked, like everything else until the Lean checker covers the rule.

What this does not cover: a rule that is sound on every leaf it is ever given but charges less than its work (the reviewer is asked to look for this; the cost model's conventions are in the prompt), and code that behaves differently outside the audit's leaves on purpose (the reviewer reads the code for this). The Lean checker, being built separately, is the real answer to both: a rule with a Lean soundness proof and a Lean implementation no longer needs to be trusted. A rule adopted here is the candidate for that.

## The first rule: token_convex

`rules/token_convex/` is the first rule through the route (19 October 2026). The agent's four-token proofs stayed at B/23 to B/124 because a leaf where several positions vary is bounded weight by weight, and the weights can add up to far more than one. The rule keeps the softmax's scores and bounds the attention-weighted sum by its exact minimum over the box of scores, or over every choice of one token per position (Dinkelbach's method), pessimising over the wrong outputs first as Gross et al.'s cubic proof does. `SOUNDNESS.md` has the argument and `PROPOSAL.md` the idea. Implemented by hand this first time; checked and reviewed as any candidate (`status.json`).

What the first pass through the route found: the adversarial review (an independent agent, given only the files and the audit) confirmed two memo-keying bugs that the new rule shared with token_interval, neither reachable on the model folders of the day. An nn.Linear's bias step read back its product's rows (the bias was dropped). Two terms with one origin, as in h @ A + h @ B, read each other's rows at the next product. Both are fixed in the core (commits 587d440 and 02304ec), with regression tests and two synthetic model folders (`tests/stub_general`, `tests/stub_twopaths`) that the audit now samples with random weights. Without them the audit would have missed both: no trained model used those operations. So the audit samples every architecture the evaluator accepts, not only the ones that are trained. The rule was then checked again from scratch under a new route id (`token-convex-2026-10-19b`): its tests, and a full audit of 1,960 leaves over seven model folders (869 certified, 11,504 inputs rechecked with the single rule), with no violation. The second review (about 25,000 fuzzed leaves over eleven architectures) found no counterexample, and its regression sequences, audited in the box, held. Verdict SOUND; adopted on 19 October 2026 (`rules/token_convex/status.json`, `AUDIT.json`, `REVIEW.md`). The review's remaining points were not about soundness: the reason for one invariant in SOUNDNESS.md (it is in REVIEW.md, and goes into the argument at the rule's next pass through the route, since any edit to its files needs one), and a crash in the interval arithmetic for products beyond 2^63, fixed in the core.

## The second rule: token_convex version 2, and what three reviews found

On 19 October 2026 `token_convex` went through the route three more times, to add leaves where the query varies: Gross et al.'s sub-cubic idea (bound the attention for every query at once) in a form that does not know the model, with the exact score table per pair of tokens in place of their low-rank approximation (`rules/token_convex/PROPOSAL.md`, from the section on version 2; `SOUNDNESS.md`, sections 6 to 9). Each version was implemented by hand outside `rules/`, so the adopted one stayed in use until the next passed, and each was reviewed by the same independent agent, which had not seen the implementation being written.

| Route id | Version | Audit (leaves, certified, inputs rechecked) | Review |
| --- | --- | --- | --- |
| `token-convex-2-2026-10-19` | 2: leaves where the query varies | 1,966; 923; 25,969 | SOUND |
| `token-convex-2.1-2026-10-19` | 2.1: a second, per-input pass with one varying position | 2,302; 1,028; 44,143 | SOUND |
| `token-convex-2.2-2026-10-19` | 2.2: claims corrected, a repeated pass skipped | 2,323; 992; 44,063 | SOUND |

No review found a soundness problem. What they did find:

- **Version 2 claimed more than it did.** It used the softmax's structure in leaves with one varying position too, and there, on the synthetic folders `tests/stub_general` and `tests/stub_twopaths`, it failed to certify leaves that token_interval and version 1 certify (for example a bound of -137,868 where every input's margin is at least +9,887). Its description said it did everything token_interval does, and one of its tests asserted an exactness that held only on the trained network it ran on. Version 2.1 evaluates such a leaf again, every value per input as version 1 does, when the new levels leave it uncertified, and keeps the larger bound; the test now runs on random networks too.
- **Version 2.1's corrected claims were still too broad.** With one varying position the rule is as exact as token_interval, and token_interval itself boxes values where an operation has no per-input rule (xorformer-majority's model concatenates values). The core's own description of token_interval made the same claim and is corrected too. A group's bound is rounded at 2^-64 of its rows' unit, which a constructed network with a margin of 7e-26 exposes. And when the first pass built no softmax structure, the second pass repeated it at the same cost. Version 2.2 states both claims as they are and skips the repeat.
- **Paths no model folder reached.** A query made of two terms, a negative query weight, several softmaxes in one decision, and scores or query values used outside the attention: no trained model does these, so neither the tests nor the audit exercised the code. `tests/stub_query` now does, with random weights in every audit. Extending it exposed a crash in the core: token_interval's `concretize` failed on scalar rows (a sum of scores over the positions, then an operation without a token rule). It is fixed, with a regression test that fails on the old code.
- **Regression sequences.** The audit's audited cases from the three reviews are in `tests/rule_route/regressions.json`, so every later audit runs them. The review's advice for synthetic folders: carry explicit weights, since a changed folder silently changes what `random:<seed>:<scale>` draws.

The last review's remaining points are wording in the rule's description (the list of boxing operations is not exhaustive, a stopped query search can still be certified by the second pass at the rounding edge, "kept" for "made", a one-token position costs 2 at level 0). They wait for the rule's next pass, since any edit to its files needs one. The replaced versions are kept as `rules/.replaced-token_convex-<time>/`, which the checker neither loads nor hashes. What version 2 buys is in `results/query-gap-2026-10-19/README.md`.
