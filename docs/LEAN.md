# The Lean checker: idea and work plan

This is the plan for turning the Python checker in `core/check/` into a verified Lean checker. Nothing in it is built yet. It is written so that someone can start from it in a fresh session with only this repository.

## 1. The idea

A compact proof (Gross et al.) is not a proof about one network. It is a proof template with the weights as a parameter: "for any weights W, if these checks on W pass, then the accuracy is at least q". In this repository the template is the proof-file language (`split-tree-v1`: a split tree with `single`, `interval` and `skip` leaves, and the global rules `contract`, `symmetry` and `approximate`), and the Python checker is the program that runs the checks.

"Lean formalise compact proofs" therefore means two things, and they are one job seen at two levels:

1. **Formalise the template.** Define the network class, the proof language and certified accuracy in Lean, implement the checker as Lean functions, and prove the soundness theorem: if the Lean checker accepts (network, proof file) with count n, then the network answers at least n inputs correctly. One theorem per rule, one induction over the split tree, proved once by a person.
2. **Get a Lean proof per network for free.** For a specific trained network, a proof file the agent produced plus one run of the verified checker is a Lean proof that this network has accuracy at least n / N. Nobody writes Lean per network; the agent writes data, Lean verifies it. The pipeline already has the hooks for exactly this (section 3).

What this buys:

- The bug class "certified bound below the true value" (which the original Python implementation of the paper had, per Joshua's mentor) becomes impossible by construction: with that bug, the theorem could not be proved.
- An untrusted agent can hill-climb freely, because only proof files the verified checker accepts count, and accepted ones are theorems.
- Every result in the reports flips from "Python-checked" to "Lean-backed" with no other change to the loop.

The Python checker stays. It is what the loop runs every round; Lean rechecks frontier entries during a run and every reported proof at the end.

## 2. What exists

**The Python checker**, about 1,300 lines, all in `core/check/`:

| File | Role |
| --- | --- |
| `proof.py` | the proof schema, the split-tree walk and partition check, the symmetry orbit count |
| `trace.py` | the network graph (ops `input`, `linear`, `sum`, `add`), traced from `model.py` with torch.fx |
| `evaluate.py` | exact evaluation: singles (concrete inputs), intervals (boxes), the contract rule |
| `approx.py` | the approximate rule, forms `dense`, `low_rank`, `row_segments` |
| `arith.py` | exact dyadic arithmetic (`Exact`: integer array times a power of two), proof-number parsing |
| `checker.py` | `check_proof`: validation, global rules, leaves, counting, the result record |
| `cost.py` | the length (operation count); not needed for soundness |

**The specification of the rules** is `docs/RULES.md`: one informal soundness argument per rule. The Lean checker should be written against that document, not against the Python code, so the two are independent implementations of one spec. `core/check/rules.py` has the short rule descriptions shown to the agent.

**The proof file format** (`core/check/proof.py` docstring):

```
{"schema": "split-tree-v1", "network": "<id>",
 "symmetry": false, "contract": [...], "approximate": [...],
 "tree": <node>}
<node> = {"split": {"position": p, "cuts": [c1, ..., ck]}, "children": [...]}
       | {"leaf": "single"} | {"leaf": "skip"}
       | {"leaf": "interval"} | {"leaf": "interval", "approx": "<name>"}
```

Numbers in proof files are dyadic rationals as strings or JSON numbers (integers, decimals, fractions with power-of-two denominators; no exponent notation; numerator at most 160 bits, exponent at most 1100). See `arith.py`.

**The network class.** Inputs are one-hot tokens of shape (positions, values). The graph has one input node, `linear` nodes (a torch `nn.Linear`, weight (out, in), optional bias), `sum` nodes over one dimension, and `add` nodes. Weights are float32, so every weight is a dyadic rational and converts exactly. For max2 (`models/max2/model.py`):

```
logits = unembedding(linear(embedding(sum over positions of one-hot)))
```

three bias-free linear maps, sizes v64 (d_vocab 64, d_model 8) and v128 (128, 16), two positions, label = larger token. Weights live in `models/max2/zoo/<id>.npz` with keys `embedding.weight`, `linear.weight`, `unembedding.weight`.

**The hooks** that will call the Lean checker:

- `models/<name>/config.yaml` may set `lean_check`: a command as a list of strings in which `{proof}` is a JSON proof file and `{weights}` the network's `.npz`. It runs in `models/<name>/lean/`. Its last line of stdout must be a JSON object `{"certified": n}`.
- `core/lean.py` runs it as a spot check when a recipe enters the frontier (config `lean_spot_check: true`), appends to the run's `lean.jsonl`, and halts the run if Lean and Python disagree.
- `core/final.py` rechecks every held-out proof with it, and the report labels results Lean-backed only for rules that have Lean proofs.

**Test material.** `models/max2/baselines/` holds three known strategies (brute force, symmetry, contract plus interval). `tests/` has the checker tests, including comparisons with brute force for symmetry counting and the approximate forms. Every run archive holds proof files with the Python checker's certified count; those are golden values for the Lean checker.

## 3. What the Lean checker must do

**Interface.** A compiled Lean 4 program that reads the proof file, the network graph and the weights, runs the checks, and prints `{"certified": n}`. It must handle a v128 brute-force proof (16,384 single leaves) and the frontier proofs (a few thousand leaves) in seconds to a minute; this needs compiled Lean, not kernel reduction.

**Inputs.** The proof JSON directly (Lean 4 core has `Lean.Json`). The weights and graph need a format Lean can read. Recommended: a trusted Python script (`models/max2/lean/check.py`, part of the `lean_check` command) converts the `.npz` into a JSON file of exact dyadic integers plus one exponent per matrix (`Exact.from_float` in `arith.py` does this conversion) together with the traced graph (`Graph.describe()` in `trace.py`), and then runs the Lean binary. That script is trusted code of about thirty lines; a reviewer checks by hand that the max2 graph it emits matches `model.py`.

**Definitions (Lean).**

- Dyadic numbers or plain `Rat`; vectors and matrices over them. Mathlib's `Matrix` is fine for statements; computation should use arrays.
- `Graph`: the node list with ops `input`, `linear` (weight, optional bias), `sum dim`, `add`. Semantics `eval : Graph → Weights → Input → Vector` as a mathematical function (the "true" network).
- `Input`: a list of tokens, one per position; `N` = number of inputs = product of the vocabulary sizes.
- The task interface: `label : Input → Fin outputs`, `constantLabel : Box → Option label`, `labelSymmetric : Prop`. For max2 these are `max`, "largest lower end equals largest upper end", and true.
- `Proof`: the parsed proof file. `Box`: one inclusive range per position.
- `correct net input := ∀ j ≠ label input, logit (label input) > logit j` and `accuracy := #{correct} / N`.

**Functions (Lean, executable).**

1. `walk`: validate the tree, produce the list of leaves with their boxes (`proof.py: walk`).
2. `evalSingle`: exact forward pass on one input; the leaf is certified if the label's logit is strictly largest (`evaluate.py: run_singles`).
3. `evalInterval`: bound the network over a box: one-hot sets stay symbolic until the first linear map (per coordinate min and max over the allowed columns), later linear maps act on boxes (centre, radius), and the output map gives a lower bound on every margin (`evaluate.py: run_interval`, and the exact per-position case after a full contraction).
4. `contract`: replace a consecutive single-use chain of linear maps by their product and pushed-through bias (`evaluate.py: contract`).
5. `symmetryOk`: the input is used only through a sum over positions (`trace.py: summed_over_positions_first`), and the task declares `labelSymmetric`.
6. `orbitCount`: the number of inputs a box certifies under symmetry, counting sorted inputs weighted by their distinct reorderings (`proof.py: sorted_orbit_count`).
7. `approxEps` and `rowMinDiffs` for the three forms (`approx.py`).
8. `check : Graph → Weights → Proof → Option Nat`: everything above, returning the certified count or `none` for a rejected proof.

The length (cost model) is not needed and should stay in Python.

**Theorems (Lean).**

- `walk_partition`: the leaves' boxes partition the input space. By induction over the tree, from the cut conditions in `docs/RULES.md`, "Split tree".
- `single_sound`: `evalSingle` returns true only if `correct net input`. Needs `eval` of the executable arithmetic to agree with the mathematical `eval`.
- `interval_sound`: if `evalInterval box label` is true then every input in the box is correct. Interval arithmetic through linear maps, and the exact one-hot case.
- `contract_sound`: the contracted graph computes the same function. Associativity of matrix multiplication plus the consecutiveness check.
- `symmetry_sound`: if `symmetryOk` then `correct net x ↔ correct net (sort x)`, and `orbitCount` equals the number of inputs whose sorted version lies in the box. Then no input is counted twice across leaves (uses `walk_partition`).
- `approx_sound`: with `eps = max |W - P|`, the bound `min (P[l,t] - P[j,t]) - 2 eps` is below `min (W[l,t] - W[j,t])`, for each of the three forms.
- `check_sound` (the one that matters):

```
check g w p = some n  →  n ≤ #{x | correct (eval g w) x}
```

A per-network corollary is then mechanical: for a concrete weights file and proof file, `n ≤ #correct` by `check_sound` applied to `by native_decide` (or `decide` on the compiled checker), so each frontier point becomes a theorem about that network.

**What stays outside the theorem**, and is acceptable:

- The JSON parser: a parse error can only reject, never accept wrongly.
- The float32 to dyadic conversion and the graph export in the trusted Python script, plus the human check that the exported graph is the architecture in `model.py`.
- `native_decide` trusts the Lean compiler. If that is unwanted, the kernel can check small networks by `decide`, slowly.

## 4. Order of work

Each step has a "done when". Steps 1 to 4 give a Lean checker that agrees with Python on everything (useful on its own as an independent implementation); steps 5 to 8 give the theorems.

1. **Definitions and the walker.** Done when `walk` accepts and rejects the same trees as the Python walker on the tests in `tests/`, and `walk_partition` is proved.
2. **Single leaves and the exporter.** The trusted Python exporter; `evalSingle`; `check` restricted to `single` and `skip`. Done when the brute-force proof for every development network gives the certified count in the zoo manifest (real accuracy times N).
3. **Contract and symmetry.** Done when the two other baselines in `models/max2/baselines/` give the Python counts on every development network.
4. **Interval and approximate.** Done when every proof file in an existing run archive gives the Python count (`core/lean.py` can run this as a batch: point `lean_check` at the binary and run `python -m core.final`).
5. **`single_sound` and `contract_sound`.** Exact linear algebra only.
6. **`symmetry_sound`.** The orbit-counting argument; compare with the Python test that enumerates 1, 2 and 3 positions.
7. **`interval_sound`.** Interval arithmetic through linear maps and the one-hot case.
8. **`approx_sound`**, three forms, and then `check_sound`.
9. **Wire in.** Set `lean_check` in `models/max2/config.yaml`, turn on `lean_spot_check`, run the fake round-0 config and one real run, and update `docs/RULES.md` and the report labels. Done when `core.final` reports every max2 result as Lean-backed.

A rough size: steps 1 to 4 are days for someone fluent in Lean 4; steps 5 to 8 are weeks, with `interval` and `approximate` taking most of it. If time is short, a checker that verifies `single`, `contract` and `symmetry` and rejects proofs that use `approximate` is already enough for the symmetry and contraction baselines to be Lean-backed; the report label is per rule.

## 5. Decisions to make early

- **Number representation.** Dyadic (integer, exponent) as in Python, or `Rat`. Dyadic keeps all arithmetic in integers and matches the weights; `Rat` is simpler to prove about. Either is fine; the proof-number limits (160 bits, exponent 1100) should be kept so a proof file cannot make the Lean checker slow.
- **Generic graph or max2 only.** The spec wants the checker generic over the four ops, which is what the Python checker is. A first version may fix the max2 shape (three linear maps around a sum) if that gets to a sound checker faster; the theorems then need to be generalised later.
- **Executable versus mathematical definitions.** Keep two: the fast array-based functions and the clean mathematical `eval`, with lemmas connecting them. Proving directly about the fast code is the usual trap.
- **Where the code lives.** `models/max2/lean/` per the spec's layout, with a `lakefile` and the exporter; the generic parts could later move to `core/lean/` when a second model exists.

## 6. Why the mentor wants this

From the Iliad conversation: the Python implementation behind the paper had bugs, including one where a certified upper bound on the loss dropped below the true population loss; a hill-climbing loop over proofs is only as trustworthy as its checker, since an agent can "reward hack by faking stuff"; and the stated end goal is that for a given set of weights the agent produces a certificate that Lean turns into a concrete number on the length-versus-accuracy frontier. The plan above delivers that goal with the agent writing data rather than Lean.
