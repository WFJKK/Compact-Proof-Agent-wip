# The scaling proofs after a run (23 November 2026)

Asked for by the user on 23 November 2026, after the first linear max-of-4 run: "I think we do want proofs for
all three parameters... an option that it tries that for a certain budget and a certain time... after I looked
at the compact proofs. It should start with V and then the two others." The parameters are those the paper's
Table 1 states its proofs' costs in: the number of token values, the number of positions, the model's width.

## What was there

The scaling question (`open_lane.scaling: true`, since October) is one session at the end of a run, about the
locked proof only, with the sizes left to the agent. It was off in the recent runs to keep them within a day.

## What was built

- `python3 -m core.loop scale --run <run folder>`: started by a person on a finished run. Refuses a run whose
  proof rounds or stages are not done, and a model folder that does not name its sizes.
- One session per size, in order: V, then n, then d (`open_lane.scaling_steps`, each with its own minutes and
  dollar cap; by default 60 minutes and $20 for V, 30 minutes and $10 each for n and d). V gets the most:
  it is where a checker that fixes the vocabulary has to be rewritten to read it and proved equal to the
  submitted one at this network's value; the later steps start from that work.
- The model folder names its sizes (`open_lane.scaling_sizes`): `d_vocab`, `n_ctx`, `d_model`, and for the
  attention models `d_model` and `d_head` together.
- Every scored proof on the run's frontier is in scope, not only the locked one. The locked proof is in the
  workspace as in the scaling question; the others' modules beside it where they do not clash; every proof's
  certificate and plan in `py/handed_in_proofs.json`.
- Per size, the session hands in the formula of each proof's length, brute force's, the verdict, and what the
  proof certifies at other values (shown, assumed or unknown); in Lean, as lemmas: the bill at this size for
  every weight, the bill as an exact formula in the size, its leading order against brute force's. A cost
  that depends on something other than the sizes (how many pieces a plan makes) gets that as a parameter of
  the formula, with its value on this network: the user's point that a genuine proof need not change the
  power of a size.
- For each accepted lemma, Lean is asked which proofs' checkers the compiled modules hold, term for term:
  the locked one in the session (`lock.same_checker`, as in the scaling question), the others after it. The
  report prints every statement in full beside that answer; a statement is still the agent's own, so a person
  reads it.
- `stages.json` keeps the steps under `scaling_proofs` (their rounds after the run's last, the proofs, each
  step's lemmas and answer). Running the command again goes on with the steps not done; `--only V` runs the
  next step alone.
- The round log names an accepted lemma's theorem (it printed an empty `lemma:` before).
- With a later pipeline (24 November). The first use, on attn-max4-ptl-1 after `git pull`, stopped at once:
  the command opened the run as a resume does, and a resume refuses a run whose checker code or model folder
  changed since it started, which the pull that brought the steps had done (the folders gained
  `open_lane.scaling_sizes`). The steps add lemmas and never a score, so they now open such a run when the
  Lean checker is the run's and the model folder differs only in its `open_lane` block, read back with git
  from the run's pipeline commit and checked against the hash the run recorded. Each step records the
  pipeline it ran with and what changed; its records carry the pipeline's hashes as they are now.

## The links, and further sessions (24 November 2026)

The first scaling proofs ran on 24 November on attn-max4-ptl-1 and linear-max4-ptl-1 (`claude/scaling-results`
in the project notes). What they showed:

- Most formulas stayed unproved. The prompt asked for formulas "with as much of it as you can prove", in
  order of strength, and the sessions handed in a formula worked out by hand and checked in Python, with a
  lemma at the network's own size. On the attention run only that was in Lean: the checker has 64, 4 and 32
  written into its loops. On the linear run the width was proved for every value (the checker reads it from
  the weights), the number of positions through a copy of the checker with it as a parameter, proved equal
  to the submitted one by `rfl`; and the number of token values not at all, although the lemmas quantify over
  it: each carries the hypothesis `graph.values = V`, the checker's own test against the network's graph,
  which fixes it at 64. The agent's summary, and the first reading of it here, took those lemmas for every V.
- Lemmas that compare two formulas of the agent's own (`billN n < bruteN n`) were counted as "shown by Lean
  to hold a submitted proof's checker", because the modules they were compiled with hold it.
- Sessions stopped early: after 8 and 6 of 30 minutes, 19 of 60. Two wrote that the clock had stopped them;
  it had not. The prompt gave the session's seconds and the seconds kept for the answer, and the tools gave
  the seconds left before those: read together as if the reserve were still to subtract.
- A third of a session's compiles went on building the locked proof's modules one at a time, and a session
  looked in vain for the Python model the one before it had written (`py/billmodel.py`).

What was built:

- The result for a size is four links, each a theorem or missing: `general` (a checker with the size as a
  parameter that is the submitted one at the network's value), `cost` (its exact bill at every value),
  `formula` (that bill in closed form or between bounds), `brute` (brute force's cost and the comparison).
  The prompts say what is not a result: a formula worked out by hand, a Python model, a Lean function
  evaluated at a few sizes; and what makes a checker not general, with the hypothesis that fixes a size.
- A first session, `general`, for the first two links and all three sizes at once (their shared work), then
  V, n and d for the other two (`open_lane_scaling_general_v1`, `open_lane_scaling_step_v2`). By default 90
  minutes and $30, then 45 minutes and $15 each. Only the cost of the general checker is asked, never its
  soundness at other sizes: the service's network module holds one graph and one task.
- `--again [steps]` adds a further session for each named step to a run whose steps are done, with
  `--minutes` and `--usd`; the two runs of 23 November go on this way. Earlier results are never rewritten;
  a further session is told which earlier sessions were asked for formulas and not for the links.
- A session starts with everything compiled (`Session._prebuild`, not charged, before its clock), with the
  modules the earlier sessions left unsubmitted and with their Python files. Its prompt gives its time as
  minutes of tool time, then minutes for the answer, and says what `remaining.seconds` is.
- The answer's THEOREMS section names, per size and link, the theorem that holds it; the pipeline records
  whether that theorem is the named theorem of an accepted submission (the service checks the axioms of
  that theorem alone) and shows the links per size in the status and the report. Per lemma it records which
  proofs' checkers the statement names; the status counts lemmas "with a submitted proof's checker in its
  statement" (named, and found by Lean in its modules), also for the earlier sessions, read from their
  statements.

What stays as it was: the statement is the agent's own and the service checks no theorem shape, so that a
named theorem says what its link asks is for a person to read. A full result is about the method's cost at
other sizes: it says nothing of the general checker's soundness there, nor of what it would certify on a
network trained at another size.

## Checked

- Tests (`tests/test_scaling_steps.py`): the general session and the three sizes in order, a workspace compiled
  beforehand and not charged, drafts and Python files carried, the links read and tabulated, the statement's
  checker names, `--again` (with its own time, after steps that are done, the first sessions named as such);
  a run opened by a later pipeline, and the changes that refuse it; the order, each step's time in its prompt, the proofs and their files
  in the workspace, a lemma checked against both proofs' checkers, what carries over, `--only`, the refusals,
  the report and the status; each model folder's sizes.
- A rehearsal on the cloud machine with the real Lean service: a finished run on max4-v64-s0 (the dry-start
  probe as its proof), then the three steps, each submitting a lemma about the locked checker; Lean found the
  locked checker in each.
- The two runs of 23 November (attn-max4-ptl-1 from ded98e7, linear-max4-ptl-1 from 451f296): their model
  folders read back from git hash to what each run recorded, and differ from today's only in `open_lane`.

## Not done

- No fixed theorem shapes: the service does not check that a lemma states a bill formula of the checker; the
  report shows the statement and a person reads it.
- The steps run in one fixed order and do not change the plan of an earlier step; a step that finds nothing
  leaves the next one to start from the proofs alone.
