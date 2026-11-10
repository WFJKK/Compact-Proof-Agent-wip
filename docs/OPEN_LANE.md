# The open lane

The open lane lets the agent prove things about a network in Lean instead of writing a split-tree proof
file: any argument the kernel accepts counts, and a proof written in the counted language gets a length in
the same units as a proof file (cost-v4; the prices of operations are cost-v3's, and cost-v4 only stopped
charging a proof file's plan, so that the same proof costs the same in both lanes). The Lean side (the acceptance service, the counted language, the
scoring policy) lives in the Lean project CompactCheck
(https://github.com/WFJKK/Compact-Proof-Checker, `docs/OPEN_LANE.md` and `docs/COUNTED.md`
there). This document is the pipeline side: how a run uses it.

## What changes in a run

With `open_lane.enabled: true` in the run config, an agent round is a session with tools instead of one
response:

- The prompt (`core/agent/prompts/open_lane_v1.md`, `open_lane_v2.md` or `open_lane_v3.md`, built by
  `core/open_lane/prompt.py`) gives the specification (Spec.lean), the protected module's interface, the
  counted language with its prices (Counted.lean, CountedOps.lean), a scored brute-force proof as the worked
  example (`open_lane.example`), the tools and their budgets, the scoreboard, the receipts so far, the sources
  of the agent's accepted submissions from earlier rounds, and its latest notes. No rule descriptions. Template
  v2 adds further Lean sources (`open_lane.extra_sources`) and says how to split an instance proof; a run of
  facts in the example that differ only in their numbers is shortened to its first two and its last. Template
  v3 (the pilot configs' since 27 October 2026) lists the carried modules of the workspace (below) instead of
  pasting the accepted sources, and tells the agent that the instance is one `decide +kernel` over the whole
  run with `set_option maxRecDepth 1000000 in` before it: Lean's default recursion limit stops the kernel's
  evaluation of a bill after a few thousand charges, and the server pilot of 26 October built a model of its
  checker and run lemmas to get past it (the Lean project's docs/COUNTED.md, "The instance in one theorem").
- The tools (`core/open_lane/session.py`): `lean_check` saves a module in the session's workspace and
  compiles it through the service against the protected module of a network and claim;
  `run_python` runs code in the recipe sandbox with the network's weights; `search_library` searches the
  Lean project's sources and docs and `read_file` reads a stretch of one of them, or of the examples the
  prompt shows (the two brute-force examples and the run's worked example; never another example: the rest
  are earlier proofs of the pilots' own networks, and reading one would be copying, not research);
  `submit_candidate` hands
  modules to the acceptance service and returns the receipt. Each call is logged append-only (`tools.jsonl`); the budgets (`compile_calls`,
  `python_calls`, `submissions`) persist in `session.json`, so a session that is started again continues
  them.
- Carried modules (since 27 October 2026): a round's session starts with the modules of every submission
  the service accepted in the run's earlier rounds (the latest accepted version of each module path) in its
  workspace, compiled there before the agent begins, in import order, through the same `accept.py compile` as
  `lean_check` and without charge to the budgets; `session.json` (`carried`) and the prompt (template
  `open_lane_v3`) say what was carried and whether it compiled. `read_file` reads the workspace's modules
  (`Candidate/<Name>.lean`), and `submit_candidate` adds the workspace modules that the listed ones import,
  so a carried module is imported, never retyped. Nothing about acceptance changes: the service compiles and
  checks every module of a submission afresh. Before this, each round started with an empty workspace and the
  prompt showed the latest accepted sources cut to 12,000 characters, and the server pilot of 26 October spent
  rounds 3 and 4 rebuilding modules it had already had accepted (claude/server-pilots-2026-10-26.md).
- The records (`core/open_lane/records.py`) come from the receipts: `ok` when verified and scored (count
  and length; it enters the frontier like a proof file's record), `verified` when accepted without a
  length, else the receipt's status with its reason. An attempt without a submission gets `no_submission`.
  A receipt certifying more inputs than the network gets right halts the run, as the Python checker's
  invariant does.
- Round 0 still replays the baselines named in the config as proof files (`rule_set` must be written in
  the config: the pilot uses `[single, skip]`); the fixed rules lane's one-response loop is the baseline condition,
  run separately (`config/open-lane-baseline-tiny.yaml`).
- The stall trigger: after `stall_rounds` agent rounds without an accepted submission, the prompt asks
  for a change of approach rather than a refinement. Patience stops an open-lane run after `patience`
  agent rounds without a new accepted artifact, not after rounds without a metric gain; an artifact is
  new by its claim (`core.loop.claim_identity`: a scored proof's network, count and length; a verified
  proof's network and count, when no proof of that count exists; a lemma's network and statement), never
  by its files or its theorem's name, so a resubmission with a comment changed is not progress and a
  second theorem from an unchanged file is. The hard budgets (rounds, the session's calls and clock) are
  unchanged.
- Held-out evaluation (`core.final`) refuses an open-lane run: its proofs are Lean modules for the
  development networks, and transferring a method to held-out networks needs the frozen-method route of
  the next ticket.

Layout of an open-lane attempt:

    round_003/attempt_0/
        open_lane/session.json, tools.jsonl, workspace/, submissions/000/{manifest.json, Candidate/, receipt.json}
        mcp.json                 the CLI's MCP configuration (claude_code backend)
        response.md              the session's final text (CLAIM, WHY IT HELPS, NOTES)
        response_meta.json       tokens, turns, tools used, submissions
        results.json             the records

## The service is the Lean project's

`scripts/accept.py` of the Lean project owns target binding, proof validation, the scoring policy and the
receipts; the pipeline is its client. `lean_check` is `accept.py compile` (a module compiled in the service's
box against the protected module, for development; never evidence), `submit_candidate` is `accept.py submit`.
`lean-checker.lock` at the repository root pins the Lean commit this pipeline version expects; `preflight`
refuses a run against a Lean project at another commit or with uncommitted changes. A run records the
service's identity when it starts (`accept.py identity`: the commit, the toolchain, trusted-source and
policy digests every receipt carries, the acceptcheck binary; `lean_checker` in `versions.json`), and
resuming checks the current service against it and refuses if anything differs, or if the lock has moved
since: a run keeps the checker it started with, and a new checker is a new run. Every receipt carries the
same five digests; an accepted receipt must have all of them, equal to the recorded identity, before it
becomes a record, and a receipt rejected early is checked on the digests it has; a mismatch or a missing
digest halts the run (`core.open_lane.records.check_receipt_identity`).

A submission of kind `auxiliary` is a lemma with any statement: accepted with no count and no score,
recorded with status `lemma`, and shown to the agent in later rounds with its statement.

## Scoring and the next evaluation

The primary objective is Q_exact (`core.scoring.q_exact`): the log-area of the verified frontier over
[max(E, B/1000), B], the expected certified accuracy at a budget drawn log-uniformly from that range,
computed from the proofs' actual lengths; `metric: Q_exact` in a run config. The frontier is the record and
cost of finishing the tie-breaker, computed with the single rule's exact charge per uncovered input (from
the run's brute-force baseline record) rather than an average. Q_grid stays available; it cannot see an
improvement between two of its budgets (pilot 2's full proof from 1,031 to 719). Q_exact is clean when the
evaluator chooses where proofs are requested; when the agent chooses its own points it inherits Q's
placement effect, which is why the next evaluation requests a frozen method's proofs on a fixed schedule
(docs/decisions/frozen-transfer.md).

Since 26 October the pilots are driven by Q_above (`core.scoring.q_above`, docs/SPEC.md section 5 and
docs/decisions/q-above.md): the frontier's log-area above the brute-force line, over the room above it.
Brute force on k inputs is a proof the agent can always write (k calls of the single rule at c each, plus E),
and Q_exact counted its area as score; the first attention pilot spent four of its first nine submissions on
such subsets, which scored 0.15 with no compression at all. Under Q_above they score 0, the receipts tell the
agent whether each proof is above the line, and a scored proof keeps the loop's patience alive only if it
raised Q_above (lemmas as before). `python -m core.rescore --run <run>` re-scores a finished run.

## The reference count

The zoo's `real_correct` comes from the float forward pass; the Lean specification counts over the reals
with the exact weights. `python -m core.check.exact_counts models/<name>` records the Python checker's own
brute-force count per network (`checked_correct`; `checked_semantics` exact for linear networks, enclosure
for attention ones) and reports any network where it differs from the float count: on every max2, tiny
max2 and attn-max2 network the two agree. The run halts on a count above the exact reference; a Lean count
above the float count alone is flagged in the record (`reference_warning`), since that count is an
approximation.

## Backends

- `fake`: `open_lane.fake_scripts` lists JSON scripts of tool calls (`core/open_lane/backends.py`),
  replayed in order against the real tools and service; everything else is as in a real run. The tests
  (`tests/test_open_lane.py`) run the scored brute-force example through it.
- `claude_code`: the Claude Code CLI headless, as in the fixed rules lane, with the tools attached as an MCP
  server over stdio (`core/open_lane/mcp_server.py`, started by the CLI with the command in `mcp.json`) and
  nothing else: no built-in tools, no files, no project settings, `--max-turns open_lane.max_turns`, the
  session's wall clock `open_lane.worker_seconds`. The CLI's environment has the API keys removed. The
  session's final text is the response; what it submitted stands even if the session runs out of time.
  Not exercised with a live CLI yet: the pilot is the first run (see below).

## Running the pilot

On the machine with the Claude Code login and the Lean project:

1. Build the Lean project's targets: `lake build CompactCheck.Soundness CompactCheck.CountedOps compactcheck
   acceptcheck` (a plain `lake build` also builds the tutorial module, which imports all of Mathlib).
2. Point `open_lane.lean_project` in `config/open-lane-pilot-tiny.yaml` at it; `preflight` checks for the
   built `acceptcheck`.
3. `python -m core.loop run --config config/open-lane-pilot-tiny.yaml`, in tmux. The run resumes with
   `python -m core.loop resume --run <runs_dir>/open-lane-pilot-tiny`.
4. Then `config/open-lane-pilot-max2-v64.yaml` (one network), and the baseline condition.

The tiny attention pilots (`config/open-lane-pilot-attn-{max2,min2,max4,min4}-tiny.yaml`, models in
`tests/attn_*_tiny`) need the Lean project at the commit of `lean-checker.lock` (the general single rule,
`I.gsingle`) and one more target, `lake build CompactCheck.CountedGeneralSound`. Each comes in two
experimental conditions that differ only in `open_lane.knowledge`: the configs above are the
minimal-knowledge condition (the base counted language), and the `-maximum` configs add the fixed rules lane's
rules for groups of inputs on attention networks as operations (the interval rule `I.ginterval` and the
token_interval rule `I.gtokenIntervals`, a list of boxes per call). A maximum run's worked example is a
demonstration of `gtokenIntervals` on three boxes of the other task's network of the same architecture
(`examples/open_lane/attn_*_tiny_tokens_demo` in the Lean project): a complete proof of the run's own
network would be a proof handed over, and under Q_above resubmitting it would score.
The service checks a checker against the condition's allowlist, records the condition in every receipt and
in its policy digest, and a run checks every receipt against the identity it recorded, so one frontier never
mixes the conditions; the prompt tells the agent which condition it is in. Their worked example is
the attention brute force, whose instance is proved from one kernel-decided fact per input: one
`decide +kernel` over all forward passes does not fit in memory (the Lean project's docs/COUNTED.md,
"Attention networks"). A fact takes about 1.8 s on the two-position networks and 2.3 s on the
four-position ones, so a checker that falls back to the single rule on all 256 inputs of max4 takes about
10 minutes to compile; the four-position configs give the session three hours.

Next to the attention max4 and min4 pilots, linear ones on the same task and size
(`config/open-lane-pilot-{max4,min4}-tiny.yaml`, models `tests/max4_tiny` and `tests/min4_tiny`: the max2
model's architecture at 4 positions, 4 tokens, width 4, 256 inputs, both seeds at full accuracy; a single
leaf costs 51, E is 48). Their worked example is the linear scored brute force. All the tiny pilots run up
to 7 rounds.

The receipts record the isolation the service had: Landlock on Linux, `process (weak)` on a Mac, where
Docker is not used by the service. The pilot's gate (the ticket): one agent-produced open-lane candidate
accepted, or the archive recording transparently why none was.

For runs that must survive a laptop going offline, docs/SERVER.md sets up a small Linux server.

The fixed rules lane's counterpart of these pilots, for the comparison: `config/fixed-rules-pilot-attn-*-tiny.yaml`.
The agent writes Python recipes that produce proof files and the checker's rules do the mathematics, with
the rules the Lean checker has (`single`, `interval`, `token_interval`, `skip`; not `token_convex`), scored
by Q_above like the open-lane pilots. Every proof that enters the frontier is checked by the Lean checker
during the run (`lean_spot_check`; the tiny model folders' `lean_check` runs `scripts/lean_check_proof.py`
against the Lean project at `COMPACT_PROOF_LEAN` or the pilots' default path, and a disagreement halts the
run), and `scripts/check_run.py` of the Lean project checks every proof afterwards. The counts are
Lean-verified; the lengths are the Python checker's accounting (cost-v4), which the Lean operations
reproduce leaf by leaf (`scripts/test_gtokens_cost.py` there).

## What a scored proof costs

Length = the bill of the checker on the protected weights + E (one per weight entry) + one per certificate
number. The counted operations charge what a proof file's leaf pays for the same work (`single`: one exact
forward pass; `interval`: the interval rule on a box; `gsingle`: one forward pass of a network with
attention, at the same prices for its operations). There is no `tree` charge: a scored proof's structure
is its program, bounded by the service's description-size budget instead. Since cost-v4 (9 November 2026)
a proof file's plan is free too (its tree, rules and flags; only the numbers it supplies, in its
approximations, are read at 1 each), so the same proof costs the same in both lanes: brute force on the
tiny network is 4,112 in both. Under cost-v3 the proof file paid 4,323 for it (73 tree nodes and 138
numbers and strings read).
