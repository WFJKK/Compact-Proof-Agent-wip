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

- The prompt (`core/agent/prompts/open_lane_v1.md` to `open_lane_v6.md`, built by
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
  Template v5 (10 November 2026) is for a run on one network scored on cost of finishing: the
  goal says what follows the rounds (the seed check and the scaling question, below) and what that asks of a
  proof, the score comes before the rules, the rules of scoring are lists, there is advice on how to work
  (the checker's modules apart from the instance's), and the answer's WHY IT HELPS asks for the mechanism,
  the checker step that relies on it and what would make the checker certify less on another network.
  Template v6 (11 November 2026, the pilot's) is v5 with the work in Python first: the agent formalises a
  checker when it has a clear reason to expect it to be valuable (a better score, a new mechanism, a cost that
  grows more slowly with the sizes; when is its to decide), runs it on the protected weights with `#eval`
  before proving it, for a count and a bill the prompt calls provisional (the count is what the checker
  claims, true only by its soundness proof; the bill is the compiled code's, which the kernel has not checked;
  the service runs the checker itself), and submits the central lemma of a soundness proof early, as a lemma,
  so that it is carried. It tells of edits, the clock and the drafts (below). v5 is kept.
  Template v4 is v5's counterpart for a run over several networks (parked). Under `metric: cost_of_finishing`
  the scoreboard, the receipts and the aim show that one score and the cheapest way to finish; under the
  other metrics they are what they were. Neither template says anything about an architecture: that comes
  from the model folder (`open_lane.notes`, below).
- The tools (`core/open_lane/session.py`): `lean_check` saves a module in the session's workspace and
  compiles it through the service against the protected module of a network and claim (its full source, or
  since 11 November 2026 `edits` to the module saved at that path: each replaces an `old` text that must
  occur exactly once, in order, and no edits compile the module as saved);
  `run_python` runs code in the recipe sandbox with the network's weights, in a folder that holds the
  model's code, the harness and the weights and nothing of the fixed rules (no `helpers.py`, which names
  them; the check before a run scans the folder's text files), and the agent's Python workspace `py/`
  (below); `search_library` searches the
  files of the Lean project that the run shows the agent and `read_file` reads a stretch of one of them
  (the run's surface, below: in the minimal-knowledge condition the specification, the semantics and the
  counted language, with the run's worked examples; no docs, none of the fixed rules' sources, never another
  example: the rest are earlier proofs of the pilots' own networks);
  `submit_candidate` hands
  modules to the acceptance service and returns the receipt. Each call is logged append-only (`tools.jsonl`;
  a lean_check's entry has the module's lines and hash as saved, and `run_python`'s code is kept whole in
  `python/<n>.py`); the budgets (`compile_calls`, `python_calls`, `submissions`) persist in `session.json`,
  so a session that is started again continues them. Every answer says what is left of them, and of the
  clock.
- The Python workspace (since 12 November 2026). Each `run_python` call starts in a fresh folder, but for
  `py/`: the session's workspace (`py/` in the session folder) is put there, importable (`import name` loads
  `py/name.py`), and what the code leaves there is the workspace afterwards, within
  `open_lane.python_workspace_mb` and `python_workspace_files` (50 MB and 200 files by default; unchanged
  files are kept first, then changed ones, smallest first). The pipeline reads only plain files with one
  name: no link is followed, a hard link is passed over, and names are letters, digits and `_ . -`. A
  call's answer says what was saved, removed or not kept, and why. `save_as` (`py/<name>.py`) keeps the
  call's code as a module before it runs. `read_file` reads the workspace's text files. A new session of a
  proof round starts with the workspace the latest earlier round's session ended with, listed in the
  prompt with each file's size and the round it was last saved in; the sessions after the proof rounds
  start with an empty one. Nothing in it is checked or counted. Before this, every call started from
  nothing, and what the agent computed in Python reached its next round only as words in its notes.
- The tools answer one call at a time, in the order the agent makes them, and the prompt says so (in round
  2 of the test run of 11 November the agent meant to compile and submit at once).
- The clock (since 11 November 2026). The backend starts it in the session before each run of the agent,
  for that run's limit (`open_lane.worker_seconds`), and its last `open_lane.notes_reserve_seconds` (600 by
  default) are kept for the agent's answer, whose NOTES the next round starts from. Every tool's answer says
  how many seconds are left before them (`remaining.seconds`). No call starts when none are left: the tools
  refuse, and say to answer. No call runs past them: a compile, a program or a submission still running then
  is stopped with every process it started (the box's runner and Lean included), and the agent gets a
  compile's answer saying so, or a receipt with status timeout. Lean's further questions after a compile or
  a submission wait for the session's end when the time is too short. The module is saved before a compile
  starts, and the program before it runs. Before this, a compile could take an hour while the session's own
  limit ran out (the first test run on the Mac, 11 November), and the session ended with no answer and so no
  notes.
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
- Drafts (since 11 November 2026): the agent's unfinished work goes on with it. A new session of a proof
  round also gets the modules that the workspace of the latest earlier round's session held when it ended and
  that are not the version a carried module has (`session.draft_modules`): at their own path, or set apart in
  `drafts/` (which `read_file` reads, as `drafts/Candidate/<Name>.lean`) when an accepted module holds the
  path. The prompt lists them apart from the carried modules as drafts, not accepted, with when each was last
  saved and whether it compiled then; they are never compiled before the agent begins, and nothing in them
  counts until a submission of them is accepted. A draft left as it was goes on to the next round the same way;
  one set apart goes no further once something else is saved at its path. The sessions after the proof rounds
  get none. A round whose session ended without the agent's answer leaves no notes: the next prompt says so
  and shows the latest notes there are.
- What the agent is shown (since 10 November 2026; docs/decisions/agent-told-nothing.md). The agent is told
  nothing about what works on a network, so what a run shows of the Lean project is a surface
  (`core/open_lane/surface.py`): per knowledge condition, a list of files in
  `core/open_lane/surface/<condition>/SURFACE.yaml`, some of them as excerpts kept next to it (every line of
  an excerpt is a line of the Lean project's file, in order, except its marked notes). The tools reach the
  surface and nothing else, the prompt pastes what they serve, and before a run starts (and when it
  resumes) `core.loop.check_surface` checks that the excerpts are parts of the files and that nothing shown
  matches an expression the surface forbids. The Lean library is one package, though, with everything in
  scope of what the agent compiles. So in the minimal condition a proof is counted only if none of its
  constants mentions a constant of the library that the surface does not show
  (`core/open_lane/offered.py`): Lean is asked where each constant is declared and what a submission's
  constants mention (`inspect_oleans.lean`, with the library the project built), the agent is told at the
  compile and with the receipt (`offered`), and the verdict is kept as `offered.json` next to the receipt.
  Not closed by this: the agent can still ask Lean about the library (`#print`), and on an unconfined
  machine its code can read files. The decision note says what a run on this version shows and what it
  does not.
- The records (`core/open_lane/records.py`) come from the receipts: `ok` when verified and scored (count
  and length; it enters the frontier like a proof file's record), `verified` when accepted without a
  length, else the receipt's status with its reason. An attempt without a submission gets `no_submission`.
  A scored proof that uses what its run does not offer of the Lean library is `verified`, with the reason:
  the service scored it, the run does not count it.
  A receipt certifying more inputs than the network gets right halts the run, as the Python checker's
  invariant does.
- Round 0 still replays the baselines named in the config as proof files (`rule_set` must be written in
  the config: the pilot uses `[single, skip]`); the fixed rules lane's one-response loop is the baseline condition,
  run separately (`config/open-lane-baseline-tiny.yaml`).
- The stall trigger: after `stall_rounds` agent rounds without an accepted submission, the prompt asks
  for a change of approach rather than a refinement. Patience stops an open-lane run after `patience`
  agent rounds without a new accepted artifact, not after rounds without a metric gain (under Q_above and
  cost of finishing a scored proof counts only if it raised the score, below); an artifact is
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
        open_lane/session.json, tools.jsonl, context.jsonl, workspace/, drafts/, py/, python/,
                 submissions/000/{manifest.json, Candidate/, receipt.json}
                                 (and lock.json in a session after the proof rounds: the lock as applied,
                                 and for the seed check whether Lean found the locked checker in the proof)
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

Since 10 November the pilot is driven by cost of finishing (docs/decisions/one-network-pilot.md): B over
the cheapest way to finish the network from the checked proofs (a proof's length plus brute force on every
correct input it leaves out, at the single rule's exact charge), never below 1. A run on several networks
takes the geometric mean (`core.scoring.run_cost_of_finishing`). There are no budgets to land under and no
points to place; brute force on any subset of the inputs is 1; a scored proof keeps the loop's patience
alive only if it raised the score. The agent is shown this score alone. Q, Q_grid, Q_exact and Q_above are
still computed for the reports.

## After the proof rounds

A pilot run is about one network and has two more sessions after its proof rounds
(`core/open_lane/stages.py`), each a round of the run, resumable like any round:

- The seed check (`open_lane.seed_check: {network: <id>}`). The checker of the run's best scored proof is
  locked and run, unchanged, on a second network: a development network of the same model and size
  setting, another seed. The agent writes that network's instance and nothing else. The lock is by module
  (`core/open_lane/lock.py`): the modules that declare the checker and the soundness theorem, with what
  they import, are locked; the instance must be declared outside them, in a module that imports them.
  Which module declares a constant and what a module imports is asked of Lean, never read off the source:
  a Lean program (`core/open_lane/inspect_oleans.lean`, run with the service's Lean) reads the `.olean`
  files the service compiled. In the session the locked modules cannot be saved over, they are written
  into the workspace again from the lock before every compile and submission (with the protected module's
  name replaced by the second network's, and nothing else), and the submission must name the locked
  checker and soundness theorem. When a scored proof is accepted, Lean is asked whether its checker is the
  locked one: the kernel terms of the checker and of everything of the candidate's it depends on, the
  soundness statement, and the graph and task they reach must be the lock's (`lock.verified` in the
  record, with the reason when not). The outcome is one of three: `certified` (a scored proof accepted
  with the locked checker, a claim of 0 included), `unverified` (accepted, but the checker is not shown to
  be the locked one: not a measurement) or `no_result` (the session did not complete the check: never
  zero coverage). If Lean cannot be asked, nothing is decided: the run halts and a resume asks again.
  During the proof rounds the receipts say of every scored proof whether it can be locked, and why not.
- The scaling question (`open_lane.scaling: true`). The agent states how the locked checker's cost grows
  with the sizes, against brute force's, and submits what it can prove of that as lemmas. The session
  takes lemmas only, and nothing in it is scored. For each accepted lemma Lean is asked the seed check's
  question, and the report says whether the checker named in its statement is the locked one.

`stages.json` in the run folder records when and why the proof rounds ended, which proof was locked (and
any better proof passed over because it could not be), each stage's round and what it found. Once it
exists the run makes no more proof rounds: the proof rounds end at the round limit or by patience, not
when a backend runs out or the model declines. The stages' records carry `stage` and never enter a
frontier or a score; the report has a section for them, with the cost of finishing on both networks side
by side.

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
  nothing else: no built-in tools, no files, no project settings, no memory, `--max-turns
  open_lane.max_turns`, the session's wall clock `open_lane.worker_seconds` (the clock above, started before
  each run of the CLI; a run that reaches the limit is stopped with every process under it, the tools' server
  and a compile it was waiting for included). The CLI's environment has the
  API keys removed and its auto-memory and an organisation's memory switched off. Its init event, where it
  says what it loaded, is kept with every session (`cli` in the response's metadata) and must show the five
  tools of the `cpl` server, connected, and nothing else, or the run stops, and none of the session's proofs
  counts (each run of the CLI is checked, as soon as it prints the init event, and a session that fails is
  stopped at once; the verdicts are kept in the session's `context.jsonl`); a
  machine with an organisation's
  managed Claude Code configuration is refused. The session's final text is the response; what it
  submitted stands even if the session runs out of time. What the CLI still adds to what the model receives,
  as measured with Claude Code 2.1.322: docs/decisions/agent-told-nothing.md. What a claude.ai login adds on
  a given machine: `python -m core.open_lane.context_check --config <run config>` (one short session).

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

The pilot (10 November 2026) is written once, `config/pilot/base.yaml` (cost of finishing, template v5,
minimal knowledge, the scaling question on), and a run is a file next to it that extends it
(`extends: <file>`, a path next to the config; the file's own settings go on top) and names the model, one
network and the seed check's network:

- `config/pilot/linear-max2.yaml`: the linear max-of-2 network at vocabulary size 64 and hidden width 8
  (`models/max2`), proof rounds on `max2-v64-s0`, the seed check on `max2-v64-s1`.

What an open-lane run needs to know about an architecture is the model folder's to state, under `open_lane`
in its `config.yaml`: the worked example and the further Lean sources (`example`, `extra_sources`) and notes
for the agent about the architecture in Lean's kernel (`notes`, shown by templates v4 and v5). A run config
that sets one of these itself overrides the folder; a folder that states nothing leaves the defaults. So a
pilot on another model (linear or attention; max or min of 2 or 4) is a model folder and a config of a few
lines. Its size must be one at which a copy of the weights does not fit a checker: at least one unit per bit
of the weights against the service's description budget of 8,192 + 4E (34,044 against 12,544 for the linear
network at 64 tokens; on the tiny networks a copy fits).

`open_lane.split_example` (the pilot's base sets it) names a file of the Lean project where an instance is
put together from small decided facts, which a long run needs: template v5 says where it is and `read_file`
may read it. The pilot uses the brute-force example of the tiny attention network.

Parked, unused by the pilot: runs over several sizes (`config/open-lane-ladder-base.yaml` and the two
configs that extend it, template v4, the model folders `tests/max2_ladder` and `tests/attn_maxn_tiny`). A
second worked example (`open_lane.second_example`, a scored proof that is not brute force; the prompt
points to it and `read_file` may read it) is off: it is more knowledge than the earlier pilots had, and on
a linear model the proof it would show is the linear network's own.

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
