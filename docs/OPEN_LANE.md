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
  occur exactly once, in order, and no edits compile the module as saved; since 13 November 2026 `checker`,
  the name of the agent's checker, adds a scoring preview: the counted-language closure and the description
  size against the budget, measured as the score step measures them, with the largest definitions, and since
  17 November 2026 the service's last-bits test, run on the compiled checker (`last_bits`: its count and bill on
  the network and its count on each copy; the call tells the service how long it has, `--limit-s`, so that
  these runs never push a finished compile past the call's limit); and `plan`
  builds the protected module with a planned checker's plan; since 17 November 2026 the answer names the
  protected modules the service built, `protected_modules`: the claim's and, beside it, the network's own,
  `Protected.N_<network>`, which no claim renames, so that a module importing it alone stays compiled when
  the claim changes, docs/decisions/network-module-v13.md);
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
- A compile's own limit (since 16 November 2026). One lean_check is stopped after
  `open_lane.compile_seconds` (600 by default, at most 3,600) unless the call asks for more with `max_seconds`
  (at most 3,600), and never past the session's time; the answer gives the limit that applied (`limit_s`),
  and a compile stopped at its own limit says how to ask for more. The prompt's budgets say the limit, and
  the formalization templates (open_lane_v6, open_lane_formalization_v1) say that the kernel compares two
  statements that differ in form by computing. Before this, one compile of a glue module ran 2,802 s, most of
  a 90-minute session, with nothing learnt (attn-min2-ptl-2, round 1, 13 November). Lean prints a module's
  messages only when it has finished it, so a stopped compile does not say where it was; the service's
  per-command markers of the 13 November design (`stopped_in`, timings) are not built here.
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

## Who runs the checker (18 November 2026)

A scored result has two parts: the checker is sound for every set of weights (mathematics), and on this
network's weights it returns the count at the bill (arithmetic). `open_lane.instance` says who establishes
the second (docs/decisions/run-by-compiled-code-v15.md; the Lean project's docs/COUNTED.md, "The run by
compiled code").

- `kernel` (the default): the agent proves the run as an instance theorem, which Lean's kernel checks, and
  claims the count and the bill. Nothing is trusted beyond the kernel.
- `compiled`: the agent proves soundness and nothing else. The service has the kernel check the soundness
  theorem and then runs the compiled checker on the network itself, for the count and the bill. That trusts
  Lean's compiler for one evaluation and takes the kernel's evaluation of the run, minutes to more than
  an hour per submission in the pilots, off every submission.

A compiled run needs `workflow_mode: python_then_lean` and a worked example without an instance theorem,
which the model folder names (`open_lane.compiled` in its config.yaml: `example`, `notes`). What differs in
such a run:

- The prompts are `open_lane_discovery_v2`, `open_lane_formalization_v2` and, for the sessions after the
  proof rounds, the first part of `open_lane_v7`: the kernel run's texts with the passages about the
  instance rewritten (tests/test_open_lane_compiled.py holds them to that).
- `lean_check` takes no claimed count and compiles against the network's own protected module. With
  `checker` its preview holds the run: the count, the bill and the length a submission of that checker
  gets, and the last-bits test.
- `submit_candidate` takes a checker with its soundness theorem (`scored`: checker, sound, certificate,
  plan), or a lemma. The session adds `run: compiled`. A scored block with an instance or a bill is refused
  by the session, before a submission is spent.
- A proof is locked whole (core/open_lane/lock.py): there is no instance to keep apart. The seed check's
  session writes no Lean. It gives the second network's certificate and plan and the service runs the
  locked checker there.
- Every record carries `run` (kernel or compiled), the receipt its `execution_assurance`, and the report
  says of each proof on the frontier how its run was established.

A run keeps the mode it started with: it is part of the recorded schedule, and a resume with another is
refused.

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

## Choosing a workflow

How the proof rounds are organised is chosen before a run starts, with `open_lane.workflow_mode`, and kept for
the run's whole life (the run records it; a resume with another schedule is refused).

- `interleaved` (the default): every round, the agent explores in Python and develops and submits Lean proofs.
  `prompt_template` picks the template and `patience` can end the proof rounds early. Every run made before the
  setting existed is this, and resumes as it was.
- `python_then_lean`: a fixed schedule of two phases (core/open_lane/workflow.py). Rounds 1 to
  `discovery_rounds` are discovery, the rounds after them up to `rounds_max` formalization; the seed check and
  the scaling question follow as before. `discovery_rounds` is at least 1 and less than `rounds_max`.
  Patience does not apply in either phase; the hard limits, a stop, a backend's failure and the model declining
  stop a run as before, and a resume continues the same phase. The phases choose their own templates
  (`open_lane_discovery_v1`, `open_lane_formalization_v1`, recorded in each round's meta); `prompt_template`
  goes on deciding only for interleaved runs.

To run the new mode, start a separate run from a config that sets it, for example

    python3 -m core.loop run --config config/pilot/linear-max2-python-then-lean.yaml

(the linear pilot with discovery rounds 1 to 4 and formalization rounds 5 to 7: a first setting to try, not a
claim that the split is the best one). `--set open_lane.workflow_mode=python_then_lean --set
open_lane.discovery_rounds=3` does the same on another config.

What the agent has in a python_then_lean proof round, besides the five tools:

- A research folder, `Research/`, the run's (<run>/research/): every session of either phase reads and writes the
  same files. `research_write(path, text)` and `research_list(prefix)`; `read_file` reads its text files. A
  candidate record, `Research/candidates/<id>.json`, has at least the keys id, title, mechanism_claim,
  proof_sketch, predictions, experiment_refs, counterexamples, estimated_coverage, estimated_cost,
  cost_estimation_method, unresolved_questions and agent_assessment; no key and no assessment may say that it
  is proved. `Research/shortlist.json` is a list of {id, reason} in order of priority. Held to
  `research_workspace_mb` and `research_workspace_files`; paths of plain parts only, no link followed.
- `run_python(code, network, files, outputs)`: the declared input files are put in the folder, read-only; the
  declared outputs are what the code writes at `out/Research/...`, kept in the research folder when the code
  completes. Every call is kept as an experiment record (attempt_j/open_lane/experiments/<call>/: code,
  inputs, outputs, status, diagnostics, read-only), and the answer says whether the code raised
  (`python.ok`). A failed or stopped experiment is marked incomplete and its outputs stay in its record.
- In discovery: `lean_check` and auxiliary `submit_candidate` calls name `candidate_id` and `question` and
  draw on the phase's Lean allowance, a total over the phase: `probe_compile_calls`,
  `probe_auxiliary_submissions` and `probe_seconds` (the service's work and Lean's questions included). A call
  takes its share before it starts and settles it when it ends; a call that never settled counts whole, so a
  crash or a resume gives nothing back. All three zero: no Lean in discovery. Proofs of Target wait for
  formalization. Outcomes are recorded as compiled, compiler_error, timeout, infrastructure_error, accepted or
  rejected; a compile is never an acceptance.
- At the transition (before the first formalization round, once): a read-only copy of the research folder
  (<run>/workflow/discovery/) and the shortlist the folder holds, or, without one, the candidates unranked.
- In formalization: the session's normal budgets, Python, the research folder, and `candidate_id` to name the
  candidate a proof comes from.

What counts is unchanged: the receipts. Research records, estimates and the agent's assessments never enter a
frontier or a score; an accepted auxiliary lemma stays a lemma; a formalization round's scored proof is an
ordinary record (with `phase`, never `stage`) and enters the frontier and the score. `status` and the report
show the mode, the rounds, time and tool calls of each phase, the Lean checks and their outcomes, the
candidates with their estimates, and the accepted proofs that name each candidate.

## Continuing an earlier run

A run keeps the Lean service it started with, so a run whose service has changed since cannot be resumed. To go
on with its work anyway, start a new run that continues it: `open_lane.continue_from` names the earlier run (its
id under `runs_dir`, or the path of its folder), which must be an open-lane run of the same model and networks
with at least one complete proof round (core/open_lane/continuation.py). For example

    python3 -m core.loop run --config config/pilot/attn-min2-ptl-continue.yaml --sandbox seatbelt --auth api_key

When it starts, the run copies, once and read-only, into <run>/inherited/: the earlier run's config, versions,
archive and stages record; for each complete proof round its meta, the agent's answers, each session's state and
tool log, and every submission (manifest, receipt, the pipeline's notes beside them and the submitted modules);
for the last of those rounds also the session's workspace modules, drafts and Python files; and its research
folder. `inherited/record.json` lists every copied file with its sha256. The research folder is also copied into
the run's own, each file's index entry naming the run it came from. The earlier run's folder is only read; its
incomplete rounds and its sessions after the proof rounds are not copied.

Round k of the continuation starts as round K + k of the earlier run would have (K its last proof round): the
modules the service accepted there are carried into the workspace and compiled before the agent begins, the last
session's unfinished modules and Python files go on as drafts, and until the run has notes of its own the latest
notes are the earlier run's, named as such. The earlier run's submissions are listed apart under the run's own,
with whether the same acceptance service answered them; `open_lane.continue_note` is shown with them, for what
the person starting the continuation knows about them (a rejection that was a fault of the service, fixed since):
facts about the service and the receipts only, never what a proof of the network looks like.

Nothing of the earlier run counts in the continuation: its archive, frontier, score and budgets are its own. In
the python_then_lean workflow a continuation may set `discovery_rounds: 0` and formalise from round 1; the
transition then records the research folder as the earlier run left it, with its shortlist. A continuation can
itself be continued: its copy goes along (inherited/inherited/), and the carried modules are the latest accepted
version of each path across all of them.

### Before the run: a dry start, and carried modules under a changed library (17 November 2026)

A continuation usually runs with a newer Lean service than the earlier run did, and a carried module may no
longer compile with it. Then nothing that imports it compiles either, and the agent has to find out why, mend
it and compile the rest again, one lean_check a module, on the round's time. In run attn-min2-ptl-3 that is
FarRun.lean and the four modules that import it, the soundness proofs and the instance. Two things keep that
out of a run.

    python3 -m core.open_lane.dry_start --config <run config> --sandbox seatbelt --check

makes the first round's session as the run would, in a folder of its own (`<runs_dir>/_dry_start/<run_id>`,
removed afterwards), with no agent and no API call: it copies the earlier run, puts the carried modules into
a workspace, has the service compile them, and says which compiled and how long each took. With `--check` it
submits the best carried scored proof again from that workspace: whether the service as it is now accepts and
scores it, its description size against the budget, and how long the check takes on this machine. It ends
with READY or NOT READY and why (core/open_lane/dry_start.py). It goes by the modules of that proof's
submission. Other carried modules, of an earlier proof written for another claimed count, usually no longer
compile beside the newer versions of what they import (five of attn-min2-ptl-3's 31); they are named, and
the agent is told the same in its prompt.

`open_lane.carried_replace` gives a carried module in a version adapted to the library:

    carried_replace:
      - path: Candidate/FarRun.lean
        with: config/pilot/carried/attn-min2-ptl-3/FarRun.lean
        replaces_sha256: <the sha256 of the carried version>
        note: <one or two sentences, shown to the agent with the module>

The workspace gets the replacement where the carried module is the version it was made for; a later accepted
version of the path is carried as it is. The session's record names both digests, and the agent is told that
the workspace holds an adapted version. A replacement that fits no carried module in the run's first round
stops the run before the round begins. It is for a change of the library alone (a proof that unfolded a
definition the library has since changed): the statements stay, and nothing about the network is added.

### Starting from modules that no run can hand on (18 November 2026)

`open_lane.start_drafts` gives a fresh run's first session modules to start from:

    start_drafts:
      - path: Candidate/MaxDirect.lean
        with: config/pilot/start/pilot-linear-max2-test-2/MaxDirect.lean
        note: <where it comes from and what the service said of it, shown to the agent>
        scored: {checker: Candidate.MaxDirect.D, sound: Candidate.MaxDirect.D_sound, certificate: []}

They are drafts: listed apart in the prompt with the note, never compiled before the agent begins, never
accepted until a session submits them. It is for work outside any run folder that `continue_from` could
take: the complete linear proof of 11 November was written a minute after its session ended, so its run
never counted it, and it no longer compiles under today's library. A run with start drafts may have no
discovery round. `scored` is optional, for the dry start alone and for a run with `instance: compiled`:
the dry start compiles each start draft, reports the run the service makes of the named checker, and with
`--check` submits it. What a start draft holds is checked against the run's surface like everything else
the run shows (a forbidden expression in it stops the run before it starts). The note holds facts about
the module's origin, never what a proof of the network looks like.

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
  into the workspace again from the lock before every compile and submission (with the names of the
  protected modules they were written against replaced by those of the call: the network's own module by
  the second network's, the claim's by the one of that network, claimed count, certificate and plan; nothing
  else), and the submission must name the locked
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
- The reading (`open_lane.code_review: true`, since 17 November 2026). A session reads the locked checker's
  code and answers one question: does its count come from what it computes on the weights it is given, or
  from numbers of this network written into its code? A checker's own code is free, the Lean service's size
  budget cannot keep a copy of a small network's weights out, and its last-bits test sees a copy only where
  it is compared exactly (docs/decisions/weights-in-code-v14.md). The session has the locked modules to
  read, the certificate and the plan the proof was accepted with (`py/locked_proof.json` in its Python
  workspace, as every session after the proof rounds has since 18 November), `run_python` to compare what
  it finds with the weights, and no way to submit. Its answer ends with a
  verdict, clean, suspect or unclear, and what it found; the status and the report carry it, marked as a
  language model's reading. It is an alarm for a person and never moves a score. The answer's headings
  (and the scaling steps' below) are read by `core/open_lane/answer.py`, which takes them in markdown bold
  too and after other text on a line: a session's answer is its messages joined, and before 23 November
  2026 the text written before a tool call ran straight into the answer (`...the modules.**VERDICT:**
  clean`), which the first reading on attn-max4-ptl-1 lost ("no verdict").

The scaling proofs (since 23 November 2026) come after a finished run and never during one: a person starts
them once the run's proofs have been looked at,

    python3 -m core.loop scale --run <run folder> [--only V] [--budget-usd 300]

One session per size, in this order: the number of token values V, the number of positions n, the width d,
each with the other two held at the network's values (`core/open_lane/scaling_steps.py`). The model folder
says which of its sizes each one is (`open_lane.scaling_sizes`; an attention model's width and head width
vary together), and `open_lane.scaling_steps` gives each step's minutes and dollars (by default V 60 minutes
and $20, n and d 30 minutes and $10 each). The sessions are about every scored proof on the run's frontier,
not only the locked one: the locked proof's modules are in the workspace, locked, as in the scaling question;
the other proofs' modules are there to read and import where they do not clash with the locked ones; every
proof's certificate and plan are in `py/handed_in_proofs.json`. Each session asks, for its size, the formula
of each proof's length part by part, brute force's, the verdict, and what the proof certifies at other values
of the size; and in Lean, as lemmas, the bill at this size for every weight, the bill as an exact formula in
the size, and its leading order against brute force's. Where a cost depends on something other than the
sizes (how many pieces a plan makes), that is a parameter of the formula, with its value on this network. A
step carries the modules of the lemmas the earlier steps had accepted and their answers. For each accepted
lemma Lean is asked which of the proofs' checkers the modules the service compiled hold, term for term (for
the locked proof in the session, for the others after it); the report prints each statement in full beside
that answer. The steps are rounds of the run after its last; `stages.json` keeps them under
`scaling_proofs`, and running the command again goes on with the steps not done. Nothing is scored.

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
- `config/pilot/attn-min2.yaml`: the attention min-of-2 network at vocabulary size 64 and width 8
  (`models/attn-min2`, size v64d8, added 12 November 2026), proof rounds on `attn-min2-v64d8-s1`, the seed
  check on `attn-min2-v64d8-s2`; `config/pilot/attn-min2-quick.yaml` is one round of 90 minutes of it,
  without the seed check and the scaling question. Not the zoo's width 32 (the paper's): there the protected
  module exceeded Lean's default recursion depth, and the kernel's loops over a tensor cost the square of its
  length (docs/decisions/attn-min2-width8.md; both mended on 16 and 17 November 2026, policies v10 and v13 of
  the Lean service, so width 32 is open to a run now). The minimal surface shows the exp bounds (Exp.lean and
  ExpSound.lean as excerpts) for every run.
- `config/pilot/linear-max4.yaml` and `config/pilot/linear-min4.yaml` (18 November 2026): the linear network
  on four tokens (`models/max4`, `models/min4`: the max2 model's module on four positions) at vocabulary size
  64 and hidden width 8, proof rounds on `<model>-v64-s0`, the seed check on `<model>-v64-s1`. 16,777,216
  inputs: brute force is never run, B comes from the shapes, and round 0 replays no baselines. The first run
  on each is `linear-<model>-ptl-1.yaml` (python_then_lean, the checker's run made by the service, one
  discovery round and four formalization rounds from an empty workspace, then the reading), and its dry start
  is `linear-<model>-dry.yaml`, which gives the same run a probe module so that the service compiles, checks,
  runs and scores something on the network before an agent works on it
  (docs/decisions/linear-four-tokens.md).
- `config/pilot/attn-max4.yaml` (23 November 2026): the attention max-of-4 network at the paper's own size
  (`models/attn-max4` at v64: vocabulary size 64, width 32, 16,777,216 inputs), proof rounds on
  `attn-max4-v64-s0`, the seed check on `attn-max4-v64-s2`, no baselines replayed. The first run is
  `attn-max4-ptl-1.yaml` (as `linear-max4-ptl-1` but with sessions of 90 minutes and caps of $40 and $200),
  and its dry start `attn-max4-dry.yaml` (docs/decisions/attention-max4-paper-size.md).

What an open-lane run needs to know about an architecture is the model folder's to state, under `open_lane`
in its `config.yaml`: the worked example and the further Lean sources (`example`, `extra_sources`) and notes
for the agent about the architecture in Lean's kernel (`notes`, shown by templates v4 and v5). A run config
that sets one of these itself overrides the folder; a folder that states nothing leaves the defaults. So a
pilot on another model (linear or attention; max or min of 2 or 4) is a model folder and a config of a few
lines. Its size must be one at which a copy of the weights does not fit a checker. Since the service's policy
v11 (16 November 2026) its description budget is 8,192 + 4E, or half of the least a copy holds (each weight's
sign and significant bits) where that is more, at most 16,384; a copy holds at least twice the budget wherever
the half decides it (26,020 against 13,010 for the linear network at 64 tokens, 31,127 against 15,563 for the
attention network at width 8) and more than the budget elsewhere. On the tiny networks a copy fits. The
reasons are in the Lean project's docs/COUNTED.md, "The size budget"; docs/decisions/size-budget-v11.md has
the decision. That budget stops a plain copy only: a table written with an alphabet of variables measures about
a third of its bits (measured 17 November, policy v12), so on a network of this size no size budget keeps a
determined copy out. Since policy v14 (17 November) no budget is above 24,576, and every scored proof's
checker is run again on copies of the network whose weights differ in their last bits: one whose count rests
on an exact stored copy certifies nothing there and is refused scoring. A copy that is rounded and compared
with a tolerance passes that test; the reading (above) is the alarm for it, and nothing decides it
(docs/decisions/weights-in-code-v14.md). The seed check (above), with the plan bounded in information, a
quarter of what a copy holds (policy v12: docs/decisions/no-wasted-runs-v12.md), shows whether a checker
carries over to another network. It is a measurement beside the score and no condition for it: a proof may
rest on a circuit that only the first network has.

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
