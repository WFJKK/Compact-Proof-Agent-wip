# Python first, a clock on every call, drafts (11 November 2026)

## What happened

In the first test run of the pilot on a Mac (`pilot-linear-max2-test-2`), round 1's session waited on one
compile for over an hour while the session's own limit (three hours) ran out. The session
ended without the agent's answer, so without notes, and with no submission. Round 2 began from scratch: the
workspace holds only accepted modules, and there were none; the notes said only that the session ran out
of time. The tools had shown no clock, and a compile could take up to its own limit of an hour whatever was
left of the session.

A review of that run asked for the discovery and the optimisation to happen in Python, and for a checker to
be written in Lean only when it is promising, with its count and bill read from Lean before its proof is
written.

## The decision

1. Python first (prompt template open_lane_v6, the pilot's; v5 is kept). The agent explores in Python,
   formalises a candidate when it has a clear reason to expect it to be valuable (a better score, a new
   mechanism, or a cost that grows more slowly with the network's sizes, even before it beats the best
   score), and decides itself when to move to Lean. It runs a checker on the protected weights with `#eval`
   before proving it. The prompt calls that count and bill provisional: the count is what the checker
   claims, which only its soundness proof makes true, and the bill is the compiled code's, which the kernel
   has not checked. The service runs the submitted checker itself and takes no number a module prints;
   nothing about acceptance or scoring changes. The central lemma of a soundness proof is submitted early,
   as a lemma, so that it is accepted and carried.
2. A clock on every call. The backend starts it before each run of the agent. Its last
   `open_lane.notes_reserve_seconds` (600 by default) are kept for the agent's answer. Every tool's answer
   says how many seconds are left before them. No call starts when none are left, and none runs past them:
   a compile, a program or a submission still running is stopped with every process it started, Lean
   included. A run of the CLI that reaches its limit is stopped the same way (before, the tools' server
   under it finished its call, up to an hour, beside the next session). The module is saved before a
   compile starts, the program before it runs.
3. Drafts. The modules the last session left in its workspace that no accepted submission has as they are go
   into the next session, at their own path or set apart in `drafts/` when an accepted module holds the
   path. They are listed apart as drafts, never compiled before the agent begins, and accepted only by a
   submission, as any module: surviving into another round gives a module no status. A round that ended
   without the agent's answer is named in the next prompt, which shows the latest notes there are.
4. Edits. `lean_check` takes `edits` to the module saved at a path instead of its whole source: each
   replaces an old text that must occur exactly once. No edits compile the module as saved.
5. The check of what Claude Code loaded is made on its init event when the CLI prints it, and a session that
   fails is stopped at once (commit 6477d65). Before, it was made after the session, which a session that
   cannot count would have used up whole.

Tested in the cloud session through the real Claude Code CLI (2.1.322) and the real Lean service, with a
stand-in model server (no model called), two rounds of the pilot's configuration with a clock of 1,260 s and
a reserve of 1,080 s: the edits applied and compiled, a refused edit spent nothing, a program that slept 400 s
was stopped at the 152 s the session had left, the next call was refused for want of time, the answer's
notes reached round 2, and round 2's prompt listed the unfinished module as a draft (it compiled when last
saved), which read_file read. Run first with the cloud session's own environment, the CLI loaded a browser's
MCP server from the parent session's variables, and the check stopped the session at its init event with no
request to the model.

## Added on 12 November: a Python workspace

In test-3 (11 November, two rounds of 45 minutes on max2-v64-s0) the Lean drafts went on to round 2, but the
Python did not: every `run_python` call started in an empty folder, and round 2 began by computing the
combined weight matrix again. What the agent had found in Python reached round 2 only as words in its notes.

Now `py/` is the agent's Python workspace: the files its code leaves there are there for its later calls and
its next round, `import name` loads `py/name.py`, `save_as` keeps a call's code as such a module, and
`read_file` reads the text files. It is held to `open_lane.python_workspace_mb` and `python_workspace_files`,
and the pipeline takes only plain files with plain names from a program's folder (no link followed, no hard
link). Nothing in it is checked or counted, as nothing in Python is. The prompt also says that the tools answer
one call at a time: in test-3's round 2 the agent meant to compile and submit at once, and the two ran one
after the other.

Not done:

- A cache of the Lean library's reading for the rule on proofs. Measured on the whole library: reading and
  classifying it takes about 45 ms of each question's 1.9 s; the rest is Lean starting the inspection
  program. A cache would save almost nothing.
- Keeping compiled modules between rounds, and a pipeline scoreboard of provisional bills: the agent's own
  `#eval` gives it the bill.

## What runs before this show

Runs on v5 and earlier: sessions without a clock, whose calls could outlast them, and a workspace that
began each round with accepted modules only. Their counts and lengths stand; a round that ended without
notes left the next one less to start from than a v6 round has.
