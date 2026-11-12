# A Python-then-Lean workflow, chosen per run (12 November 2026)

## What was asked

A specification (prepared against d412698) for an optional mode: early rounds for Python experiments and
mathematical arguments, later rounds for formalising the strongest candidates in Lean, with a small Lean
allowance during discovery; the interleaved approach stays the default, and old configs and saved runs keep
their behaviour.

## The decision

`open_lane.workflow_mode` (interleaved, python_then_lean) with `discovery_rounds`, `probe_compile_calls`,
`probe_auxiliary_submissions`, `probe_seconds`, and two more, `research_workspace_mb` and
`research_workspace_files`, for the research folder's limits. docs/OPEN_LANE.md ("Choosing a workflow") says
how it works; core/open_lane/workflow.py and research.py hold it.

Where the specification and the code of today met:

- The Python workspace py/ (3f8641b, after the specification's commit) stays in both modes as it is. The
  research folder is beside it: py/ is the agent's scratch notebook, carried from session to session;
  Research/ is the run's record, with experiment records kept apart from the working files.
- The phase is its own field (`phase`), never `stage`; the sessions after the proof rounds keep the five tools
  and their restrictions.
- The tool inventory is chosen per session: a python_then_lean proof round has seven tools and its own system
  prompt; the init event of every run of the CLI is checked against the session's inventory.
- A submission's candidate is kept beside its manifest (research.json), not in it: the manifest is the
  service's proof-file schema, which does not change.
- core/runner.py gained declared inputs and outputs. It is one of the sandbox files a run pins, so a run started
  on an earlier commit does not resume on this one (as with every change to the runner).

Tested (tests/test_python_then_lean.py): the eighteen cases of the specification on stand-ins for the Lean
project and its service, with the fake backend, and a discovery Lean check, an accepted auxiliary lemma and a
scored formalization proof against the real Lean service at 3320eab.
