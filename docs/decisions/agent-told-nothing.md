# The agent is told nothing about what works on a network (10 November 2026)

## What happened

The open lane was set up in October on one condition: the agent starts from brute force and finds for
itself what makes a proof shorter (that the network can be contracted, that it is symmetric, where bounds
over groups of inputs hold). The prompt followed it: it says what a proof is and what it costs, and no rule.

The tools did not. Since 20 October `read_file` and `search_library` reached the whole Lean project: its
docs, its README and every source file. That project was written around the fixed rules lane, so what the
agent could read was

- descriptions of the rules that work on these networks, and their Lean sources and soundness proofs;
- the history of the earlier pilots: which proofs they found, by name, and how short they were;
- the README, which names the paper this work follows, a name the model folders forbid in any prompt.

The prompt itself pointed to one of these docs, pasted the interface with the rules for groups of inputs
in it, and the model folder's notes said that a checker "many times shorter than brute force" exists.

In the test run of 10 November (`pilot-linear-max2-test`, stopped in round 1) the agent read two docs and
the sources of the contraction, symmetry and interval rules, and computed the singular values of the
product of the weight matrices within ten minutes.

So no open-lane run since 20 October shows unaided discovery. The counts and lengths of those runs stand:
the service checked them. What they say about what an agent finds by itself does not.

## The decision

The agent is told the specification, what a proof is and what it costs. It is told nothing about what
works on a network: no rule, no earlier proof or its length, no doc. Four things keep that.

1. A surface (`core/open_lane/surface.py`, `core/open_lane/surface/<condition>/SURFACE.yaml`). What a run
   shows of the Lean project is a named list per knowledge condition. In the minimal condition: the
   specification, the network's semantics, the counted language with the single-input rule and its price,
   the allowlist, and the run's worked examples. No docs, no README, none of the fixed rules' sources. Where
   a file holds both (the interface, the task, the soundness file), the run shows an excerpt, kept in this
   repository: every line of an excerpt is a line of the Lean project's file, in order, except its own
   marked notes. `read_file` and `search_library` reach the surface and nothing else, and the prompt pastes
   what they serve. A run records a digest of what it shows and keeps it: a resume on a surface that
   changed is refused.
2. The prompt. It lists the files the run offers and points to no doc. The trap of a split instance, which
   it used to send the agent to a doc for, is stated in it. The model folder's notes say how the tools behave
   at a size, never how short a proof has been.
3. The check before a run starts (`core.loop.check_surface`), and again on a resume. The excerpts are parts
   of the files. Nothing the run sends, and no file its tools reach, matches an expression the surface
   forbids: the names and vocabulary of the fixed rules, of earlier runs and of the paper, with the model
   folder's own terms and its held-out networks. A run does not start otherwise, so a change in the Lean
   project or in a template that brings a hint back is found before an agent reads it.
4. The rule on proofs (`core/open_lane/offered.py`). The Lean library is compiled as one package, so the
   rules are in scope of every module the agent compiles, whether or not it can read them. A proof is
   therefore counted only if none of its own constants (a definition, a statement or a proof) mentions a
   constant of the library that the surface does not show. Lean is asked, as for the lock: its own record
   of where each constant is declared says whether the line is one the run shows, and the modules the
   service compiled say what a submission's constants mention. A constant Lean made itself (an equation of
   a definition, a matcher, a recursor) goes with the declaration its name extends, in whichever module
   Lean keeps it. Lean keeps such a constant with the first module that asks for it, which need not be the
   module of its declaration (on the whole library that holds for a fifth of the constants). Going by the
   keeping module had two faults: the equation of a rule that the soundness file keeps was taken for shown,
   and the rule with it; and a proof that unfolds a definition the run shows was taken for a use of what it
   does not show, where a module of the rules keeps that definition's equation. A constant with no
   declaration of the library behind it counts as shown if it is named outside the library's namespace (it
   belongs to Lean's own library or to Mathlib), and goes by the modules that keep it otherwise. What a
   shown definition unfolds to is not held against a proof. A structure with a field the run does not show
   may not be taken apart either (a pattern match, `cases`, its recursor or its constructor's injectivity
   lemmas bind every field, the hidden ones included): in the minimal condition, Interp and Task. The agent
   is told to use their projections. The agent is told at the compile and again with the receipt: which of
   its constants, and what they mention. A proof that is not clean stays accepted and is recorded without a
   length; the receipt is kept as the service wrote it. Before a run starts, Lean's reading is checked
   against constants the surface names as shown and as closed, on the library the project built. The base
   allowlist of the Lean service still admits the linear interval rule (`Interp.interval`), so without this
   rule a minimal-knowledge run would have scored a checker built on it.

The maximum-knowledge condition supplies the rules on purpose and keeps what it showed, without the README.

## What reaches the model besides the run's own text (11 November 2026)

The pilot's configuration (`config/pilot/linear-max2.yaml`, two rounds) was run through the real Claude Code
CLI (2.1.322) and the real Lean service, with the CLI's requests sent to a stand-in model server on the same
machine. The server recorded every request and answered with scripted tool calls; no model was called. Decoys
were put where Claude Code looks for instructions: the user's CLAUDE.md, rules, skills, sub-agents, hooks
and MCP servers; a CLAUDE.md, CLAUDE.local.md, AGENTS.md, rules and MCP servers in the folders above the
session's working folder, and a git history there; the auto-memory folder; an organisation's managed
configuration.

- The run's own text: the prompt, the five tools' descriptions, the tools' answers.
- What Claude Code adds: one line of system prompt ("You are a Claude agent, built on Anthropic's Claude
  Agent SDK."), a note on the environment (working folder, platform, model name, date, a token count), the
  token count after each tool call, two generic nudges (to keep the user informed; to ask for independent
  things together), and a placeholder tool it says never to call. None of it is about a network.
- With the backend's flags no decoy reached the model but two. The auto-memory folder's MEMORY.md is pasted
  as instructions; on a Mac it is empty, since the folder is keyed by the session's fresh working folder,
  and it is now switched off (`CLAUDE_CODE_DISABLE_AUTO_MEMORY`, with `CLAUDE_CODE_DISABLE_ORG_MEMORY`). An
  organisation's managed configuration (`/Library/Application Support/ClaudeCode` on a Mac) reaches the
  model whatever the flags say, its CLAUDE.md and what its hooks print: a machine that has one is refused.
  Without the flags every decoy reached the model.
- `run_python`'s folder held the fixed rules lane's `helpers.py`, whose proof function has the options
  symmetry, contract and approximate, next to split trees and "the contract rule". In the capture these
  were the only forbidden expressions that reached the model. The folder now holds the wrapper around the
  agent's code, `model.py`, the harness, the weights and input.json, and the check before a run scans its
  text files.
- Lean names a file by its absolute path, which names the run and the machine's user. The agent is shown a
  module's path in Candidate/ instead (in Lean's messages and in receipts), and the mark for forbidden text in
  Lean's output is taken on that: in the first test run on the Mac, whose id begins with "pilot", every
  compile with a message had been marked.
- Every session keeps the CLI's init event (what it loaded). Anything beyond the five tools of the `cpl`
  server, connected, stops the run: another tool or MCP server, a skill, a slash command, a memory folder.
  Every run of the CLI in a session is checked, one that ran out of time on what the CLI printed until then,
  and the verdicts are kept next to the session's receipts (`context.jsonl`). If one run failed its check,
  printed nothing to check, or was answered by another model, the run stops and none of the session's proofs
  counts, after a resume too: they are recorded without a length. (The review of e6221f0 found that a session
  that ran out of time skipped the check, and a resumed one counted the proofs of the run that failed it.)
- Not testable with a stand-in: what a claude.ai login adds. This version of the CLI has code for an
  account's and a team's memory, behind the login and switches Anthropic sets on its servers. Such a memory
  would show as a memory folder in the init event; anything that leaves no trace there would show only in
  what a real session receives. `python -m core.open_lane.context_check --config <run config>` runs one
  session as the backend does and asks the model to copy out everything it was given (one short session on
  the machine's login). It is a diagnostic, not a proof: the model's account can leave things out. A CLI
  that fails, reports nothing of what it loaded, or gets no answer is reported as inconclusive (exit 2).

The open lane has no API backend. One would send the run's own text and nothing else.

## What this does not close

- Lean itself. The agent can ask Lean about any constant of the library (`#print`), a search tactic can
  offer it a lemma that is not shown, and unfolding the interpreter or a task prints the names of their
  hidden fields. The rule on proofs keeps a run from counting a proof built on what was found that way. It
  does not keep the agent from seeing it. The prompt asks it not to look, and a compile whose output matches
  a forbidden expression is marked in the session's log (`showed`) and named in the round's log, so that a
  reviewer reads what Lean printed before taking a round as unaided. Only the Lean project can close this:
  a base package that the rules are not part of, an interface and a task without the rules' fields
  (the ticket of 10 November).
- The machine. With Landlock (Linux) the agent's `run_python` code is confined to its folder: in the capture
  of 11 November its attempts to list the folders above were refused. With the sandbox in process mode (a
  Mac), the agent's `run_python` code can read files, and
  on a machine without Landlock the Lean service compiles the agent's modules unconfined, where Lean can
  read files too. A run that is to count as unaided needs a confined machine (docs/SERVER.md). A run on an
  unconfined machine says so when it starts.
- What the agent knows. The hygiene list keeps the paper's name out of what a run shows. It cannot remove
  what a model has read.
- The specification. The prompt states the task ("the correct output is the largest token"), and the
  networks' names contain the model's. That is what the theorem is about, not how the network computes it.
- Attention models, in part. The general single rule is on the surface (its price, its run, its
  correctness, as excerpts), so brute force on an attention network is within what a run offers. The bounds
  on `exp` and their soundness lemma (Exp.lean, ExpSound.lean) are not yet: a proof that uses the `exp`
  operation would rest on a lemma the run does not show. Before a pilot on an attention model, they get
  excerpts.
- The maximum-knowledge condition's docs tell of earlier runs. Not reviewed.

## What runs before this show

Open-lane runs from 20 October to 10 November: correct counts and lengths, no evidence about discovery.
The claim "the agent found this by itself" needs a run on this version, on a confined machine, with the
Lean project's base apart from its rules.
