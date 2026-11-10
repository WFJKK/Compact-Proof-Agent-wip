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
   keeping module had two faults: the equation of a rule that the soundness file keeps was taken for
   shown, and the rule with it; and a proof that unfolds a definition the run shows was taken for a use of
   what it does not show, where a module of the rules keeps that definition's equation. A constant with no
   declaration of the library behind it counts as shown if it is named outside the library's namespace (it
   belongs to Lean's own library or to Mathlib), and goes by the modules that keep it otherwise. What a
   shown definition unfolds to is not held against a proof. The agent is told at the compile and again
   with the receipt: which of its constants, and what they mention. A proof that is not clean stays
   accepted and is recorded without a length; the receipt is kept as the service wrote it. Before a run
   starts, Lean's reading is checked against constants the surface names as shown and as closed, on the
   library the project built. The base allowlist of the Lean service still admits the linear interval rule
   (`Interp.interval`), so without this rule a minimal-knowledge run would have scored a checker built on
   it.

The maximum-knowledge condition supplies the rules on purpose and keeps what it showed, without the README.

## What this does not close

- Lean itself. The agent can ask Lean about any constant of the library (`#print`), a search tactic can
  offer it a lemma that is not shown, and unfolding the interpreter or a task prints the names of their
  hidden fields. The rule on proofs keeps a run from counting a proof built on what was found that way. It
  does not keep the agent from seeing it. The prompt asks it not to look, and a compile whose output matches
  a forbidden expression is marked in the session's log (`showed`) and named in the round's log, so that a
  reviewer reads what Lean printed before taking a round as unaided. Only the Lean project can close this:
  a base package that the rules are not part of, an interface and a task without the rules' fields
  (the ticket of 10 November).
- The machine. With the sandbox in process mode (a Mac), the agent's `run_python` code can read files, and
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
