# The checker's run by compiled code, as an option (18 November 2026)

Decided with the user on 18 November 2026, after a conversation with Louis on 15 November about what makes
Lean slow here. The Lean service's policy v15 (Compact-Proof-Checker, docs/COUNTED.md, "The run by compiled
code") and `open_lane.instance` in this pipeline.

## The two parts of a result

A scored result says: the network answers at least n inputs correctly, and establishing that costs L.
It has two parts.

1. Soundness, which is mathematics. For every set of weights w, the checker D counts no more inputs than
   the network with those weights answers correctly:

       D(w) ≤ correct(w)   for all w

2. The run, which is arithmetic. On this network's weights W the checker returns n and is billed L:

       D(W) = n at bill L

Part 1 is where the understanding of the network is. Part 2 is a long calculation on exact fractions.

Until now Lean's kernel checked both. The kernel is the small program that checks proofs, built to be
trusted, not to be fast: it evaluates the run by rewriting terms. Lean's compiler turns the same definition
of D into a program that computes D(W) directly.

## What was slow

The kernel's evaluation of part 2 took most of every submission and shaped what an agent could do in a
session.

| Proof | Check with the run in the kernel | Check with the run compiled |
| --- | --- | --- |
| linear max2 v64 (4,095 inputs, length 298,016) | 82 minutes on the Mac (11 November) | 21 s |
| attn-min2 v64d8 (1,889 inputs, length 192,059) | 515 s | 78 s |
| brute force, tiny linear network | 29 s | 14 s |

The 21 s and 78 s are from the cloud machine, the 515 s too. The counts and bills are the same in every
row. Beyond the time: the agent wrote ten modules for the linear proof, nine of them only to get the run
through the kernel in pieces. With the run compiled the proof is one module.

## What was decided

- Build it as an option and make it the usual one for new runs. The kernel mode stays.
- Every receipt, record and report line says which mode a result has (`run`: kernel or compiled;
  `execution_assurance`: kernel_checked_instance or compiled_instance).
- The default of the setting stays kernel, so a config written before the choice runs as it did. A new
  pilot config sets `instance: compiled`.

## What is trusted in each mode

In both modes the kernel checks soundness, with the standard axioms only. The difference is part 2.

- kernel: nothing beyond the kernel.
- compiled: Lean's compiler and runtime for one evaluation, D on W. The service checks first that D is
  its own compiled code (no `implemented_by`, `extern`, `export`, `csimp`, `initialize`; nothing
  `noncomputable`), checks D's type in the kernel, and runs it in the box.

The link between what ran and what was proved is a library theorem (`CostM.exec_of_billed`): the compiled
program computes the same `CostM.billed (D Interp.counting) ⟨weights, cert⟩` that the kernel mode proves a
value of.

A compiler bug that made the run return a larger count than the definition gives would produce a wrong
result. That is the price. The kernel mode has no such exposure, which is why it stays for a result one
wants at the highest assurance: a proof found in compiled mode can be given an instance theorem later.

For comparison (looked up on 18 November): Gross et al.'s compact proofs are written arguments with
PyTorch floating-point computations, with the gap between floats and reals left open. Lean's own
`bv_decide` rests on an axiom that trusts compiled code. Soundness in the kernel with the run compiled is
well above the first and of the kind of the second.

## What a session does differently

- The agent writes D and proves it sound. It claims no count and proves nothing about the run.
- `lean_check` with `checker` makes the run before a submission: count, bill, length, and the last-bits
  test. Under a kernel run those numbers were provisional until the instance was through.
- `submit_candidate` takes `{checker, sound, certificate, plan}`. A scored block with an instance or a
  bill is refused by the session, before a submission is spent.
- The seed check writes no Lean. The whole proof is locked (there is no instance to keep apart), and its
  session gives the second network's certificate and plan; the service runs the locked checker there.

## Start drafts

Built with it, for the linear run: `open_lane.start_drafts` gives a fresh run modules to start from, as
drafts. The complete linear proof of 11 November lives in a run folder whose archive never counted it (the
receipt was written a minute after the session ended) and does not compile under today's library, so
`continue_from` cannot carry it. Its checker module, adapted, is given to `linear-max2-ptl-2` this way. A
start draft is not accepted and counts for nothing until a session submits it. The dry start compiles it,
shows the service's run of its checker, and with `--check` submits it.

## What this does not change

- The counted language, the size budget, the plan's bound, the 120 s kernel budget for the general layer
  and the last-bits test apply as before. In compiled mode everything submitted is general layer.
- The agent is still told nothing about what the network does.
- A checker whose run stops on a copy keeps the count of its run on the network and is refused a score.

## Not done

- No GPU. Louis suggested one for matrix products. The cost here was the kernel rewriting terms on exact
  fractions, which a GPU does not touch, and the compiled run of the largest proof takes seconds.
- No attempt to make the compiled run part of the trusted base by an axiom inside Lean. The service runs
  it and records that it did.
