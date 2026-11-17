# The network in a protected module of its own, and the specification in the kernel (17 November 2026)

Built on 17 November 2026 after the user's question what had blocked progress in run attn-min2-ptl-3 and
whether the remedies scale ("do those things": the module split with the false-alarm fix, then fast reads for
the specification side). The Lean service's policy v13 (Compact-Proof-Checker, docs/COUNTED.md) and what this
pipeline needs to go with it.

## What was in the way

- Every change of the claimed count, the certificate or the plan renames the protected module, and every
  module that imports it is edited and compiled again: about 20 lean_check calls and 20 minutes in round 2.
- The service refused a proof in which two modules each held the same equation lemma of a definition
  ("declares Candidate.Far.rows.eq_2 twice", round 1). Lean derives such lemmas where a definition is first
  unfolded and imports the copies as one theorem.
- The module in which the kernel runs the network's graph on symbols needed more than 5 GB. For the kernel
  an array is a list, and the specification builds and reads arrays entry by entry.
- The lock's rename for the seed check did not know about a plan: a planned checker's locked module would
  have been given the name of a protected module the service does not build. Found while reading the code;
  no run had reached it.

## What was built

In the Lean service (policy v13):

- `Protected.N_<network>`: the graph, the weights and the task with the definitions the module of a claim
  has for them, under a name no claim changes; likewise a certificate's module and a plan's, named by their
  content. The claim's module is what it was, text for text. A module that imports the network's module alone
  stays compiled when the claim changes, and a fact about its `weights` proves the same statement about the
  claim's: the kernel unfolds both to one term.
- A first version made the claim's `graph` an abbreviation of the network's. A proof kept from an earlier
  run then failed: `simp only [graph, ...]` stopped at the network's name. So the definitions are written out
  in both modules, and everything written against the claim's module compiles as before.
- A theorem two modules hold with one statement is one theorem. A definition in two modules, or one name
  with two statements, is refused as before.
- `CompactCheck/SemanticsKernel.lean`: every operation of the specification a second time, built from lists
  and read through a tree, each proved equal to the specification's (`semOps_eqK`, `semGraph_eqK`). On the
  run's three theorems on a 2-core cloud machine (imports alone: 2 s, 2.1 GB): as submitted, the first is
  killed at 5.8 GB after 79 s, the others take 14 s at 2.6 GB and 39 s at 5.8 GB. With `rw [semOps_eqK]`
  added and nothing else: 18 s at 3.9 GB, 3 s, 20 s at 2.8 GB. With the proof's own tensors built from lists
  as well: 7 s, 4 s, 6 s, at most 2.8 GB.

In this pipeline:

- The lock (core/open_lane/lock.py, inspect.py, inspect_oleans.lean) knows the protected modules by what
  they hold. Under the lock every name a locked module holds becomes the name of the module that holds the
  same for the call: the network's, and the claim's by network, claimed count, certificate and plan.
- A checker has the same fingerprints whichever of the two modules it names: Lean's account writes both
  names the same, and the two constants have one text (checked: modules where they differ are not read).
- The fingerprints no longer hold the height the kernel is told to unfold a definition at. It changes with
  how the library is layered (policy v10 put a tree under its reads) and the term does not, so a proof
  compiled before such a change and after it would have counted as two checkers.
- The dry start, with --check and a seed check planned, reads the carried proof's lock from the earlier
  run's submission and from the one it has just made, and says when they are not the same checker or when
  the earlier one cannot be read. If no proof of the run scores better than the carried one, that is the
  lock the seed check would use.
- The prompts say how the modules fit together and how to keep the kernel's cost down for arrays; the
  minimal surface shows SemanticsKernel.lean; lean_check answers with the names of the protected modules.
- A theorem two modules hold with one statement is no duplicate for the lock either.

## The dry start of attn-min2-ptl-4, run on the cloud machine (2 cores, 6 GB for a process)

    python3 -m core.open_lane.dry_start --config config/pilot/attn-min2-ptl-4.yaml --check

With the service at policy v13 and the two adapted modules (FarRun, SymRun2): all 26 carried modules of the
best proof compile (600 s in all; SymRun2 34 s, the fact modules 35 to 50 s each), and the proof is accepted
and scored again as the agent would submit it: 1,889 inputs, length 192,059, description size 11,156 of
15,563; the check took 553 s. Before this change the same machine could not compile SymRun2 or replay the
submission. The lock read from that fresh submission: 12 locked modules, 14 free, the graph and the task as
context. What the cloud machine cannot say is whether the lock read from the earlier run's own submission
is the same checker: that run's compiled modules are on the Mac. The dry start there says it.

## Does it scale

- Compiles on a change of claim: from all modules to the one that names the claim, for a proof written that
  way. The claim's module itself is compiled once per claim, in time proportional to the weights, as before.
- Width: the protected module of a network of width 32 did not compile at all (Lean's recursion depth at
  tensors of 2,048 entries, its compiler's step limit at 4,096). It does now: attn-min2-v64-s0 (8,257
  weights) in 78 s for both modules, attn-min2-v128-s0 (12,353) in 143 s, on 2 cores. At those widths a new
  claim costs about a minute for its module.
- Reads in the kernel, of the weights (policy v10) and of the specification's tensors (this change): from
  the index to its logarithm per read. Building a tensor: from the square of its size to its size.
- What does not change: a submission compiles every module again in the service's own box, so a
  submission's time is the proof's whole kernel work. Every theorem's memory is held until it is done.

## Open

- The carried modules of attn-min2-ptl-3 import the claim's module of that run. They compile as they are; the
  agent is told to move the imports when the next claim makes it edit them anyway.
- Candidate/SymRun2.lean is given `rw [semOps_eqK]` in its three decided theorems by
  open_lane.carried_replace in config/pilot/attn-min2-ptl-4.yaml (the statements are the same; the agent is
  told). It compiled on the Mac as it was; the adapted version is there because every submission compiles the
  module again, and so that the whole carried proof can be checked on a 6 GB machine.
- Whether a score counts only with its seed check (docs/decisions/no-wasted-runs-v12.md).
