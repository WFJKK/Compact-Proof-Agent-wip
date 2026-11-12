# The attention min-of-2 pilot at width 8 (12 November 2026)

## What was asked

A first open-lane pilot on attention: min-of-2 on the one-layer, one-head, attention-only transformer
(`models/attn-min2`), one round, through the API on a server.

## What was measured at the zoo's size (v64: vocabulary 64, width 32, the paper's own size)

On the Lean project at 3320eab, Lean 4.35.0-rc4, in a 7 GB cloud sandbox, network `attn-min2-v64-s0`:

- The service's protected module does not compile: "maximum recursion depth has been reached" at the weights
  (8,256 numbers, the embedding 2,048 of them). With `set_option maxRecDepth 100000 in` before `def weights`
  it compiles in 26 s (a 33 MB .olean). The option changes how Lean elaborates that definition, not what is
  proved; no network of the earlier pilots needed it (their tensors have at most 512 entries).
- `#eval` of the general single rule on one input: 8,675 charged operations (c), at 2.2 GB.
- `decide +kernel` of the same: out of memory within 30 s. So is the conversion of the weights alone
  (`dweights`), which the rule makes first.
- In the kernel an array is a list. Loading the libraries alone takes 1.5 s and 2.2 GB. A dot product of 32
  terms with E's first 32 entries took 3.0 s in all and 0.3 GB more; with E's entries 1,600 to 1,631, 7.6 s
  and 1.1 GB more. On the linear max-of-2 network 32 such products took 1.9 s and no more memory.

## What was measured at width 8 (v64d8)

- Training: 10 seeds, 30 s each on a CPU, all at 4,096 of 4,096 (float and the Python checker's enclosure).
  E 1,296, B 4,371,728, c 1,067. Held out by the split: s0, s4, s5, s9.
- The protected module compiles unchanged in 9 s. A copy of the weights measures about 31,000 units
  against the description budget of 8,192 + 4E = 13,376, so it does not fit a checker.
- The kernel converting one tensor to the general rule's form: 0.4 s for an 8 by 8 matrix (64 entries), 10 s
  and 2.1 GB for the embedding (512 entries). The general single rule on one input still did not fit in 7 GB.

## The decision

Joshua chose width 8 for the pilot (`config/pilot/attn-min2.yaml`, network `attn-min2-v64d8-s1`, seed check
`attn-min2-v64d8-s2`) and a first round of 90 minutes (`config/pilot/attn-min2-quick.yaml`), on a server with
32 GB. Width 32 waits: it needs the recursion option in the Lean project's `scripts/make_protected.py` (a new
lock commit; to be written only when a tensor has more than 512 entries, so that the protected modules of the
networks that work today stay byte for byte the same), and its kernel costs are about 16 times width 8's per
pass over a tensor.

The model folder's notes tell the agent how the kernel behaves at these sizes (the cost of indexing, the
measured figures), not what a proof looks like (agent-told-nothing.md). The minimal surface now shows the exp
bounds: without `expInterval_spec` a checker that uses `I.exp` could not be proved sound.

Tested: a stand-in round of `attn-min2-quick` through the real Claude Code CLI and the real Lean service, no
model called: the surface check passed (20 files, 977 of the library's 4,498 constants shown), the baseline
certified 4,096 of 4,096 at B, run_python read the weights and kept a file in py/, the ExpSound excerpt read,
a module with `#eval`s on the protected weights compiled, and a lemma proved from `expInterval_spec` was
accepted and counted as offered.
