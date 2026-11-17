# What guards a run against a copy and against lost work (17 November 2026)

Built on 17 November 2026 at the user's request ("make this foolproof, no wasted runs"), after run
attn-min2-ptl-3 and the size budget of policy v11. The Lean service's policy v12 (Compact-Proof-Checker,
docs/COUNTED.md) and this pipeline's dry start. What is open at the end is the user's to decide.

## What was found

- Time was the limit in attn-min2-ptl-3. Round 2 used 49 of its 90 minutes, 32 of them on Lean (35 lean_check
  calls, 950 s; one submission, 875 s), and stopped with 40 minutes left: one more cycle of facts and check
  did not fit. Fast reads (policy v10) cut that kernel work about 6 to 8 times on the cloud machine.
- The carried proof does not compile with the service as it is now: FarRun.lean proved two lemmas about a read
  by unfolding the old definition, and the soundness proofs and the instance import it (4 of the proof's 26
  modules). The agent would have to find that out, mend the file and compile five modules again.
- Five more carried modules, of round 1's proof alone (FarInst3, FarR1 to FarR4, claimed count 1,474), will not
  compile at the start of a continuation: they were written for another protected module than the newer
  versions of what they import. They are superseded, and the agent is told they did not compile.
- Every change of the claimed count, the certificate or the plan renames the protected module, so every module
  that imports it is edited and compiled again (about 20 calls and 20 minutes in round 2).
- The size budget cannot hold a copy out on a network of this size, whatever its number. The measure counts a
  variable as one node, so a function of 256 variables is an alphabet: 32,768 random bits, more than a copy of
  attn-min2 v64d8's weights holds, measure 11,536, under the budget of v11 (15,563) and of v10 (13,376).
  Charging each node the bits that name it would close that and make honest code measure three to four times
  as much, more than the weights. The budget stops a plain copy and no more.
- A plan's entries are plain numbers the checker may compute on for free, and the plan was bounded in entries,
  not in information: 4 entries of 32 bits per input are far more than the weights.

## What was built

- Policy v12, the plan's information: a plan's length in a prefix code is at most a quarter of what a copy of
  the weights holds at least (7,781 bits on attn-min2 v64d8; the honest plan of the windowed proof measures 775).
- Policy v12, nothing lost: a proof that the kernel verified and a budget then refused keeps its measured bill
  and length in the receipt and in the run's record. No frontier uses them.
- `open_lane.carried_replace`: a carried module in a version adapted to the library, used where the carried one
  is the version it was made for, recorded with both digests and told to the agent.
- `python3 -m core.open_lane.dry_start --config <config> --check`: the first round's workspace made as the run
  would make it, with no agent and no API call. It says which carried modules compile, how long they take, and
  whether the best carried proof is still accepted and scored, and how long that check takes on the machine.
  Run on the cloud machine on round 2's submission (2 cores, 6 GB): with FarRun.lean replaced, 25 of the 26
  modules compile with the kernel on (the eleven fact modules in 32 to 54 s each) and the checker previews at
  11,156 of 15,563. The 26th, SymRun2 (three kernel decides on the symbolic semantics, which the library's change
  does not touch), needs more memory than that machine has, as does the kernel's replay of the whole submission;
  both ran on the Mac in attn-min2-ptl-3. The complete check is the Mac's to make.
- The prompts state the plan's bound; lean_check's preview shows the plan's bits beside the description size.

## What holds against a copy

Not a size. The seed check (docs/OPEN_LANE.md, "After the proof rounds") locks the checker of the best scored
proof and runs it, unchanged, on a second seed. The code was fixed before that network was shown, so a copy
in it certifies nothing there; what the agent writes for the second network is the instance, whose only free
data is the plan, now bounded in information. A run whose checker certifies on the second seed about what it
certifies on the first did not get there by a copy.

## Open

- The seed check was off in attn-min2-ptl-1 to 3. config/pilot/attn-min2-ptl-4.yaml turns it on
  (attn-min2-v64d8-s2). Whether a score counts only with its seed check is not decided.
- The protected module's split (the network in a module of its own, the claim, certificate and plan in others
  named by their content), approved on 16 November, is not built. Until then a round gets 120 lean_check calls.
- The round-2 checker holds its 61 thresholds in its code. Locked, they are the first seed's on the second
  seed; the agent is told that another seed may compute differently.
