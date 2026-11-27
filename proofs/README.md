# The proofs

Every proof in the README's tables, as it was submitted to the Lean service and as the service scored it. Each
folder holds:

- `Candidate/`: the Lean modules, with the checker and its soundness theorem;
- `manifest.json`: what was submitted (the checker, the soundness theorem, the plan, the certificate, `"run":
  "compiled"`);
- `receipt.json`: the Lean service's receipt (accepted, scored, the certified count, the bill and the length, the
  axioms, the last-bits test, and the sha256 of every module, which match the files here);
- `offered.json` (the agent's proofs only): the check that the proof uses only what the run showed the agent of the
  Lean library.

All were accepted and scored by the same Lean service: Compact-Proof-Checker at eab37d3, policy
open-lane-policy-v15, cost-v3, knowledge minimal, the checker run by compiled code. Linear max of 4 is the network
`max4-v64-s0`, attention max of 4 is `attn-max4-v64-s0`, both in `models/`.

| Folder | Proof | Checker | Accuracy lower bound | Length (% of brute force) | R |
| --- | --- | --- | ---: | ---: | ---: |
| [`linear-max4/Tree.D`](linear-max4/Tree.D) | agent, round 3 | `Candidate.Tree.D` | 94.39% | 0.264% | 17.6 |
| [`linear-max4/TreeP.D`](linear-max4/TreeP.D) | agent, round 4 | `Candidate.TreeP.D` | 98.47% | 0.615% | 51.4 |
| [`linear-max4/TreeQ.D`](linear-max4/TreeQ.D) | agent, round 5, locked | `Candidate.TreeQ.D` | 99.41% | 0.820% | 82.4 |
| [`linear-max4/pure-convexity`](linear-max4/pure-convexity) | reference: pure convexity | `Candidate.Ref.D` | 71.55% | 0.0051% | 3.5 |
| [`linear-max4/convexity-bad-tokens-fixed`](linear-max4/convexity-bad-tokens-fixed) | reference: convexity, bad tokens fixed | `Candidate.Ref.D` | 99.80% | 0.190% | 527 |
| [`linear-max4/Ref.D`](linear-max4/Ref.D) | reference: best known proof | `Candidate.Ref.D` | 99.80% | 0.0067% | 14,864 |
| [`attn-max4/Checker.D-window-2`](attn-max4/Checker.D-window-2) | agent, round 3, window 2 everywhere | `Candidate.Checker.D` | 99.99% | 0.00563% | 17,755 |
| [`attn-max4/Checker.D-windows-from-plan`](attn-max4/Checker.D-windows-from-plan) | agent, round 3, windows from the plan | `Candidate.Checker.D` | 99.99% | 0.00474% | 21,098 |
| [`attn-max4/Checker2.D`](attn-max4/Checker2.D) | agent, round 4 | `Candidate.Checker2.D` | 99.99% | 0.00387% | 25,845 |
| [`attn-max4/Checker3.D`](attn-max4/Checker3.D) | agent, round 4 | `Candidate.Checker3.D` | 99.99% | 0.00331% | 30,223 |
| [`attn-max4/Checker4.D`](attn-max4/Checker4.D) | agent, round 4 | `Candidate.Checker4.D` | 99.99% | 0.00313% | 31,905 |
| [`attn-max4/Checker5.D`](attn-max4/Checker5.D) | agent, round 5 | `Candidate.Checker5.D` | 99.99% | 0.00305% | 32,820 |
| [`attn-max4/Checker6.D`](attn-max4/Checker6.D) | agent, round 5 | `Candidate.Checker6.D` | 99.99% | 0.00281% | 35,535 |
| [`attn-max4/Checker7.D`](attn-max4/Checker7.D) | agent, round 5, locked | `Candidate.Checker7.D` | 99.99% | 0.00279% | 35,851 |

- The agent's proofs are the submissions of the runs `linear-max4-ptl-1` and `attn-max4-ptl-1`, checked on the
  run's machine (macOS, seatbelt). Their receipts are the service's reply as the run kept it, which adds
  `receipt_path` (where the service wrote the receipt) and `submission` (its number in the round). The reference
  proofs were written by us, not by the agent, and checked in the cloud (Linux, Landlock); the agent has never
  seen them.
- The two convexity proofs are one checker with two plans. It was built from Ref.D's modules and kept the Lean
  name `Candidate.Ref.D`.
- Gross et al.'s cubic and sub-cubic proofs on `attn-max4-v64-s0` are to be added.

To check one again, submit its folder from a clone of Compact-Proof-Checker at eab37d3:

    python3 scripts/accept.py submit <the folder> --repo <this repo> --work <a work folder> \
        --mode landlock --knowledge minimal

with `--mode seatbelt` on macOS. The service only reads the folder; it writes the new receipt to
`<a work folder>/receipts/`. The new receipt should agree with `receipt.json` in the status, the count, the bill,
the length and the modules' digests. The times differ, and on another machine also the isolation and the digests
of the Lean and acceptcheck binaries. Ref.D was checked again this way on 27 November 2026, on the machine that
first checked it: every field agreed except the times.
