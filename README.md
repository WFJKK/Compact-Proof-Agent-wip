# Compact-Proof-Agent-wip

A pipeline in which an agent hill-climbs towards shorter compact proofs of the accuracy of small trained
networks; in the open lane every proof is checked by Lean. The design is in `docs/SPEC.md` and
`docs/OPEN_LANE.md`.

## Big picture

To be written.

### Pareto Frontier of a compact proof

To be written.

## Reward function

The score of a run is

$$R = \frac{B}{\mathrm{length} + c \cdot (\mathrm{right} - \mathrm{certified})}$$

- B: the cost of brute force, one exact forward pass on every input at the cost rule's prices, plus one per
  weight.
- length: the cost of checking the proof, the operations its checker does on the network's weights, plus one
  per weight and one per number in its certificate. The checker's code and its plan are not charged; their
  size is capped instead.
- c: the cost of brute force on one input, one forward pass.
- right: the number of inputs the network answers correctly; certified: the number of them the proof
  certifies.

R is the value of the run's best proof and never below 1: brute force alone scores 1. A proof counts only if
the Lean service accepts it.

## Agentic setup / Auto-research

To be written.

## Results

### Experiment 1: Linear

#### Linear max of 4

##### Architecture and training

- Sizes: 64 tokens, 4 slots per input, width 8.
- Weights: three matrices and no biases: an embedding (8 × 64), a hidden matrix (8 × 8) and an unembedding
  (64 × 8). The embedding takes the sum of the four tokens' one-hot vectors, and there is no nonlinearity.
- Task: output the largest of the four tokens.
- Inputs: four tokens, each uniformly random from 0 to 63, drawn fresh at every step.
- Loss and optimiser: cross-entropy with AdamW (learning rate 0.001, betas 0.9 and 0.999, weight decay 0.01),
  batch 1,024, float32.
- Starting weights: uniform in ±1/√k, where k is the number of inputs to the matrix (64 for the embedding, 8
  for the other two).
- Stopping: a fixed 80,000 steps, where the accuracy had levelled off (seed 0 on 200,000 sampled inputs: 99.77%
  at 40,000 steps, 99.81% at 80,000).
- Networks: ten, from seeds 0 to 9, about 3 minutes each. They give the largest token on 99.78% to 99.84% of
  all 64⁴ inputs. The run is on seed 0, which is right on 16,743,886 of the 16,777,216 inputs (99.80%).

##### Price, runtime, agent, internet, inference

- Price: $37.42 for the run (one discovery round, four proof rounds and the reading of the checker), $35.38
  for the six scaling sessions after it.
- Runtime: 2 h 34 min for the run's six sessions, 1 h 29 min for the six scaling sessions. Both include the
  Lean service's checks, which run inside the sessions.
- Agent: Claude Fable 5.1 (`claude-fable-5-1`), thinking effort extra high (Claude Code's `--effort xhigh`).
- Agent tools: `run_python` (runs Python in a sandbox, with the network's weights), `lean_check` (compiles a
  Lean module against the network's protected modules), `read_file` and `search_library` (read the workspace
  and search the Lean library the run offers), `submit_candidate` (hands a checker and its soundness proof to
  the Lean service, which checks and scores it), and in the proof rounds `research_write` and
  `research_list` (a research folder kept across sessions).
- Hyperparameters: money cap $30 a round and $180 a run; 5 rounds (1 discovery, 4 proof) of at most 60
  minutes; per session 60 Lean compiles, 40 Python runs and 4 submissions. The scaling sessions had 30 to 90
  minutes and $10 to $30 each.
- Internet: not used (Claude Code's own tools are switched off, so there are no web tools, and the agent's
  Python runs with the network blocked).
- Inference: not counted (the pipeline does not record how often the agent's Python ran the network).

##### Scores

On seed 0, from the Lean service's receipts. For this network B = 11,257,513,024 and c = 671, and the network
is right on 16,743,886 inputs. The table starts at round 3 because that is the first round in which the agent
submitted an actual compact proof. The previous rounds were used for discovery, "proofs" in Python and general
lemmas in Lean, which were useful for the proofs.

| Proof | Round | Accuracy lower bound | Length (% of brute force) | B / length | R |
| --- | ---: | ---: | ---: | ---: | ---: |
| Brute force (the network itself) | | 99.80% (16,743,886 inputs) | 100% (11,257,513,024) | 1 | 1 |
| Tree.D | 3 | 94.39% (15,836,170 inputs) | 0.264% (29,705,220) | 379 | 17.6 |
| TreeP.D | 4 | 98.47% (16,520,886 inputs) | 0.615% (69,289,128) | 162 | 51.4 |
| TreeQ.D, locked | 5 | 99.41% (16,677,894 inputs) | 0.820% (92,356,844) | 122 | 82.4 |

##### Evaluation

For each proof: how it works, whether it is a proof idea or only inference optimisation (caching or memorising
parts of the network's computation instead of explaining it), and whether it is mechanistic (uses how the
network computes its answer). The three proofs share one argument and differ only in how finely they cut.

- Linearity (all three). The embedding sums the one-hot vectors and there is no nonlinearity, so each logit is a
  sum of one entry per position of the 64 × 64 table M = ULE, computed once (36,864 operations). This is caching,
  so inference optimisation, as are the tables of each competitor's minimum on each interval that the checker
  builds for each m. Both are computed from the weights inside the checker and counted in its length, and the
  linearity comes from the architecture, not from training.
- Boxes (all three). For an input with largest token m, the margin against another answer j is a sum of one term
  per position, D_j(t) = M[m,t] − M[j,t]. Over a box (a range of tokens per position, the largest fixed at m)
  the smallest margin is the sum of the per-position minima, so one test against the 63 other answers certifies
  every input in the box. This is a proof idea, not inference optimisation: TreeQ.D covers the 16.8 million
  inputs with about 243,000 boxes, about 69 inputs per test without running the network on any of them, and this
  is where its compression to 0.82% of brute force comes from. The cost grows like V³ against brute force's V⁵
  (proved for Tree.D, and for the other two when the cuts per level stay bounded). It is a standard tool
  (interval bounds with branch and bound), not new mathematics.
- Cuts (where they differ). Tree.D cuts each position's range at 1, 2, 4, 8, 16 and 32 below m, the same for every
  m, by a fixed rule. TreeP.D has its own cuts for each m (128 numbers), TreeQ.D finer ones from a greedy search
  on the weights (491 numbers). TreeP.D and TreeQ.D add no idea to Tree.D: their plans are fitted to this seed
  and mark where the margins are tight, not why, so the climb from R = 17.6 to 82.4 is fitting rather than
  explaining. Whether a plan carries over to another seed has not been tested.
- Memorising: none found. A language model's reading of the checker found no numbers of the network written
  into it; the count does not change when the lowest bits of the weights change; the plan (1,539 bits) is too
  small to hold the weights (26,138 bits); and soundness is proved for every plan, so no plan can make the
  checker over-count.
- Mechanistic: partly. Beyond the architecture the proofs use one learned property: the margins are tight only
  when other tokens are close to m, so the boxes can be coarse far below m and must be fine near it. The plan
  marks where, but it was found by search, and the proofs do not say why the network outputs the largest token.
  They also test all 63 other answers in every box and treat reorderings of an input separately.
- Not built: the agent's candidates c001 and c002 add the symmetry of the input (boxes of multisets, since order
  does not matter) and check fewer competitors, at an estimated 0.43 and 3.24 million operations; c001's plan was
  too large, and c002 needs a proof that counts the reorderings, which the agent did not write. Convexity (pure
  inputs such as (a, a, a, m) bound the others) appears nowhere in the agent's notes.

### Experiment 2: Attention

To be written.
