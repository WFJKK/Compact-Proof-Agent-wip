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

While we have given the Pareto frontier above, we now want to evaluate the proofs in more detail. We want to
understand in detail what the proofs understood about the structure present in these networks and what they
used. Moreover, we want to distinguish between mere inference optimisation and understanding that is
"mechanistic". Most importantly, we want to compare what the agent handed in as a proof with the best known
proof, which mixes ideas from Louis Jaburi's tutorial notebook
([LouisYRYJ/Proof_based_approach_tutorial](https://github.com/LouisYRYJ/Proof_based_approach_tutorial)) with
ideas of the author, worked out with Claude. There is also a distinction to make between the ideas the agent had,
which we read from the run's records (the notes it kept in its research folder in every round, the candidate
proofs it described there with costs estimated in Python, and the transcripts of its sessions), and the ones the
agent actually submitted in Lean. All the proofs the agent handed in in the 5 rounds are based on the same three
ideas:

**1. Linearity.** The embedding adds up the one-hot vectors of the four tokens x = (x₁, x₂, x₃, x₄) and there is
no nonlinearity, so the score of each output j is a sum of four entries of one 64 × 64 table, which the checker
computes once:

$$s_j(x) = \sum_{i=1}^{4} M_{j, x_i}, \qquad M = ULE$$

The network answers the output with the highest score.

**2. Boxes.** Let m be the largest token of x. The network is right on x when m beats every other answer j, that
is, when all 63 margins are positive:

$$\mathrm{margin}_j(x) = s_m(x) - s_j(x) = \sum_{i=1}^{4} D_j(x_i)$$

where $D_j(t) = M_{m,t} - M_{j,t}$ says how much a token t, in any position, helps m against j. For the input
(5, 35, 40, 38) the score of 40 is 84.01 and its closest rival, 41, scores 73.73: a margin of 10.28.

A box is a set of inputs given by a set of allowed tokens for each position,
$T_1 \times T_2 \times T_3 \times T_4$. For example, tokens 0 to 7 in position 1, 33 to 39 in position 2, 40 in
position 3 and 38 to 39 in position 4 give a box of 112 inputs. One position holds m, the positions before it allow
only tokens below m and those after it tokens up to m, so every input in the box has largest token m. Since each
part of the margin depends on one position only, the worst input in the box takes the worst token at each position
separately:

$$\min_{x \in \mathrm{box}} \mathrm{margin}_j(x) = \sum_{i=1}^{4} \min_{t \in T_i} D_j(t)$$

In the example box the worst case against 41, the tightest of the 63, is 0.08 − 2.74 + 9.35 − 2.74 = 3.94. All 63
worst cases are positive, so all 112 inputs are right; if one were not positive, some input in the box would not be
right, so the test is exact. It saves work because the box holds the product of the numbers of allowed tokens (8 ×
7 × 1 × 2 = 112 inputs), while the test only looks at their sum (8 + 7 + 1 + 2 = 18 values of $D_j$ for each
competitor). The same set of tokens appears in many boxes, so the checker computes each set's minimum once; a box
test is then four stored minima added and compared with zero for each competitor, about as much work as checking a
single input.

**3. A tree of boxes.** All 16.8 million inputs are split into boxes: by the largest token m, by the first
position that holds m, and by cutting the tokens of every other position into ranges, finely near m, where $D_j$
changes quickly and the network's mistakes are, and coarsely far below m, where $D_j$ hardly changes. Every
combination of one range per position is one box. TreeQ.D has about 243,000 boxes, 69 inputs each on average.

The three proofs differ only in where the tree cuts: by a fixed rule (Tree.D), by a list of cuts for each m
(TreeP.D), and by finer lists from a search on the weights (TreeQ.D).

### Experiment 2: Attention

To be written.
