# Inventory: the max-of-2 notebook

Source: `proof_public.ipynb` in [LouisYRYJ/Proof_based_approach_tutorial](https://github.com/LouisYRYJ/Proof_based_approach_tutorial/blob/master/proof_public.ipynb), branch `master`, read on 9 October 2026.

## Model

- `MLP(params)` has three linear maps without biases: `embedding` (d_vocab to d_model), `linear` (d_model to d_model) and `unembedding` (d_model to d_vocab).
- `forward(a)` is `unembedding(linear(embedding(a.sum(dim=1))))`, written through a helper method `g(x) = unembedding(linear(x))`.
- Input: one-hot tokens of shape (batch, n_ctx, d_vocab). Output: logits over d_vocab.
- Consequences used later:
    - The network is linear in the summed one-hot input. Its logits are M(e_t1 + e_t2), where M = U W E is a d_vocab × d_vocab matrix of rank at most d_model.
    - The output depends on the input only through the sum, so it is symmetric in the two tokens.

## Task and data

- Task: given n_ctx = 2 tokens in {0, ..., d_vocab - 1}, output the larger one.
- `TrainingDataMax.__getitem__` ignores its index and draws a fresh random pair on every call.
- `TrainingDataMax.__init__` calls `set_seed(57)`, which resets the global random state whenever a dataset object is built. `train()` builds three of them.
- `train()` uses `random_split` to keep 5% of d_vocab² items per epoch. Since items are drawn fresh, this only sets the number of random samples per epoch; the notebook itself notes this.

## Training

- Settings: n_ctx 2, d_vocab 2048, d_model 128, 2 epochs, batch size 1024, 5% of d_vocab² samples per epoch, AdamW with learning rate 0.001 and default weight decay, cross-entropy loss.
- That comes to about 410 optimizer steps. The last printed training losses are 0.21 to 0.27.
- Section 3 repeats this for max-of-3 with d_vocab 256.

## Proof strategies

What is proved: an upper bound on the expected cross-entropy loss over all inputs. Length is measured as wall-clock time.

| Strategy | Idea | Result | Time (d_vocab 2048) |
| --- | --- | --- | --- |
| Brute force | average the loss over all d_vocab² inputs | exact | 102 s |
| Symmetry | f(t1, t2) = f(t2, t1): evaluate pairs with t1 < t2 once, weighted by 2, plus the diagonal | exact | 65 s |
| Convexity | the loss is convex in the summed embedding, so a mixed input is bounded by doubled inputs | loose upper bound; evaluates only the d_vocab doubled inputs | 11 s |

Section 3 applies the convexity idea to max-of-3. Section 4, "Implementing the cubic proof", is a heading with no content.

## Mismatches with the spec, and proposed fixes

| # | Notebook | Spec | Proposed fix |
| --- | --- | --- | --- |
| 1 | Bounds the loss | Certifies accuracy | Accuracy first, as the spec says. A loss bound needs rigorous bounds on exp and log; add it later as a second property. |
| 2 | Length is wall-clock time | Length is counted operations | Use the operation count of `cost-v1`; report wall-clock time only as information. |
| 3 | 5% of d_vocab² samples per epoch, which is one or two optimizer steps at small vocabularies | Training settings in the model's config | The config sets a number of optimizer steps, each on a fresh uniform batch. The notebook's optimizer, learning rate and batch size are the defaults. |
| 4 | `set_seed(57)` inside the dataset makes every run see the same data | 10 seeds per size setting | The trainer seeds parameter initialisation and data sampling from each network's own seed. |
| 5 | d_vocab 2048, d_model 128 | Sizes proposed in Step 2 | Exact checking of 2048² pairs × 2048 outputs is too slow for an inner loop. Propose smaller sizes with the same property, a vocabulary well above the hidden width, and confirm them with E and B in Step 3. |
| 6 | `MLP` takes a `Parameters` object | Sizes as constructor arguments | `MLP(n_ctx, d_vocab, d_model)`, body unchanged. |
| 7 | No accuracy is reported | Real accuracy per network in the manifest | The trainer measures it by float brute force over all inputs. |
| 8 | Convexity proof of the loss | Not among the accuracy baselines | Not applicable to accuracy as written; left out of the baselines. |

## Not covered by the spec

- The max-of-3 variant (section 3). A second size setting with n_ctx 3 is possible later through `config.yaml`, since nothing in the core assumes two positions.
- With d_model below d_vocab, M has rank at most d_model and cannot represent the ideal "larger token wins" matrix exactly, so some networks may stay below 100% accuracy. Step 2 measures this.
