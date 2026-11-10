import torch as t


class FourHeads(t.nn.Module):
    """An attention-only transformer read at the last position, with four heads that score the positions in
    three ways, built so that the rule route's audit reaches token_convex version 2's paths that the attention
    model folders do not (found by the adversarial review of 19 October 2026):

    - head 1's query is (last @ WQ1 + last @ WQ2) * s: two terms at the query position, and a learned scale
      that can be negative; its scores depend on two tokens (the key's and the query's);
    - head 2 scores the positions with a fixed vector (scores exact per token);
    - head 3 scores them with a fixed vector through a matrix-vector product (scores as a box);
    - the last position enters the output at weight -0.5 (a query-position term with a negative weight);
    - two values computed from head 1's query leave the token rules: its square, summed, and its product with
      the keys summed over the positions;
    - head 4 has a query of its own from the last position (two softmaxes with scores per pair of tokens in one
      decision), and its scores also leave the token rules (summed over the positions);
    - the first position enters the output through a matrix (a term outside the softmaxes at a position other
      than the query's: a constant when that position holds one token, else a term bounded over its tokens).

    No trained zoo: the audit uses it with random weights."""

    def __init__(self, n_ctx: int, d_vocab: int, d_model: int):
        super().__init__()
        self.n_ctx = n_ctx

        def init(*shape):
            fan_in = shape[0] if shape else 1
            return t.nn.Parameter((t.rand(tuple(shape)) * 2 - 1) * fan_in**-0.5)

        d = d_model
        self.E, self.P = init(d_vocab, d), init(n_ctx, d)
        self.WQ1, self.WQ2, self.s = init(d, d), init(d, d), init()
        self.WK1, self.WV1, self.O1 = init(d, d), init(d, d), init(d, d)
        self.WK2, self.WV2, self.O2, self.c2 = init(d, d), init(d, d), init(d, d), init(d)
        self.WK3, self.WV3, self.O3, self.c3 = init(d, d), init(d, d), init(d, d), init(d)
        self.WQ4, self.WK4, self.WV4, self.O4 = init(d, d), init(d, d), init(d, d), init(d, d)
        self.F, self.R, self.U = init(d, d), init(1, d), init(d, d_vocab)

    def forward(self, x):
        residual = x @ self.E + self.P
        last = residual[:, self.n_ctx - 1]
        q = (last @ self.WQ1 + last @ self.WQ2) * self.s
        keys1 = residual @ self.WK1
        a1 = t.softmax(t.sum(keys1 * q.unsqueeze(1), dim=2), dim=1)
        h1 = t.sum(a1.unsqueeze(2) * (residual @ self.WV1), dim=1)
        a2 = t.softmax(t.sum((residual @ self.WK2) * self.c2, dim=2), dim=1)
        h2 = t.sum(a2.unsqueeze(2) * (residual @ self.WV2), dim=1)
        a3 = t.softmax((residual @ self.WK3) @ self.c3, dim=1)
        h3 = t.sum(a3.unsqueeze(2) * (residual @ self.WV3), dim=1)
        q4 = last @ self.WQ4
        scores4 = t.sum((residual @ self.WK4) * q4.unsqueeze(1), dim=2)
        a4 = t.softmax(scores4, dim=1)
        h4 = t.sum(a4.unsqueeze(2) * (residual @ self.WV4), dim=1)
        g = t.sum(q.unsqueeze(1) * q.unsqueeze(1), dim=2) + t.sum(t.sum(keys1 * q.unsqueeze(1), dim=1), dim=1).unsqueeze(1)
        g = g + t.sum(scores4, dim=1).unsqueeze(1)
        out = h1 @ self.O1 + h2 @ self.O2 + h3 @ self.O3 + h4 @ self.O4 + last * -0.5 + residual[:, 0] @ self.F + g @ self.R
        return out @ self.U
