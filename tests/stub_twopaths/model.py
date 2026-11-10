import torch as t


class TwoPaths(t.nn.Module):
    """The one-head attention-only transformer of the attention model folders, with two things they do not
    have: the head's output mapped by two matrices and added (head @ A + head @ B), and a residual linear map
    h + h @ W before the unembedding. Each makes one Mix carry two terms with the same origin and position but
    different rows, which a memo keyed only by (node, origin, position) confuses (found by the rule route's
    adversarial review, 19 October 2026). No trained zoo: the audit uses it with random weights."""

    def __init__(self, n_ctx: int, d_vocab: int, d_model: int):
        super().__init__()
        self.n_ctx = n_ctx

        def init(*shape):
            return t.nn.Parameter((t.rand(*shape) * 2 - 1) * shape[0] ** -0.5)

        self.E, self.P = init(d_vocab, d_model), init(n_ctx, d_model)
        self.WQ, self.WK, self.WV = init(d_model, d_model), init(d_model, d_model), init(d_model, d_model)
        self.A, self.B, self.W, self.U = init(d_model, d_model), init(d_model, d_model), init(d_model, d_model), init(d_model, d_vocab)

    def forward(self, x):
        residual = x @ self.E + self.P
        last = residual[:, self.n_ctx - 1]
        q = last @ self.WQ
        keys = residual @ self.WK
        values = residual @ self.WV
        weights = t.softmax(t.sum(keys * q.unsqueeze(1), dim=2), dim=1)
        head = t.sum(weights.unsqueeze(2) * values, dim=1)
        h = last + (head @ self.A + head @ self.B)
        h = h + h @ self.W
        return h @ self.U
