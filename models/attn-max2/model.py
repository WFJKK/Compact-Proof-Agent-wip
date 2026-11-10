import torch as t


class OneHeadTransformer(t.nn.Module):
    """A one-layer, one-head, attention-only transformer with no biases and learned
    positional embeddings, read at the last position.

    Tokens arrive one-hot, shape (batch, n_ctx, d_vocab). Each position's residual is its
    token embedding plus its positional embedding. The last position attends over all
    n_ctx positions (causal attention reads everything at the last position) with the
    usual scale 1/sqrt(d_head), adds the head's output to its residual, and the
    unembedding gives one logit per token. The parameters are E, P, Q, K, V, O
    and U, initialised like torch's default linear layers.
    """

    def __init__(self, n_ctx: int, d_vocab: int, d_model: int, d_head: int):
        super().__init__()
        self.n_ctx = n_ctx
        self.scale = float(d_head) ** -0.5

        def init(*shape):
            fan_in = shape[0]
            return t.nn.Parameter((t.rand(*shape) * 2 - 1) * fan_in**-0.5)

        self.E = init(d_vocab, d_model)
        self.P = init(n_ctx, d_model)
        self.WQ = init(d_model, d_head)
        self.WK = init(d_model, d_head)
        self.WV = init(d_model, d_head)
        self.WO = init(d_head, d_model)
        self.U = init(d_model, d_vocab)

    def forward(self, x):
        residual = x @ self.E + self.P  # (batch, n_ctx, d_model)
        last = residual[:, self.n_ctx - 1]  # (batch, d_model): the position whose output is read
        q = (last @ self.WQ) * self.scale  # (batch, d_head)
        keys = residual @ self.WK  # (batch, n_ctx, d_head)
        values = residual @ self.WV  # (batch, n_ctx, d_head)
        scores = t.sum(keys * q.unsqueeze(1), dim=2)  # (batch, n_ctx)
        weights = t.softmax(scores, dim=1)
        head = t.sum(weights.unsqueeze(2) * values, dim=1)  # (batch, d_head)
        out = last + head @ self.WO
        return out @ self.U
