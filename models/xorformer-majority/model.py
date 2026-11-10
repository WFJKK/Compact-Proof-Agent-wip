import torch as t


class AttentionOnly(t.nn.Module):
    """One-layer attention-only transformer on n bits and a query token "=" (xorformer, model.md).

    The parameters, their initialisation and the function are those of xorformer's
    TorchAttentionCore. Two differences of form only: the bits arrive one-hot, shape
    (batch, n_bits, 2), so (1 - x) e_0 + x e_1 is written x @ token_embeddings[0:2]; and the
    output is the pair of logits (0, S) with S = readout . r - threshold, so the predicted
    bit is 1 exactly when S > 0, and cross-entropy on (0, S) is xorformer's BCE on S.
    """

    def __init__(self, n_bits: int, heads: int, d_model: int, d_head: int):
        super().__init__()
        self.n_bits = n_bits
        self.heads = heads
        scale = 0.2
        self.token_embeddings = t.nn.Parameter(t.randn(3, d_model) * scale)  # e_0, e_1, e_=
        self.positional_embeddings = t.nn.Parameter(t.randn(n_bits + 1, d_model) * scale)
        self.WQ = t.nn.Parameter(t.randn(heads, d_head, d_model) * scale)
        self.WK = t.nn.Parameter(t.randn(heads, d_head, d_model) * scale)
        self.WV = t.nn.Parameter(t.randn(heads, d_head, d_model) * scale)
        self.WO = t.nn.Parameter(t.randn(heads, d_model, d_head) * scale)
        self.readout = t.nn.Parameter(t.randn(d_model) * scale)
        self.threshold = t.nn.Parameter(t.zeros(()))

    def forward(self, x):
        n = self.n_bits
        bits = x @ self.token_embeddings[0:2] + self.positional_embeddings[0:n]  # (batch, n, d_model)
        query = self.token_embeddings[2] + self.positional_embeddings[n]  # (d_model,), the same for every input
        positions = t.cat([bits, query.expand(x.shape[0], 1, query.shape[0])], dim=1)  # (batch, n + 1, d_model)
        residual = query
        for h in range(self.heads):
            q = self.WQ[h] @ query
            keys = positions @ self.WK[h].T
            values = positions @ self.WV[h].T
            weights = t.softmax(keys @ q, dim=1)  # attention of the query token over all n + 1 positions
            head = t.sum(weights.unsqueeze(-1) * values, dim=1)
            residual = residual + head @ self.WO[h].T
        score = residual @ self.readout - self.threshold
        return t.stack([t.zeros_like(score), score], dim=1)
