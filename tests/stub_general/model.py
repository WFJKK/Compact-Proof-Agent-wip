import torch as t


class TinyAttention(t.nn.Module):
    """A tiny network beyond linear maps for the checker's tests and the rule route's audit. It uses what the
    attention models here do not: nn.Linear layers with biases, on the one-hot input and on the residual stream,
    a parameter vector as the query, and a bias on the output."""

    def __init__(self, n_ctx: int, d_vocab: int, d_model: int):
        super().__init__()
        self.n_ctx = n_ctx
        self.embed = t.nn.Linear(d_vocab, d_model, bias=True)
        self.query = t.nn.Parameter(t.randn(d_model))
        self.value = t.nn.Linear(d_model, d_model, bias=True)
        self.unembed = t.nn.Linear(d_model, d_vocab, bias=True)

    def forward(self, x):
        h = self.embed(x)  # (batch, n_ctx, d_model)
        scores = t.sum(h * self.query, dim=2)  # (batch, n_ctx)
        weights = t.softmax(scores, dim=1)
        head = t.sum(weights.unsqueeze(2) * self.value(h), dim=1)  # (batch, d_model)
        return self.unembed(h[:, self.n_ctx - 1] + head)
