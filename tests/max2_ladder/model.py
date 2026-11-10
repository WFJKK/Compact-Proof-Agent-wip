import torch as t


class MLP(t.nn.Module):
    def __init__(self, n_ctx: int, d_vocab: int, d_model: int):
        super().__init__()
        self.n_ctx = n_ctx

        self.embedding = t.nn.Linear(d_vocab, d_model, bias=False)
        self.linear = t.nn.Linear(d_model, d_model, bias=False)
        self.unembedding = t.nn.Linear(d_model, d_vocab, bias=False)

    def g(self, x):

        return self.unembedding((self.linear(x)))

    def forward(self, a):

        return self.g(self.embedding(a.sum(dim=1)))
