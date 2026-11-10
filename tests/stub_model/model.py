import torch


class Tiny(torch.nn.Module):
    """A tiny linear network for the core's tests: one-hot tokens are summed,
    then pass through two linear maps with biases."""

    def __init__(self, n_ctx: int, d_vocab: int, d_hidden: int):
        super().__init__()
        self.n_ctx = n_ctx
        self.inp = torch.nn.Linear(d_vocab, d_hidden, bias=True)
        self.out = torch.nn.Linear(d_hidden, d_vocab, bias=True)

    def forward(self, x):
        return self.out(self.inp(x.sum(dim=1)))
