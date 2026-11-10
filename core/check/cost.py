"""Cost model cost-v4: a proof's length is the work the checker does on numbers to check it.

Each operation on exact numbers (one multiply-add, addition, subtraction or
comparison) counts 1. Specifically:

- extract: converting the weights exactly, 1 per parameter (this is E, the
  minimum any proof pays).
- read: 1 per number the proof supplies for the checker to compute with, which
  are the entries of its approximations: every value of a dense one, every
  entry of a low_rank one's left and right, and the start, end and value of
  every segment of a row_segments one.
- contract: multiplying an a x b by a b x c matrix costs a*b*c; pushing a
  bias through costs one matrix-vector product.
- approximate: 2 per entry of the approximated matrix (difference and
  comparison), plus a*r*c to multiply out low-rank factors; row_segments also
  costs 1 per entry and 2 per segment, for the column index that locates a
  range's segments. An interval range bounded through an approximation costs,
  for dense, 2 per token per output; for low_rank, 2r per token plus 3r per
  output; for row_segments, 2 per merge step of the two rows' segments (a
  difference and a comparison, the same as a dense range per token, so it pays
  only where segments are long) plus 2 per output to locate its segments; and
  then 1 per output to subtract the error.
- single: running the network on one input. A linear map applied to a one-hot
  input costs its output size per position (a column lookup); applied to a
  vector, in*out; a bias, a sum or an addition costs its output size; the
  final comparison of the label's output with every other output costs
  (outputs - 1).
- interval: like single, but on bounds over a set of inputs. A linear map
  applied to a set of one-hot tokens costs 2*out per token in the set (minimum
  and maximum); applied to a box it costs 2*in*out (centre and radius). For
  the output, a linear map applied directly to one-hot sets costs
  2*outputs per token in each position's set; with an approximation it costs
  what the approximation's form needs (see the approximate rule); applied to a
  box it costs 3*in*outputs.

The plan costs nothing: the split tree (its positions, cuts and leaf rules),
the contraction chains, the symmetry flag, names and notes. Walking the tree
and counting the inputs a leaf certifies (under symmetry too) is bookkeeping
with whole numbers, not work on the network's numbers. The proof file's size is
capped instead: its numbers and strings, and its tree's nodes, are limited in
proportion to the number of inputs.

Networks with operations beyond linear maps (softmax attention, say) are
evaluated by core.check.general and counted the same way, operation by
operation. single, per input: 1 per multiply-add of a matrix product (a one-hot
input times a weight matrix is a lookup: its output size per position), 1 per
entry of a sum, difference, product or exp, (size - 1) per entry of a sum over
a dimension, 3 per entry of a softmax, and (outputs - 1) for the final
comparison. interval: 2 for each of these (lower and upper bound), and the
input lookup costs 2*out per allowed token at a position (out for a single
token). The parts that do not depend on the input are computed once per proof
and charged to extract, which then also counts their operations.

token_interval leaves (networks beyond linear maps) count the same operations
on the values they keep. tables: a row that depends on its token alone (the
lookup, then constants) is computed once per proof, whichever leaf needs it
first, and reused: a lookup costs its output size per token, a product with a
constant matrix in*out per row, adding or multiplying by a constant the row's
size, a sum over a dimension (size - 1) per entry of the result. token_interval:
the rest, per leaf: the same counts per row, or per input where a value is kept
per input (when at most one position varies), doubled for interval values; a
product of a constant matrix with a term's constant part in*out per entry (its
size, if that part is zero); boxing rows into entrywise bounds 2 per entry;
3 per entry of a softmax and 1 of an exp, doubled; and the decision: per term
and other output, 3 per input with an exact weight or 5 with an interval weight
(one position varying), or 3 per token plus 8 (several), then 1 per input and
other output for the minimum, and (outputs - 1) for the constant part.

E is the extract cost. B is the length of the brute-force proof, which checks
every input with the single rule and nothing else: E plus the number of inputs
times the single rule's charge.

Rules adopted through the rule route (rules/<name>/, core/check/plugins.py)
charge their per-leaf work to a category of their own, named in their rule.py,
and work they share across leaves to tables; their description, shown to the
agent, says what they charge. A proof without their leaves has the same length
as before, so adopting a rule changes no earlier number.
"""

from __future__ import annotations

from collections import defaultdict

VERSION = "cost-v4"
# cost-v4 (9 Nov 2026) stops charging the plan: the tree (1 per node), the symmetry count (1 per accepted
# leaf) and reading the plan (1 per number, string or boolean of the proof file outside its approximations'
# numbers). read keeps the approximations' numbers, which cost-v3 counted the same way. Nothing else
# changes, so a proof is shorter by its tree's nodes, its plan's scalars and, with symmetry, its accepted
# leaves; E is unchanged and B is shorter by the brute-force tree's nodes and scalars and the file's two
# strings. The open lane never charged the plan (a checker's code is capped, not charged; its operations on
# numbers are charged at these prices), so the same proof now costs the same in both lanes: brute force on
# the tiny max-of-2 network is 4,112 in both (4,323 here under cost-v3).
# cost-v3 (16 Oct 2026) adds the token_interval rule and its two categories, tables and token_interval.
# Nothing else changes: a proof without token_interval leaves has the same length as under cost-v2, and E
# and B are unchanged.
# cost-v2 (13 Oct 2026) differs from cost-v1 in the approximate rule only: a row_segments merge step
# costs 2, not 1 (under cost-v1 an exact approximation with one segment per entry made the dense range
# check look half as long while doing the same work; an agent found and used this), locating a row's
# segments is charged (two lookups in an index that costs 1 per entry and 2 per segment to build),
# and the error subtraction and the low-rank differences are charged. E and B are unchanged.

CATEGORIES = ("extract", "read", "contract", "approximate", "single", "interval", "tables", "token_interval")
# The categories of adopted rules (core/check/plugins.py adds them when it loads a rule).
EXTRA_CATEGORIES: set[str] = set()


class Counter:
    def __init__(self):
        self.by_rule: dict[str, int] = defaultdict(int)

    def add(self, category: str, n) -> None:
        if category not in CATEGORIES and category not in EXTRA_CATEGORIES:
            raise ValueError(f"unknown cost category {category!r}")
        n = int(n)
        if n < 0:
            raise ValueError("costs are never negative")
        self.by_rule[category] += n

    @property
    def total(self) -> int:
        return int(sum(self.by_rule.values()))

    def as_dict(self) -> dict:
        return {k: int(v) for k, v in sorted(self.by_rule.items()) if v}


def count_scalars(obj, limit: int | None = None) -> int:
    """Numbers, strings and booleans in a JSON value (iterative; stops past limit)."""
    n = 0
    stack = [obj]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            stack.extend(x.values())
        elif isinstance(x, list):
            stack.extend(x)
        elif x is not None:
            n += 1
            if limit is not None and n > limit:
                return n
    return n
