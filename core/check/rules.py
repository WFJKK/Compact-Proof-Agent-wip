"""The generic rules. These descriptions are shown to the agent verbatim.

Leaf rules apply to one piece of the split tree; global rules are top-level
keys of the proof file. A model folder may add rules of its own in rules.py.
Rules adopted through the rule route (rules/<name>/, core/check/plugins.py)
are leaf rules too; their descriptions come from their own rule.py.
"""

RULES = {
    "split": (
        'Tree node. {"split": {"position": p, "cuts": [c1, ..., ck]}, "children": [...]} divides the '
        "current token range [lo, hi] of position p into [lo, c1-1], [c1, c2-1], ..., [ck, hi]. Cuts "
        "must increase strictly with lo < c1 and ck <= hi; there is one child per piece, in order. The "
        "root covers every input, so the leaves always partition the inputs."
    ),
    "single": (
        'Leaf rule {"leaf": "single"}. The leaf must hold exactly one input. The checker runs the '
        "network on it exactly; it is certified if the label's output is strictly larger than every "
        "other output. In a network with operations beyond linear maps (softmax attention, say), exp and "
        "the division in softmax are enclosed in rational bounds 2**-120 apart, and the label's lower bound "
        "must exceed every other output's upper bound."
    ),
    "interval": (
        'Leaf rule {"leaf": "interval"}. The correct output must be the same for every input in the '
        "leaf (the task checks this). The checker bounds the network over the whole leaf exactly: "
        "one-hot inputs stay symbolic until the first linear map, which sees the exact columns of the "
        "allowed tokens (per coordinate, the minimum and maximum over them); later linear maps act on "
        "boxes (centre and radius). If the last linear map is applied directly to the one-hot inputs "
        "(for example after a contraction), the bound is exact per position: the minimum over that "
        "position's tokens of the label's row minus every other row. The leaf is certified if every "
        "margin's lower bound is positive. With \"approx\": \"<name>\", ranges of more than one token use "
        "that approximation instead of the dense minimum. In a network with operations beyond linear maps, "
        "the input may only be multiplied by a weight matrix, which gives per position the entrywise minimum "
        "and maximum of the allowed tokens' rows; everything after that is interval arithmetic on such "
        "entrywise bounds: sums and products exactly, exp by rational bounds, and each softmax weight between "
        "its own lowest exponential over its lowest plus the others' highest, and the reverse. Bounds of "
        "different entries are treated as independent, so wide boxes lose precision."
    ),
    "token_interval": (
        'Leaf rule {"leaf": "token_interval"}. For networks with operations beyond linear maps (softmax '
        "attention, say). The correct output must be the same for every input in the leaf. Instead of boxing a "
        "position's tokens at the first lookup, the checker keeps every allowed token's values exact: the lookup "
        "x @ W gives, per position, the exact row of W for each allowed token; adding a constant, multiplying by a "
        "constant matrix, an elementwise product with an exact tensor and a sum over a non-position dimension keep "
        "the rows exact per token. Selecting one position, or summing rows weighted by one scalar per position (an "
        "attention weight) over the positions, gives a sum of terms weight * exact row; later constant matrices act "
        "on each term's rows exactly (by linearity), so the rows reach the logits without being boxed. Rows that "
        "depend on their token alone (a lookup, then constants) are computed once per proof and reused by every "
        "leaf. If at most one position holds more than one token, every other value is kept per input too, wherever "
        "an operation has a per-input rule (some have none, such as concatenating, stacking or expanding values, and "
        "box them over the leaf); where every value is kept per input, the bound is the smallest margin over the "
        "leaf's inputs, "
        "exact up to the 2**-120 rounding of exp and softmax, for much less than a single check per input. If "
        "several positions vary, values that mix them (attention "
        "scores, softmax weights) become entrywise intervals, and each term is bounded over its own tokens and "
        "weight interval separately, which is sound but looser. Only for networks beyond linear maps."
    ),
    "skip": 'Leaf rule {"leaf": "skip"}. Certifies nothing and costs nothing.',
    "contract": (
        'Global rule. "contract": [{"name": N, "chain": [a, b, ...]}] replaces consecutive linear maps '
        "a, then b, ... (each feeding only the next) by their exact product, computed once in the "
        "cheapest order and charged once. Later leaves use the product. Names are the network graph's "
        "node names (for an nn.Linear submodule, its attribute name). Only for networks built from "
        "nn.Linear maps, sums and additions."
    ),
    "symmetry": (
        'Global rule. "symmetry": true is accepted only if the network uses its input only through a '
        "sum over positions, so its output is the same for every reordering of the positions, and the "
        "task declares that reordering never changes the correct output. Then "
        "each accepted leaf certifies the inputs in it whose tokens are in non-decreasing order, "
        "together with all their reorderings. Inputs in a leaf that are not in order count nothing "
        "there; they are certified through their sorted version wherever that lies. Only for networks "
        "built from nn.Linear maps, sums and additions."
    ),
    "approximate": (
        'Global rule. "approximate": [{"name": P, "of": M, "form": ...}] gives a simpler matrix P for '
        "linear map M (usually a contraction), in one of three forms: dense (\"values\": the full "
        'matrix), low_rank ("left": outputs x r, "right": r x inputs) or row_segments ("rows": for '
        "each output row, [start, end, value] triples covering every column in order). The checker "
        "computes eps = max |M - P| exactly, at 2 per entry (row_segments: 3 per entry plus 2 per "
        "segment, for a column index), plus 1 per number read from P's form. Interval leaves with \"approx\": P "
        "then bound the minimum over a position's tokens t of M[l,t] - M[j,t] by the same minimum for P, "
        "minus 2 eps, computed from P's form: dense costs 2 per token per output (like the exact check); "
        "row_segments costs 2 per merge step of the two rows' segments plus 2 per output to locate its "
        "segments (so it pays only where segments are long); low_rank costs 2r per token plus 3r per "
        "output; each then costs 1 per output for the eps. Only for networks built from nn.Linear maps, "
        "sums and additions."
    ),
}

GENERIC_RULES = ("single", "interval", "token_interval", "skip", "contract", "symmetry", "approximate")
LEAF_RULES = ("single", "interval", "token_interval", "skip")
NUMBERS = (
    "Numbers in proof files are dyadic rationals (denominator a power of two), like the float32 weights "
    "they describe: integers, decimals such as \"1.25\", fractions such as \"-3/4\", or finite floats; all are "
    "read exactly. No exponent notation (\"1e-9\") and no other denominators (\"1/3\"); keep them within a few "
    "hundred bits."
)


def adopted_rules() -> dict:
    """Rules adopted through the rule route (core/check/plugins.py), by name."""
    from .plugins import adopted

    return adopted()


def generic_rules() -> tuple:
    """The rules a run may name: the generic ones and the adopted ones."""
    return GENERIC_RULES + tuple(sorted(adopted_rules()))


def leaf_rules() -> tuple:
    return LEAF_RULES + tuple(sorted(adopted_rules()))


def describe(rule_names=GENERIC_RULES) -> str:
    extra = adopted_rules()
    lines = [f"- split: {RULES['split']}"]
    for name in rule_names:
        if name in RULES:
            lines.append(f"- {name}: {RULES[name]}")
        elif name in extra:
            lines.append(f"- {name}: {extra[name].description}")
    lines.append(NUMBERS)
    return "\n".join(lines)
