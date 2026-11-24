"""`python3 -m core.loop scale --run <run folder>`: the scaling proofs, as a command that follows a finished run
(core/open_lane/after_run.py says what such a command is made of)."""

from __future__ import annotations

from ..stages import StageError
from . import later_pipeline, show, steps
from .plan import ScalingError

NAME = "scale"
HELP = ("after a finished open-lane run: the scaling proofs, the cost of its proofs in each size of its network as "
        "theorems (the checker with its sizes as parameters, then a session per size; core/open_lane/scaling)")
Error = (ScalingError, StageError)
changed_since = later_pipeline.accept
status_lines = show.status_lines
report_lines = show.report_lines


def add_arguments(parser) -> None:
    """The command's own arguments (the loop driver adds --run and --budget-usd). A step is `general` or the
    symbol of a size of the run's network (`sizes` with --again: every size); which symbols there are is known
    only with the run, so they are checked when the command runs."""
    parser.add_argument("--only", nargs="+", metavar="STEP", help="run only these steps now; they must be the next ones in order")
    parser.add_argument("--again", nargs="*", default=None, metavar="STEP",
                        help="once the steps are done: add a further session for each of these steps (none named: for each "
                             "configured step) and run them; each starts from all that was accepted and from what the "
                             "earlier sessions left")
    parser.add_argument("--minutes", type=float, help="with --again: the session time of each added session")
    parser.add_argument("--usd", type=float, help="with --again: the dollar cap of each added session")
    parser.add_argument("--end-proof-rounds", action="store_true",
                        help="for a run that plans no stage after its proof rounds, so that nothing says they are over: they "
                             "are, for good, and the run's best scored proof that can be locked is locked")


def run(ctx, args, backend, run_round) -> None:
    """`ctx`: the run, opened; `backend` and `run_round`: the run's backend and core.rounds.run_round, from the
    loop driver, as the stages after the proof rounds get them."""
    if not (ctx.cfg.get("open_lane") or {}).get("enabled"):
        raise ScalingError("the scaling proofs are for open-lane runs")
    steps.run_steps(ctx, backend, run_round, only=args.only, again=args.again, minutes=args.minutes, usd=args.usd,
                    end_proof_rounds=bool(getattr(args, "end_proof_rounds", False)))
