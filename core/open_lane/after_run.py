"""The commands that follow a finished open-lane run: `python3 -m core.loop <name> --run <run folder>`.

Each is a package of its own, and the loop driver and the report know it only through this list. Its command
module has:

- NAME and HELP: the subcommand and its line of help;
- add_arguments(parser): its own arguments (the loop driver adds --run and --budget-usd);
- changed_since(run, started, folder, bad, log): the versions it goes on with when the pipeline changed since the
  run started, or a ValueError saying why the run cannot be opened (core.loop.open_context);
- run(ctx, args, backend, run_round), and Error, the errors of it that are reported to the person;
- status_lines(run) and report_lines(run): what the status and the report show of it.

Adding one is a package and a line here: nothing of it goes into the loop driver, the sessions or a model folder.
"""

from __future__ import annotations


def commands() -> dict:
    from .scaling import command as scaling

    return {scaling.NAME: scaling}
