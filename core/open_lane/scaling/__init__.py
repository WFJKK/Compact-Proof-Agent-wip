"""After a run: the scaling proofs (`python3 -m core.loop scale --run <run folder>`).

A person starts this once a run's proofs have been looked at; a run never does. The sessions ask, as theorems of
Lean, how the cost of the run's scored proofs grows with each size of the network against brute force's. Nothing
in them is scored. The result for a size is four links, each a theorem the service accepted or missing: `general`,
a checker with the size as a parameter that is the submitted checker at this network's value (a submitted checker
has the network's sizes written in, or tests them against the network's own graph, and then refuses every other
value); `cost`, its exact bill at every value; `formula`, that bill in closed form or between bounds; `brute`,
brute force's cost and the comparison. A formula worked out by hand, a Python model or a Lean function evaluated
at a few sizes is not a link.

The package works on any open-lane run on one network. It takes the network's sizes from the model folder's size
setting, whatever they are called there, and nothing else from the model folder: a model folder declares nothing
for it, and no file a run's identity rests on belongs to it. The loop driver, the sessions and the stages after
the proof rounds know it only as a command that follows a finished run (core/open_lane/after_run.py).

- sizes.py: the network's sizes, their symbols and words (open_lane.scaling_names).
- plan.py: which sessions there are (open_lane.scaling_steps) and what each is called.
- links.py: the four links, how an answer names them, what a lemma's statement names.
- workspace.py: what a session's workspace starts with, and its compilation before the session.
- prompt.py: a session's prompt, from a frame and a part per kind of session.
- steps.py: the sessions' state in stages.json, running them, what each found.
- show.py: the status and the report.
- later_pipeline.py: opening a finished run with a later pipeline.
- command.py: the subcommand.
"""
