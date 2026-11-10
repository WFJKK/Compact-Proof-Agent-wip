"""Agent backends: where a round's responses come from.

Every backend has `available(index)` and `respond(prompt, index, where)`:
index counts the attempts this backend has answered in the run, so a resumed
run asks for the same response again; prompt is a core.agent.build_prompt.Prompt
(or None in round 0); where is the attempt's folder. fake replays files, manual
waits for a person to write the response, and api (Step 8) asks the model.
"""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class Response:
    text: str
    meta: dict = field(default_factory=dict)


class BackendError(RuntimeError):
    pass
