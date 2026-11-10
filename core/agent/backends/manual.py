"""The manual backend: a person plays the agent.

The loop writes the round's prompt.md; this backend says where it is and waits
until a response.md appears in the attempt's folder and stops changing. Stop
with Ctrl-C at any time; resume picks up the same round and keeps waiting, or
uses the response if it is there by then.
"""

from __future__ import annotations

import time
from pathlib import Path

from . import Response

POLL_S = 2.0
SETTLE_S = 1.0


class ManualBackend:
    name = "manual"

    def __init__(self, log=print, poll_s: float = POLL_S, settle_s: float = SETTLE_S):
        self.log, self.poll_s, self.settle_s = log, poll_s, settle_s

    def available(self, index: int) -> bool:
        return True

    def respond(self, prompt, index: int, where=None) -> Response:
        if where is None:
            raise ValueError("the manual backend needs the attempt's folder")
        where = Path(where)
        target = where / "response.md"
        self.log(
            f"  prompt: {where.parent / 'prompt.md'}\n"
            f"  waiting for the response at {target} (Ctrl-C stops; resume continues from here)"
        )
        while True:
            if target.is_file() and target.stat().st_size > 0:
                size = target.stat().st_size
                time.sleep(self.settle_s)
                if target.stat().st_size == size:
                    break
            time.sleep(self.poll_s)
        return Response(
            text=target.read_text(),
            meta={"backend": self.name, "source": "response.md", "input_tokens": 0, "output_tokens": 0, "cost_usd": 0.0},
        )
