"""The fake backend: replays responses from files, in order.

Each source is a response file or a folder of them (its *.md files, sorted by
name). Round 0 uses a model folder's baselines/ this way; tests and dry runs
use it in place of the LLM.
"""

from __future__ import annotations

from pathlib import Path

from . import BackendError, Response


class FakeBackend:
    name = "fake"

    def __init__(self, sources):
        self.items: list[tuple[Path, str]] = []
        for src in sources:
            p = Path(src)
            if p.is_dir():
                files = sorted(p.glob("*.md"))
            elif p.is_file():
                files = [p]
            else:
                raise BackendError(f"no responses at {p}")
            self.items += [(f, f.read_text()) for f in files]

    def __len__(self) -> int:
        return len(self.items)

    def available(self, index: int) -> bool:
        return 0 <= index < len(self.items)

    def respond(self, prompt, index: int, where=None) -> Response:
        if not self.available(index):
            raise BackendError(f"the fake backend has {len(self.items)} responses; asked for number {index + 1}")
        path, text = self.items[index]
        return Response(
            text=text,
            meta={"backend": self.name, "source": path.name, "input_tokens": 0, "output_tokens": 0, "cost_usd": 0.0},
        )
