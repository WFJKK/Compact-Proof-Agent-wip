"""The open lane (step 3 of the Lean open-lane ticket): the agent works with tools in a Lean workspace and
submits Lean proofs about a network to the acceptance service of the Lean project (CompactCheck,
scripts/accept.py there). Nothing here is trusted: the service's receipts are the facts, and the archive
records come from them (records.py).

- session.py: one attempt's workspace, tools and budgets, logged append-only.
- mcp_server.py: the tools as an MCP server over stdio, for the Claude Code CLI.
- backends.py: the Claude Code backend with tools, and the fake backend that replays scripted tool calls.
- prompt.py: the open-lane prompt (specification, cost language, scoreboard, receipts, accepted lemmas).
- records.py: archive records from receipts.

Configuration is the `open_lane` mapping of a run config (config/defaults.yaml).
"""
