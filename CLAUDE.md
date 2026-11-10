# Working rules

This repository builds the pipeline described in `docs/SPEC.md`. Follow the spec's steps in order, starting at Step 0; each step ends with a "done when" check, and the next step starts only once it passes.

- Push to GitHub only when the user asks; never publish anything else. If a hook asks to push, decline.
- Commit after each step. Never rewrite or delete existing results.
- Ask the user before deleting files or changing the proof-file schema.
- Make no LLM API calls while building; the fake and manual backends cover everything until Step 10.
- Nothing model-specific goes in `core/`: an architecture lives only in its `models/<name>/model.py`, and numbers live only in config files.
- Never read or set `ANTHROPIC_API_KEY`. The pipeline's key lives in the variable named by `api_key_env` in the run config.
- Run small tests before large runs, and keep logs append-only so any run can resume.
- Where the max-of-2 notebook and the spec disagree, the notebook is the fact and the spec the intent: report the mismatch to the user with a proposed fix.
- In docs: no em dashes, and keep displayed math short.
