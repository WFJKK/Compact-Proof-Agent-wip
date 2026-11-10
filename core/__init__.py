"""Model-agnostic core of the compact-proof loop.

Nothing in this package may name a model or hardcode a model's sizes;
everything model-specific lives in a model folder (see core.model_folder).
"""

import sys

# A run halts when bytecode it could load appears in trusted folders (core.rounds), so no process
# of this pipeline writes any: not the run itself, and not a second run, a status command or the
# tests started next to it, whatever the shell sets. Only this file's own compiled copy can still
# be written, by an interpreter that has none yet, before this line runs.
sys.dont_write_bytecode = True

__version__ = "0.1.0"
