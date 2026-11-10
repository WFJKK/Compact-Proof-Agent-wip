"""The trusted checker. It is the same for every model: it builds the network
from the model folder's model.py, loads the weights itself, and recomputes
every claim in a proof file with exact arithmetic.
"""
