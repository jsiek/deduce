"""Shared pytest config for the unit/ test suite.

Puts the repository root on ``sys.path`` so individual test modules
can do plain ``import abstract_syntax`` etc. without each one
recomputing the path.
"""

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))
