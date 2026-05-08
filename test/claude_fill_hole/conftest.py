"""Shared fixtures for the claude_fill_hole sidecar tests.

Adds the repo root to sys.path so ``tools.claude_fill_hole`` resolves
without an editable install. The sidecar is a self-contained tool
with its own optional ``anthropic`` dep; the validator + agent loop
itself doesn't need the dep, only ``__main__.py``'s real-API path
does.
"""

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
