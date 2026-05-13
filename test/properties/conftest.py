import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))
sys.argv = [str(REPO_ROOT / "deduce.py")]

from flags import set_quiet_mode  # noqa: E402

set_quiet_mode(True)
