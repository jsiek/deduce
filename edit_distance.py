from math import ceil
from typing import Iterable, Optional


def edit_distance(s1: str, s2: str) -> int:
    m = len(s1); n = len(s2)
    F: dict[tuple[int, int], int] = {}
    F[(0, 0)] = 0
    for i in range(1, m+1):
        F[(i, 0)] = i

    for j in range(1, n+1):
        F[(0, j)] = j

    for i in range(1, m+1):
        for j in range(1, n+1):
            match = F[(i-1, j-1)] + (0 if s1[i-1] == s2[j-1] else 1)
            delete = F[(i-1, j)] + 1
            insert = F[(i, j-1)] + 1
            F[(i, j)] = min(match, delete, insert)
    return F[(m, n)]

def did_you_mean_hint(name: str, candidates: Iterable[str]) -> str:
    """Build a ``did you intend: ...`` suggestion for an undefined name.

    Returns a newline-prefixed, tab-indented list of every candidate within
    ``ceil(len(name) / 5)`` edits of ``name``, or the empty string when none
    are close enough. Shared by the ``uniquify`` name-resolution error paths
    for variables, proof variables, and rule-induction/inversion hypotheses.
    """
    close = [c for c in candidates
             if edit_distance(name, c) <= ceil(len(name) / 5)]
    return '\n\tdid you intend: ' + ', '.join(close) if close else ''


def closest_keyword(word: str, keywords: Iterable[str]) -> Optional[str]:
    best_yet: Optional[tuple[str, int]] = None
    for kw in keywords:
        d = edit_distance(word, kw)
        if d <= ceil(len(word) / 6):
            if best_yet is None or d < best_yet[1]:
                best_yet = (kw, d)
    if best_yet:
        return best_yet[0]
    else:
        return None
