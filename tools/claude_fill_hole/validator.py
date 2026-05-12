"""Proof validation backends.

Two backends, same interface (``Validator.validate``):

- ``SubprocessValidator`` -- forks ``python deduce.py --quiet`` on a
  tempfile in the same directory as the user's file (so relative
  imports resolve). Default v0; works without a running LSP server.
- ``LspValidator`` -- calls ``deduce/validateProof`` over JSON-RPC.
  Faster once the in-flight incremental-checking work lands. Not
  implemented yet -- the placeholder is here so the pluggable shape
  is visible from day one.

The agent loop calls ``validator.validate(proof_text)`` and gets back
``ValidationOutcome(ok, error)``; everything below the seam is
backend-specific.
"""

from __future__ import annotations

import os
import subprocess
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


@dataclass(frozen=True)
class ValidationOutcome:
    """Result of one ``validate_proof`` invocation."""

    ok: bool
    error: Optional[str] = None


class Validator(ABC):
    """Backend for the agent loop's ``validate_proof`` tool."""

    @abstractmethod
    def validate(self, proof_text: str) -> ValidationOutcome:
        """Splice ``proof_text`` into the request's source at the
        hole's range and return whether the file checks."""


class SubprocessValidator(Validator):
    """Forks ``deduce.py --quiet`` on a tempfile copy of the source.

    Tempfile is written into the same directory as the original file
    so relative ``import``s and ``--dir`` resolution work the same as
    they would for the user's own ``deduce.py file.pf`` invocation.
    Hidden filename (``.{stem}.fillhole.{pid}.{n}.pf``) so a crash
    that leaves the file behind isn't visible in the user's
    directory listing; cleaned up best-effort on each call.
    """

    def __init__(
        self,
        file_path: str,
        content: str,
        hole_start_offset: int,
        hole_end_offset: int,
        deduce_cmd: tuple[str, ...] = ("python3", "deduce.py"),
        deduce_root: Optional[str] = None,
        no_stdlib: bool = False,
        timeout_seconds: float = 60.0,
        max_proof_text_bytes: int = 32 * 1024,
    ) -> None:
        self.file_path = file_path
        self.content = content
        self.hole_start_offset = hole_start_offset
        self.hole_end_offset = hole_end_offset
        self.deduce_cmd = deduce_cmd
        self.deduce_root = deduce_root or os.path.dirname(os.path.abspath(file_path))
        self.no_stdlib = no_stdlib
        self.timeout_seconds = timeout_seconds
        self.max_proof_text_bytes = max_proof_text_bytes
        self._call_count = 0

    def validate(self, proof_text: str) -> ValidationOutcome:
        if len(proof_text.encode("utf-8")) > self.max_proof_text_bytes:
            return ValidationOutcome(
                ok=False,
                error=(
                    f"proof text exceeds {self.max_proof_text_bytes} bytes; "
                    "cap is meant to catch runaway model output"
                ),
            )

        spliced = (
            self.content[: self.hole_start_offset]
            + proof_text
            + self.content[self.hole_end_offset :]
        )

        self._call_count += 1
        tmp_path = self._tempfile_path()
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                f.write(spliced)

            cmd = list(self.deduce_cmd)
            if self.no_stdlib:
                cmd.append("--no-stdlib")
            cmd.append(tmp_path)

            return self._run_deduce(cmd)
        finally:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass  # best-effort

    def _tempfile_path(self) -> str:
        stem = Path(self.file_path).stem
        directory = os.path.dirname(os.path.abspath(self.file_path))
        return os.path.join(
            directory, f".{stem}.fillhole.{os.getpid()}.{self._call_count}.pf"
        )

    def _run_deduce(self, cmd: list[str]) -> ValidationOutcome:
        try:
            proc = subprocess.run(
                cmd,
                cwd=self.deduce_root,
                capture_output=True,
                text=True,
                timeout=self.timeout_seconds,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return ValidationOutcome(
                ok=False,
                error=f"deduce.py timed out after {self.timeout_seconds:.0f}s",
            )
        except FileNotFoundError as e:
            # The deduce_cmd executable wasn't found. Reported as a
            # hard failure rather than a model-recoverable one.
            return ValidationOutcome(
                ok=False, error=f"could not invoke deduce.py: {e}"
            )

        if proc.returncode == 0:
            return ValidationOutcome(ok=True)

        # On failure, deduce.py prints its error to stderr (or
        # sometimes stdout). Truncate to the last ~4kB so it fits
        # in a tool-result block without thrashing the model's
        # context window.
        error_text = (proc.stderr or proc.stdout or "").strip()
        return ValidationOutcome(ok=False, error=_tail(error_text, 4096))


class LspValidator(Validator):
    """Calls ``deduce/validateProof`` over JSON-RPC. Not implemented.

    Placeholder so the pluggable-backend shape is visible. Will be
    wired up once the in-flight incremental-checking work lands and
    the LSP daemon's ``deduce/validateProof`` becomes the cheap path.
    """

    def __init__(self, *args, **kwargs) -> None:
        raise NotImplementedError(
            "LspValidator is a follow-up; use SubprocessValidator for now"
        )

    def validate(self, proof_text: str) -> ValidationOutcome:
        raise NotImplementedError


# ---------------------------------------------------------------------------
# Mid-proof goal queries: HoleQuerier
# ---------------------------------------------------------------------------
#
# Sibling to Validator: instead of "splice this proof and run the
# checker to completion", it answers "splice this partial proof
# (which itself contains a `?') and tell me what the goal looks like
# at that `?'".  Used by the agent loop's `query_goal' tool, which
# does NOT count toward the validate budget -- it's a peek at the
# proof state mid-construction so the model can see intermediate
# goals (e.g. inside an induction case) before committing to a full
# proof.
#
# Implementation: imports `lsp.query.hole_context_at' directly
# (in-process), so the deduce environment must already be
# bootstrapped (see __main__.py).


@dataclass(frozen=True)
class _Given:
    """Local copy of the Given shape from `lsp.query`, included here
    so test code that imports HoleQuerier doesn't have to also import
    the deduce env."""

    label: Optional[str]
    formula: str


@dataclass(frozen=True)
class QueryOutcome:
    """Result of one ``query_goal`` invocation.

    On success: ``goal`` is the rendered formula at the queried
    `?'; ``givens`` is the tuple of in-scope hypothesis labels and
    formulas at that point.  On failure: ``error`` carries a
    human-readable reason (no `?' in proof_text, splice didn't reach
    the hole, parse error in the spliced source, etc.) and the other
    fields are empty.
    """

    ok: bool
    goal: Optional[str] = None
    givens: tuple = ()
    error: Optional[str] = None


class HoleQuerier:
    """Splice a partial proof and report the goal at the first `?' inside.

    The model uses this to inspect intermediate goals during proof
    construction without burning a `validate_proof' attempt.  Typical
    flow: write a proof skeleton with `?' marking where you want to
    see the goal, call query_goal, read the goal, refine the
    skeleton, repeat.

    Constructor takes the same splice anchors as SubprocessValidator
    (file_path, content, hole offsets) plus the prelude tuple so
    `hole_context_at' can resolve standard-library imports.
    """

    def __init__(
        self,
        file_path: str,
        content: str,
        hole_start_offset: int,
        hole_end_offset: int,
        prelude: tuple = (),
        max_proof_text_bytes: int = 32 * 1024,
    ) -> None:
        self.file_path = file_path
        self.content = content
        self.hole_start_offset = hole_start_offset
        self.hole_end_offset = hole_end_offset
        self.prelude = prelude
        self.max_proof_text_bytes = max_proof_text_bytes

    def query(self, proof_text: str) -> QueryOutcome:
        if len(proof_text.encode("utf-8")) > self.max_proof_text_bytes:
            return QueryOutcome(
                ok=False,
                error=(
                    f"proof text exceeds {self.max_proof_text_bytes} bytes; "
                    "cap is meant to catch runaway model output"
                ),
            )
        if "?" not in proof_text:
            return QueryOutcome(
                ok=False,
                error=(
                    "proof_text contains no `?'; query_goal needs at least "
                    "one `?' marking where you want to inspect the goal"
                ),
            )

        spliced = (
            self.content[: self.hole_start_offset]
            + proof_text
            + self.content[self.hole_end_offset :]
        )
        # Find the first `?` AT OR AFTER the splice point -- earlier
        # `?'s would belong to other (already-filled or unrelated) holes
        # in the file, which we don't want to query.
        new_q_offset = spliced.find("?", self.hole_start_offset)
        if new_q_offset < 0:
            return QueryOutcome(
                ok=False,
                error="splice produced no `?' to query (unexpected)",
            )

        line, col = _offset_to_line_col_1indexed(spliced, new_q_offset)

        try:
            from lsp.query import Position, hole_context_at
        except ImportError as e:
            return QueryOutcome(
                ok=False,
                error=(
                    f"could not import lsp.query for goal lookup: {e} "
                    "(sidecar must be invoked with deduce repo root on "
                    "PYTHONPATH and the deduce env bootstrapped)"
                ),
            )

        try:
            ctx = hole_context_at(
                self.file_path,
                spliced,
                Position(line=line, column=col),
                prelude=self.prelude,
                include_lemmas=False,
            )
        except Exception as e:  # pragma: no cover -- defensive
            return QueryOutcome(
                ok=False,
                error=f"goal lookup raised: {e}",
            )

        if ctx is None:
            return QueryOutcome(
                ok=False,
                error=(
                    "couldn't reach the `?' to query -- check for parse "
                    "or type errors before that point in your proof"
                ),
            )

        givens = tuple(
            _Given(label=g.label, formula=g.formula) for g in ctx.givens
        )
        return QueryOutcome(ok=True, goal=ctx.goal, givens=givens)


def _offset_to_line_col_1indexed(text: str, offset: int) -> tuple:
    """Convert a 0-indexed byte offset to a 1-indexed (line, column).

    Mirrors lsp.query._offset_to_line_col but lives here so HoleQuerier
    doesn't need to reach into lsp.query's private surface."""
    line = 1
    col = 1
    for i, ch in enumerate(text):
        if i == offset:
            return line, col
        if ch == "\n":
            line += 1
            col = 1
        else:
            col += 1
    return line, col


def _tail(text: str, max_bytes: int) -> str:
    """Return the last ``max_bytes`` of ``text``, byte-safe.

    A naive ``text[-max_bytes:]`` is character-based and can be much
    larger than expected when the text contains multi-byte characters.
    Decode/encode through bytes so the cap actually holds.
    """
    encoded = text.encode("utf-8")
    if len(encoded) <= max_bytes:
        return text
    truncated = encoded[-max_bytes:].decode("utf-8", errors="ignore")
    return "...[truncated]...\n" + truncated
