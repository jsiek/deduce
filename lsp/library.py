"""Library-mode entry point for the Deduce pipeline.

This is Step 1 of the LSP/MCP plan (see docs/lsp-plan.md). It exposes a
single function, ``check_file``, that runs the same parse + uniquify +
type/proof check pipeline as ``deduce.py`` but returns a structured
``CheckResult`` instead of printing and calling ``exit``. The CLI in
``deduce.py`` is now a thin wrapper around it.

Globals from ``flags.py`` (verbosity, parser choice, import directories)
still apply: this is library mode but not yet daemon-safe. Step 6 of the
plan tackles state isolation across calls.
"""

from __future__ import annotations

import os
import sys
import traceback as _traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional, Sequence

from lark.tree import Meta

import parser as _lark_parser
import rec_desc_parser as _rd_parser
from abstract_syntax import (
    Import,
    add_uniquified_module,
    get_recursive_descent,
    get_uniquified_modules,
)
from flags import get_verbose
from proof_checker import check_deduce, uniquify_deduce


@dataclass
class CheckResult:
    """Outcome of running the Deduce pipeline on a single file.

    Attributes:
        ok:               True iff parse + uniquify + check_deduce all
                          succeeded.
        error_message:    ``str(exception)`` if the pipeline raised.
                          ``None`` when ``ok`` is True.
        error_traceback:  Full Python traceback at the point of failure,
                          for callers that want it (e.g. ``--traceback``).
                          ``None`` when ``ok`` is True.
        module_name:      Module name derived from the filename
                          (``Path(filename).stem``).
        ast:              Post-uniquify AST. Populated on success and on
                          failures that occur after parse + uniquify
                          (e.g. type-check failures). ``None`` on parse
                          or uniquify failure.
    """

    ok: bool
    error_message: Optional[str]
    error_traceback: Optional[str]
    module_name: str
    ast: Optional[Any]


def check_file(
    filename: str,
    tracing_functions: Sequence[str] = (),
    prelude: Sequence[str] = (),
) -> CheckResult:
    """Run the Deduce pipeline on ``filename`` and return a CheckResult.

    Does not print to stdout (apart from verbose-mode tracing controlled
    by ``flags.py``) and never calls ``sys.exit``. All recoverable errors
    surface through ``CheckResult.error_message``.

    Args:
        filename:           Path to the ``.pf`` file to check.
        tracing_functions:  Function names to trace (``--trace``).
        prelude:            Module names to import as a private prelude
                            in front of the file. Pass ``[]`` for no
                            prelude (matches ``--no-stdlib``).
    """
    module_name = Path(filename).stem
    if get_verbose():
        print("Deducing file:", filename)

    ast: Optional[Any] = None
    try:
        cached = get_uniquified_modules()
        if module_name in cached:
            ast = cached[module_name]
        else:
            with open(filename, "r", encoding="utf-8") as f:
                program_text = f.read()

            deduce_dir = os.path.dirname(sys.argv[0])
            if get_recursive_descent():
                _rd_parser.set_deduce_directory(deduce_dir)
                _rd_parser.set_filename(filename)
                _rd_parser.init_parser()
                ast = _rd_parser.parse(
                    program_text, trace=get_verbose(), error_expected=False
                )
            else:
                _lark_parser.set_deduce_directory(deduce_dir)
                _lark_parser.set_filename(filename)
                _lark_parser.init_parser()
                ast = _lark_parser.parse(
                    program_text, trace=get_verbose(), error_expected=False
                )

            if len(prelude) > 0:
                # The LALR parser returns a tuple here while the recursive
                # descent parser returns a list, so coerce before concat.
                imports = [
                    Import(Meta(), name, visibility="private") for name in prelude
                ]
                ast = imports + list(ast)

            uniquify_deduce(ast)
            add_uniquified_module(module_name, ast)

        check_deduce(ast, module_name, True, list(tracing_functions))
        return CheckResult(
            ok=True,
            error_message=None,
            error_traceback=None,
            module_name=module_name,
            ast=ast,
        )
    except Exception as e:
        return CheckResult(
            ok=False,
            error_message=str(e),
            error_traceback=_traceback.format_exc(),
            module_name=module_name,
            ast=ast,
        )
