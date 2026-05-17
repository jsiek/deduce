from __future__ import annotations

# Compatibility facade for the split abstract_syntax package.  Existing
# callers can keep using `import abstract_syntax as ast` or
# `from abstract_syntax import Var, Env, uniquify_deduce` while the
# implementation lives in cohesive submodules.

from importlib import import_module
from types import ModuleType
from typing import Any

_MODULE_NAMES = (
    "core",
    "terms",
    "proofs",
    "declarations",
    "env",
    "literals",
    "rewrite",
    "ops",
    "theorems",
)

_MODULES: tuple[ModuleType, ...] = tuple(
    import_module(f"{__name__}.{module_name}") for module_name in _MODULE_NAMES
)
(
    core,
    terms,
    proofs,
    declarations,
    env,
    literals,
    rewrite,
    ops,
    theorems,
) = _MODULES

_DYNAMIC_NAMES = {
    "current_module",
    "reduce_only",
    "reduce_all",
    "dont_reduce_opaque",
    "eval_all",
    "reduced_defs",
    "uniquified_modules",
    "collected_imports",
    "default_mark_LHS",
    "num_rewrites",
}

def _public_names(module: ModuleType) -> list[str]:
    return [name for name in vars(module) if not name.startswith("_")]

def _shared_names(module: ModuleType) -> list[str]:
    return [
        name
        for name in vars(module)
        if not (name.startswith("__") and name.endswith("__"))
    ]

__all__: list[str] = []
for _module in _MODULES:
    for _name in _public_names(_module):
        if _name not in __all__:
            __all__.append(_name)

# Many migrated methods still resolve peer classes and helper functions as
# module globals, matching their former single-file lookup behavior.  Populate
# each submodule with the complete public surface after all modules import.
_SHARED_GLOBALS: dict[str, Any] = {}
for _module in _MODULES:
    for _name in _shared_names(_module):
        _SHARED_GLOBALS[_name] = getattr(_module, _name)

for _module in _MODULES:
    for _name, _value in _SHARED_GLOBALS.items():
        if _name not in _DYNAMIC_NAMES:
            vars(_module).setdefault(_name, _value)

for _name, _value in _SHARED_GLOBALS.items():
    if _name not in _DYNAMIC_NAMES:
        globals()[_name] = _value

_DYNAMIC_OWNERS = {
    "current_module": core,
    "reduce_only": terms,
    "reduce_all": terms,
    "dont_reduce_opaque": terms,
    "eval_all": terms,
    "reduced_defs": terms,
    "uniquified_modules": declarations,
    "collected_imports": theorems,
    "default_mark_LHS": rewrite,
    "num_rewrites": rewrite,
}

def __getattr__(name: str) -> Any:
    if name in _DYNAMIC_OWNERS:
        return getattr(_DYNAMIC_OWNERS[name], name)
    for module in reversed(_MODULES):
        if hasattr(module, name):
            return getattr(module, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")

def __dir__() -> list[str]:
    return sorted(set(globals()) | set(__all__))
