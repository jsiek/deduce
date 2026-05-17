"""Compatibility facade for the split checker implementation.

The implementation now lives in cohesive ``checker_*`` modules.  This
module intentionally preserves the historical ``proof_checker`` import
surface while downstream callers migrate to the narrower modules.
"""

from types import ModuleType
import sys

import checker_cache as _checker_cache
import checker_logic as _checker_logic
import checker_induction as _checker_induction
import checker_types as _checker_types
import checker_predicates as _checker_predicates
import checker_proofs as _checker_proofs
import checker_pipeline as _checker_pipeline

_CHECKER_MODULES = (
    _checker_cache,
    _checker_logic,
    _checker_induction,
    _checker_types,
    _checker_predicates,
    _checker_proofs,
    _checker_pipeline,
)

_STATE_ATTRS = {
    "name_id": _checker_proofs,
    "imported_modules": _checker_pipeline,
    "checked_modules": _checker_pipeline,
    "modules": _checker_types,
    "dirty_files": _checker_types,
}


def _public_items(module):
    return {
        name: value
        for name, value in vars(module).items()
        if not name.startswith("__") and name not in {"annotations"}
    }


def _link_modules():
    namespace = {}
    owners = {}
    for module in _CHECKER_MODULES:
        for name, value in _public_items(module).items():
            namespace[name] = value
            owners[name] = module
    for module in _CHECKER_MODULES:
        module.__dict__.update(namespace)
    return namespace, owners


_namespace, _owners = _link_modules()
for _name, _value in _namespace.items():
    if _name not in _STATE_ATTRS:
        globals()[_name] = _value

__all__ = sorted(
    name for name in set(_namespace) | set(_STATE_ATTRS)
    if not name.startswith("_")
)


def __getattr__(name):
    module = _STATE_ATTRS.get(name)
    if module is not None:
        return getattr(module, name)
    try:
        return _namespace[name]
    except KeyError as exc:
        raise AttributeError(name) from exc


class _ProofCheckerFacade(ModuleType):
    def __setattr__(self, name, value):
        module = _STATE_ATTRS.get(name)
        if module is not None:
            setattr(module, name, value)
            if name in globals():
                globals().pop(name, None)
            return
        if name in _namespace:
            _namespace[name] = value
            owner = _owners.get(name)
            if owner is not None:
                setattr(owner, name, value)
            for checker_module in _CHECKER_MODULES:
                checker_module.__dict__[name] = value
        super().__setattr__(name, value)


sys.modules[__name__].__class__ = _ProofCheckerFacade
