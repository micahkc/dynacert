"""Registry of analysis approaches (see `base.py` for the interface).

    from dynacert import approaches, problem
    prob = problem.load("examples/ClosedLoop.mo")
    for name, a in approaches.REGISTRY.items():
        print(name, a.layer, a.assess(prob))

Every module in this package is imported on first import (`pkgutil`), so a new approach only
needs a module with an `@register`ed class. Order: lmi, monte_carlo, falsify, tube, then the
rest alphabetically; registration order is the order `dynacert MODEL.mo` lists them in.
"""

from __future__ import annotations

import importlib
import pkgutil
import sys

from .base import (ANALYSIS, ANALYZE, CERTIFICATE, CERTIFY, KIND_LAYER, LAYER_TITLES, LAYERS,
                   VALIDATE, VALIDATION, VIEW, Approach, Assessment, Outcome)

REGISTRY: dict[str, Approach] = {}

CORE = ("lmi", "monte_carlo", "falsify", "tube")   # imported first, failures are errors


def register(cls):
    """Class decorator: add an approach to the registry under `cls.name`. An approach that does
    not declare `layer` gets it from `kind`."""
    if not cls.name or cls.name in REGISTRY:
        raise ValueError(f"approach name {cls.name!r} is empty or taken")
    inst = cls()
    if not inst.layer:
        inst.layer = KIND_LAYER.get(inst.kind, ANALYZE)
    if inst.layer not in LAYERS:
        raise ValueError(f"approach {cls.name!r}: unknown layer {inst.layer!r}")
    REGISTRY[cls.name] = inst
    return cls


def get(name: str) -> Approach:
    try:
        return REGISTRY[name]
    except KeyError:
        raise KeyError(f"unknown approach {name!r}; available: {', '.join(REGISTRY)}") from None


def by_layer(layer: str) -> list[Approach]:
    """The approaches of one layer, in registration order."""
    return [a for a in REGISTRY.values() if a.layer == layer]


def assess(name: str, prob) -> Assessment:
    """Assess one approach; an approach that raises is reported as infeasible, not a crash."""
    from .. import timing

    try:
        with timing.phase(f"assess:{name}"):
            return get(name).assess(prob)
    except Exception as e:  # noqa: BLE001 - a buggy assessment must not hide the others
        return Assessment.no(f"assessment failed: {type(e).__name__}: {e}")


def assess_all(prob) -> dict:
    return {name: assess(name, prob) for name in REGISTRY}


def module_order(names) -> list[str]:
    """Discovery order: the core modules first, then the rest alphabetically."""
    names = [n for n in names if n != "base" and not n.startswith("_")]
    return [n for n in CORE if n in names] + sorted(n for n in names if n not in CORE)


def _discover():
    found = [m.name for m in pkgutil.iter_modules(__path__)]
    for name in module_order(found):
        if name in CORE:
            importlib.import_module(f"{__name__}.{name}")
            continue
        try:
            importlib.import_module(f"{__name__}.{name}")
        except Exception as e:  # noqa: BLE001 - a broken plugin must not take down the CLI
            print(f"dynacert: approach module {name!r} not loaded: {type(e).__name__}: {e}",
                  file=sys.stderr)


_discover()

__all__ = ["ANALYSIS", "ANALYZE", "CERTIFICATE", "CERTIFY", "LAYERS", "LAYER_TITLES", "VALIDATE",
           "VALIDATION", "VIEW", "Approach", "Assessment", "Outcome", "REGISTRY", "assess",
           "assess_all", "by_layer", "get", "module_order", "register"]
