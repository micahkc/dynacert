"""Registry of analysis approaches (see `base.py` for the interface).

    from dynacert import approaches, problem
    prob = problem.load("examples/ClosedLoop.mo")
    for name, a in approaches.REGISTRY.items():
        print(name, a.assess(prob))
"""

from __future__ import annotations

from .base import CERTIFICATE, VALIDATION, Approach, Assessment, Outcome

REGISTRY: dict[str, Approach] = {}


def register(cls):
    """Class decorator: add an approach to the registry under `cls.name`."""
    if not cls.name or cls.name in REGISTRY:
        raise ValueError(f"approach name {cls.name!r} is empty or taken")
    REGISTRY[cls.name] = cls()
    return cls


def get(name: str) -> Approach:
    try:
        return REGISTRY[name]
    except KeyError:
        raise KeyError(f"unknown approach {name!r}; available: {', '.join(REGISTRY)}") from None


def assess(name: str, prob) -> Assessment:
    """Assess one approach; an approach that raises is reported as infeasible, not a crash."""
    try:
        return get(name).assess(prob)
    except Exception as e:  # noqa: BLE001 - a buggy assessment must not hide the others
        return Assessment.no(f"assessment failed: {type(e).__name__}: {e}")


def assess_all(prob) -> dict:
    return {name: assess(name, prob) for name in REGISTRY}


# registration order is the order `dynacert MODEL.mo` lists them in
from . import lmi, monte_carlo, falsify, tube  # noqa: E402,F401
from . import structure  # noqa: E402,F401  (structure, layered)

__all__ = ["CERTIFICATE", "VALIDATION", "Approach", "Assessment", "Outcome", "REGISTRY",
           "assess", "assess_all", "get", "register"]
