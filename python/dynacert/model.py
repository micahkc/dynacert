"""Load a model rendered by rumoca's `sympy-dae` target.

The module is produced from the same DAE IR, in the same compilation, as the Lean
specification (`lean-dae` target). Its `EQUATIONS` list matches the conjuncts of Lean's
`Equations` one to one, in order.
"""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass, field
from pathlib import Path

import sympy as sp

from .lean import ident, sanitize


@dataclass
class Var:
    name: str
    role: str
    shape: tuple
    symbol: object
    binding: object
    start: object
    fixed: object
    unit: str | None
    description: str | None
    annotations: dict | None

    @property
    def lean(self) -> str:
        return ident(self.name)

    @property
    def scalar(self) -> bool:
        return tuple(self.shape) == ()


@dataclass
class Model:
    name: str
    variables: list[Var]
    equations: list            # one entry per Lean `Equations` conjunct
    der: dict                   # state name -> derivative symbol
    annotations: dict | None
    module: object = field(repr=False, default=None)

    @property
    def ns(self) -> str:
        return sanitize(self.name)

    def role(self, *roles) -> list[Var]:
        return [v for v in self.variables if v.role in roles]

    @property
    def params(self) -> list[Var]:
        return self.role("parameter", "constant")

    @property
    def inputs(self) -> list[Var]:
        return self.role("input")

    @property
    def states(self) -> list[Var]:
        return self.role("state")

    @property
    def algebraics(self) -> list[Var]:
        return self.role("algebraic", "output")

    def var(self, name: str) -> Var:
        for v in self.variables:
            if v.name == name:
                return v
        raise KeyError(name)

    @property
    def n_bound(self) -> int:
        """Number of conjuncts of Lean's `Params.Bound`."""
        return sum(1 for v in self.params if v.binding is not None)

    @property
    def n_init(self) -> int:
        """Number of conjuncts of Lean's `Initial`."""
        return sum(1 for v in self.states if v.start is not None)

    def equations_flat(self) -> list:
        """All scalar equations (structured families expanded)."""
        out = []
        for e in self.equations:
            out.extend(e if isinstance(e, (list, tuple)) else [e])
        return out

    def param_values(self, keep=()) -> dict:
        """Scalar parameter symbol -> bound value, array parameters expanded elementwise.

        Parameters named in `keep` are left out (they stay symbolic).
        """
        vals = {}
        for v in self.params:
            if v.binding is None or v.name in keep:
                continue
            b = v.binding
            if isinstance(v.symbol, sp.MatrixBase):
                bs = list(b) if isinstance(b, sp.MatrixBase) else [b] * len(v.symbol)
                vals.update(zip(list(v.symbol), map(sp.sympify, bs)))
            else:
                vals[v.symbol] = sp.sympify(b)
        return vals


def load(path: str | Path) -> Model:
    path = Path(path)
    name = f"_dynacert_model_{path.stem}"
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    variables = []
    for group in (mod.PARAMETERS, mod.INPUTS, mod.STATES, mod.ALGEBRAICS):
        for r in group:
            variables.append(Var(r["name"], r["role"], tuple(r["shape"] or ()), r["symbol"],
                                 r.get("binding"), r.get("start"), r.get("fixed"), r.get("unit"),
                                 r.get("description"), r.get("vendor_annotations")))
    # keep rumoca's declaration order within each role (Lean structure field order)
    return Model(mod.MODEL_NAME, variables, list(mod.EQUATIONS), dict(mod.DX),
                 getattr(mod, "MODEL_ANNOTATIONS", None), mod)
