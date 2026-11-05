"""Load a model rendered by rumoca's `sympy-dae` target.

The module is produced from the same DAE IR, in the same compilation, as the Lean
specification (`lean-dae` target). Its `EQUATIONS` list matches the conjuncts of Lean's
`Equations` one to one, in order.
"""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path

import sympy as sp
from sympy.utilities.lambdify import implemented_function

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
    # Declaration facts from rumoca's DAE (None from exports that predate them)
    path: tuple | None = None           # instance path, `mass.a.f` -> ("mass", "a", "f")
    physical: dict | None = None        # flow, stream, quantity, display_unit, type_name
    minimum: list | None = None         # per-scalar `min` / `max` / `nominal`
    maximum: list | None = None
    nominal: list | None = None
    state_select: str | None = None
    causality: str | None = None

    @property
    def component(self) -> str:
        """The top-level sub-model instance the variable belongs to ("" at top level)."""
        if self.path is not None:
            return self.path[0] if len(self.path) > 1 else ""
        return self.name.split(".", 1)[0] if "." in self.name else ""

    @property
    def flow(self) -> bool:
        return bool(self.physical and self.physical.get("flow"))

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
    # per `equations` entry: {"origin": "source" | generated kind, "span": (src, start, end)}
    origins: list | None = None

    @property
    def ns(self) -> str:
        return sanitize(self.name)

    def role(self, *roles) -> list[Var]:
        return [v for v in self.variables if v.role in roles]

    def var(self, name: str) -> Var | None:
        """The variable `name`, or the array variable a scalar name like `x[2]` belongs to."""
        by = {v.name: v for v in self.variables}
        while name not in by and name.endswith("]") and "[" in name:
            name = name[:name.rindex("[")]
        return by.get(name)

    def component_of(self, name: str) -> str:
        v = self.var(name)
        if v is not None:
            return v.component
        return name.split(".", 1)[0] if "." in name else ""

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
        """Scalar parameter symbol -> bound value; array parameters are expanded elementwise.

        Parameters named in `keep` are left out (they stay symbolic).
        """
        vals = {}
        for v in self.params:
            if v.binding is None or v.name in keep:
                continue
            if isinstance(v.symbol, sp.MatrixBase):
                b = v.binding
                bs = list(b) if isinstance(b, sp.MatrixBase) else [b] * len(v.symbol)
                vals.update(zip(list(v.symbol), map(sp.sympify, bs)))
            else:
                vals[v.symbol] = sp.sympify(v.binding)
        return vals


INLINE_OPS = 400  # an inlined function result larger than this stays opaque


def _flat(a) -> list:
    return list(a) if isinstance(a, sp.MatrixBase) else [a]


def _is_polynomial(res) -> bool:
    entries = _flat(res)
    if sum(sp.count_ops(e) for e in entries) > INLINE_OPS:
        return False
    return all(sp.sympify(e).is_polynomial() for e in entries)


def opaque_calls(functions: dict):
    """A `call` handler for rumoca's `equations(call=...)`.

    Polynomial functions (rotation matrices, quaternion and SE₂(3) products, kinematics) are
    inlined, so the equations still show their structure. The others (logs, Jacobians,
    normalization: anything with branches, `atan2`, `sqrt`) stay opaque: each output entry is an
    applied function `name[i](args…)` of the flattened arguments. Expanding the inlined form of
    those is what makes analysis intractable. Each opaque entry carries the Modelica function as
    its numeric implementation, so `lambdify` still evaluates it."""
    impls: dict = {}
    kinds: dict = {}

    def kind(name, shapes):
        """Inline or opaque, and the output shape: decided once per function and argument
        shapes, on fresh symbols (evaluating on the actual arguments is the blowup)."""
        key = (name, shapes)
        if key not in kinds:
            dummies = [sp.Symbol(f"_a{k}") if s is None
                       else sp.Matrix(*s, sp.symbols(f"_a{k}_0:{s[0] * s[1]}"))
                       for k, s in enumerate(shapes)]
            res = functions[name](*dummies)
            kinds[key] = (_is_polynomial(res),
                          res.shape if isinstance(res, sp.MatrixBase) else None)
        return kinds[key]

    def numeric(name, shapes):
        f = functions[name]

        @lru_cache(maxsize=4096)
        def run(*scalars):
            args, k = [], 0
            for shape in shapes:
                n = 1 if shape is None else shape[0] * shape[1]
                vals = [sp.Float(s) for s in scalars[k:k + n]]
                args.append(vals[0] if shape is None else sp.Matrix(*shape, vals))
                k += n
            return [float(sp.N(e)) for e in _flat(f(*args))]
        return run

    def call(name, *args):
        shapes = tuple(a.shape if isinstance(a, sp.MatrixBase) else None for a in args)
        inline, out_shape = kind(name, shapes)
        if inline:
            return functions[name](*args)
        key = (name, shapes)
        if key not in impls:
            run = numeric(name, shapes)
            n = 1 if out_shape is None else out_shape[0] * out_shape[1]
            base = sanitize(name.replace(".", "_"))  # lambdify needs identifiers
            impls[key] = [implemented_function(sp.Function(f"{base}_{i}" if n > 1 else base),
                                               lambda *s, i=i, run=run: run(*s)[i])
                          for i in range(n)]
        flat_args = [s for a in args for s in _flat(a)]
        out = [fi(*flat_args) for fi in impls[key]]
        return out[0] if out_shape is None else sp.Matrix(*out_shape, out)

    return call


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
            path = r.get("path")
            variables.append(Var(r["name"], r["role"], tuple(r["shape"] or ()), r["symbol"],
                                 r.get("binding"), r.get("start"), r.get("fixed"), r.get("unit"),
                                 r.get("description"), r.get("vendor_annotations"),
                                 tuple(path) if path is not None else None, r.get("physical"),
                                 r.get("minimum_values"), r.get("maximum_values"),
                                 r.get("nominal_values"), r.get("state_select"),
                                 r.get("causality")))
    # Modelica function calls: inline the polynomial ones, keep the rest opaque (opaque_calls)
    functions = getattr(mod, "FUNCTIONS", None)
    eqs = mod.equations(call=opaque_calls(functions)) if functions else mod.EQUATIONS
    # keep rumoca's declaration order within each role (Lean structure field order)
    return Model(mod.MODEL_NAME, variables, list(eqs), dict(mod.DX),
                 getattr(mod, "MODEL_ANNOTATIONS", None), mod,
                 getattr(mod, "EQUATION_ORIGINS", None))
