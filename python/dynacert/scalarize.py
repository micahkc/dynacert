"""Array variables as scalar coordinates ("scalarization").

rumoca exports a Modelica array `Real p[3]` as one variable: in sympy a column `Matrix` of
symbols `p[1]`, `p[2]`, `p[3]`, in Lean a field `p : Fin 3 → ℝ` (a matrix `Real K[2, 3]` is
`Matrix (Fin 2) (Fin 3) ℝ`), with Modelica `p[k]` written `p (k-1)`. An array equation is one
conjunct of Lean's `Equations` relating vectors (`dx.p = x.v`, `dx.v = p.K *ᵥ x.x + u.d`), or a
family `∀ i : Fin n, …` / `∀ i : ℕ, a ≤ i → i ≤ b → …` (a `for` loop); the sympy view has the
same conjunct as a list of equations.

The linear methods and the Monte Carlo harness work on scalars. `model(m)` is the same model
with every array element as its own scalar variable (named `p[1]`, `K[1,2]`; Lean term `p 0`,
`K 0 1`) and every equation conjunct split into scalar equations, each with the Lean proof term
that extracts it from the conjunct (`congrFun h 0`, `h 0 1`, `h 2 (by norm_num) (by norm_num)`).
`spec(sp, m)` reads the `__Dynacert` annotations of array variables per component (see
`spec.py`). A model without arrays is returned unchanged.

Untrusted, like the rest of the generator: the emitted Lean evaluates each extracted component
with `simp only [SIMPS]` (lemmas in `Dynacert/Linear/Scalar.lean`) before `linear_combination`,
and the kernel re-checks every step.
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass, field, replace

import sympy as sp

from . import spec as spec_mod
from .lean import ident
from .model import Model, Var

# `simp only` set evaluating one component of rumoca's vector expressions (tested by the
# examples in Dynacert/Linear/Scalar.lean; keep the two in sync).
SIMPS = ("Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, "
         "Matrix.of_apply, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_zero, "
         "Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ, Pi.add_apply, "
         "Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply, "
         "Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, "
         "Matrix.mul_apply, Fin.isValue, Rumoca.slice, Rumoca.at1, Rumoca.at2, Rumoca.skew, "
         "Fin.succ_zero_eq_one, Fin.succ_one_eq_two, fin_succ_eq_mk, Fin.val_succ, Fin.val_zero, "
         "Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, "
         "Nat.one_le_ofNat, Nat.reduceLeDiff, and_self, dite_true, le_refl, fin_mk_ofNat, "
         "Pi.zero_apply, Matrix.zero_apply, cross_apply")
LEAN_IMPORT = "Dynacert.Linear.Scalar"


class ScalarizeError(ValueError):
    pass


# `disturbance(bound = b, norm = "2")` on an array input: the Euclidean ball `‖d‖ ≤ b`. The
# per-channel LMI would need equal rates within the group and a grouped budget in the Lean
# proof, the polyhedral and layered methods a non-box disturbance set, and the Monte Carlo
# harness sampling in the ball; none of this is implemented, so it is rejected (with this
# message) rather than certified as the weaker per-component claim.
NORM2 = ('disturbance {name}: norm = "2" (a Euclidean ball ‖{name}‖ ≤ bound) is not supported '
         'yet; remove `norm` to bound each component, |{name}[i]| ≤ bound')


@dataclass
class ElemVar(Var):
    """One element of an array variable, as a scalar variable."""
    base: str = ""          # Modelica name of the array
    index: tuple = ()       # 0-based index (Lean)

    @property
    def lean(self) -> str:
        return ident(self.base) + "".join(f" {i}" for i in self.index)


@dataclass
class ScalarModel(Model):
    """`Model` with array elements as scalar variables and scalar equations only.

    `n_bound` and `n_init` count the conjuncts of the original `Params.Bound` / `Initial`;
    `eq_handles[k]` is the Lean term (in conjunct names `eq0`, `eq1`, …) proving scalar
    equation `k`, or None without a Lean export; `state_hyps[name]` is `(i, idx)`: the state is
    conjunct `i` of `IsSolutionOn` and `idx` the Lean index arguments (`""` for a scalar)."""
    base: Model | None = None
    eq_handles: list | None = None
    n_conj: int = 0
    state_hyps: dict = field(default_factory=dict)

    @property
    def n_bound(self) -> int:
        return self.base.n_bound

    @property
    def n_init(self) -> int:
        return self.base.n_init

    def equations_flat(self) -> list:
        return list(self.equations)


def has_arrays(m: Model) -> bool:
    return any(not v.scalar for v in m.variables)


def elem_name(base: str, idx) -> str:
    """Modelica name of an element from its 0-based index: `p[1]`, `K[1,2]`."""
    return f"{base}[{','.join(str(i + 1) for i in idx)}]"


def _indices(shape) -> list[tuple]:
    return list(itertools.product(*(range(n) for n in shape)))


def _entries(x, n: int) -> list:
    """`x` (a Matrix, a list, a scalar, or None) as `n` per-element values."""
    if x is None:
        return [None] * n
    if isinstance(x, sp.MatrixBase):
        vals = list(x)
    elif isinstance(x, (list, tuple)):
        vals = list(x)
    else:
        return [x] * n
    if len(vals) != n:
        raise ScalarizeError(f"expected {n} values, got {len(vals)}")
    return vals


def elements(v: Var) -> list[Var]:
    """The scalar variables of `v` (itself if scalar), row-major (sympy's `list(Matrix)`)."""
    if v.scalar:
        return [v]
    idx = _indices(v.shape)
    syms = list(v.symbol)
    if len(syms) != len(idx):
        raise ScalarizeError(f"{v.name}: shape {v.shape} but {len(syms)} symbols")
    n = len(idx)
    out = []
    try:
        cols = (_entries(v.binding, n), _entries(v.start, n), _entries(v.fixed, n))
    except ScalarizeError as e:
        raise ScalarizeError(f"array {v.name}: {e}") from None
    for k, (ix, s, b, st, fx) in enumerate(zip(idx, syms, *cols)):
        out.append(ElemVar(elem_name(v.name, ix), v.role, (), s, b, st, fx, v.unit,
                           v.description, v.annotations, base=v.name, index=ix))
    return out


# --- Lean conjuncts ---------------------------------------------------------------------------

def _lean_conjuncts(lean_src: str) -> list[str]:
    from .lie_link import LinkError, equations_text

    try:
        return equations_text(lean_src)
    except LinkError as e:
        raise ScalarizeError(str(e)) from None


_FIN = re.compile(r"∀ ((?:\w+ )*\w+) : Fin (\d+), ")
_NAT = re.compile(r"∀ (\w+) : ℕ, (\d+) ≤ \1 → \1 ≤ (\d+) → ")


def binders(text: str) -> list[tuple]:
    """The `for`-loop binders of a Lean conjunct: `("fin", n)` or `("nat", lo, hi)`, outermost
    first."""
    s = text[1:] if text.startswith("(∀ ") else text
    out = []
    while True:
        m = _FIN.match(s)
        if m:
            out += [("fin", int(m.group(2)))] * len(m.group(1).split())
            s = s[m.end():]
            continue
        m = _NAT.match(s)
        if m:
            out.append(("nat", int(m.group(2)), int(m.group(3))))
            s = s[m.end():]
            continue
        return out


def _binder_args(bs, combo) -> str:
    parts = []
    for b, val in zip(bs, combo):
        parts.append(f" {val}" if b[0] == "fin" else f" {val} (by norm_num) (by norm_num)")
    return "".join(parts)


def _combos(bs) -> list[tuple]:
    return list(itertools.product(*(range(b[1]) if b[0] == "fin" else range(b[1], b[2] + 1)
                                    for b in bs)))


def _split_eq(eq, handle: str, rank2_cols1: bool):
    """Scalar equations of `eq` (scalar or matrix sides) with their Lean handles."""
    if not isinstance(eq, sp.Equality):
        raise ScalarizeError(f"not an equation: {eq}")
    lhs, rhs = eq.lhs, eq.rhs
    if not isinstance(lhs, sp.MatrixBase) and not isinstance(rhs, sp.MatrixBase):
        return [(eq, handle)]
    if not (isinstance(lhs, sp.MatrixBase) and isinstance(rhs, sp.MatrixBase)
            and lhs.shape == rhs.shape):
        raise ScalarizeError(f"array equation with mismatched sides: {eq}")
    r, c = lhs.shape
    out = []
    if c == 1 and not rank2_cols1:
        for i in range(r):
            out.append((sp.Eq(lhs[i, 0], rhs[i, 0], evaluate=False), f"(congrFun {handle} {i})"))
    else:
        if c == 1:
            raise ScalarizeError("an array equation of shape [n, 1] is ambiguous (vector or "
                                 "one-column matrix)")
        for i in range(r):
            for j in range(c):
                out.append((sp.Eq(lhs[i, j], rhs[i, j], evaluate=False),
                            f"(congrFun (congrFun {handle} {i}) {j})"))
    return out


def _scalar_equations(m: Model, lean_src: str | None):
    """Scalar equations, their Lean handles (None without `lean_src`), and the conjunct count."""
    texts = _lean_conjuncts(lean_src) if lean_src is not None else None
    if texts is not None and len(texts) != len(m.equations):
        raise ScalarizeError(f"array equations: parsed {len(texts)} Lean equations, the sympy view has "
                             f"{len(m.equations)}")
    rank2_cols1 = any(len(v.shape) == 2 and v.shape[1] == 1 for v in m.variables)
    eqs, handles = [], []
    for j, e in enumerate(m.equations):
        entries = list(e) if isinstance(e, (list, tuple)) else [e]
        h = f"eq{j}"
        if texts is None:
            for x in entries:
                eqs += [q for q, _ in _split_eq(x, h, rank2_cols1)]
            continue
        bs = binders(texts[j])
        if bs:
            combos = _combos(bs)
            if len(combos) != len(entries):
                raise ScalarizeError(f"array equation {j}: {len(entries)} sympy equations for "
                                     f"{len(combos)} loop values in `{texts[j][:80]}`")
            hs = [f"({h}{_binder_args(bs, c)})" for c in combos]
        else:
            if len(entries) != 1:
                raise ScalarizeError(f"array equation {j}: a family of {len(entries)} equations "
                                     f"without a recognized loop in `{texts[j][:80]}`")
            hs = [h]
        for x, hx in zip(entries, hs):
            for q, hq in _split_eq(x, hx, rank2_cols1):
                eqs.append(q)
                handles.append(hq)
    return eqs, (handles if texts is not None else None), len(m.equations)


# --- the scalar model and spec ------------------------------------------------------------------

def model(m: Model, lean_src: str | None = None) -> Model:
    """The scalar view of `m` (`m` itself when it has no arrays). With `lean_src`, each scalar
    equation also carries its Lean handle (`ScalarModel.eq_handles`). Cached on `m`."""
    if isinstance(m, ScalarModel) or not has_arrays(m):
        return m
    cache = m.__dict__.setdefault("_dynacert_scalar", {})
    key = lean_src is not None
    if key not in cache:
        variables = [e for v in m.variables for e in elements(v)]
        der = {}
        state_hyps = {}
        for i, v in enumerate(m.states):
            d = m.der[v.name]
            if v.scalar:
                der[v.name] = d
                state_hyps[v.name] = (i, "")
                continue
            for e, ds in zip(elements(v), list(d)):
                der[e.name] = ds
                state_hyps[e.name] = (i, "".join(f" {k}" for k in e.index))
        eqs, handles, n_conj = _scalar_equations(m, lean_src)
        cache[key] = ScalarModel(m.name, variables, eqs, der, m.annotations, m.module,
                                 base=m, eq_handles=handles, n_conj=n_conj,
                                 state_hyps=state_hyps)
    return cache[key]


def _pick(x, k: int, n: int, what: str):
    if isinstance(x, list):
        if len(x) != n:
            raise ScalarizeError(f"{what}: {len(x)} values for {n} components")
        return x[k]
    return x


def spec(sp_: spec_mod.Spec, m: Model) -> spec_mod.Spec:
    """`sp_` with every annotated array variable replaced by its components (see `spec.py`).
    Names that are already components (or scalars) are kept."""
    base = m.base if isinstance(m, ScalarModel) else m
    arrays = {v.name: v for v in base.variables if not v.scalar}

    def comps(name):
        v = arrays.get(name)
        return None if v is None else elements(v)

    out = replace(sp_, disturbances=[], certify=[], uncertain=[], references=[], initial=[])
    for d in sp_.disturbances:
        es = comps(d.name)
        if es is None:
            if isinstance(d.bound, list):
                raise ScalarizeError(f"{d.name}: a list of bounds for a scalar input")
            out.disturbances.append(replace(d, norm=None))
            continue
        if d.norm == "2":
            raise ScalarizeError(NORM2.format(name=d.name))
        for k, e in enumerate(es):
            out.disturbances.append(spec_mod.Disturbance(
                e.name, _pick(d.bound, k, len(es), d.name), None, d.name))
    for n in sp_.certify:
        es = comps(n)
        out.certify += [n] if es is None else [e.name for e in es]
    for u in sp_.uncertain:
        es = comps(u.name)
        if es is None:
            out.uncertain.append(u)
            continue
        out.uncertain += [spec_mod.Uncertain(e.name, _pick(u.lo, k, len(es), u.name),
                                             _pick(u.hi, k, len(es), u.name))
                          for k, e in enumerate(es)]
    for r in sp_.references:
        es = comps(r.name)
        if es is None:
            out.references.append(r)
            continue
        if r.derivative:
            ds = comps(r.derivative)
            if ds is None or len(ds) != len(es):
                raise ScalarizeError(f"reference {r.name}: its derivative {r.derivative} must be "
                                     "an array of the same shape")
        out.references += [spec_mod.Reference(
            e.name, ds[k].name if r.derivative else None,
            _pick(r.start, k, len(es), r.name)) for k, e in enumerate(es)]
    for b in sp_.initial:
        es = comps(b.name)
        if es is None:
            out.initial.append(b)
            continue
        out.initial += [spec_mod.InitialBox(e.name, _pick(b.lo, k, len(es), b.name),
                                            _pick(b.hi, k, len(es), b.name))
                        for k, e in enumerate(es)]
    return out


def view(m: Model, sp_: spec_mod.Spec, lean_src: str | None = None):
    """`(model(m, lean_src), spec(sp_, m))`; both unchanged for a model without arrays."""
    if not has_arrays(m) and not isinstance(m, ScalarModel):
        return m, sp_
    return model(m, lean_src), spec(sp_, m)
