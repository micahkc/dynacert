"""Sector-multiplier certificates for nonlinear closed loops (untrusted search).

Implements the methods of "Where to Tear: Compositional Invariant-Tube Certificates for a
Nonlinear Quadrotor" (Condie) on a rumoca model:

* **Exact linear part plus residual channels** (§V-A). The closed loop is written exactly as
  `ẋ = A x + B_p p + B_w w`, where `A` is the Jacobian at the operating point and every
  residual `pᵢ` is either a *sector* channel `pᵢ = δᵢ(t) qᵢ`, `δᵢ ∈ [ℓᵢ, uᵢ]` on a region, or
  a *bounded* channel `|pᵢ| ≤ βᵢ`. The split is found from the equations (`extract`): every
  nonlinear atom (`sin`, `cos`, `√(s² + h²)`, `atan2(y, h)`) is its first-order part plus a
  remainder, and products are split the way the paper's Table II does.
* **Rigorous bounds.** `ℓ, u, β` are explicit rational functions of the region box, each
  backed by a lemma of `Dynacert/Sector/Atoms.lean` (Taylor inequalities, no grid).
* **LMI (8)** with multipliers `τᵢ`, energy weights and the region fixed point (Algorithm 1);
  one ellipsoid per bounded signal (Lemma 1). Blocks with quadratic supply rates (LMI (9),
  Proposition 1) use the same code with a partition of the states (`cuts.py`).

Everything here is untrusted; `emit_sector.py` emits the Lean certificate that the kernel
checks.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np
import sympy as sp

from . import exact as ex


class SectorError(Exception):
    pass


# --- model analysis ------------------------------------------------------------------------------

@dataclass
class Coord:
    """A region coordinate: a linear form `row · z` of the states, named by a model expression."""
    name: str
    expr: object        # sympy expression in model symbols (state or linear algebraic)
    row: list           # Fractions over the states


@dataclass
class Atom:
    kind: str           # "sin" | "cos" | "norm" | "atan2"
    sym: object         # placeholder symbol used in the decomposition
    expr: object        # the sympy expression it stands for (model symbols), e.g. sin(theta)
    alg: str | None     # algebraic variable defined by it (`f_norm`), if any
    # arguments: (coord index, scale λ, offset c0): argument = c0 + λ·coord
    args: dict = field(default_factory=dict)
    lean_args: dict = field(default_factory=dict)   # Lean terms of the arguments
    h0: Fraction | None = None


@dataclass
class Channel:
    kind: str           # "sector" | "bounded"
    expr: object        # sympy expression of pᵢ (model symbols)
    col: dict           # state index -> Fraction coefficient in ẋ
    rule: tuple         # how its bound is proved (see `gain`/`bound`)
    q: int | None = None        # sector: region-independent linear form index into `qforms`
    qscale: Fraction = Fraction(1)


@dataclass
class SectorProblem:
    model_name: str
    ns: str
    states: list            # state names (= coordinates z, in order)
    sfields: list           # Lean fields of the states
    A: list                 # n×n Fractions
    dists: list             # disturbance input names
    dist_fields: list
    dist_bounds: list       # Fractions
    Bw: list                # n×nd Fractions
    coords: list            # region coordinates (Coord)
    atoms: list             # Atom
    channels: list          # Channel
    qforms: list            # linear forms (rows over states) used as sector q's
    qexprs: list            # their model expressions
    outputs: list           # (name, row, lean field) of the certified outputs
    param_values: dict      # parameter name -> Fraction
    eqs: list               # sympy residuals (params substituted) in Lean conjunct order
    syms: dict              # name -> sympy symbol (states, algebraics, inputs)
    lin_alg: dict           # linear algebraic name -> row over states
    alg_eq: dict            # algebraic name -> equation index defining it
    poly_alg: list = field(default_factory=list)    # inlined polynomial algebraics, in order

    @property
    def n(self) -> int:
        return len(self.states)


def _frac(x) -> Fraction:
    x = sp.nsimplify(x, rational=True)
    if not x.is_Rational:
        raise SectorError(f"not a rational constant: {x}")
    return Fraction(int(x.p), int(x.q))


def _param_values(m) -> dict:
    vals = {v.symbol: sp.sympify(v.binding) for v in m.params if v.binding is not None}
    for _ in range(len(vals) + 1):
        new = {k: sp.nsimplify(sp.sympify(v).xreplace(vals), rational=True)
               for k, v in vals.items()}
        if new == vals:
            break
        vals = new
    return vals


def _subs(e, vals):
    """Substitute parameter values without expanding inside function arguments."""
    e = sp.sympify(e).xreplace(vals)
    return e.replace(lambda a: a.is_Float, lambda a: sp.nsimplify(a, rational=True))


def _row(expr, xs) -> list[Fraction] | None:
    """Coefficients of an expression affine in `xs` with zero constant term, else None."""
    expr = sp.expand(expr)
    row = []
    for x in xs:
        c = sp.diff(expr, x)
        if c.free_symbols:
            return None
        row.append(_frac(c))
    rest = sp.expand(expr - sum(sp.Rational(r.numerator, r.denominator) * x
                                for r, x in zip(row, xs)))
    if rest.free_symbols:
        return None
    return row if rest == 0 else None


def _affine(expr, xs):
    """(constant, row) for an affine expression in `xs`, else None."""
    expr = sp.expand(expr)
    c0 = expr.subs({x: 0 for x in xs})
    if c0.free_symbols:
        return None
    row = _row(expr - c0, xs)
    return None if row is None else (_frac(c0), row)


def extract(prob) -> SectorProblem:
    """Exact linear part, residual channels and region coordinates from the model."""
    m, spec = prob.model, prob.spec
    if any(not v.scalar for v in m.variables):
        raise SectorError("array variables are not supported by the sector method yet")
    if spec.uncertain:
        raise SectorError("uncertain parameters are not supported by the sector method yet")
    if spec.references:
        raise SectorError("references are not supported by the sector method yet (it "
                          "certifies a tube about an equilibrium)")
    if spec.initial:
        raise SectorError("initialSet is not supported by the sector method yet")
    if not spec.certify:
        raise SectorError("nothing to certify: annotate outputs with __Dynacert(certify)")
    vals = _param_values(m)
    pvals = {}
    for v in m.params:
        if v.symbol in vals:
            try:
                pvals[v.name] = _frac(vals[v.symbol])
            except SectorError:
                pass
    states = [v for v in m.states]
    xs = [v.symbol for v in states]
    dist_names = [d.name for d in spec.disturbances]
    for d in spec.disturbances:
        if isinstance(d.bound, list) or d.norm == "2":
            raise SectorError("only scalar componentwise disturbance bounds are supported")
    ins = {v.name: v.symbol for v in m.inputs}
    others = [n_ for n_ in ins if n_ not in dist_names]
    if others:
        raise SectorError(f"inputs other than disturbances are not supported: {others}")
    ws = [ins[d] for d in dist_names]
    syms = {v.name: v.symbol for v in m.variables if v.role != "parameter"}
    algs = {v.name: v for v in m.algebraics}
    eqs = [_subs(e.lhs - e.rhs, vals) for e in m.equations]
    # defining equation of each algebraic and of each derivative
    alg_eq, der_eq, alg_rhs = {}, {}, {}
    dsyms = {d: n_ for n_, d in m.der.items()}
    for k, e in enumerate(m.equations):
        lhs = e.lhs
        if lhs in dsyms:
            der_eq[dsyms[lhs]] = k
        elif isinstance(lhs, sp.Symbol) and lhs.name in algs:
            alg_eq[lhs.name] = k
            alg_rhs[lhs.name] = _subs(e.rhs, vals)
        else:
            raise SectorError(f"equation {k + 1} is not of the form `der(x) = …` or `y = …`")
    if set(der_eq) != {v.name for v in states}:
        raise SectorError("every state needs one explicit `der(x) = …` equation")
    if set(alg_eq) != set(algs):
        raise SectorError("every algebraic variable needs one explicit `y = …` equation")
    # linear algebraics (affine in states, possibly through other linear algebraics)
    lin_alg: dict = {}
    for _ in range(len(algs) + 1):
        for name, rhs in alg_rhs.items():
            if name in lin_alg:
                continue
            r = rhs.xreplace({syms[k]: sum(sp.Rational(c.numerator, c.denominator) * x
                                           for c, x in zip(row, xs))
                              for k, row in lin_alg.items()})
            if r.free_symbols - set(xs):
                continue
            row = _row(r, xs)
            if row is not None:
                lin_alg[name] = row

    def lin_row(e):
        """Row over states of an expression linear in states and linear algebraics."""
        r = sp.sympify(e).xreplace({syms[k]: sum(sp.Rational(c.numerator, c.denominator) * x
                                                 for c, x in zip(row, xs))
                                    for k, row in lin_alg.items()})
        if r.free_symbols - set(xs):
            return None
        return _affine(r, xs)

    coords: list[Coord] = []

    def coord_of(e):
        """(coord index, λ, c0) with e = c0 + λ·coord."""
        a = lin_row(e)
        if a is None:
            raise SectorError(f"atom argument {e} is not affine in the states")
        c0, row = a
        nz = [c for c in row if c != 0]
        if not nz:
            raise SectorError(f"atom argument {e} is constant")
        lead = nz[0]
        canon = [c / lead for c in row]
        for i, c in enumerate(coords):
            ref = [v / [w for w in c.row if w != 0][0] for v in c.row]
            if ref == canon:
                return i, lead / [w for w in c.row if w != 0][0], c0
        # name the coordinate by a model symbol with this row (state or linear algebraic)
        name, cexpr, crow = None, None, None
        for k, v in enumerate(states):
            if canon == [Fraction(int(j == k)) for j in range(len(xs))]:
                name, cexpr, crow = v.name, v.symbol, canon
        for k, row in lin_alg.items():
            if name is None and row[[i for i, c in enumerate(row) if c != 0][0]] != 0:
                lead_k = [c for c in row if c != 0][0]
                if [c / lead_k for c in row] == canon:
                    name, cexpr, crow = k, syms[k], row
        if name is None:
            raise SectorError(f"no model variable equals the region coordinate of {e}")
        coords.append(Coord(name, cexpr, crow))
        lead_c = [w for w in crow if w != 0][0]
        return len(coords) - 1, lead / lead_c, c0

    atoms: list[Atom] = []

    def atom_of(kind, expr, alg=None, **args):
        for a in atoms:
            if a.expr == expr:
                return a
        a = Atom(kind, sp.Symbol(f"_atom{len(atoms)}"), expr, alg)
        if kind in ("sin", "cos"):
            i, lam, c0 = coord_of(args["L"])
            if c0 != 0:
                raise SectorError(f"{kind}({args['L']}) is not centred at the operating point")
            a.args = {"L": (i, lam, c0)}
        elif kind == "norm":
            a.args = {"s": coord_of(args["s"]), "h": coord_of(args["h"])}
            if a.args["s"][2] != 0:
                raise SectorError(f"thrust norm: {args['s']} is not centred")
            a.h0 = a.args["h"][2]
            if a.h0 <= 0:
                raise SectorError("thrust norm: h(0) must be positive")
        elif kind == "unit":
            # q0 = √(1 − Σ xₖ²): the scalar part of a unit quaternion in the vector-part chart
            a.args = {f"x{k}": coord_of(x) for k, x in enumerate(args["xs"])}
            if any(v[2] != 0 for v in a.args.values()):
                raise SectorError(f"{expr}: the vector part is not centred")
            a.h0 = Fraction(1)
            a.lean_args = {f"x{k}": x for k, x in enumerate(args["xs"])}
            atoms.append(a)
            return a
        elif kind == "atan2":
            a.args = {"y": coord_of(args["y"]), "h": coord_of(args["h"])}
            if a.args["y"][2] != 0:
                raise SectorError(f"atan2: {args['y']} is not centred")
            a.h0 = a.args["h"][2]
            if a.h0 <= 0:
                raise SectorError("atan2(y, h): h(0) must be positive")
        a.lean_args = {k_: v_ for k_, v_ in args.items()}
        atoms.append(a)
        return a

    # nonlinear algebraics -> atoms; polynomial ones are inlined
    nl_alg, poly_cand = {}, {}
    for name, rhs in alg_rhs.items():
        if name in lin_alg:
            continue
        unit = _unit_args(rhs)
        if unit is not None:
            nl_alg[name] = atom_of("unit", rhs, name, xs=unit)
        elif isinstance(rhs, sp.Pow) and rhs.exp == sp.Rational(1, 2) and rhs.base.is_Add \
                and len(rhs.base.args) == 2 and all(isinstance(t, sp.Pow) and t.exp == 2
                                                    for t in rhs.base.args):
            t0, t1 = rhs.base.args
            # the order of the sum as sympy keeps it; pick s = the centred one
            (s_, h_) = (t0.base, t1.base)
            if lin_row(s_) and lin_row(s_)[0] != 0:
                s_, h_ = h_, s_
            nl_alg[name] = atom_of("norm", rhs, name, s=s_, h=h_)
        elif isinstance(rhs, sp.atan2):
            nl_alg[name] = atom_of("atan2", rhs, name, y=rhs.args[0], h=rhs.args[1])
        else:
            poly_cand[name] = rhs
    # polynomial algebraics: polynomials in states, linear algebraics, atoms and each other
    base = set(xs) | {syms[k] for k in lin_alg} | {syms[k] for k in nl_alg}
    poly_alg: dict = {}
    for _ in range(len(poly_cand) + 1):
        for name, rhs in poly_cand.items():
            if name in poly_alg:
                continue
            ok = base | {syms[k] for k in poly_alg}
            if rhs.free_symbols <= ok and rhs.is_polynomial(*rhs.free_symbols) \
                    and not rhs.atoms(sp.Function):
                poly_alg[name] = rhs
    for name, rhs in poly_cand.items():
        if name not in poly_alg:
            raise SectorError(f"algebraic {name} = {rhs}: unsupported nonlinearity (the sector "
                              "method knows polynomials, sin, cos, √(s²+h²), √(1 − Σx²), "
                              "atan2(y, h))")

    def inline(e):
        """Substitute the polynomial algebraics (repeatedly: they may use each other)."""
        rep = {syms[k]: v for k, v in poly_alg.items()}
        for _ in range(len(rep) + 1):
            e2 = e.xreplace(rep)
            if e2 == e:
                break
            e = e2
        return e

    def to_poly(e):
        """Replace atoms by placeholder symbols."""
        e = inline(sp.sympify(e))
        e = e.xreplace({syms[k]: a.sym for k, a in nl_alg.items()})
        rep = {}
        for f in e.atoms(sp.sin, sp.cos):
            rep[f] = atom_of("sin" if isinstance(f, sp.sin) else "cos", f, L=f.args[0]).sym
        e = e.xreplace(rep)
        if e.atoms(sp.Function) or e.atoms(sp.Pow) and any(not p.exp.is_Integer
                                                           for p in e.atoms(sp.Pow)):
            raise SectorError(f"unsupported nonlinearity in {e}")
        return sp.expand(e)

    by_sym = lambda: {a.sym: a for a in atoms}
    poly_raw: list = []     # (row, coef, [(sym, coord, λ, row over states)], j, unit atom)
    poly_bnd: dict = {}     # row -> [(coef, [], j, unit atom)]
    n = len(xs)
    A = [[Fraction(0)] * n for _ in range(n)]
    Bw = [[Fraction(0)] * len(ws) for _ in range(n)]
    chans: dict = {}
    order: list = []

    def add_chan(kind, expr, row_i, coef, rule, q=None):
        expr = sp.sympify(expr)
        key = (kind, sp.srepr(expr))
        if key not in chans:
            chans[key] = Channel(kind, expr, {}, rule, q)
            order.append(key)
        c = chans[key]
        c.col[row_i] = c.col.get(row_i, Fraction(0)) + Fraction(coef)

    qforms, qexprs = [], []

    def qform(expr):
        a = lin_row(expr)
        if a is None or a[0] != 0:
            raise SectorError(f"sector variable {expr} is not linear in the states")
        if a[1] in qforms:
            return qforms.index(a[1])
        qforms.append(a[1])
        qexprs.append(expr)
        return len(qforms) - 1

    def atom_lin(a):
        """(φ0, linear expression φ1 in model symbols) of an atom."""
        if a.kind == "sin":
            return Fraction(0), a.expr.args[0]
        if a.kind == "cos":
            return Fraction(1), sp.Integer(0)
        h = a.lean_args["h"]
        if a.kind == "norm":
            return a.h0, sp.expand(h - rat(a.h0))
        return Fraction(0), a.lean_args["y"] / rat(a.h0)

    def rho_expr(a):
        phi0, phi1 = atom_lin(a)
        lhs = syms[a.alg] if a.alg else a.expr
        return lhs - rat(phi0) - phi1

    def lin_or_atom(f):
        return by_sym().get(f)

    for i, v in enumerate(states):
        k = der_eq[v.name]
        rhs = _subs(m.equations[k].rhs, vals)
        poly = to_poly(rhs)
        const = Fraction(0)
        for term in sp.Add.make_args(poly):
            c, facs = term.as_coeff_mul()
            c = _frac(c)
            flist = []
            for f in facs:
                b, e_ = f.as_base_exp()
                if not e_.is_Integer or e_ < 1:
                    raise SectorError(f"unsupported term {term}")
                flist += [b] * int(e_)
            wf = [f for f in flist if f in ws]
            if wf:
                if len(flist) != 1:
                    raise SectorError(f"disturbance enters nonlinearly: {term}")
                Bw[i][ws.index(wf[0])] += c
                continue
            atm = [by_sym()[f] for f in flist if f in by_sym()]
            lin = [f for f in flist if f not in by_sym()]
            if not flist:
                const += c
                continue
            if any(a.kind == "unit" for a in atm) or (not atm and len(lin) >= 2):
                if any(a.kind != "unit" for a in atm) or len({id(a) for a in atm}) > 1:
                    raise SectorError(f"term {term} in der({v.name}) mixes the quaternion chart "
                                      "with other atoms")
                const += _poly_term(c, lin, atm, i, A, lin_row, coord_of, poly_raw, poly_bnd)
                continue
            if not atm:
                if len(lin) != 1:
                    raise SectorError(f"polynomial term {term} in der({v.name}) is not "
                                      "supported (only atoms and linear terms)")
                ar = lin_row(lin[0])
                if ar is None:
                    raise SectorError(f"term {term} is not linear")
                const += c * ar[0]
                for j in range(n):
                    A[i][j] += c * ar[1][j]
                continue
            if len(atm) == 1 and not lin:
                const += _single_atom(atm[0], c, i, A, add_chan, qform, atom_lin, rho_expr,
                                      lin_row, syms)
                continue
            if len(atm) + len(lin) == 2:
                const += _pair(atm, lin, c, i, A, add_chan, qform, atom_lin, rho_expr,
                               lin_row, syms)
                continue
            raise SectorError(f"term {term} in der({v.name}) has more than two factors")
        if const != 0:
            raise SectorError(f"der({v.name}) is {const} at the origin: the operating point is "
                              "not an equilibrium")
    for i, L, terms in _assign_q(poly_raw, A, xs, syms):
        k = qform(L)
        add_chan("sector", _poly_delta(terms, syms) * qexprs[k], i, 1, ("poly", terms), k)
    for i, terms in poly_bnd.items():
        add_chan("bounded", _poly_delta(terms, syms), i, 1, ("poly", terms))
    channels = [chans[k] for k in order]
    channels = [c for c in channels if any(v != 0 for v in c.col.values())]
    for c in channels:
        if c.kind == "sector" and c.q is None:
            raise SectorError("internal: sector channel without q")
    outputs = []
    for name in spec.certify:
        if name in [v.name for v in states]:
            k = [v.name for v in states].index(name)
            outputs.append((name, [Fraction(int(j == k)) for j in range(n)], states[k].lean))
        else:
            raise SectorError(f"certified output {name} must be a state")
    return SectorProblem(
        model_name=m.name, ns=m.ns, states=[v.name for v in states],
        sfields=[v.lean for v in states], A=A, dists=dist_names,
        dist_fields=[m.var(d).lean for d in dist_names],
        dist_bounds=[Fraction(d.bound) for d in spec.disturbances], Bw=Bw, coords=coords,
        atoms=atoms, channels=channels, qforms=qforms, qexprs=qexprs, outputs=outputs,
        param_values=pvals, eqs=eqs, syms=syms, lin_alg=lin_alg, alg_eq=alg_eq,
        poly_alg=list(poly_alg))


def rat(x: Fraction):
    return sp.Rational(Fraction(x).numerator, Fraction(x).denominator)


def _unit_args(rhs):
    """The xₖ of `√(1 − Σ xₖ²)` (symbols), else None."""
    if not (isinstance(rhs, sp.Pow) and rhs.exp == sp.Rational(1, 2)):
        return None
    rest = sp.expand(1 - rhs.base)
    xs = []
    for t in sp.Add.make_args(rest):
        if not (isinstance(t, sp.Pow) and t.exp == 2 and t.base.is_Symbol):
            return None
        xs.append(t.base)
    return sorted(xs, key=str) if xs else None


def _q_priority(sym, xs):
    """Which linear factor of a product becomes the sector variable `q` (the others form δ):
    linear algebraics (outer-loop commands) first, then states declared later (rates before
    attitude before translation), as in the planar model's `−s_z sin θ` (q = −s_z)."""
    return (0, 0) if sym not in xs else (1, -xs.index(sym))


def _poly_term(c, lin, atm, i, A, lin_row, coord_of, poly_raw, poly_bnd):
    """`c·Π lin·q0^m` with q0 = 1 + ρ (ρ = q0 − 1): first-order part into `A`, products of
    small factors into `poly_raw` (second order: the sector variable is chosen once `A` is
    complete, by `_assign_q`), third order and up (ρ counts twice) into the row's bounded group.
    Returns the constant part."""
    unit = atm[0] if atm else None
    m_ = len(atm)
    const = Fraction(0)
    for j in range(m_ + 1):
        coef = c * math.comb(m_, j)
        if not lin:
            if j == 0:
                const += coef
            else:
                poly_bnd.setdefault(i, []).append((coef, [], j, unit))
            continue
        if len(lin) == 1 and j == 0:
            ar = lin_row(lin[0])
            if ar is None:
                raise SectorError(f"{lin[0]} is not linear in the states")
            const += coef * ar[0]
            for k in range(len(A)):
                A[i][k] += coef * ar[1][k]
            continue
        facs = []
        for f in lin:
            ar = lin_row(f)
            if ar is None or ar[0] != 0:
                raise SectorError(f"factor {f} of a product is not centred at the operating point")
            ci, lam, _ = coord_of(f)
            facs.append((f, ci, lam, ar[1]))
        if len(facs) + 2 * j >= 3:
            # third order and up (ρ = q0 − 1 is second order): one bounded channel per row
            poly_bnd.setdefault(i, []).append((coef, [t[:3] for t in facs], j, unit))
        else:
            poly_raw.append((i, coef, facs, j, unit))
    return const


def _assign_q(poly_raw, A, xs, syms):
    """Write the second-order products of each row as sector channels `δ · L(z)`.

    * If a factor already enters the row linearly (`A_i · row_f ≠ 0`), the product is a bounded
      change of that loop's gain: `q` is that factor (the strongest one) and the products with
      the same `q` are summed into `δ` (in v̇_x, `2 (g − s_z) qy` gives `q = qy`,
      `δ = −2 s_z`: a few percent of `2g`).
    * Otherwise one linear factor (`_q_priority`) is kept as the product's share of `q` and the
      other is `δ`; products with the same `δ` are merged, so their linear factors add up to one
      `L`. This keeps cancellations: in v̇_z, `−2 s_x qy − 4g qy² = −2g · qy · (2qy + s_x/g)`,
      a tilt times the pitch *tracking error*.

    `DYNACERT_SECTOR_Q=gain|delta` forces one rule. Returns `[(row, L, terms)]` with
    `terms = [(coef, others, j, unit)]` and `δ = Σ coef · Π others · ρʲ`."""
    import os

    mode = os.environ.get("DYNACERT_SECTOR_Q", "auto")
    groups: dict = {}
    order = []
    for i, coef, facs, j, unit in poly_raw:
        a = [abs(sum(A[i][k] * row[k] for k in range(len(row)))) for _, _, _, row in facs]
        gain = mode == "gain" or (mode == "auto" and max(a) > 0)
        if gain:
            k = min(range(len(facs)), key=lambda t: (-a[t],) + _q_priority(facs[t][0], xs))
        else:
            k = min(range(len(facs)), key=lambda t: _q_priority(facs[t][0], xs))
        others = sorted(((f, ci, lam) for t, (f, ci, lam, _) in enumerate(facs) if t != k),
                        key=lambda o: str(o[0]))
        qf = facs[k][0]
        if gain:
            key = (i, "q", str(qf))
            if key not in groups:
                groups[key] = (qf, [])
                order.append(key)
            groups[key][1].append((coef, others, j, unit))
            continue
        key = (i, tuple(str(o[0]) for o in others), j, id(unit) if j else None)
        if key not in groups:
            groups[key] = (sp.Integer(0), [(Fraction(1), others, j, unit)])
            order.append(key)
        L, t = groups[key]
        groups[key] = (L + rat(coef) * qf, t)
    out = []
    for key in order:
        L, t = groups[key]
        L = sp.expand(L)
        if L != 0:
            out.append((key[0], L, t))
    return out


def _poly_delta(terms, syms):
    """Σ coef · Π others · ρʲ as a model expression (ρ = q0 − 1)."""
    out = sp.Integer(0)
    for coef, others, j, unit in terms:
        t = rat(coef)
        for f, _, _ in others:
            t = t * f
        if j:
            t = t * (syms[unit.alg] - 1) ** j
        out += t
    return out


def unit_rho_bound(a: Atom, R) -> Fraction | None:
    """`|q0 − 1| ≤ X/(2 − X)` with `X = Σ bₖ²` (needs X ≤ 1), rounded up."""
    X = sum((_arg_bound(a, k, R) ** 2 for k in a.args), Fraction(0))
    if X > 1:
        return None
    return up(X / (2 - X))


def poly_term_bounds(terms, R):
    """Bounds of each term `|coef · Π others · ρʲ|` (without the coefficient), or None."""
    out = []
    for coef, others, j, unit in terms:
        b = Fraction(1)
        for _, ci, lam in others:
            b *= abs(lam) * R[ci]
        if j:
            r = unit_rho_bound(unit, R)
            if r is None:
                return None
            b *= r ** j
        out.append(b)
    return out


def poly_bound(terms, R):
    bs = poly_term_bounds(terms, R)
    if bs is None:
        return None
    return sum((abs(t[0]) * b for t, b in zip(terms, bs)), Fraction(0))


def _single_atom(a, c, i, A, add_chan, qform, atom_lin, rho_expr, lin_row, syms):
    """c·φ = c φ0 + c φ1 + c ρ: returns the constant c φ0."""
    phi0, phi1 = atom_lin(a)
    ar = lin_row(phi1) if phi1 != 0 else (Fraction(0), [Fraction(0)] * len(A))
    for j in range(len(A)):
        A[i][j] += c * ar[1][j]
    rho = rho_expr(a)
    if a.kind == "sin":
        add_chan("sector", rho, i, c, ("sinrem", a), qform(a.expr.args[0]))
    elif a.kind == "atan2":
        add_chan("sector", rho, i, c, ("atan2rem", a), qform(a.lean_args["y"]))
    else:  # cos, norm: bounded remainder
        add_chan("bounded", rho, i, c, ("prod", [("rho", a)]))
    return c * phi0 + c * ar[0]


def _pair(atm, lin, c, i, A, add_chan, qform, atom_lin, rho_expr, lin_row, syms):
    """Two-factor terms, split as in the paper's Table II. Returns the constant part."""
    if len(atm) == 1:
        F, S = lin[0], atm[0]                     # linear × atom
        if S.kind in ("sin",):
            # F·S = sector (q = F, δ = S)
            add_chan("sector", F * S.expr, i, c, ("prod_gain", S), qform(F))
            return Fraction(0)
        if S.kind == "cos":
            # F·C = F + F·(C - 1)
            ar = lin_row(F)
            for j in range(len(A)):
                A[i][j] += c * ar[1][j]
            add_chan("bounded", F * (S.expr - 1), i, c, ("prod", [("lin", F), ("rho", S)]))
            return c * ar[0]
        raise SectorError(f"product of {F} with {S.kind} is not supported")
    a, b = atm
    # pick S: the factor vanishing at the origin with a nonzero linear part (sin, atan2)
    if a.kind in ("sin", "atan2") and b.kind not in ("sin", "atan2"):
        F, S = b, a
    elif b.kind in ("sin", "atan2") and a.kind not in ("sin", "atan2"):
        F, S = a, b
    elif a.kind == "cos" or b.kind == "cos":
        F, S = (b, a) if a.kind == "cos" else (a, b)
        if F.kind == "cos":
            raise SectorError("cos·cos terms are not supported")
        # F·C = F + F·(C - 1): F as a single atom, F·(C-1) bounded
        k0 = _single_atom(F, c, i, A, add_chan, qform, atom_lin, rho_expr, lin_row, syms)
        Fx = syms[F.alg] if F.alg else F.expr
        add_chan("bounded", Fx * (S.expr - 1), i, c, ("prod", [("atom", F), ("rho", S)]))
        return k0
    else:
        raise SectorError(f"product of {a.kind} and {b.kind} is not supported")
    if S.kind != "sin":
        raise SectorError(f"product with {S.kind} is not supported")
    if F.kind == "cos":
        raise SectorError("cos·sin terms are not supported")
    phi0, phi1 = atom_lin(F)
    # F·S = F0·S + F1·S + ρF·S
    k0 = _single_atom(S, c * phi0, i, A, add_chan, qform, atom_lin, rho_expr, lin_row, syms)
    if phi1 != 0:
        add_chan("sector", phi1 * S.expr, i, c, ("prod_gain", S), qform(phi1))
    rho = rho_expr(F)
    add_chan("bounded", rho * S.expr, i, c, ("prod", [("rho", F), ("atom", S)]))
    return k0


# --- region-dependent constants (mirror the lemmas of Dynacert/Sector/Atoms.lean) -----------------

def _arg_bound(a: Atom, key: str, R) -> Fraction:
    i, lam, _ = a.args[key]
    return abs(lam) * R[i]


def _h_range(a: Atom, R):
    c = _arg_bound(a, "h", R)
    return a.h0 - c, a.h0 + c


def gain(ch: Channel, R):
    """Sector interval `[ℓ, u]` of a sector channel on the region `R` (exact)."""
    kind, a = ch.rule
    if kind == "poly":
        b = poly_bound(a, R)
        return None if b is None else (-b, b)
    if kind == "sinrem":
        aa = _arg_bound(a, "L", R)
        return -aa * aa / 6, Fraction(0)
    if kind == "prod_gain":          # δ = sin(L), |δ| ≤ a
        aa = _arg_bound(a, "L", R)
        return -aa, aa
    if kind == "atan2rem":
        b = _arg_bound(a, "y", R)
        h0, h1 = _h_range(a, R)
        if h0 <= 0 or b > h0:
            return None
        k = 1 / a.h0
        return (1 - b * b / (3 * h0 * h0)) / h1 - k, 1 / h0 - k
    raise SectorError(kind)


def factor_bound(f, R, coords=None):
    kind, a = f
    if kind == "lin":
        raise SectorError("linear factors in bounded channels need a region coordinate")
    if a.kind == "sin":
        aa = _arg_bound(a, "L", R)
        return aa if kind == "atom" else aa ** 3 / 6
    if a.kind == "cos":
        aa = _arg_bound(a, "L", R)
        return Fraction(1) if kind == "atom" else aa * aa / 2
    if a.kind == "norm":
        b = _arg_bound(a, "s", R)
        h0, h1 = _h_range(a, R)
        if h0 <= 0:
            return None
        rho = b * b / (2 * h0)
        return h1 + rho if kind == "atom" else rho
    raise SectorError(f"no bound for {kind} of {a.kind}")


def bound(ch: Channel, R):
    """Peak bound β of a bounded channel on the region `R` (exact), or None."""
    if ch.rule[0] == "poly":
        return poly_bound(ch.rule[1], R)
    out = Fraction(1)
    for f in ch.rule[1]:
        b = factor_bound(f, R)
        if b is None:
            return None
        out *= up(b)        # the Lean proof bounds each factor by this rounded value
    return out


DEN = 10**6


def down(x: Fraction, den: int = DEN) -> Fraction:
    """A small-denominator rational ≤ x."""
    return Fraction(math.floor(Fraction(x) * den), den)


def up(x: Fraction, den: int = DEN) -> Fraction:
    """A small-denominator rational ≥ x."""
    return Fraction(math.ceil(Fraction(x) * den), den)


def constants(sp_: SectorProblem, R):
    """Sector intervals and bounds on the region (rounded outward to small denominators), or
    None if a bound is undefined there."""
    gains, betas = [], []
    for ch in sp_.channels:
        if ch.kind == "sector":
            g = gain(ch, R)
            if g is None:
                return None
            gains.append((down(g[0]), up(g[1])))
            betas.append(None)
        else:
            b = bound(ch, R)
            if b is None:
                return None
            gains.append(None)
            betas.append(up(b))
    return gains, betas


# --- LMI (8)/(9) --------------------------------------------------------------------------------

@dataclass
class Block:
    """One subsystem of a partition: its states and the signals entering its rows."""
    idx: list               # state indices
    signals: list           # ("chan", j) | ("dist", j) | ("iface", e)
    A: np.ndarray
    B: np.ndarray           # columns per signal
    sectors: list           # (signal position, q row over ζ_b = (x_b, w_b), channel j)
    gamma_sig: list         # signal positions with an energy weight (bounded / disturbance)
    supply_in: list         # (signal position, interface e): +σ_e u²
    supply_out: list        # (row over x_b, interface e): -σ_e y²


@dataclass
class Interface:
    sender: int
    row: list               # Fraction row over the full state (support in the sender block)
    receivers: list = field(default_factory=list)


def build_blocks(sp_: SectorProblem, parts: list[list[int]]):
    """Signals, interface forms and supply terms of a partition of the states."""
    n = sp_.n
    A = np.array([[float(v) for v in r] for r in sp_.A])
    owner = {i: b for b, idx in enumerate(parts) for i in idx}
    ifaces: list[Interface] = []

    def iface(row, receiver):
        """Split `row` (over the full state) by sender block; returns [(e, coef)]."""
        out = []
        for b, idx in enumerate(parts):
            if b == receiver:
                continue
            piece = [row[j] if j in idx else Fraction(0) for j in range(n)]
            if all(v == 0 for v in piece):
                continue
            lead = [v for v in piece if v != 0][0]
            canon = [v / lead for v in piece]
            for e, I in enumerate(ifaces):
                lead_e = [v for v in I.row if v != 0][0]
                if I.sender == b and [v / lead_e for v in I.row] == canon:
                    out.append((e, lead / lead_e))
                    break
            else:
                ifaces.append(Interface(b, piece))
                out.append((len(ifaces) - 1, Fraction(1)))
        return out

    blocks = []
    for b, idx in enumerate(parts):
        sig, cols = [], []
        sectors, gsig = [], []
        nb = len(idx)
        # interface inputs from the off-block linear coupling
        iface_cols: dict = {}
        for r_, i in enumerate(idx):
            row = [sp_.A[i][j] if owner[j] != b else Fraction(0) for j in range(n)]
            for e, coef in iface(row, b):
                iface_cols.setdefault(e, [0.0] * nb)
                iface_cols[e][r_] += float(coef)
        for j, ch in enumerate(sp_.channels):
            col = [float(ch.col.get(i, 0)) for i in idx]
            if any(col):
                sig.append(("chan", j))
                cols.append(col)
        for j in range(len(sp_.dists)):
            col = [float(sp_.Bw[i][j]) for i in idx]
            if any(col):
                sig.append(("dist", j))
                cols.append(col)
        # sector q's may need interface signals too
        for pos, s_ in enumerate(list(sig)):
            if s_[0] == "chan" and sp_.channels[s_[1]].kind == "sector":
                qrow = sp_.qforms[sp_.channels[s_[1]].q]
                for e, _ in iface([qrow[j] if owner[j] != b else Fraction(0)
                                   for j in range(n)], b):
                    iface_cols.setdefault(e, [0.0] * nb)
        for e, col in iface_cols.items():
            sig.append(("iface", e))
            cols.append(col)
            ifaces[e].receivers.append(b)
        m_ = len(sig)
        for pos, s_ in enumerate(sig):
            if s_[0] == "chan" and sp_.channels[s_[1]].kind == "sector":
                ch = sp_.channels[s_[1]]
                qrow = sp_.qforms[ch.q]
                qz = [qrow[i] for i in idx] + [Fraction(0)] * m_
                for e, coef in iface([qrow[j] if owner[j] != b else Fraction(0)
                                      for j in range(n)], b):
                    qz[nb + sig.index(("iface", e))] += coef
                sectors.append((pos, qz, s_[1]))
            elif s_[0] in ("chan", "dist"):
                gsig.append(pos)
        blocks.append(Block(list(idx), sig, A[np.ix_(idx, idx)],
                            np.array(cols).T if cols else np.zeros((nb, 0)), sectors, gsig,
                            [], []))
    for e, I in enumerate(ifaces):
        sb = blocks[I.sender]
        sb.supply_out.append(([I.row[i] for i in sb.idx], e))
        for r in I.receivers:
            rb = blocks[r]
            rb.supply_in.append((rb.signals.index(("iface", e)), e))
    return blocks, ifaces


def signal_bounds(sp_, blk: Block, betas):
    """Peak bound of each energy-weighted signal of a block."""
    out = {}
    for pos in blk.gamma_sig:
        kind, j = blk.signals[pos]
        out[pos] = betas[j] if kind == "chan" else sp_.dist_bounds[j]
    return out


def _theta(nz: int, m: int, pos: int, qz, lo: float, hi: float) -> np.ndarray:
    """Matrix of ζ ↦ (p - ℓ q)(u q - p) over ζ = (x, w), with p = w[pos]."""
    N = nz + m
    e = np.zeros(N)
    e[nz + pos] = 1.0
    qq = np.array([float(v) for v in qz])
    u = e - lo * qq
    v = hi * qq - e
    return 0.5 * (np.outer(u, v) + np.outer(v, u))


def lmi_blocks(sp_, blocks, ifaces, gains, betas, alpha, objective_row, margin=1e-7,
               fixed_sigma=None, budget_split=None, prox=None, only=None, obj_scale=1.0):
    """CVXPY problem for LMI (9) on every block (LMI (8) when there is one block).

    Returns (problem, variables). `objective_row` (over the full state) is the support
    direction minimized; None gives a feasibility problem. `fixed_sigma` fixes the interface
    supply rates (sender and receiver), `budget_split` fixes each block's share of the budget,
    `only` builds block `only` alone (an ADMM subproblem): its interface rates and budget share
    are free local copies, pulled towards `prox` = {"rho", "sig_in", "sig_out", "budget"}."""
    import cvxpy as cp

    n = sp_.n
    cons, Ps, gam, tau = [], [], [], []
    sig_in = {}   # (block, e) -> var
    sig_out = {}  # e -> var
    for e in range(len(ifaces)):
        sig_out[e] = cp.Variable(nonneg=True)
    for bi, blk in enumerate(blocks):
        for pos, e in blk.supply_in:
            sig_in[(bi, e)] = cp.Variable(nonneg=True)
    budgets = []
    scales = []
    for bi, blk in enumerate(blocks):
        nb, m_ = len(blk.idx), len(blk.signals)
        if only is not None and bi != only:
            scales.append(None)
            Ps.append(None)
            gam.append(None)
            tau.append(None)
            budgets.append(None)
            continue
        P = cp.Variable((nb, nb), symmetric=True)
        g = cp.Variable(m_, nonneg=True)
        t = cp.Variable(len(blk.sectors), nonneg=True) if blk.sectors else None
        Ps.append(P)
        gam.append(g)
        tau.append(t)
        # normalize each signal (sector channel by max(|ℓ|, |u|), bounded signal by its peak) so
        # that the multipliers stay O(1); γ and τ are unscaled in `_member`
        bnd = signal_bounds(sp_, blk, betas)
        scl = np.ones(m_)
        for pos, (kind, j) in enumerate(blk.signals):
            if kind == "chan" and sp_.channels[j].kind == "sector":
                lo, hi = gains[j]
                scl[pos] = max(abs(float(lo)), abs(float(hi))) or 1.0
            elif pos in bnd and float(bnd[pos]) > 0:
                scl[pos] = float(bnd[pos])
        scales.append(scl)
        Bb = blk.B * scl[None, :]
        top = blk.A.T @ P + P @ blk.A + alpha * P
        M = cp.bmat([[top, P @ Bb], [Bb.T @ P, np.zeros((m_, m_))]])
        # energy, sector, supply
        Ew = np.zeros((nb + m_, nb + m_))
        terms = []
        for pos in range(m_):
            if pos not in blk.gamma_sig:
                cons.append(g[pos] == 0)
        for pos in blk.gamma_sig:
            E = np.zeros((nb + m_, nb + m_))
            E[nb + pos, nb + pos] = 1.0
            terms.append(-g[pos] * E)
        for k, (pos, qz, j) in enumerate(blk.sectors):
            lo, hi = gains[j]
            terms.append(t[k] * _theta(nb, m_, pos, qz, float(lo) / scl[pos],
                                       float(hi) / scl[pos]))
        for pos, e in blk.supply_in:
            E = np.zeros((nb + m_, nb + m_))
            E[nb + pos, nb + pos] = 1.0
            terms.append(-sig_in[(bi, e)] * E)
        for row, e in blk.supply_out:
            r = np.concatenate([[float(v) for v in row], np.zeros(m_)])
            terms.append(sig_out[e] * np.outer(r, r))
        M = M + sum(terms) if terms else M
        # strictness margin in the original (unscaled) signal coordinates
        Dm = np.diag(np.concatenate([np.ones(nb), scl ** 2]))
        cons.append(M << -margin * Dm)
        cons.append(P >> margin * np.eye(nb))
        budgets.append(sum(g[pos] * float(bnd[pos] / scl[pos]) ** 2 for pos in blk.gamma_sig)
                       / alpha if blk.gamma_sig else cp.Constant(0))
    for e, I in enumerate(ifaces):
        if only is not None:
            break
        recv = [sig_in[(r, e)] for r in I.receivers]
        if fixed_sigma is not None:
            for r in I.receivers:
                cons.append(sig_in[(r, e)] <= fixed_sigma[e] / len(I.receivers))
            cons.append(sig_out[e] >= fixed_sigma[e])
        else:
            cons.append(sum(recv) <= sig_out[e])
    bvar = None
    if only is not None:
        bvar = cp.Variable(nonneg=True)
        cons.append(budgets[only] <= bvar)
        if budget_split is not None:
            cons.append(bvar <= budget_split[only])
        if fixed_sigma is not None:
            for (bi, e), v in sig_in.items():
                if bi == only:
                    cons.append(v <= fixed_sigma[e] / len(ifaces[e].receivers))
            for e, v in sig_out.items():
                if ifaces[e].sender == only:
                    cons.append(v >= fixed_sigma[e])
    elif budget_split is not None:
        for bi in range(len(blocks)):
            cons.append(budgets[bi] <= budget_split[bi])
    else:
        cons.append(sum(budgets) <= 1)
    obj = 0
    tvar = None
    if objective_row is not None:
        tvar = cp.Variable()
        # support of the composed ellipsoid Σ_b x_bᵀ P_b x_b ≤ 1: c = Σ_b c_b,
        # (cᵀ P⁻¹ c) = Σ_b c_bᵀ P_b⁻¹ c_b
        ts = []
        for bi, blk in enumerate(blocks):
            cb = np.array([float(objective_row[i]) for i in blk.idx])
            if not cb.any() or (only is not None and bi != only):
                continue
            tb = cp.Variable()
            ts.append(tb)
            cons.append(cp.bmat([[Ps[bi], cb[:, None]], [cb[None, :], cp.reshape(tb, (1, 1))]])
                        >> 0)
        cons.append(tvar >= sum(ts) if ts else tvar >= 0)
        # Clarabel's stopping rule has an absolute gap: scale small objectives up to O(1)
        obj = tvar * obj_scale
    if only is not None and objective_row is None:
        obj = bvar                      # a block without the objective: smallest budget share
    if only is not None:
        # local copies of the shared scalars of this block only
        sig_in = {k: v for k, v in sig_in.items() if k[0] == only}
        sig_out = {e: v for e, v in sig_out.items() if ifaces[e].sender == only}
        if prox is not None:
            obj = obj / prox.get("scale", 1.0)
            pen = [cp.square(v - prox["sig_in"][k]) for k, v in sig_in.items()]
            pen += [cp.square(v - prox["sig_out"][e]) for e, v in sig_out.items()]
            pen.append(cp.square(bvar - prox["budget"]))
            obj = obj + prox["rho"] / 2 * sum(pen)
    prob = cp.Problem(cp.Minimize(obj), cons)
    return prob, {"P": Ps, "gamma": gam, "tau": tau, "sig_in": sig_in, "sig_out": sig_out,
                  "t": tvar, "budgets": budgets, "budget": bvar, "scale": scales,
                  "blocks": blocks}


def solve(prob):
    import cvxpy as cp

    try:
        prob.solve(solver=cp.CLARABEL)
    except Exception:  # noqa: BLE001  (solver failures mean "no certificate")
        return False
    return prob.status in ("optimal", "optimal_inaccurate")


@dataclass
class Member:
    """One certified ellipsoid family member (Lemma 1): an objective and its storage."""
    name: str
    row: list               # objective direction over the full state
    alpha: float
    P: list                 # per block, numpy
    gamma: list             # per block
    tau: list               # per block
    sig_in: dict
    sig_out: dict
    support: float          # √(cᵀP⁻¹c) at level 1


def _unscale(var):
    """γ and τ of the original signals from the normalized SDP variables."""
    gam, tau = [], []
    for g, t, scl, blk in zip(var["gamma"], var["tau"], var["scale"], var["blocks"]):
        if g is None:
            gam.append(None)
            tau.append(np.zeros(0))
            continue
        gam.append(np.maximum(g.value, 0) / scl ** 2)
        if t is None:
            tau.append(np.zeros(0))
        else:
            tau.append(np.maximum(t.value, 0) / np.array([scl[pos] ** 2
                                                          for pos, _, _ in blk.sectors]))
    return gam, tau


def _member(name, row, alpha, var) -> Member:
    gam, tau = _unscale(var)
    return Member(name, row, alpha, [P.value for P in var["P"]], gam, tau,
                  {k: max(float(v.value), 0.0) for k, v in var["sig_in"].items()},
                  {k: max(float(v.value), 0.0) for k, v in var["sig_out"].items()},
                  math.sqrt(max(float(var["t"].value), 0.0)))


def projection(blocks, P_list, row) -> float:
    """Support √(cᵀP⁻¹c) of the composed ellipsoid Σ_b x_bᵀP_b x_b ≤ 1 in direction `row`."""
    s = 0.0
    for blk, P in zip(blocks, P_list):
        cb = np.array([float(row[i]) for i in blk.idx])
        if cb.any():
            s += float(cb @ np.linalg.solve(P, cb))
    return math.sqrt(s)


ALPHAS = tuple(np.geomspace(0.05, 6.0, 16))


def best_member(sp_, blocks, ifaces, gains, betas, name, row, alphas=ALPHAS, refine=2):
    """The smallest support over an α grid, refined geometrically around the best grid point."""
    best = None
    scale = [None]

    def tryal(al):
        nonlocal best
        if scale[0] is None:     # first feasible solve sets the objective scale
            prob, var = lmi_blocks(sp_, blocks, ifaces, gains, betas, float(al), row)
            if not solve(prob) or var["t"].value is None:
                return
            scale[0] = 1.0 / max(float(var["t"].value), 1e-12)
        prob, var = lmi_blocks(sp_, blocks, ifaces, gains, betas, float(al), row,
                               obj_scale=scale[0])
        if solve(prob) and var["t"].value is not None:
            mb = _member(name, row, float(al), var)
            if best is None or mb.support < best.support:
                best = mb

    for al in alphas:
        tryal(al)
    step = (alphas[1] / alphas[0]) if len(alphas) > 1 else 1.0
    for _ in range(refine):
        if best is None:
            break
        step = math.sqrt(step)
        a0 = best.alpha
        for al in (a0 / step, a0 * step):
            tryal(al)
    return best


@dataclass
class SearchResult:
    ok: bool
    region: list            # Fractions per coordinate
    members: list
    iterations: int
    history: list
    message: str = ""


def objectives(sp_: SectorProblem):
    """One ellipsoid per bounded signal: the certified outputs and the region coordinates."""
    out = [(name, row) for name, row, _ in sp_.outputs]
    for c in sp_.coords:
        if not any(row == c.row or [-v for v in row] == c.row for _, row in out):
            out.append((c.name, c.row))
    return out


_POOL_CTX: dict = {}


def _pool_member(args):
    gains, betas, name, row, alphas = args
    c = _POOL_CTX
    return best_member(c["sp"], c["blocks"], c["ifaces"], gains, betas, name, row, alphas)


def workers(n_jobs: int) -> int:
    """Processes for independent LMI solves: `DYNACERT_WORKERS`, else a third of the cores (the
    machine is shared)."""
    import os

    env = os.environ.get("DYNACERT_WORKERS")
    k = int(env) if env else max(1, (os.cpu_count() or 1) // 3)
    return max(1, min(k, n_jobs))


def members_for(sp_, blocks, ifaces, gains, betas, objs, alphas=ALPHAS):
    """`best_member` for every objective; in parallel (fork) when there are several."""
    k = workers(len(objs))
    if k == 1:
        return [best_member(sp_, blocks, ifaces, gains, betas, name, row, alphas)
                for name, row in objs]
    import multiprocessing as mp
    from concurrent.futures import ProcessPoolExecutor

    _POOL_CTX.update(sp=sp_, blocks=blocks, ifaces=ifaces)
    with ProcessPoolExecutor(k, mp_context=mp.get_context("fork")) as ex_:
        return list(ex_.map(_pool_member, [(gains, betas, name, row, alphas)
                                           for name, row in objs]))


def region_fixed_point(sp_: SectorProblem, parts=None, max_iter=40, grow=1.02, verbose=None,
                       alphas=ALPHAS, init=None) -> SearchResult:
    """Algorithm 1: region fixed point with one ellipsoid per objective (Lemma 1)."""
    parts = parts or [list(range(sp_.n))]
    blocks, ifaces = build_blocks(sp_, parts)
    objs = objectives(sp_)
    # start from the linearized certificate (channels with zero region)
    R = [Fraction(1, 100) for _ in sp_.coords] if init is None else list(init)
    history = []
    for it in range(max_iter):
        cst = constants(sp_, R)
        if cst is None:
            return SearchResult(False, R, [], it, history, "a sector bound became undefined "
                                "(the region left the domain of an atom)")
        gains, betas = cst
        members = members_for(sp_, blocks, ifaces, gains, betas, objs, alphas)
        for (name, _), mb in zip(objs, members):
            if mb is None:
                return SearchResult(False, R, [], it, history,
                                    f"LMI infeasible on the region (objective {name})")
        r = [min(projection(blocks, mb.P, c.row) for mb in members) for c in sp_.coords]
        history.append({"region": [float(v) for v in R], "projections": r,
                        "supports": {mb.name: mb.support for mb in members}})
        if verbose:
            verbose(f"  iter {it}: region " + ", ".join(
                f"|{c.name}| ≤ {float(v):.4g}" for c, v in zip(sp_.coords, R))
                + "; certified " + ", ".join(f"{c.name} {v:.4g}" for c, v in zip(sp_.coords, r)))
        if all(rv < float(Rv) for rv, Rv in zip(r, R)) and it > 0:
            return SearchResult(True, R, members, it + 1, history)
        R = [max(Rv, ex.frac(grow * rv, 10**4)) for Rv, rv in zip(R, r)]
    return SearchResult(False, R, [], max_iter, history, "no fixed point within the iteration "
                        "limit")


# --- exact certificate data ----------------------------------------------------------------------

def dom_ok(R) -> bool:
    k = len(R)
    return all(sum((abs(R[i][j]) + abs(R[j][i])) / 2 for j in range(k) if j != i) <= R[i][i]
               for i in range(k))


def dom_witness(M, dens=(10**3, 10**4, 10**6, 10**8, 10**10)):
    """`(L, d)` with `M - Lᵀ diag(d) L` diagonally dominant and `d ≥ 0` (exact check), from a
    rounded floating-point LDLᵀ of `M - εI`; None if `M` is not safely positive definite."""
    k = len(M)
    Mf = np.array([[float(v) for v in r] for r in M])
    Mf = (Mf + Mf.T) / 2
    lam = np.linalg.eigvalsh(Mf)
    if lam[0] <= 0:
        return None
    for frac_eps in (0.5, 0.25, 0.1):
        Mm = Mf - frac_eps * lam[0] * np.eye(k)
        L0 = np.eye(k)
        d = np.zeros(k)
        for j in range(k):
            d[j] = Mm[j, j] - sum(L0[j, p] ** 2 * d[p] for p in range(j))
            if d[j] <= 0:
                break
            for i in range(j + 1, k):
                L0[i, j] = (Mm[i, j] - sum(L0[i, p] * L0[j, p] * d[p] for p in range(j))) / d[j]
        else:
            for den in dens:
                L = [[Fraction(0) if L0[j, i] == 0 else
                      (Fraction(1) if i == j else ex.frac(L0[j, i], den)) for j in range(k)]
                     for i in range(k)]                       # L = L0ᵀ (unit upper)
                dq = [down(Fraction(float(v)), den) if v > 0 else Fraction(0) for v in d]
                R = [[M[i][j] - sum(L[p][i] * dq[p] * L[p][j] for p in range(k))
                      for j in range(k)] for i in range(k)]
                if dom_ok(R):
                    return L, dq
    return None


def round_mat(X, den):
    Q = [[ex.frac(float(v), den) for v in r] for r in X]
    return ex.symmetrize(Q)


@dataclass
class ExactBlock:
    idx: list
    A: list
    B: list
    q: list                 # rows over (x_b, w_b)
    ch: list                # signal positions of the sector channels
    lo: list
    hi: list
    gamma: list
    sigma: list
    r: list                 # rows over (x_b, w_b)
    P: list
    alpha: Fraction
    tau: list
    L: list
    d: list
    PL: list                # DomWitness of P
    Pd: list
    signals: list
    deltas: dict            # signal position -> peak bound (energy-weighted signals)


@dataclass
class ExactMember:
    name: str
    blocks: list
    alpha: Fraction
    budget: Fraction        # Σ γ δ²
    level: Fraction         # c ≥ budget / α
    outer: Fraction         # b > c: {V ≤ b} lies in the region


def lmi_matrix(eb: ExactBlock):
    """The Lean `SectorData.lmi` matrix, exactly (same formula, same index order)."""
    n, m_ = len(eb.A), len(eb.B[0]) if eb.B and eb.B[0] else 0
    A, B, P, al = eb.A, eb.B, eb.P, eb.alpha
    At = ex.transpose(A)
    top = ex.add(ex.add(ex.matmul(At, P), ex.matmul(P, A)), ex.scale(al, P))
    PB = ex.matmul(P, B) if m_ else [[] for _ in range(n)]
    N = n + m_
    M = [[Fraction(0)] * N for _ in range(N)]
    for i in range(n):
        for j in range(n):
            M[i][j] = -top[i][j]
        for j in range(m_):
            M[i][n + j] = -PB[i][j]
            M[n + j][i] = -PB[i][j]
    for j in range(m_):
        M[n + j][n + j] += eb.gamma[j]

    def add_form(kappa, u, v):
        for a in range(N):
            for b in range(N):
                M[a][b] += kappa * (u[a] * v[b] + v[a] * u[b]) / 2

    for i in range(len(eb.ch)):
        e = [Fraction(0)] * N
        e[n + eb.ch[i]] = Fraction(1)
        qi = eb.q[i]
        u = [e[a] - eb.lo[i] * qi[a] for a in range(N)]
        v = [eb.hi[i] * qi[a] - e[a] for a in range(N)]
        add_form(-eb.tau[i], u, v)
    for s_, r in zip(eb.sigma, eb.r):
        add_form(s_, r, r)
    return M


def exact_member(sp_, blocks, ifaces, gains, betas, mb: Member, dens=(10**4, 10**6, 10**8)):
    """Round a member to exact data with dominance witnesses; None if rounding fails."""
    al = ex.frac(mb.alpha, 10**4)
    if al <= 0:
        return None
    for den in dens:
        ebs = []
        budget = Fraction(0)
        sig_out = {e: up(Fraction(v), den) for e, v in mb.sig_out.items()}
        ok = True
        for bi, blk in enumerate(blocks):
            nb, m_ = len(blk.idx), len(blk.signals)
            A = [[sp_.A[i][j] for j in blk.idx] for i in blk.idx]
            B = []
            for i in blk.idx:
                row = []
                for kind, j in blk.signals:
                    if kind == "chan":
                        row.append(sp_.channels[j].col.get(i, Fraction(0)))
                    elif kind == "dist":
                        row.append(sp_.Bw[i][j])
                    else:
                        row.append(_iface_coef(sp_, ifaces[j], i, blk))
                B.append(row)
            q = [list(qz) for _, qz, _ in blk.sectors]
            chp = [pos for pos, _, _ in blk.sectors]
            lo = [gains[j][0] for _, _, j in blk.sectors]
            hi = [gains[j][1] for _, _, j in blk.sectors]
            gam = [down(Fraction(float(v)), den) if pos in blk.gamma_sig else Fraction(0)
                   for pos, v in enumerate(mb.gamma[bi])]
            tau = [down(Fraction(float(v)), den) for v in mb.tau[bi]]
            sigma, rr = [], []
            for pos, e in blk.supply_in:
                sigma.append(down(Fraction(mb.sig_in[(bi, e)]), den))
                rr.append([Fraction(0)] * nb + [Fraction(int(k == pos)) for k in range(m_)])
            for row, e in blk.supply_out:
                sigma.append(-sig_out[e])
                rr.append(list(row) + [Fraction(0)] * m_)
            P = round_mat(mb.P[bi], den)
            deltas = signal_bounds(sp_, blk, betas)
            eb = ExactBlock(list(blk.idx), A, B, q, chp, lo, hi, gam, sigma, rr, P, al, tau,
                            [], [], [], [], list(blk.signals), deltas)
            W = dom_witness(lmi_matrix(eb))
            Wp = dom_witness(P)
            if W is None or Wp is None:
                ok = False
                break
            eb.L, eb.d = W
            eb.PL, eb.Pd = Wp
            budget += sum((gam[pos] * deltas[pos] ** 2 for pos in blk.gamma_sig), Fraction(0))
            ebs.append(eb)
        if not ok:
            continue
        # interconnection: Σ receivers ≤ sender (exact)
        for e, I in enumerate(ifaces):
            recv = sum((ebs[r].sigma[_in_index(blocks[r], e)] for r in I.receivers),
                       Fraction(0))
            if recv > sig_out[e]:
                ok = False
        if not ok:
            continue
        level = up(budget / al, 10**8)
        return ExactMember(mb.name, ebs, al, budget, level, Fraction(0))
    return None


def _in_index(blk: Block, e: int) -> int:
    return [ee for _, ee in blk.supply_in].index(e)


def _iface_coef(sp_, I, i, blk):
    """Coefficient of interface signal `I` in row `i` of a block (its off-block coupling is
    `coef · (I.row · z)`)."""
    row = [sp_.A[i][k] if k not in blk.idx else Fraction(0) for k in range(sp_.n)]
    lead = [k for k in range(sp_.n) if I.row[k] != 0][0]
    return row[lead] / I.row[lead] if row[lead] != 0 else Fraction(0)


@dataclass
class Box:
    member: int
    block: int
    row: list               # over the block's states
    level: Fraction
    bound: Fraction
    L: list
    d: list


def box_cert(P, level, row, bound):
    """DomWitness of `b² P - c rowrowᵀ` (Lean `LinearBoxDom`), or None."""
    n = len(P)
    M = [[bound ** 2 * P[i][j] - level * row[i] * row[j] for j in range(n)] for i in range(n)]
    return dom_witness(M)


def _block_of(members, row):
    """The block containing the support of `row` (the same partition in every member)."""
    for b, eb in enumerate(members[0].blocks):
        if all(row[i] == 0 for i in range(len(row)) if i not in eb.idx):
            return b
    return None


def _support(eb, row, level):
    Pf = np.array([[float(v) for v in r] for r in eb.P])
    c = np.array([float(row[i]) for i in eb.idx])
    return math.sqrt(max(float(level), 0) * float(c @ np.linalg.solve(Pf, c)))


@dataclass
class ExactCert:
    region: list            # Fractions per coordinate
    gains: list
    betas: list
    members: list           # ExactMember
    region_boxes: list      # per coordinate: Box at level outer
    output_boxes: list      # per output: Box at level c


def finalize(sp_, R, gains, betas, members) -> ExactCert | None:
    """Levels, region inclusion levels and box certificates (exact)."""
    region_boxes = []
    for ci, c in enumerate(sp_.coords):
        b = _block_of(members, c.row)
        if b is None:
            return None
        best = min(range(len(members)),
                   key=lambda k: _support(members[k].blocks[b], c.row, members[k].level))
        region_boxes.append((ci, best, b))
    for k, em in enumerate(members):
        ratios = []
        for ci, kk, b in region_boxes:
            if kk != k:
                continue
            eb = em.blocks[b]
            s1 = _support(eb, sp_.coords[ci].row, 1)
            ratios.append((float(R[ci]) / s1) ** 2)
        outer = (Fraction(min(ratios)) * Fraction(999, 1000)) if ratios else 2 * em.level
        outer = down(outer, 10**6)
        if outer <= em.level:
            return None
        em.outer = outer
    boxes = []
    for ci, k, b in region_boxes:
        eb = members[k].blocks[b]
        row = [sp_.coords[ci].row[i] for i in eb.idx]
        W = box_cert(eb.P, members[k].outer, row, R[ci])
        if W is None:
            return None
        boxes.append(Box(k, b, row, members[k].outer, R[ci], *W))
    oboxes = []
    for name, orow, _ in sp_.outputs:
        b = _block_of(members, orow)
        if b is None:
            return None
        k = min(range(len(members)),
                key=lambda k: _support(members[k].blocks[b], orow, members[k].level))
        eb = members[k].blocks[b]
        row = [orow[i] for i in eb.idx]
        bound = up(Fraction(_support(eb, orow, members[k].level)) * Fraction(1000001, 1000000),
                   10**6)
        W = box_cert(eb.P, members[k].level, row, bound)
        if W is None:
            return None
        oboxes.append(Box(k, b, row, members[k].level, bound, *W))
    return ExactCert(list(R), gains, betas, members, boxes, oboxes)


def resolve(sp_, blocks, ifaces, gains, betas, mb: Member, margin: float):
    """Re-solve a member's LMI at its α with a larger strictness margin (for rounding)."""
    prob, var = lmi_blocks(sp_, blocks, ifaces, gains, betas, mb.alpha, mb.row, margin=margin,
                           obj_scale=1.0 / max(mb.support ** 2, 1e-12))
    if not solve(prob) or var["t"].value is None:
        return None
    return _member(mb.name, mb.row, mb.alpha, var)


def certify_exact(sp_, res: SearchResult, parts=None, members=None):
    """Exact certificate from a successful search (or given members), or None."""
    parts = parts or [list(range(sp_.n))]
    blocks, ifaces = build_blocks(sp_, parts)
    gains, betas = constants(sp_, res.region)
    for margin in (1e-3, 1e-4):
        ems = []
        for mb in (members or res.members):
            m2 = resolve(sp_, blocks, ifaces, gains, betas, mb, margin) if members is None \
                else mb
            em = exact_member(sp_, blocks, ifaces, gains, betas, m2) if m2 else None
            if em is None:
                break
            ems.append(em)
        else:
            out = finalize(sp_, res.region, gains, betas, ems)
            if out is not None:
                return out
    return None


def certify_grow(sp_, res: SearchResult, parts=None, grows=(1.02, 1.05, 1.1), verbose=None,
                 alphas=ALPHAS):
    """`certify_exact`; if the fixed point left too little slack for the rounding margin, enlarge
    the region, re-verify the fixed point there and try again. Returns (cert or None, result)."""
    cert = certify_exact(sp_, res, parts)
    for g in grows:
        if cert is not None:
            break
        init = [ex.frac(g * float(r), 10**4) for r in res.region]
        if verbose:
            verbose(f"  rounding: no slack, enlarging the region by {g}")
        res2 = region_fixed_point(sp_, parts, max_iter=3, verbose=verbose, alphas=alphas,
                                  init=init)
        if not res2.ok:
            continue
        res = res2
        cert = certify_exact(sp_, res, parts)
    return cert, res
