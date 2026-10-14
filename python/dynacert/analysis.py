"""Symbolic analysis of a model's equations (sympy, exact rationals).

Given the model's equations in the same order as Lean's `Equations` conjuncts, this module

* substitutes parameter values exactly (as `Params.Bound` does in Lean),
* eliminates derivatives and algebraic variables to an explicit ODE,
* extracts `A`, `B` for models linear in states and disturbances, and
* computes `linear_combination` multipliers proving each derivative identity from the
  equations, so the Lean link proof is a single `ring` check per component.

Everything here is untrusted; Lean re-checks each identity.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import sympy as sp


def to_fraction(x) -> Fraction:
    x = sp.nsimplify(x, rational=True) if not isinstance(x, sp.Rational) else x
    if not x.is_Rational:
        raise ValueError(f"not an exact rational: {x}")
    return Fraction(int(x.p), int(x.q))


@dataclass
class Explicit:
    """`der(x) = f(x, u)` and `y = g(x, u)` after parameter substitution and elimination."""
    der: dict      # state symbol -> expression in states/inputs
    alg: dict      # algebraic symbol -> expression in states/inputs
    residuals: list  # equation residuals (lhs - rhs) after parameter substitution


def substitute_params(equations, param_values: dict):
    """Residuals `lhs - rhs` with parameters replaced by exact values (in dependency order)."""
    vals = dict(param_values)
    # resolve parameters bound to expressions of other parameters
    for _ in range(len(vals) + 1):
        changed = False
        for k, v in vals.items():
            nv = sp.sympify(v).subs(vals)
            if nv != v:
                vals[k] = nv
                changed = True
        if not changed:
            break
    res = []
    for eq in equations:
        r = (eq.lhs - eq.rhs) if isinstance(eq, sp.Equality) else sp.sympify(eq)
        res.append(sp.nsimplify(sp.expand(r.subs(vals)), rational=True))
    return res


def eliminate(residuals, der_syms, alg_syms) -> Explicit:
    unknowns = list(der_syms) + list(alg_syms)
    sol = sp.solve(residuals, unknowns, dict=True)
    if len(sol) != 1:
        raise ValueError("equations do not determine derivatives and algebraics uniquely")
    s = sol[0]
    missing = [u for u in unknowns if u not in s]
    if missing:
        raise ValueError(f"underdetermined: {missing}")
    return Explicit({d: sp.expand(s[d]) for d in der_syms},
                    {a: sp.expand(s[a]) for a in alg_syms}, residuals)


def linear_rows(exprs, xs, ws):
    """`exprs = A xs + B ws` exactly, with rational `A`, `B`; raises otherwise."""
    A, B = [], []
    allv = list(xs) + list(ws)
    for expr in exprs:
        expr = sp.expand(expr)
        coeffs = []
        for v in allv:
            c = sp.diff(expr, v)
            if c.free_symbols:
                raise ValueError(f"not linear with constant coefficients in {v}: {expr}")
            coeffs.append(to_fraction(c))
        rest = sp.expand(expr - sum(sp.Rational(c.numerator, c.denominator) * v
                                    for c, v in zip(coeffs, allv)))
        if rest != 0:
            raise ValueError(f"remainder {rest} in {expr} (affine terms or other inputs)")
        A.append(coeffs[:len(xs)])
        B.append(coeffs[len(xs):])
    return A, B


def rat(x: Fraction):
    return sp.Rational(x.numerator, x.denominator)


def multipliers(residuals, target, params=()):
    """λ with `target ≡ Σ λₑ residualₑ` identically (exact rationals), as (index, λ) pairs.

    `target` is `lhs - rhs` of the identity to prove; `linear_combination Σ λₑ * eₑ` then
    closes it by `ring`.
    """
    lams = sp.symbols(f"lam0:{len(residuals)}")
    combo = sp.expand(sum(l * r for l, r in zip(lams, residuals)) - target)
    syms = sorted(combo.free_symbols - set(lams) - set(params), key=str)
    poly = sp.Poly(combo, *syms) if syms else None
    eqs = list(poly.coeffs()) if poly is not None else [combo]
    sol = sp.linsolve(eqs, lams)
    if not sol:
        raise ValueError("identity is not a linear combination of the equations")
    (vals,) = sol
    free = {s: 0 for v in vals for s in v.free_symbols}
    out = []
    for i, v in enumerate(vals):
        v = sp.simplify(sp.sympify(v).subs(free))
        if v != 0:
            out.append((i, to_fraction(v) if not (v.free_symbols & set(params)) else v))
    return out
