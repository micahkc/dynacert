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


def _solve_linear(residuals, unknowns):
    """The unique solution when every residual is affine in the unknowns (the usual case:
    derivatives and algebraics enter linearly, with state- and input-dependent coefficients);
    None otherwise."""
    U = set(unknowns)
    rows, rhs = [], []
    for r in residuals:
        r = sp.expand(r)
        coeffs = [sp.diff(r, u) for u in unknowns]
        if any(c.free_symbols & U for c in coeffs):
            return None
        rest = sp.expand(r - sum(c * u for c, u in zip(coeffs, unknowns)))
        if rest.free_symbols & U:
            return None
        rows.append(coeffs)
        rhs.append(-rest)
    M = sp.Matrix(rows)
    if M.shape[0] < len(unknowns) or M.rank() < len(unknowns):
        return None
    sol = sp.linsolve((M, sp.Matrix(rhs)), unknowns)
    if not sol:
        return None
    (vals,) = sol
    if any(v.free_symbols & U for v in vals):
        return None
    return [dict(zip(unknowns, vals))]


@dataclass
class Mode:
    """One branch combination of a switching model (`if`-expressions): the condition under which
    it is active (in states, inputs and parameters only) and its explicit dynamics."""
    choice: tuple            # branch index per Piecewise, in `piecewise_atoms` order
    condition: object        # sympy boolean (True for an unconditional branch)
    explicit: Explicit
    residuals: list          # residuals with every Piecewise replaced by the chosen branch


MAX_MODES = 64


def piecewise_atoms(residuals) -> list:
    """The Piecewise subexpressions of the residuals, outermost first, deterministic order."""
    found = []
    for r in residuals:
        for pw in sp.preorder_traversal(sp.sympify(r)):
            if isinstance(pw, sp.Piecewise) and pw not in found:
                found.append(pw)
    return found


def _branch_condition(pw, k):
    """Condition of branch k of a Piecewise: its own condition and every earlier one false."""
    conds = [c for _, c in pw.args]
    cond = sp.And(*[sp.Not(c) for c in conds[:k]], conds[k])
    return sp.simplify_logic(cond) if cond.free_symbols else cond


def modes(residuals, der_syms, alg_syms) -> list[Mode]:
    """Expand a switching model into its modes. Each mode replaces every Piecewise by one branch
    and is solved as a smooth system; its condition is rewritten in states and inputs by
    substituting that mode's algebraic solution. Modes whose condition is identically false are
    dropped. A model without Piecewise has one mode with condition True."""
    import itertools

    atoms = piecewise_atoms(residuals)
    if not atoms:
        return [Mode((), sp.true, _eliminate_smooth(residuals, der_syms, alg_syms), residuals)]
    combos = list(itertools.product(*[range(len(pw.args)) for pw in atoms]))
    if len(combos) > MAX_MODES:
        raise ValueError(f"{len(combos)} switching modes (more than {MAX_MODES})")
    out = []
    for choice in combos:
        rep = {pw: pw.args[k][0] for pw, k in zip(atoms, choice)}
        res = [sp.sympify(r).xreplace(rep) for r in residuals]
        if piecewise_atoms(res):               # nested conditionals inside a chosen branch
            raise ValueError("nested if-expressions are not supported")
        ex = _eliminate_smooth(res, der_syms, alg_syms)
        sub = {**ex.alg, **{d: ex.der[d] for d in der_syms}}
        cond = sp.And(*[_branch_condition(pw, k) for pw, k in zip(atoms, choice)])
        cond = cond.xreplace(sub) if cond not in (sp.true, sp.false) else cond
        if cond == sp.false:
            continue
        out.append(Mode(tuple(choice), cond, ex, res))
    if not out:
        raise ValueError("no switching mode is ever active")
    return out


def eliminate(residuals, der_syms, alg_syms) -> Explicit:
    """Explicit form; switching models (Piecewise) become a Piecewise over their modes."""
    ms = modes(residuals, der_syms, alg_syms)
    if len(ms) == 1:
        return ms[0].explicit
    def merge(sym, part):
        pairs = [(getattr(m.explicit, part)[sym], m.condition) for m in ms[:-1]]
        return sp.Piecewise(*pairs, (getattr(ms[-1].explicit, part)[sym], True))
    return Explicit({d: merge(d, "der") for d in der_syms},
                    {a: merge(a, "alg") for a in alg_syms}, residuals)


def _eliminate_smooth(residuals, der_syms, alg_syms) -> Explicit:
    unknowns = list(der_syms) + list(alg_syms)
    sol = _solve_linear(residuals, unknowns)
    if sol is None:
        # nonlinear in the unknowns: skip sympy's solution checking and simplification, which
        # can run for minutes on transcendental terms (tanh, sqrt, ...)
        sol = sp.solve(residuals, unknowns, dict=True, check=False, simplify=False)
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
    # only the undetermined multipliers are free; uncertain parameters must stay symbolic
    free = {s: 0 for v in vals for s in v.free_symbols if s in set(lams)}
    out = []
    for i, v in enumerate(vals):
        v = sp.simplify(sp.sympify(v).subs(free))
        if v != 0:
            out.append((i, to_fraction(v) if not (v.free_symbols & set(params)) else v))
    return out
