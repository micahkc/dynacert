"""Certified finite-horizon funnels for nonlinear tracking (untrusted search).

Implements the method of Condie, Woodbury, Pant and Goppert, *Continuous-time certified invariant
funnels for nonlinear tracking systems via polytopic embeddings and univariate sum-of-squares*,
for the decay rate α = 0 (the finite-horizon funnel of their Corollary 2, which is rational and so
checkable by the Lean kernel):

1. **Problem** (`extract`). The model's closed loop `ẋ = f(x, t, w)`, the reference `x*(t)` from
   `__Dynacert(nominal = "...")` annotations on the states (states without one use their start
   value), and the horizon from the model annotation `__Dynacert(horizon = T)`. The error
   `z = x - x*` must satisfy `ż = A₀ z + Σⱼ aⱼ (gⱼ(x_kⱼ) - gⱼ(x*_kⱼ)) + B w` with `gⱼ = sin` (the
   feedforward makes `x*` an exact solution; this is checked symbolically).
2. **Embedding** (paper, Lemma 1). On segment `i`, while `|z_k| < ρ_k`, each `sin` difference is a
   gain `κ ∈ [lo, hi]` times `z_k`; `lo`, `hi` are rational enclosures of `cos` on
   `[min x*_k - ρ_k, max x*_k + ρ_k]`, where the range of the polynomial `x*_k` on the segment comes
   from its Bernstein coefficients (what Lean checks).
3. **Synthesis** (paper, Algorithm 1 and program (13)). Piecewise-polynomial `P(t)`, univariate
   matrix SOS for the dissipation inequality at every vertex and for the band rows, continuity at
   the knots; the band loop shrinks `ρ` until the certified ellipsoid stays inside it.
4. **Exact certificate** (`exact_certificate`). Rational `P` with exact continuity, rational
   Gram matrices projected onto the coefficient identity, `LDLᵀ` witnesses.

Every number produced here is re-checked by the Lean kernel (`Dynacert.Nonlinear.FunnelCert`).
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np
import sympy as sp

from . import exact
from .structure import explicit, scalar_residuals


class FunnelError(Exception):
    pass


# --- problem ---------------------------------------------------------------------------------

@dataclass
class Atom:
    """A nonlinearity `g(x_k)` entering the dynamics with coefficient vector `a` (per state)."""
    kind: str               # "sin"
    k: int                  # state index
    a: list                 # Fraction per state equation


@dataclass
class FunnelProblem:
    name: str
    states: list[str]
    t: object                                  # sympy time symbol
    xs: list                                   # state symbols
    f: list                                    # ẋ = f(x, t, w) (exact rationals)
    w_names: list[str]
    ws: list
    w_bounds: list[Fraction]
    nominal: list                              # x*(t), sympy polynomials in t (or constants)
    nominal_names: list                        # algebraic variable name or None
    horizon: Fraction
    A0: list                                   # n×n Fractions
    B: list                                    # n×m Fractions
    atoms: list[Atom]
    outputs: list                              # (name, row c (Fractions)): output = cᵀ z
    params: dict = field(default_factory=dict)


def _rat(x) -> sp.Rational:
    return sp.nsimplify(x, rational=True)


def _frac(x) -> Fraction:
    r = sp.Rational(x)
    return Fraction(int(r.p), int(r.q))


def extract(prob) -> FunnelProblem:
    m, spec = prob.model, prob.spec
    ann = (m.annotations or {}).get("__Dynacert", {})
    if "horizon" not in ann:
        raise FunnelError("needs a finite horizon: annotate the model with "
                          "annotation(__Dynacert(horizon = T))")
    horizon = Fraction(str(ann["horizon"]))
    if any(not v.scalar for v in m.variables):
        raise FunnelError("needs scalar variables")
    if not spec.certify:
        raise FunnelError("nothing to certify: annotate outputs with __Dynacert(certify)")
    t = m.module.t
    vals = {k: _rat(v) for k, v in m.param_values().items()}
    res = [sp.nsimplify(sp.sympify(r).subs(vals), rational=True) for r in scalar_residuals(m)]
    states = m.states
    ders = [m.der[v.name] for v in states]
    algs = [v.symbol for v in m.algebraics]
    sol = explicit(res, ders + algs)
    xs = [v.symbol for v in states]
    f = [sp.simplify(sol[d]) for d in ders]
    w_names = spec.disturbance_names
    ws = [m.var(d).symbol for d in w_names]
    w_bounds = [Fraction(str(d.bound)) for d in spec.disturbances]
    other_inputs = [v.name for v in m.inputs if v.name not in w_names]
    if other_inputs:
        raise FunnelError(f"inputs other than disturbances are not supported: {other_inputs}")

    # reference x*(t)
    nominal, nominal_names = [], []
    for v in states:
        nm = (v.annotations or {}).get("__Dynacert", {}).get("nominal")
        if nm is not None:
            expr = sp.simplify(sol[m.var(nm).symbol])
            if expr.free_symbols - {t}:
                raise FunnelError(f"nominal {nm} of {v.name} depends on more than time")
            nominal.append(sp.expand(expr)); nominal_names.append(nm)
        else:
            nominal.append(_rat(v.start if v.start is not None else 0)); nominal_names.append(None)
    for v, xs0 in zip(states, nominal):
        if v.start is None or sp.simplify(_rat(v.start) - xs0.subs(t, 0)) != 0:
            raise FunnelError(f"{v.name} must start on its nominal (x(0) = x*(0))")
    # x* solves the undisturbed closed loop
    sub_star = dict(zip(xs, nominal)) | {w: 0 for w in ws}
    for i, (fi, xi) in enumerate(zip(f, nominal)):
        if sp.simplify(sp.diff(xi, t) - fi.subs(sub_star)) != 0:
            raise FunnelError(f"the reference is not a solution of the undisturbed loop "
                              f"(der({states[i].name}))")
    # structure: f = A0 x + Σ a_j sin(x_k) + c(t) + B w
    atoms, S = [], {}
    for fi in f:
        for at in fi.atoms(sp.sin, sp.cos):
            arg = at.args[0]
            if arg in xs and at not in S:
                if isinstance(at, sp.cos):
                    raise FunnelError("cos(state) nonlinearities are not supported yet")
                S[at] = sp.Dummy(f"g{len(S)}")
    fs = [fi.subs(S) for fi in f]
    allv = xs + list(S.values()) + ws
    for fi in fs:
        for v in allv:
            dv = sp.diff(fi, v)
            if dv.free_symbols & (set(allv) | {t}):
                raise FunnelError(f"der is not of the form A x + Σ a sin(x_k) + c(t) + B w: {fi}")
    A0 = [[_frac(sp.diff(fi, x)) for x in xs] for fi in fs]
    B = [[_frac(sp.diff(fi, w)) for w in ws] for fi in fs]
    for at, dmy in S.items():
        atoms.append(Atom("sin", xs.index(at.args[0]), [_frac(sp.diff(fi, dmy)) for fi in fs]))
    # outputs: linear in z with no time residue
    outputs = []
    zs = sp.symbols(f"z0:{len(xs)}")
    sub_z = {x: xs0 + z for x, xs0, z in zip(xs, nominal, zs)}
    for name in spec.certify:
        v = m.var(name)
        e = v.symbol if v.role == "state" else sol.get(v.symbol)
        ez = sp.expand(sp.sympify(e).subs(sub_z))
        c = [_frac(sp.diff(ez, z)) for z in zs]
        if sp.simplify(ez - sum(sp.Rational(ci.numerator, ci.denominator) * z
                                for ci, z in zip(c, zs))) != 0:
            raise FunnelError(f"output {name} is not linear in the error z = x - x*")
        outputs.append((name, c))
    return FunnelProblem(m.name, [v.name for v in states], t, xs, f, w_names, ws, w_bounds,
                         nominal, nominal_names, horizon, A0, B, atoms, outputs, vals)


# --- Bernstein range of a polynomial on an interval ------------------------------------------

def poly_coeffs(expr, t) -> list[Fraction]:
    """Ascending rational coefficients of a polynomial in `t`."""
    p = sp.Poly(sp.expand(expr), t)
    cs = [Fraction(0)] * (p.degree() + 1)
    for (k,), c in p.terms():
        cs[k] = _frac(c)
    return cs


def bernstein(cs: list[Fraction], lo: Fraction, hi: Fraction) -> list[Fraction]:
    """Bernstein coefficients of `Σ cs[j] t^j` on `[lo, hi]` (exact)."""
    n = len(cs) - 1
    # shift to s ∈ [0, 1]: t = lo + (hi - lo) s
    sh = [Fraction(0)] * (n + 1)
    for j, c in enumerate(cs):
        for i in range(j + 1):
            sh[i] += c * math.comb(j, i) * lo ** (j - i) * (hi - lo) ** i
    return [sum(Fraction(math.comb(k, i), math.comb(n, i)) * sh[i] for i in range(k + 1))
            for k in range(n + 1)]


# --- enclosures ---------------------------------------------------------------------------------

PI_LO = Fraction(314159, 100000)   # π > 3.14159
GRID = 10**6                       # resolution of the rational gain enclosures


def cos_enclosure(u: Fraction, v: Fraction) -> tuple[Fraction, Fraction]:
    """Rational `[lo, hi] ⊇ cos([u, v])` as `Dynacert.Nonlinear.cos_mem_Icc` proves it."""
    M = max(abs(u), abs(v))
    if M > PI_LO:
        raise FunnelError("band too wide for the cos enclosure (needs |θ| ≤ π)")
    lo = 1 - M ** 2 / 2
    if u > 0:
        hi = 1 - u ** 2 / 2 + u ** 4 / 24
    elif v < 0:
        hi = 1 - v ** 2 / 2 + v ** 4 / 24
    else:
        hi = Fraction(1)
    return lo, min(hi, Fraction(1))


@dataclass
class Segments:
    S: int
    h: Fraction
    ref_range: list            # per segment, per atom: (lo, hi) of x*_k (Bernstein hull)
    bern: list                 # per segment, per atom: Bernstein coefficients


def segments(fp: FunnelProblem, S: int) -> Segments:
    h = fp.horizon / S
    rr, bb = [], []
    for i in range(S):
        a, b = h * i, h * (i + 1)
        row, brow = [], []
        for at in fp.atoms:
            cs = poly_coeffs(fp.nominal[at.k], fp.t)
            bc = bernstein(cs, a, b)
            row.append((min(bc), max(bc)))
            brow.append(bc)
        rr.append(row); bb.append(brow)
    return Segments(S, h, rr, bb)


def vertices(fp: FunnelProblem, seg: Segments, rho: list) -> tuple[list, list]:
    """Per segment: vertex matrices and the gain intervals used (per atom)."""
    As, gains = [], []
    n = len(fp.xs)
    for i in range(seg.S):
        ivals = []
        for j, at in enumerate(fp.atoms):
            lo_r, hi_r = seg.ref_range[i][j]
            r = rho[i][at.k]
            lo, hi = cos_enclosure(lo_r - r, hi_r + r)
            # widen to a coarse grid: exact but small rationals keep the kernel's checks cheap
            ivals.append((Fraction(math.floor(lo * GRID), GRID),
                          min(Fraction(math.ceil(hi * GRID), GRID), Fraction(1))))
        Ai = []
        for sig in itertools.product(*[(g[0], g[1]) for g in ivals]):
            A = [row[:] for row in fp.A0]
            for at, s in zip(fp.atoms, sig):
                for r_ in range(n):
                    A[r_][at.k] += at.a[r_] * s
            Ai.append(A)
        As.append(Ai); gains.append(ivals)
    return As, gains


# --- SDP -----------------------------------------------------------------------------------------

def _gram_coeff_cvx(Q0, Q1, d, nu, ell):
    """`gramCoeff` for cvxpy Gram variables (blocks of size `nu`)."""
    import cvxpy as cp
    terms = []
    for a in range(d + 1):
        for b in range(d + 1):
            if a + b == ell:
                terms.append(Q0[a * nu:(a + 1) * nu, b * nu:(b + 1) * nu])
    for a in range(d):
        for b in range(d):
            if a + b + 1 == ell:
                terms.append(Q1[a * nu:(a + 1) * nu, b * nu:(b + 1) * nu])
            if a + b + 2 == ell:
                terms.append(-Q1[a * nu:(a + 1) * nu, b * nu:(b + 1) * nu])
    return sum(terms) if terms else np.zeros((nu, nu))


def diss_coeff(P, A, B, h, gamma, ell, lib=np):
    """`dissCoeff` (works on numpy arrays, cvxpy expressions, or exact Fraction matrices)."""
    n, m = len(A), len(B[0])
    R = len(P) - 1
    Pl = P[ell] if ell <= R else 0 * P[0]
    Pn = P[ell + 1] if ell + 1 <= R else 0 * P[0]
    A_ = np.array(A, dtype=float); B_ = np.array(B, dtype=float)
    TL = -((ell + 1) / h * Pn + A_.T @ Pl + Pl @ A_)
    TR = -(Pl @ B_)
    BR = np.diag(gamma) if ell == 0 else np.zeros((m, m))
    return lib.bmat([[TL, TR], [TR.T, BR]])


@dataclass
class Synthesis:
    P: list            # per segment: list of R+1 numpy matrices
    q: list            # per segment: per row
    rho: list          # per segment: per state (band half-widths; only atom states matter)
    gamma: list
    As: list
    gains: list
    seg: Segments
    d: int
    R: int
    rows: list         # band rows c (one per state: e_k)
    weights: list


def solve_sdp(fp: FunnelProblem, seg: Segments, rho, R: int, d: int, delta: float = 1e-7,
              weights=None):
    import cvxpy as cp
    n, m = len(fp.xs), len(fp.ws)
    S, h = seg.S, float(seg.h)
    T = float(fp.horizon)
    gamma = [1.0 / (float(wb) ** 2 * m * T) for wb in fp.w_bounds]   # budget = 1/T, v(T) = 1
    As, gains = vertices(fp, seg, rho)
    rows = [[1.0 if j == k else 0.0 for j in range(n)] for k in range(n)]
    P = [[cp.Variable((n, n), symmetric=True) for _ in range(R + 1)] for _ in range(S)]
    q = [[cp.Variable() for _ in range(n)] for _ in range(S)]
    cons = []
    nu_d, nu_b = n + m, n + 1
    for i in range(S):
        for A in As[i]:
            Q0 = cp.Variable(((d + 1) * nu_d, (d + 1) * nu_d), PSD=True)
            Q1 = cp.Variable((d * nu_d, d * nu_d), PSD=True) if d > 0 else None
            for ell in range(2 * d + 1):
                M = diss_coeff(P[i], A, fp.B, h, gamma, ell, lib=cp)
                if ell == 0:
                    M = M - delta * np.eye(nu_d)
                cons.append(M == _gram_coeff_cvx(Q0, Q1, d, nu_d, ell))
        for k in range(n):
            c = np.array(rows[k]).reshape(n, 1)
            Q0 = cp.Variable(((d + 1) * nu_b, (d + 1) * nu_b), PSD=True)
            Q1 = cp.Variable((d * nu_b, d * nu_b), PSD=True) if d > 0 else None
            for ell in range(2 * d + 1):
                Pl = P[i][ell] if ell <= R else np.zeros((n, n))
                if ell == 0:
                    M = cp.bmat([[Pl, c], [c.T, cp.reshape(q[i][k], (1, 1))]])
                    M = M - delta * np.eye(nu_b)
                else:
                    M = cp.bmat([[Pl, np.zeros((n, 1))], [np.zeros((1, n)), np.zeros((1, 1))]])
                cons.append(M == _gram_coeff_cvx(Q0, Q1, d, nu_b, ell))
            # (10): q v(T_{i+1}) < ρ² for the scheduled coordinates
            if any(at.k == k for at in fp.atoms):
                vend = (i + 1) / S
                cons.append(q[i][k] * vend <= float(rho[i][k]) ** 2 * (1 - 1e-6))
        if i + 1 < S:
            cons.append(sum(P[i]) == P[i + 1][0])
    w = weights or [1.0] * n
    obj = cp.Minimize(sum(w[k] * q[i][k] for i in range(S) for k in range(n)))
    pr = cp.Problem(obj, cons)
    try:
        pr.solve(solver=cp.CLARABEL)
    except Exception:  # noqa: BLE001
        return None
    if pr.status not in ("optimal", "optimal_inaccurate"):
        return None
    Pv = [[np.array(P[i][r].value) for r in range(R + 1)] for i in range(S)]
    qv = [[float(q[i][k].value) for k in range(n)] for i in range(S)]
    return Synthesis(Pv, qv, rho, gamma, As, gains, seg, d, R, rows, w)


def synthesize(fp: FunnelProblem, S: int = 16, R: int = 3, rho_init: float = 0.3,
               rho_max: float = math.pi / 2, grow: float = 1.05, iters: int = 30,
               weights=None, verbose=print):
    """Algorithm 1 of the paper, α = 0: band consistency loop over SDPs."""
    d = (R + 2) // 2            # 2d ≥ R + 1
    seg = segments(fp, S)
    n = len(fp.xs)
    sched = sorted({at.k for at in fp.atoms})
    rho = [[Fraction(0)] * n for _ in range(S)]
    for i in range(S):
        for k in sched:
            rho[i][k] = Fraction(rho_init).limit_denominator(1000)
    best = None
    for it in range(iters):
        syn = solve_sdp(fp, seg, rho, R, d, weights=weights)
        if syn is None:
            verbose(f"  funnel: iteration {it}: SDP infeasible at ρ = "
                    f"{[float(rho[i][sched[0]]) for i in range(S)][:4]}...")
            if best is not None:
                break
            rho = [[min(r * Fraction(3, 2), Fraction(rho_max).limit_denominator(1000))
                    if k in sched else r for k, r in enumerate(row)] for row in rho]
            continue
        r = [[math.sqrt(max(syn.q[i][k], 0) * (i + 1) / S) for k in range(n)] for i in range(S)]
        ok = all(r[i][k] < float(rho[i][k]) for i in range(S) for k in sched)
        worst = max(r[i][fp.outputs[0][1].index(1)] if 1 in fp.outputs[0][1] else 0
                    for i in range(S))
        verbose(f"  funnel: iteration {it}: {'consistent' if ok else 'inconsistent'}, "
                f"max bound {worst:.4f}")
        if ok:
            if best is None or worst < best[0] - 1e-6:
                best = (worst, syn)
            new = [[Fraction(grow * r[i][k]).limit_denominator(100000) if k in sched else
                    rho[i][k] for k in range(n)] for i in range(S)]
        else:
            new = [[max(rho[i][k], Fraction(grow * r[i][k]).limit_denominator(100000))
                    if k in sched else rho[i][k] for k in range(n)] for i in range(S)]
            if max(float(x) for row in new for x in row) > rho_max:
                break
        if new == rho:
            break
        rho = new
    if best is None:
        raise FunnelError("no consistent funnel certificate found")
    return best[1]


# --- exact certificate --------------------------------------------------------------------------

def _round_sym(M, den: int) -> list:
    n = len(M)
    out = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            v = Fraction(round(float((M[i][j] + M[j][i]) / 2) * den), den)   # fixed grid
            out[i][j] = out[j][i] = v
    return out


def gram_coeff_exact(Q0, Q1, d, nu, ell):
    out = exact.zeros(nu, nu)
    def blk(Q, a, b):
        return [[Q[a * nu + i][b * nu + j] for j in range(nu)] for i in range(nu)]
    for a in range(d + 1):
        for b in range(d + 1):
            if a + b == ell:
                out = exact.add(out, blk(Q0, a, b))
    for a in range(d):
        for b in range(d):
            if a + b + 1 == ell:
                out = exact.add(out, blk(Q1, a, b))
            if a + b + 2 == ell:
                out = exact.sub(out, blk(Q1, a, b))
    return out


def exact_gram(Mcoef: list, d: int, nu: int, den: int = 10**9):
    """Rational Gram matrices `Q0, Q1` with `gramCoeff = Mcoef[ℓ]` exactly and PSD witnesses,
    from a numeric Gram fit (Peyrl–Parrilo style: round, then project onto the identity)."""
    import cvxpy as cp
    Mf = [np.array([[float(x) for x in row] for row in M]) for M in Mcoef]
    Q0 = cp.Variable(((d + 1) * nu, (d + 1) * nu), PSD=True)
    Q1 = cp.Variable((d * nu, d * nu), PSD=True) if d > 0 else None
    t = cp.Variable()
    cons = [Mf[ell] == _gram_coeff_cvx(Q0, Q1, d, nu, ell) for ell in range(2 * d + 1)]
    cons += [Q0 >> t * np.eye((d + 1) * nu)]
    if d > 0:
        cons += [Q1 >> t * np.eye(d * nu)]
    cp.Problem(cp.Maximize(t), cons + [t <= 1]).solve(solver=cp.CLARABEL)
    if Q0.value is None:
        return None
    q0 = _round_sym(Q0.value, den)
    q1 = _round_sym(Q1.value, den) if d > 0 else []
    # project Q0 onto the coefficient identity (distribute each residual over its blocks)
    for ell in range(2 * d + 1):
        cur = gram_coeff_exact(q0, q1, d, nu, ell)
        E = exact.sub(Mcoef[ell], cur)
        pairs = [(a, ell - a) for a in range(d + 1) if 0 <= ell - a <= d]
        k = len(pairs)
        for a, b in pairs:
            for i in range(nu):
                for j in range(nu):
                    q0[a * nu + i][b * nu + j] += E[i][j] / k
    for ell in range(2 * d + 1):
        assert gram_coeff_exact(q0, q1, d, nu, ell) == Mcoef[ell]
    w0 = exact.psd_witness(q0)
    w1 = exact.psd_witness(q1) if d > 0 else ([], [])
    if w0 is None or w1 is None:
        return None
    return q0, q1, w0, w1


def diss_coeff_exact(P, A, B, h, gamma, ell):
    n, m = len(A), len(B[0])
    R = len(P) - 1
    Z = exact.zeros(n, n)
    Pl = P[ell] if ell <= R else Z
    Pn = P[ell + 1] if ell + 1 <= R else Z
    At = exact.transpose(A)
    TL = exact.scale(-1, exact.add(exact.scale(Fraction(ell + 1) / h, Pn),
                                   exact.add(exact.matmul(At, Pl), exact.matmul(Pl, A))))
    TR = exact.scale(-1, exact.matmul(Pl, B))
    BR = [[gamma[i] if (i == j and ell == 0) else Fraction(0) for j in range(m)]
          for i in range(m)]
    return exact.blocks(TL, TR, exact.transpose(TR), BR)


def band_coeff_exact(P, c, q, ell):
    n = len(c)
    R = len(P) - 1
    Pl = P[ell] if ell <= R else exact.zeros(n, n)
    if ell == 0:
        return exact.blocks(Pl, [[ci] for ci in c], [list(c)], [[q]])
    return exact.blocks(Pl, exact.zeros(n, 1), exact.zeros(1, n), [[Fraction(0)]])


@dataclass
class ExactCert:
    S: int
    h: Fraction
    d: int
    R: int
    P: list                 # per segment: 2d+1 rational matrices (zero-padded beyond R)
    q: list                 # per segment, per row
    rho: list               # per segment, per row (rational; non-scheduled rows: loose)
    gamma: list
    v0: Fraction
    beta: Fraction
    As: list
    gains: list
    diss: list              # per segment, per vertex: (q0, q1, w0, w1)
    band: list              # per segment, per row
    rows: list
    bounds: dict            # output name -> rational bound
    seg: Segments


def exact_certificate(fp: FunnelProblem, syn: Synthesis, den: int = 10**6,
                      verbose=print) -> ExactCert:
    n, m = len(fp.xs), len(fp.ws)
    S, d, R = syn.seg.S, syn.d, syn.R
    h = syn.seg.h
    gamma = [Fraction(round(g * den), den) for g in syn.gamma]
    budget = sum(g * wb ** 2 for g, wb in zip(gamma, fp.w_bounds))
    beta = budget                     # v(t) = β (t - T0), v0 = 0
    v0 = Fraction(0)
    # rational P with exact continuity
    P = []
    for i in range(S):
        Pi = [_round_sym(syn.P[i][r], den) for r in range(R + 1)]
        if i > 0:
            prev = P[-1]
            tot = exact.zeros(n, n)
            for r in range(R + 1):
                tot = exact.add(tot, prev[r])
            Pi[0] = tot
        P.append(Pi)
    for Pi in P:
        while len(Pi) < 2 * d + 1:
            Pi.append(exact.zeros(n, n))
    rows = [[Fraction(1) if j == k else Fraction(0) for j in range(n)] for k in range(n)]
    As = [[[[Fraction(x) for x in row] for row in A] for A in Ai] for Ai in syn.As]
    gains = syn.gains
    diss = []
    for i in range(S):
        di = []
        for A in As[i]:
            Mc = [diss_coeff_exact(P[i], A, fp.B, h, gamma, ell) for ell in range(2 * d + 1)]
            g = exact_gram(Mc, d, n + m)
            if g is None:
                raise FunnelError(f"segment {i}: dissipation SOS not exactly representable")
            di.append(g)
        diss.append(di)
    q, band, rho = [], [], []
    for i in range(S):
        vend = v0 + beta * h * (i + 1)
        qi, bi, ri = [], [], []
        for k in range(n):
            qk = Fraction(math.ceil((syn.q[i][k] * (1 + 1e-6) + 1e-9) * den), den)
            for _ in range(20):
                Mc = [band_coeff_exact(P[i], rows[k], qk, ell) for ell in range(2 * d + 1)]
                g = exact_gram(Mc, d, n + 1)
                if g is not None:
                    break
                qk = qk * Fraction(11, 10) + Fraction(1, den)
            else:
                raise FunnelError(f"segment {i}: band SOS for row {k} not exactly representable")
            qi.append(qk); bi.append(g)
            if any(at.k == k for at in fp.atoms):
                r = Fraction(syn.rho[i][k])
                if not qk * vend < r * r:
                    raise FunnelError(f"segment {i}: band margin fails after rounding")
            else:
                # loose band (not used by the embedding): any ρ with q v < ρ²
                r = Fraction(math.isqrt(int(qk * vend * 10**12) + 1) + 1, 10**6)
            ri.append(r)
        q.append(qi); band.append(bi); rho.append(ri)
    bounds = {}
    for name, c in fp.outputs:
        if sum(1 for x in c if x != 0) != 1 or max(c) != 1:
            raise FunnelError(f"output {name}: only outputs equal to one error coordinate")
        k = c.index(1)
        worst = max(q[i][k] * (v0 + beta * h * (i + 1)) for i in range(S))
        b = Fraction(math.isqrt(int(worst * 10**12)) + 1, 10**6)
        assert b * b >= worst
        bounds[name] = b
    return ExactCert(S, h, d, R, P, q, rho, gamma, v0, beta, As, gains, diss, band, rows,
                     bounds, syn.seg)
