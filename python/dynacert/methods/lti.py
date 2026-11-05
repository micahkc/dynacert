"""LTI dissipation certificates: search for `P, α, γ` and per-state box bounds.

For `ẋ = A x + B w` with `wᵀw ≤ μ`, find a symmetric `P ⪰ I` and rates `α > 0`, `γ ≥ 0` with
`[[AᵀP + PA + αP, PB], [BᵀP, -γI]] ⪯ 0`. Then `V = xᵀPx` satisfies `V̇ ≤ -αV + γμ`, so
`{V ≤ c}` is invariant for any `c ≥ max(V(x₀), γμ/α)`. Per-state bounds come from
`b² P - c eᵢeᵢᵀ ⪰ 0`.

Lean counterparts: `Dynacert.Linear.LTICert`, `LTICert.invariant`, `BoxCert`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

import numpy as np

from .. import exact
from ..exact import Mat, Vec


def lmi_matrix(A: Mat, B: Mat, P: Mat, alpha, gamma) -> Mat:
    """Mirror of `Dynacert.Linear.lmiMatrix`: `-[[AᵀP + PA + αP, PB], [BᵀP, -γI]]`."""
    n, m = len(A), len(B[0])
    At, Bt = exact.transpose(A), exact.transpose(B)
    alpha, gamma = Fraction(alpha), Fraction(gamma)
    TL = [[-(a + b + alpha * p) for a, b, p in zip(r1, r2, r3)]
          for r1, r2, r3 in zip(exact.matmul(At, P), exact.matmul(P, A), P)]
    TR = [[-v for v in r] for r in exact.matmul(P, B)]
    BL = [[-v for v in r] for r in exact.matmul(Bt, P)]
    BR = exact.eye(m, gamma)
    return exact.blocks(TL, TR, BL, BR)


def _solve_lmi(A, B, alpha, eps=1e-6):
    import cvxpy as cp

    n, m = A.shape[0], B.shape[1]
    P = cp.Variable((n, n), symmetric=True)
    g = cp.Variable()
    M = cp.bmat([[A.T @ P + P @ A + alpha * P, P @ B], [B.T @ P, -g * np.eye(m)]])
    cons = [P >> np.eye(n), M << -eps * np.eye(n + m)]
    prob = cp.Problem(cp.Minimize(g / alpha), cons)
    solver = cp.CLARABEL if "CLARABEL" in cp.installed_solvers() else cp.SCS
    try:
        prob.solve(solver=solver)
    except Exception:  # solver failure is just "no candidate"
        return None
    if P.value is None or g.value is None:
        return None
    return P.value, float(g.value)


@dataclass
class BoxBound:
    index: int
    bound: Fraction
    L: Mat
    d: Vec


@dataclass
class LTICertificate:
    P: Mat
    alpha: Fraction
    gamma: Fraction
    mu: Fraction
    level: Fraction
    lmi_L: Mat
    lmi_d: Vec
    boxes: list[BoxBound]


def search(A: Mat, B: Mat, mu, x0: Vec | None = None, alphas=None) -> dict | None:
    """Line search over `α`; returns the rational certificate with the smallest level."""
    n = len(A)
    mu = Fraction(mu)
    x0 = x0 or [Fraction(0)] * n
    alphas = np.geomspace(0.02, 10.0, 48) if alphas is None else alphas
    Af, Bf = np.array(A, dtype=float), np.array(B, dtype=float)
    best = None
    for a in alphas:
        sol = _solve_lmi(Af, Bf, float(a))
        if sol is None:
            continue
        Pf, gf = sol
        alpha = exact.frac(a)
        P = [[exact.frac((Pf[i][j] + Pf[j][i]) / 2) for j in range(n)] for i in range(n)]
        gamma = exact.frac(gf * 1.001 + 1e-9)
        W = exact.psd_witness(lmi_matrix(A, B, P, alpha, gamma))
        if W is None:
            continue
        level = max(gamma * mu / alpha, exact.quad(P, x0))
        if level <= 0:
            continue
        if best is None or level < best["level"]:
            best = dict(P=P, alpha=alpha, gamma=gamma, level=level, W=W)
    return best


def box_bound(P: Mat, c: Fraction, i) -> BoxBound:
    """Smallest (rounded-up) rational `b` with `b² P - c vvᵀ ⪰ 0` (`|vᵀx| ≤ b` on the
    ellipsoid), with its witness. `i` is a coordinate index or a row `v`."""
    n = len(P)
    v = [Fraction(int(j == i)) for j in range(n)] if isinstance(i, int) else [Fraction(x) for x in i]
    Pinv = np.linalg.inv(np.array(P, dtype=float))
    vf = np.array([float(x) for x in v])
    b = exact.frac(math.sqrt(float(c) * float(vf @ Pinv @ vf)) * 1.0001 + 1e-12, 10**4)
    for _ in range(80):
        M = [[b * b * P[r][s] - c * v[r] * v[s] for s in range(n)] for r in range(n)]
        W = exact.psd_witness(M)
        if W is not None:
            return BoxBound(i if isinstance(i, int) else -1, b, W[0], W[1])
        b = exact.frac(float(b) * 1.001, 10**4)
    raise RuntimeError(f"could not certify a bound for output {i}")


def certify(A: Mat, B: Mat, mu, x0: Vec | None = None, outputs: list[int] | None = None,
            alphas=None) -> LTICertificate | None:
    best = search(A, B, mu, x0, alphas)
    if best is None:
        return None
    outputs = list(range(len(A))) if outputs is None else outputs
    boxes = [box_bound(best["P"], best["level"], i) for i in outputs]
    L, d = best["W"]
    return LTICertificate(best["P"], best["alpha"], best["gamma"], Fraction(mu), best["level"],
                          L, d, boxes)


# --- initial boxes (Lean: Dynacert.Linear.boxBound, quad_le_boxBound) -------------------------

def box_bound_value(P: Mat, c: Vec, G: Mat, rho: Vec) -> Fraction:
    """Mirror of `Dynacert.Linear.boxBound`: an exact bound on `zᵀPz` over
    `{c + G e | |eᵢ| ≤ ρᵢ}`, namely `cᵀPc + 2 Σᵢ |(GᵀPc)ᵢ| ρᵢ + Σᵢⱼ |(GᵀPG)ᵢⱼ| ρᵢ ρⱼ`."""
    n, k = len(P), len(rho)
    Pc = [sum((Fraction(P[i][j]) * Fraction(c[j]) for j in range(n)), Fraction(0))
          for i in range(n)]
    g = [sum((Fraction(G[i][a]) * Pc[i] for i in range(n)), Fraction(0)) for a in range(k)]
    PG = [[sum((Fraction(P[i][j]) * Fraction(G[j][b]) for j in range(n)), Fraction(0))
           for b in range(k)] for i in range(n)]
    Q = [[sum((Fraction(G[i][a]) * PG[i][b] for i in range(n)), Fraction(0)) for b in range(k)]
         for a in range(k)]
    r = [Fraction(x) for x in rho]
    return (exact.quad(P, c) + 2 * sum((abs(g[a]) * r[a] for a in range(k)), Fraction(0))
            + sum((abs(Q[a][b]) * r[a] * r[b] for a in range(k) for b in range(k)), Fraction(0)))


def _box_bound_expr(P, c, G, rho):
    """cvxpy expression of `box_bound_value` (convex in `P`)."""
    import cvxpy as cp

    c = np.array([float(v) for v in c])
    G = np.array([[float(v) for v in r] for r in G])
    r = np.array([float(v) for v in rho])
    Q = G.T @ P @ G
    return (c @ P @ c + 2 * cp.sum(cp.multiply(r, cp.abs(G.T @ (P @ c))))
            + cp.sum(cp.multiply(np.outer(r, r), cp.abs(Q))))


def _init_objective(P, rate, init, cap, cons):
    """SDP objective. Without an initial box: the asymptotic level `rate = Σγⱼδⱼ²/α`. With one
    (`init = (x0, G, ρ)`): pass 1 minimizes the invariant level `max(rate, V₀)`; pass 2
    (`cap` given) minimizes `rate` subject to `max(rate, V₀) ≤ cap`, so the funnel shrinks."""
    import cvxpy as cp

    if init is None:
        return rate
    v0 = _box_bound_expr(P, *init)
    if cap is None:
        return cp.maximum(rate, v0)
    cons += [v0 <= cap, rate <= cap]
    return rate


def _funnel_search(step, alphas, init_box, slack):
    """Line search over `α`. `step(a, cap)` returns a candidate dict (with exact `level` and
    `rate`) or None. Without an initial box: the smallest level. With one: the smallest level
    `L*` first, then, among candidates with level ≤ (1 + slack)·L*, the smallest asymptotic
    rate (a level-optimal certificate balances `V₀` against the rate and its funnel is flat)."""
    best = None
    for a in alphas:
        c = step(a, None)
        if c is not None and (best is None or c["level"] < best["level"]):
            best = c
    if best is None or init_box is None or not slack:
        return best
    cap = best["level"] * (1 + Fraction(slack))
    pick = best
    for a in alphas:
        c = step(a, float(cap) / 1.002)
        if c is not None and c["level"] <= cap and c["rate"] < pick["rate"]:
            pick = c
    return pick


def _level(P, budget_over_alpha, x0, box) -> tuple[Fraction, Fraction]:
    """Invariant level and the initial bound `V₀` (the box bound, or `V(x₀)`)."""
    if box is None:
        v0 = exact.quad(P, x0)
    else:
        G, rho = box
        v0 = box_bound_value(P, x0, G, rho)
    return max(budget_over_alpha, v0), v0


# --- per-channel rates (Lean: Dynacert.Linear.ChannelCert) ------------------------------------

def channel_lmi(A: Mat, B: Mat, P: Mat, alpha, gammas) -> Mat:
    """Mirror of `Dynacert.Linear.channelLmi`: `-[[AᵀP + PA + αP, PB], [BᵀP, -diag γ]]`."""
    M = lmi_matrix(A, B, P, alpha, 0)
    n = len(A)
    for j, g in enumerate(gammas):
        M[n + j][n + j] = Fraction(g)
    return M


def _solve_channel_lmi(A, B, alpha, delta2, eps=1e-6, init=None, cap=None):
    import cvxpy as cp

    n, m = A.shape[0], B.shape[1]
    P = cp.Variable((n, n), symmetric=True)
    g = cp.Variable(m)
    M = cp.bmat([[A.T @ P + P @ A + alpha * P, P @ B], [B.T @ P, -cp.diag(g)]])
    cons = [P >> np.eye(n), M << -eps * np.eye(n + m), g >= 0]
    obj = _init_objective(P, delta2 @ g / alpha, init, cap, cons)
    prob = cp.Problem(cp.Minimize(obj), cons)
    solver = cp.CLARABEL if "CLARABEL" in cp.installed_solvers() else cp.SCS
    try:
        prob.solve(solver=solver)
    except Exception:
        return None
    if P.value is None or g.value is None:
        return None
    return P.value, [max(float(v), 0.0) for v in g.value]


@dataclass
class ChannelCertificate:
    P: Mat
    alpha: Fraction
    gammas: list[Fraction]
    deltas: list[Fraction]
    budget: Fraction
    level: Fraction
    lmi_L: Mat
    lmi_d: Vec
    boxes: list
    V0: Fraction | None = None   # bound on V over the initial set (`init_box` only)


def spectral_alphas(As, n: int = 48) -> np.ndarray:
    """Decay rates scaled to the dynamics: `V̇ ≤ -αV` needs `α < 2s`, with `s` the slowest decay
    rate (minus the spectral abscissa) over the vertices. Empty if some vertex is not Hurwitz."""
    s = min(-max(np.linalg.eigvals(np.array(A, dtype=float)).real) for A in As)
    if not s > 0:
        return np.array([])
    return np.geomspace(1e-3 * s, 1.98 * s, n)


def certify_channels(A: Mat, B: Mat, deltas, x0: Vec | None = None, outputs=None,
                     alphas=None, output_rows=None, init_box=None,
                     funnel_slack=Fraction(1, 10)) -> ChannelCertificate | None:
    """Per-channel peak bounds `|wⱼ| ≤ δⱼ`; minimizes the invariant level `Σγⱼδⱼ²/α`.

    `init_box = (G, ρ)`: the initial state ranges over `{x0 + G e | |eᵢ| ≤ ρᵢ}`; the level then
    also covers `box_bound_value(P, x0, G, ρ)` (returned as `V0`), and up to `funnel_slack`
    of the level is traded for a smaller asymptotic rate (see `_funnel_search`)."""
    n = len(A)
    deltas = [Fraction(d) for d in deltas]
    x0 = x0 or [Fraction(0)] * n
    default_grid = alphas is None
    alphas = np.geomspace(0.02, 10.0, 48) if alphas is None else alphas
    Af, Bf = np.array(A, dtype=float), np.array(B, dtype=float)
    d2 = np.array([float(d * d) for d in deltas])

    def step(a, cap):
        sol = _solve_channel_lmi(Af, Bf, float(a), d2,
                                 init=None if init_box is None else (x0, *init_box), cap=cap)
        if sol is None:
            return None
        Pf, gf = sol
        alpha = exact.frac(a)
        P = [[exact.frac((Pf[i][j] + Pf[j][i]) / 2) for j in range(n)] for i in range(n)]
        gammas = [exact.frac(g * 1.001 + 1e-9) for g in gf]
        W = exact.psd_witness(channel_lmi(A, B, P, alpha, gammas))
        if W is None:
            return None
        budget = sum((g * d * d for g, d in zip(gammas, deltas)), Fraction(0))
        level, v0 = _level(P, budget / alpha, x0, init_box)
        if level <= 0:
            return None
        return dict(P=P, alpha=alpha, gammas=gammas, budget=budget, level=level, W=W, V0=v0,
                    rate=budget / alpha)

    best = _funnel_search(step, alphas, init_box, funnel_slack)
    if best is None and default_grid:     # time scale far from the default grid: rescale
        best = _funnel_search(step, spectral_alphas([A]), init_box, funnel_slack)
    if best is None:
        return None
    if output_rows is not None:
        boxes = [box_bound(best["P"], best["level"], r) for r in output_rows]
    else:
        outputs = list(range(n)) if outputs is None else outputs
        boxes = [box_bound(best["P"], best["level"], i) for i in outputs]
    L, d = best["W"]
    return ChannelCertificate(best["P"], best["alpha"], best["gammas"], deltas, best["budget"],
                              best["level"], L, d, boxes,
                              best["V0"] if init_box is not None else None)


# --- polytopes (Lean: Dynacert.Linear.PolytopicCert) ------------------------------------------

def _solve_polytopic_lmi(As, B, alpha, delta2, eps=1e-6, init=None, cap=None):
    import cvxpy as cp

    n, m = As[0].shape[0], B.shape[1]
    P = cp.Variable((n, n), symmetric=True)
    g = cp.Variable(m)
    cons = [P >> np.eye(n), g >= 0]
    for A in As:
        M = cp.bmat([[A.T @ P + P @ A + alpha * P, P @ B], [B.T @ P, -cp.diag(g)]])
        cons.append(M << -eps * np.eye(n + m))
    obj = _init_objective(P, delta2 @ g / alpha, init, cap, cons)
    prob = cp.Problem(cp.Minimize(obj), cons)
    solver = cp.CLARABEL if "CLARABEL" in cp.installed_solvers() else cp.SCS
    try:
        prob.solve(solver=solver)
    except Exception:
        return None
    if P.value is None or g.value is None:
        return None
    return P.value, [max(float(v), 0.0) for v in g.value]


@dataclass
class PolytopicCertificate:
    P: Mat
    alpha: Fraction
    gammas: list[Fraction]
    deltas: list[Fraction]
    budget: Fraction
    level: Fraction
    witnesses: list  # one (L, d) per vertex
    boxes: list
    V0: Fraction | None = None   # bound on V over the initial set (`init_box` only)


def certify_polytopic(As: list[Mat], B: Mat, deltas, x0: Vec | None = None, outputs=None,
                      alphas=None, output_rows=None, init_box=None,
                      funnel_slack=Fraction(1, 10)) -> PolytopicCertificate | None:
    """Common `P` for all vertices `As`; per-channel peak bounds `|wⱼ| ≤ δⱼ`. `init_box` and
    `funnel_slack` as in `certify_channels`."""
    n = len(As[0])
    deltas = [Fraction(d) for d in deltas]
    x0 = x0 or [Fraction(0)] * n
    default_grid = alphas is None
    alphas = np.geomspace(0.02, 10.0, 48) if alphas is None else alphas
    Afs = [np.array(A, dtype=float) for A in As]
    Bf = np.array(B, dtype=float)
    d2 = np.array([float(d * d) for d in deltas])

    def step(a, cap):
        sol = _solve_polytopic_lmi(Afs, Bf, float(a), d2,
                                   init=None if init_box is None else (x0, *init_box), cap=cap)
        if sol is None:
            return None
        Pf, gf = sol
        alpha = exact.frac(a)
        P = [[exact.frac((Pf[i][j] + Pf[j][i]) / 2) for j in range(n)] for i in range(n)]
        gammas = [exact.frac(g * 1.001 + 1e-9) for g in gf]
        Ws = [exact.psd_witness(channel_lmi(A, B, P, alpha, gammas)) for A in As]
        if any(W is None for W in Ws):
            return None
        budget = sum((g * d * d for g, d in zip(gammas, deltas)), Fraction(0))
        level, v0 = _level(P, budget / alpha, x0, init_box)
        if level <= 0:
            return None
        return dict(P=P, alpha=alpha, gammas=gammas, budget=budget, level=level, Ws=Ws, V0=v0,
                    rate=budget / alpha)

    best = _funnel_search(step, alphas, init_box, funnel_slack)
    if best is None and default_grid:     # time scale far from the default grid: rescale
        best = _funnel_search(step, spectral_alphas(As), init_box, funnel_slack)
    if best is None:
        return None
    if output_rows is not None:
        boxes = [box_bound(best["P"], best["level"], r) for r in output_rows]
    else:
        outputs = list(range(n)) if outputs is None else outputs
        boxes = [box_bound(best["P"], best["level"], i) for i in outputs]
    return PolytopicCertificate(best["P"], best["alpha"], best["gammas"], deltas, best["budget"],
                                best["level"], best["Ws"], boxes,
                                best["V0"] if init_box is not None else None)
