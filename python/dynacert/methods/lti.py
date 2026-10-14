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


# --- per-channel rates (Lean: Dynacert.Linear.ChannelCert) ------------------------------------

def channel_lmi(A: Mat, B: Mat, P: Mat, alpha, gammas) -> Mat:
    """Mirror of `Dynacert.Linear.channelLmi`: `-[[AᵀP + PA + αP, PB], [BᵀP, -diag γ]]`."""
    M = lmi_matrix(A, B, P, alpha, 0)
    n = len(A)
    for j, g in enumerate(gammas):
        M[n + j][n + j] = Fraction(g)
    return M


def _solve_channel_lmi(A, B, alpha, delta2, eps=1e-6):
    import cvxpy as cp

    n, m = A.shape[0], B.shape[1]
    P = cp.Variable((n, n), symmetric=True)
    g = cp.Variable(m)
    M = cp.bmat([[A.T @ P + P @ A + alpha * P, P @ B], [B.T @ P, -cp.diag(g)]])
    cons = [P >> np.eye(n), M << -eps * np.eye(n + m), g >= 0]
    prob = cp.Problem(cp.Minimize(delta2 @ g / alpha), cons)
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


def certify_channels(A: Mat, B: Mat, deltas, x0: Vec | None = None, outputs=None,
                     alphas=None, output_rows=None) -> ChannelCertificate | None:
    """Per-channel peak bounds `|wⱼ| ≤ δⱼ`; minimizes the invariant level `Σγⱼδⱼ²/α`."""
    n = len(A)
    deltas = [Fraction(d) for d in deltas]
    x0 = x0 or [Fraction(0)] * n
    alphas = np.geomspace(0.02, 10.0, 48) if alphas is None else alphas
    Af, Bf = np.array(A, dtype=float), np.array(B, dtype=float)
    d2 = np.array([float(d * d) for d in deltas])
    best = None
    for a in alphas:
        sol = _solve_channel_lmi(Af, Bf, float(a), d2)
        if sol is None:
            continue
        Pf, gf = sol
        alpha = exact.frac(a)
        P = [[exact.frac((Pf[i][j] + Pf[j][i]) / 2) for j in range(n)] for i in range(n)]
        gammas = [exact.frac(g * 1.001 + 1e-9) for g in gf]
        W = exact.psd_witness(channel_lmi(A, B, P, alpha, gammas))
        if W is None:
            continue
        budget = sum((g * d * d for g, d in zip(gammas, deltas)), Fraction(0))
        level = max(budget / alpha, exact.quad(P, x0))
        if level <= 0:
            continue
        if best is None or level < best["level"]:
            best = dict(P=P, alpha=alpha, gammas=gammas, budget=budget, level=level, W=W)
    if best is None:
        return None
    if output_rows is not None:
        boxes = [box_bound(best["P"], best["level"], r) for r in output_rows]
    else:
        outputs = list(range(n)) if outputs is None else outputs
        boxes = [box_bound(best["P"], best["level"], i) for i in outputs]
    L, d = best["W"]
    return ChannelCertificate(best["P"], best["alpha"], best["gammas"], deltas, best["budget"],
                              best["level"], L, d, boxes)


# --- polytopes (Lean: Dynacert.Linear.PolytopicCert) ------------------------------------------

def _solve_polytopic_lmi(As, B, alpha, delta2, eps=1e-6):
    import cvxpy as cp

    n, m = As[0].shape[0], B.shape[1]
    P = cp.Variable((n, n), symmetric=True)
    g = cp.Variable(m)
    cons = [P >> np.eye(n), g >= 0]
    for A in As:
        M = cp.bmat([[A.T @ P + P @ A + alpha * P, P @ B], [B.T @ P, -cp.diag(g)]])
        cons.append(M << -eps * np.eye(n + m))
    prob = cp.Problem(cp.Minimize(delta2 @ g / alpha), cons)
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


def certify_polytopic(As: list[Mat], B: Mat, deltas, x0: Vec | None = None, outputs=None,
                      alphas=None, output_rows=None) -> PolytopicCertificate | None:
    """Common `P` for all vertices `As`; per-channel peak bounds `|wⱼ| ≤ δⱼ`."""
    n = len(As[0])
    deltas = [Fraction(d) for d in deltas]
    x0 = x0 or [Fraction(0)] * n
    alphas = np.geomspace(0.02, 10.0, 48) if alphas is None else alphas
    Afs = [np.array(A, dtype=float) for A in As]
    Bf = np.array(B, dtype=float)
    d2 = np.array([float(d * d) for d in deltas])
    best = None
    for a in alphas:
        sol = _solve_polytopic_lmi(Afs, Bf, float(a), d2)
        if sol is None:
            continue
        Pf, gf = sol
        alpha = exact.frac(a)
        P = [[exact.frac((Pf[i][j] + Pf[j][i]) / 2) for j in range(n)] for i in range(n)]
        gammas = [exact.frac(g * 1.001 + 1e-9) for g in gf]
        Ws = [exact.psd_witness(channel_lmi(A, B, P, alpha, gammas)) for A in As]
        if any(W is None for W in Ws):
            continue
        budget = sum((g * d * d for g, d in zip(gammas, deltas)), Fraction(0))
        level = max(budget / alpha, exact.quad(P, x0))
        if level <= 0:
            continue
        if best is None or level < best["level"]:
            best = dict(P=P, alpha=alpha, gammas=gammas, budget=budget, level=level, Ws=Ws)
    if best is None:
        return None
    if output_rows is not None:
        boxes = [box_bound(best["P"], best["level"], r) for r in output_rows]
    else:
        outputs = list(range(n)) if outputs is None else outputs
        boxes = [box_bound(best["P"], best["level"], i) for i in outputs]
    return PolytopicCertificate(best["P"], best["alpha"], best["gammas"], deltas, best["budget"],
                                best["level"], best["Ws"], boxes)
