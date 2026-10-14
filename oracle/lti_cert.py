#!/usr/bin/env python3
"""Untrusted certificate oracle for LTI models.

Solves the dissipation LMI numerically, rounds the solution to rationals, and emits a Lean file
whose proof obligations are exact rational identities checked by the Lean kernel. Nothing here
is trusted: if rounding breaks feasibility, the exact LDL^T factorization fails here (or the
kernel check fails in Lean), and no certificate is produced.

Usage:
    python oracle/lti_cert.py MODEL.json --module Dynacert.Examples.MassSpringDamper.Model \
        --out Dynacert/Examples/MassSpringDamper/Cert.lean

MODEL.json:
    {"name": "msd", "A": [["0","1"],["-11","-11/5"]], "B": [["0"],["1"]],
     "w_max": "1", "states": ["e", "ev"]}
`w_max` bounds the Euclidean norm of the disturbance (mu = w_max^2).
"""

import argparse
import json
import math
from fractions import Fraction

import cvxpy as cp
import numpy as np


def frac(x, max_den=10**6):
    return Fraction(x).limit_denominator(max_den)


def ldlt(M):
    """Exact M = L0 diag(d) L0^T with L0 unit lower triangular. Returns (L0, d) or None."""
    k = len(M)
    L0 = [[Fraction(int(i == j)) for j in range(k)] for i in range(k)]
    d = [Fraction(0)] * k
    for j in range(k):
        d[j] = M[j][j] - sum(L0[j][p] ** 2 * d[p] for p in range(j))
        for i in range(j + 1, k):
            r = M[i][j] - sum(L0[i][p] * L0[j][p] * d[p] for p in range(j))
            if d[j] == 0:
                if r != 0:
                    return None
            else:
                L0[i][j] = r / d[j]
        if d[j] < 0:
            return None
    return L0, d


def matmul(X, Y):
    return [[sum(X[i][p] * Y[p][j] for p in range(len(Y))) for j in range(len(Y[0]))]
            for i in range(len(X))]


def transpose(X):
    return [list(r) for r in zip(*X)]


def lmi_matrix(A, B, P, alpha, gamma):
    """-[[A^T P + P A + alpha P, P B], [B^T P, -gamma I]] (mirrors Dynacert.Linear.lmiMatrix)."""
    n, m = len(A), len(B[0])
    At, Bt = transpose(A), transpose(B)
    TL = [[-(a + b + alpha * p) for a, b, p in zip(r1, r2, r3)]
          for r1, r2, r3 in zip(matmul(At, P), matmul(P, A), P)]
    TR = [[-v for v in r] for r in matmul(P, B)]
    BL = [[-v for v in r] for r in matmul(Bt, P)]
    BR = [[gamma if i == j else Fraction(0) for j in range(m)] for i in range(m)]
    return [TL[i] + TR[i] for i in range(n)] + [BL[i] + BR[i] for i in range(m)]


def solve_lmi(A, B, alpha, eps=1e-6):
    n, m = A.shape[0], B.shape[1]
    P = cp.Variable((n, n), symmetric=True)
    g = cp.Variable()
    M = cp.bmat([[A.T @ P + P @ A + alpha * P, P @ B], [B.T @ P, -g * np.eye(m)]])
    cons = [P >> np.eye(n), M << -eps * np.eye(n + m)]
    prob = cp.Problem(cp.Minimize(g / alpha), cons)
    prob.solve(solver=cp.SCS if "CLARABEL" not in cp.installed_solvers() else cp.CLARABEL)
    if P.value is None:
        return None
    return P.value, g.value


def certify(A, B, mu, alphas):
    """Line search over alpha; return the rational certificate with the smallest level."""
    best = None
    Af, Bf = np.array(A, dtype=float), np.array(B, dtype=float)
    for a in alphas:
        sol = solve_lmi(Af, Bf, a)
        if sol is None:
            continue
        Pf, gf = sol
        alpha = frac(a)
        P = [[frac((Pf[i][j] + Pf[j][i]) / 2) for j in range(len(A))] for i in range(len(A))]
        gamma = frac(gf * 1.001 + 1e-9)
        W = ldlt(lmi_matrix(A, B, P, alpha, gamma))
        if W is None:
            continue
        level = gamma * mu / alpha
        if best is None or level < best["c"]:
            best = dict(P=P, alpha=alpha, gamma=gamma, c=level, lmi=W)
    return best


def box_bound(P, c, i):
    """Smallest (rounded-up) rational b with b^2 P - c e_i e_i^T PSD, checked exactly."""
    Pinv = np.linalg.inv(np.array(P, dtype=float))
    b = frac(math.sqrt(float(c) * Pinv[i][i]) * 1.0001, 10**4)
    n = len(P)
    for _ in range(50):
        M = [[b * b * P[r][s] - (c if r == s == i else 0) for s in range(n)] for r in range(n)]
        W = ldlt(M)
        if W is not None:
            return b, W
        b = frac(float(b) * 1.001, 10**4)
    raise RuntimeError(f"could not certify a box bound for state {i}")


# --- Lean emission ---------------------------------------------------------------------------

def q(x):
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def mat(X):
    return "!![" + "; ".join(", ".join(q(v) for v in r) for r in X) + "]"


def vec(v):
    return "![" + ", ".join(q(x) for x in v) + "]"


def witness_sum(W, n, m):
    """Witness for a matrix indexed by Fin n ⊕ Fin m: L = L0^T as fromBlocks."""
    L0, d = W
    L = transpose(L0)
    blk = lambda r0, r1, c0, c1: [row[c0:c1] for row in L[r0:r1]]
    Lf = (f"(fromBlocks {mat(blk(0, n, 0, n))} {mat(blk(0, n, n, n + m))}\n"
          f"        {mat(blk(n, n + m, 0, n))} {mat(blk(n, n + m, n, n + m))})")
    return Lf, f"Sum.elim {vec(d[:n])} {vec(d[n:])}"


def emit(model, module, cert, boxes):
    name = model["name"]
    n, m = len(model["A"]), len(model["B"][0])
    states = model.get("states", [f"x{i}" for i in range(n)])
    Lf, df = witness_sum(cert["lmi"], n, m)
    idx = f"Fin {n} ⊕ Fin {m}"
    out = [
        f"import {module}",
        "",
        "/-!",
        f"# Certificate for {name}",
        "",
        "GENERATED by `oracle/lti_cert.py`; do not edit. The oracle is untrusted: every fact below",
        "is checked by the Lean kernel (`decide +kernel`), with no `native_decide`.",
        "-/",
        "",
        "set_option linter.style.longLine false",
        "",
        f"namespace {module}",
        "",
        "open Matrix Set Dynacert Dynacert.Linear",
        "",
        "/-! ### Storage function `V x = xᵀ P x` and dissipation rates -/",
        "",
        f"def P : Matrix (Fin {n}) (Fin {n}) ℚ := {mat(cert['P'])}",
        f"def α : ℚ := {q(cert['alpha'])}",
        f"def γ : ℚ := {q(cert['gamma'])}",
        "",
        "/-- Exact factor `lmiMatrix A B P α γ = Lᵀ D L`. -/",
        f"def lmiL : Matrix ({idx}) ({idx}) ℚ :=",
        f"  {Lf}",
        f"def lmiD : {idx} → ℚ :=",
        f"  {df}",
        "",
        "def lmiWitness : PSDWitness (lmiMatrix model.A model.B P α γ) :=",
        "  ⟨lmiL, lmiD, by decide +kernel, by decide +kernel⟩",
        "",
        "def cert : LTICert model :=",
        "  ⟨P, α, γ, by decide +kernel, by decide +kernel, by decide +kernel, lmiWitness⟩",
        "",
        f"/-- Invariant level `γ μ / α` with `μ = {q(cert['mu'])}`. -/",
        f"def level : ℚ := {q(cert['c'])}",
        "",
        "/-! ### Per-state bounds on the invariant ellipsoid -/",
        "",
    ]
    for i, (b, W) in enumerate(boxes):
        L0, d = W
        out += [
            f"/-- `|{states[i]}| ≤ {q(b)}` on `{{xᵀPx ≤ level}}`. -/",
            f"def box{i} : BoxCert P level {i} ({q(b)}) :=",
            "  ⟨by decide +kernel, by decide +kernel,",
            f"    ⟨{mat(transpose(L0))},",
            f"     {vec(d)},",
            "     by decide +kernel, by decide +kernel⟩⟩",
            "",
        ]
    concl = " ∧ ".join(f"|x t {i}| ≤ ({q(b)} : ℚ)" for i, (b, _) in enumerate(boxes))
    out += [
        "/-- Reachability guarantee: from rest, under disturbances with `wᵀw ≤ μ`, every",
        "state stays inside its certified bound for all time. -/",
        "theorem reach {x : ℝ → Fin " + str(n) + " → ℝ} {w : ℝ → Fin " + str(m)
        + " → ℝ} {T : ℝ}",
        "    (hx : system.IsSolution x w T)",
        f"    (hw : ∀ t ∈ Ico 0 T, w t ⬝ᵥ w t ≤ ({q(cert['mu'])} : ℚ)) (h0 : x 0 = 0) :",
        f"    ∀ t ∈ Icc 0 T, {concl} := by",
        "  rw [← model_toSystem] at hx",
        "  have hc : (cert.γ : ℝ) * ((" + q(cert["mu"]) + " : ℚ) : ℝ) / cert.α ≤ (level : ℝ) := by",
        "    have : cert.γ * " + q(cert["mu"]) + " / cert.α ≤ level := by decide +kernel",
        "    exact_mod_cast this",
        "  have h0' : quad (toReal cert.P) (x 0) ≤ (level : ℝ) := by",
        "    rw [h0, quad, mulVec_zero, dotProduct_zero]",
        "    exact_mod_cast (by decide +kernel : (0 : ℚ) ≤ level)",
        "  intro t ht",
        "  have hV := cert.invariant hx hw h0' hc t ht",
        "  exact " + (", ".join(f"box{i}.abs_le hV" for i in range(len(boxes))).join("⟨⟩")
                      if len(boxes) > 1 else "box0.abs_le hV"),
        "",
        f"end {module}",
        "",
    ]
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("model")
    ap.add_argument("--module", required=True, help="Lean module defining `model` and `system`")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    model = json.load(open(args.model))
    A = [[Fraction(v) for v in r] for r in model["A"]]
    B = [[Fraction(v) for v in r] for r in model["B"]]
    mu = Fraction(model["w_max"]) ** 2
    cert = certify(A, B, mu, alphas=np.geomspace(0.05, 5.0, 40))
    if cert is None:
        raise SystemExit("no certificate found")
    cert["mu"] = mu
    boxes = [box_bound(cert["P"], cert["c"], i) for i in range(len(A))]
    with open(args.out, "w") as f:
        f.write(emit(model, args.module, cert, boxes))
    print(f"level c = {float(cert['c']):.6g}, alpha = {float(cert['alpha']):.4g}")
    for i, (b, _) in enumerate(boxes):
        print(f"  |{model.get('states', ['x%d' % k for k in range(len(A))])[i]}| <= {float(b):.6g}")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
