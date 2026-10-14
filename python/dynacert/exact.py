"""Exact rational linear algebra used to build certificates.

Everything here is untrusted: the Lean kernel re-checks every identity. These helpers only
have to produce data that passes that check.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

Mat = list[list[Fraction]]
Vec = list[Fraction]


def frac(x, max_den: int = 10**6) -> Fraction:
    """Round a float (or anything Fraction accepts) to a nearby rational."""
    return Fraction(x).limit_denominator(max_den)


def to_mat(rows: Sequence[Sequence]) -> Mat:
    return [[Fraction(v) for v in r] for r in rows]


def zeros(r: int, c: int) -> Mat:
    return [[Fraction(0)] * c for _ in range(r)]


def eye(n: int, scale=1) -> Mat:
    s = Fraction(scale)
    return [[s if i == j else Fraction(0) for j in range(n)] for i in range(n)]


def transpose(X: Mat) -> Mat:
    return [list(r) for r in zip(*X)] if X else []


def matmul(X: Mat, Y: Mat) -> Mat:
    return [[sum((X[i][p] * Y[p][j] for p in range(len(Y))), Fraction(0))
             for j in range(len(Y[0]))] for i in range(len(X))]


def matvec(X: Mat, v: Vec) -> Vec:
    return [sum((X[i][j] * v[j] for j in range(len(v))), Fraction(0)) for i in range(len(X))]


def add(X: Mat, Y: Mat) -> Mat:
    return [[a + b for a, b in zip(r, s)] for r, s in zip(X, Y)]


def sub(X: Mat, Y: Mat) -> Mat:
    return [[a - b for a, b in zip(r, s)] for r, s in zip(X, Y)]


def scale(c, X: Mat) -> Mat:
    c = Fraction(c)
    return [[c * a for a in r] for r in X]


def dot(u: Vec, v: Vec) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


def quad(P: Mat, x: Vec) -> Fraction:
    return dot(x, matvec(P, x))


def blocks(TL: Mat, TR: Mat, BL: Mat, BR: Mat) -> Mat:
    return [a + b for a, b in zip(TL, TR)] + [a + b for a, b in zip(BL, BR)]


def ldlt(M: Mat):
    """Exact `M = L0 diag(d) L0ᵀ`, `L0` unit lower triangular, `d ≥ 0`.

    Returns `(L0, d)`, or `None` if `M` is not PSD (or the pivoting-free factorization breaks).
    """
    k = len(M)
    L0 = [[Fraction(int(i == j)) for j in range(k)] for i in range(k)]
    d = [Fraction(0)] * k
    for j in range(k):
        d[j] = M[j][j] - sum((L0[j][p] ** 2 * d[p] for p in range(j)), Fraction(0))
        if d[j] < 0:
            return None
        for i in range(j + 1, k):
            r = M[i][j] - sum((L0[i][p] * L0[j][p] * d[p] for p in range(j)), Fraction(0))
            if d[j] == 0:
                if r != 0:
                    return None
            else:
                L0[i][j] = r / d[j]
    return L0, d


def psd_witness(M: Mat):
    """A `PSDWitness` for `M`: `(L, d)` with `M = Lᵀ diag(d) L`, or `None`."""
    W = ldlt(M)
    if W is None:
        return None
    L0, d = W
    return transpose(L0), d


def check_witness(M: Mat, L: Mat, d: Vec) -> bool:
    """Re-check `M = Lᵀ diag(d) L` and `d ≥ 0` exactly (mirror of the Lean check)."""
    if any(x < 0 for x in d):
        return False
    D = [[d[i] if i == j else Fraction(0) for j in range(len(d))] for i in range(len(d))]
    return matmul(matmul(transpose(L), D), L) == M


def symmetrize(P) -> Mat:
    n = len(P)
    return [[(P[i][j] + P[j][i]) / 2 for j in range(n)] for i in range(n)]
