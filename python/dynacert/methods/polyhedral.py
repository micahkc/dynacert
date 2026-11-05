"""Polyhedral robust positively invariant (RPI) sets for `ż = A z + B w`, `|wⱼ| ≤ δⱼ`.

The certificate is a polytope `S = {z | H z ≤ h}` and a Metzler matrix `M` (nonnegative off
the diagonal) with

    H A = M H          and          M h + |H B| δ < 0       (strict, componentwise),

plus, per certified output row `c`, LP-duality multipliers `λ⁺, λ⁻ ≥ 0` with `λ⁺ᵀH = c`,
`λ⁻ᵀH = -c`, `λ±ᵀh ≤ b`. Lean counterparts: `Dynacert.Linear.PolyCert.invariant` and
`PolyOutputCert.abs_le`.

Search (untrusted, numeric, then exact):

1. *Directions.* Rational facet normals `H`: ±output rows, ±their images `c e^{At}` along the
   flow (the support of the minimal RPI set is driven by these), and ± directions spread
   uniformly in the metric of a Lyapunov ellipsoid (so the polytope is "round" enough to be
   contractive). `facets` controls the total count.
2. *Row LPs.* For fixed offsets `h`, row `i` of `M` solves
   `min Σⱼ Mᵢⱼ hⱼ  s.t.  Mᵢ H = Hᵢ A,  Mᵢⱼ ≥ 0 (j ≠ i)`. By LP duality its value is the largest
   derivative of `Hᵢ z` over the face `{Hᵢ z = hᵢ, H z ≤ h}` (Nagumo on the face).
3. *Policy iteration.* Start from the polytope circumscribing a Lyapunov ellipsoid, then
   alternate `M ← row LPs(h)` and `h ← -M⁻¹ (|HB|δ + ε)` (the smallest offsets for that `M`;
   `-M⁻¹ ≥ 0` for Metzler Hurwitz `M`). The offsets decrease monotonically (Howard's
   algorithm); the limit is the tightest polytope with these normals.
4. *Exact.* Each row of `M` is re-solved exactly on its LP basis, so `H A = M H` holds in ℚ;
   `h` is rounded up, and every condition is re-verified with `Fraction`s.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np

from .. import exact
from ..exact import Mat, Vec


# --- exact checks (mirror of the Lean fields) ---------------------------------------------------

def is_metzler(M: Mat) -> bool:
    return all(M[i][j] >= 0 for i in range(len(M)) for j in range(len(M)) if i != j)


def margin(H: Mat, h: Vec, M: Mat, A: Mat, B: Mat, delta: Vec) -> Vec:
    """`M h + |H B| δ` (each entry must be `< 0`)."""
    HB = exact.matmul(H, B)
    absHB = [[abs(v) for v in r] for r in HB]
    return [a + b for a, b in zip(exact.matvec(M, h), exact.matvec(absHB, delta))]


def vecmul(l: Vec, H: Mat) -> Vec:
    return [sum((l[i] * H[i][j] for i in range(len(H))), Fraction(0)) for j in range(len(H[0]))]


@dataclass
class OutputBound:
    row: Vec          # c
    lp: Vec           # λ⁺
    lm: Vec           # λ⁻
    bound: Fraction   # b


@dataclass
class PolyhedralCertificate:
    H: Mat
    h: Vec
    M: Mat
    delta: Vec
    outputs: list[OutputBound]
    stats: dict = field(default_factory=dict)

    @property
    def facets(self) -> int:
        return len(self.H)

    def check(self, A: Mat, B: Mat, x0: Vec | None = None) -> list[str]:
        """Exact re-verification of every Lean field; returns the failures (empty = valid)."""
        errs = []
        if not is_metzler(self.M):
            errs.append("M is not Metzler")
        if exact.matmul(self.H, A) != exact.matmul(self.M, self.H):
            errs.append("H A ≠ M H")
        if any(v >= 0 for v in margin(self.H, self.h, self.M, A, B, self.delta)):
            errs.append("margin M h + |HB| δ < 0 fails")
        if x0 is not None and any(a > b for a, b in zip(exact.matvec(self.H, x0), self.h)):
            errs.append("x0 is not in the polytope")
        for o in self.outputs:
            if any(v < 0 for v in o.lp + o.lm):
                errs.append("negative multiplier")
            if vecmul(o.lp, self.H) != list(o.row) or \
                    vecmul(o.lm, self.H) != [-v for v in o.row]:
                errs.append("λᵀH ≠ ±c")
            if exact.dot(o.lp, self.h) > o.bound or exact.dot(o.lm, self.h) > o.bound:
                errs.append("λᵀh > b")
        return errs


# --- directions ---------------------------------------------------------------------------------

def _rat_dir(v: np.ndarray, den: int) -> Vec:
    """A rational direction close to `v` (scaled so max |vᵢ| = 1, denominators ≤ den)."""
    v = v / np.max(np.abs(v))
    return [Fraction(float(x)).limit_denominator(den) for x in v]


def modal_rows(A: np.ndarray, polygon: int = 12, ratio: float = 0.7):
    """Normals and offsets of a contractive polytope in real modal coordinates.

    A real eigenvalue with left eigenvector `w` gives the slab `|w z| ≤ 1`; a complex pair
    `σ ± iω` with left eigenvector `u + iv` gives a regular `p`-gon in `(u z, v z)`, which is
    contractive when `tan(π/p) < |σ/ω|` (rotation against decay). Returns `(rows, offsets)`,
    or None if `A` is (nearly) defective or a mode is too lightly damped.
    """
    lam, W = np.linalg.eig(A.T)
    if np.linalg.cond(W) > 1e8:
        return None
    rows, done = [], set()
    for i, l in enumerate(lam):
        if i in done:
            continue
        w = W[:, i]
        if abs(l.imag) < 1e-12 * max(1.0, abs(l)):
            done.add(i)
            r = w.real / np.max(np.abs(w.real))
            rows += [r, -r]
            continue
        j = min((j for j in range(len(lam)) if j not in done and j != i),
                key=lambda j: abs(lam[j] - l.conjugate()))
        done |= {i, j}
        sig, om = -l.real, abs(l.imag)
        if sig <= 0:
            return None
        p = max(polygon, math.ceil(math.pi / math.atan(ratio * sig / om)))
        if p > 400:
            return None
        u, v = w.real, w.imag
        sc = max(np.max(np.abs(u)), np.max(np.abs(v)))
        u, v = u / sc, v / sc
        for th in np.linspace(0, 2 * math.pi, p, endpoint=False):
            rows.append(math.cos(th) * u + math.sin(th) * v)
    return rows


def directions(A: np.ndarray, rows: list[np.ndarray], facets: int, den: int = 1000,
               polygon: int = 12, horizon: float = 1.0) -> tuple[list[Vec], list[Vec]] | None:
    """Rational facet normals: the modal polytope (for a contractive start), ±output rows, and
    ±their images `c e^{At}` along the flow for `t ∈ (0, horizon/σ]`, `σ` the slowest decay
    rate. The flow images carry the tightness: for the polytope's support in direction `c`, the
    face conditions along these normals reproduce a Riemann sum of `∫ |c e^{As} B| δ ds`.
    Returns `(modal, H, n_modal)`: the float modal normals (offsets 1), all rational normals,
    and how many of the first rows of `H` are the rounded modal normals."""
    from scipy.linalg import expm

    modal = modal_rows(A, polygon)
    if modal is None:
        return None
    cand = list(modal)
    flow = []
    for c in rows:
        flow += [c, -c]
    n_orb = max(0, (facets - len(modal) - len(flow)) // max(1, 2 * len(rows)))
    sig = max(1e-6, -max(np.linalg.eigvals(A).real))
    for c in rows:
        for t in np.linspace(0, horizon / sig, n_orb + 1)[1:]:
            v = c @ expm(A * t)
            if np.linalg.norm(v) > 1e-12:
                flow += [v, -v]
    out, seen, n_modal = [], set(), 0
    for idx, v in enumerate(cand + flow):
        r = _rat_dir(v, den)
        key = tuple(r)
        if key not in seen and any(x != 0 for x in r):
            seen.add(key)
            out.append(r)
            n_modal += idx < len(cand)
    return modal, out, n_modal


# --- numeric search -----------------------------------------------------------------------------

def _row_lp(Hn: np.ndarray, target: np.ndarray, i: int, h: np.ndarray, cap=None):
    """`min Σⱼ Mᵢⱼ hⱼ s.t. Mᵢ H = target, Mᵢⱼ ≥ 0 (j ≠ i)` (entries bounded by `cap` if
    given); returns the row, or None if infeasible/unbounded."""
    from scipy.optimize import linprog

    k = Hn.shape[0]
    bounds = [(0, cap)] * k
    bounds[i] = (None if cap is None else -cap, cap)
    r = linprog(h, A_eq=Hn.T, b_eq=target, bounds=bounds, method="highs")
    if r.status != 0:
        return None
    return r.x


def _row_lps(Hn, An, h, cap=None):
    k = Hn.shape[0]
    HA = Hn @ An
    M = np.zeros((k, k))
    for i in range(k):
        r = _row_lp(Hn, HA[i], i, h, cap)
        if r is None:
            return None
        M[i] = r
    return M


def _support(Hn: np.ndarray, h: np.ndarray, dirs: np.ndarray) -> np.ndarray:
    from scipy.optimize import linprog

    n = Hn.shape[1]
    out = []
    for d in dirs:
        r = linprog(-d, A_ub=Hn, b_ub=h, bounds=[(None, None)] * n, method="highs")
        out.append(np.inf if r.status != 0 else -r.fun)
    return np.array(out)


def _start_offsets(Hn, An, h_fixed, cap, rel=1e-3):
    """Offsets for a polytope whose first `len(h_fixed)` rows are a contractive polytope
    (`h_fixed`) and whose other rows start redundant: their offset is the support of the
    first rows plus a slack, grown until every row LP value is negative (so the starting `M`
    is Metzler-Hurwitz)."""
    k0 = len(h_fixed)
    sup = _support(Hn[:k0], h_fixed, Hn[k0:])
    slack = np.full(len(sup), rel * float(np.max(np.abs(h_fixed))))
    for _ in range(40):
        h = np.concatenate([h_fixed, sup + slack])
        M = _row_lps(Hn, An, h, cap)
        if M is None:
            return None
        bad = (M @ h)[k0:] >= 0
        if not np.any(bad):
            return h
        slack[bad] *= 4
    return None


def _policy_iteration(Hn, An, cvec, h0, cap, iters=100, verbose=None, deadline=None):
    """Howard's policy iteration for the least offsets: `M ← row LPs(h)`, `h ← -M⁻¹ c`.
    `M h ≤ M_prev h = -c < 0` keeps every `M` Metzler-Hurwitz and `h` decreasing."""
    M = _row_lps(Hn, An, h0, cap)
    if M is None or np.any(M @ h0 >= 0):
        return None
    h = None
    for it in range(iters):
        try:
            hn = -np.linalg.solve(M, cvec)
        except np.linalg.LinAlgError:
            return None
        if not np.all(np.isfinite(hn)):
            return None
        if h is not None and np.max(np.abs(hn - h) / np.maximum(np.abs(h), 1e-12)) < 1e-9:
            h = hn
            break
        h = hn
        if deadline is not None and time.time() > deadline:
            break
        if verbose:
            verbose(f"  policy iteration {it}: h range [{h.min():.4g}, {h.max():.4g}]")
        Mn = _row_lps(Hn, An, h, cap)
        if Mn is None:
            break
        M = Mn
    return M, h


def _refine(Hn, M, h, rows):
    """New normals: bisectors of the facets the output bounds are most sensitive to.

    With `h = -M⁻¹ c` and a dual `λ` for output `c` (`b = λᵀh`), `y = -M⁻ᵀλ ≥ 0` is the
    sensitivity of `b` to the face losses; the faces with the largest `y` get bisected with
    their neighbours (the facets in the support of their row of `M`)."""
    from scipy.optimize import linprog

    k = Hn.shape[0]
    score = np.zeros(k)
    for c in rows:
        for s in (1, -1):
            r = linprog(h, A_eq=Hn.T, b_eq=s * c, bounds=[(0, None)] * k, method="highs")
            if r.status != 0:
                continue
            try:
                y = -np.linalg.solve(M.T, r.x)
            except np.linalg.LinAlgError:
                continue
            score += np.maximum(y, 0) / max(1e-12, r.fun)
    unit = Hn / np.linalg.norm(Hn, axis=1, keepdims=True)
    top = [i for i in np.argsort(-score) if score[i] > 0]
    out = []
    # bisectors first, then (if those already exist) the quarter points
    for wts in ((1.0, 1.0), (1.0, 0.5), (0.5, 1.0)):
        for i in top:
            for j in np.nonzero(M[i] > 1e-9)[0]:
                if j == i:
                    continue
                v = wts[0] * unit[i] + wts[1] * unit[j]
                if np.linalg.norm(v) > 1e-9:
                    out += [v, -v]
    return out


# --- exact rounding -----------------------------------------------------------------------------

def _solve_exact(rowsT: list[list[Fraction]], rhs: list[Fraction]):
    """Solve the square system `X u = rhs` exactly (Gauss–Jordan), or None if singular."""
    n = len(rhs)
    Mx = [list(r) + [b] for r, b in zip(rowsT, rhs)]
    for col in range(n):
        piv = next((r for r in range(col, n) if Mx[r][col] != 0), None)
        if piv is None:
            return None
        Mx[col], Mx[piv] = Mx[piv], Mx[col]
        p = Mx[col][col]
        Mx[col] = [v / p for v in Mx[col]]
        for r in range(n):
            if r != col and Mx[r][col] != 0:
                f = Mx[r][col]
                Mx[r] = [a - f * b for a, b in zip(Mx[r], Mx[col])]
    return [Mx[r][n] for r in range(n)]


def _exact_combination(H: Mat, target: Vec, weights: np.ndarray, free: int | None,
                       den: int = 10**9):
    """Exact `l` with `l H = target`, `l ≥ 0` off index `free`, near the numeric `weights`.

    `n` independent rows of the numeric support (largest weights first) form a basis solved
    exactly; the remaining support entries are rounded. None if rounding breaks a sign."""
    k, n = len(H), len(H[0])
    Hn = np.array([[float(v) for v in r] for r in H])
    support = [j for j in sorted(range(k), key=lambda j: -abs(weights[j]))
               if abs(weights[j]) > 1e-12]
    basis: list[int] = []
    for j in support + [j for j in range(k) if j not in support]:
        cand = basis + [j]
        if np.linalg.matrix_rank(Hn[cand], tol=1e-10) == len(cand):
            basis = cand
        if len(basis) == n:
            break
    if len(basis) < n:
        return None
    l = [Fraction(0)] * k
    for j in support:
        if j not in basis:
            l[j] = Fraction(float(weights[j])).limit_denominator(den)
            if j != free and l[j] < 0:
                l[j] = Fraction(0)
    rhs = [target[c] - sum((l[j] * H[j][c] for j in support if j not in basis), Fraction(0))
           for c in range(n)]
    sol = _solve_exact([[H[j][c] for j in basis] for c in range(n)], rhs)
    if sol is None:
        return None
    for j, v in zip(basis, sol):
        l[j] = v
    if any(l[j] < 0 for j in range(k) if j != free):
        return None
    return l


def _round_up(x: float, den: int) -> Fraction:
    return Fraction(math.ceil(x * den), den)


def _nice_upper(v: Fraction, rel: float = 1e-6) -> Fraction:
    """A short rational ≥ v within a relative `rel` (for readable bounds)."""
    target = float(v) * (1 + rel) + 1e-15
    for den in (10**k for k in range(2, 16)):
        cand = Fraction(math.ceil(float(v) * den), den)
        while cand < v:
            cand += Fraction(1, den)
        if float(cand) <= target:
            return cand
    return v


# --- driver -------------------------------------------------------------------------------------

def certify(A: Mat, B: Mat, deltas, x0: Vec | None = None, output_rows=None, facets: int = 96,
            den: int = 1000, eps: float = 1e-4, polygon: int = 12, horizon: float = 1.0,
            strategy: str = "adaptive", time_limit: float | None = None, verbose=None) -> PolyhedralCertificate | None:
    """Search for an exact polyhedral RPI certificate with about `facets` facets.

    `eps` is the strict margin relative to the disturbance scale, `den` bounds the
    denominators of the facet normals, `polygon` the minimum polygon size per complex mode,
    `horizon` the flow-image span in slowest time constants. `strategy` is "adaptive"
    (start from the modal polytope and ±outputs, then repeatedly bisect the facets the bounds
    are most sensitive to) or "flow" (modal + flow images `c e^{At}`, one shot).
    `time_limit` (seconds) stops the refinement early and abandons the search (None) if the
    numeric phase overruns it. Returns None on failure.
    """
    t0 = time.time()

    deadline = None if time_limit is None else t0 + time_limit

    def fail(msg):
        if verbose:
            verbose(f"polyhedral: {msg}")
        return None

    n = len(A)
    A = exact.to_mat(A)
    B = exact.to_mat(B)
    delta = [Fraction(d) for d in deltas]
    x0 = [Fraction(v) for v in (x0 or [0] * n)]
    rows = [[Fraction(v) for v in r] for r in (output_rows or [])]
    An = np.array([[float(v) for v in r] for r in A])
    Bn = np.array([[float(v) for v in r] for r in B])
    if np.max(np.linalg.eigvals(An).real) >= 0:
        return fail("A is not Hurwitz")
    rows_n = [np.array([float(v) for v in r]) for r in rows]
    dn = np.array([float(d) for d in delta])
    cap = 1e4 * (1 + np.max(np.abs(An)))
    # rational normals; refine their denominators until the rounded modal polytope is
    # still contractive (ill-conditioned eigenvectors need finer rounding)
    for den_try in (den, den * 100, den * 10**4):
        dirs = directions(An, rows_n, 0 if strategy == "adaptive" else facets, den_try,
                          polygon, horizon)
        if dirs is None:
            return fail("no contractive modal polytope (defective A or a lightly damped mode)")
        modal, H, n_modal = dirs
        Hm = np.array([[float(v) for v in r] for r in H[:n_modal]])
        hm = _support(np.array(modal), np.ones(len(modal)), Hm)
        Mm = _row_lps(Hm, An, hm, cap)
        if Mm is not None and np.all(Mm @ hm < 0):
            den = den_try
            break
    else:
        return fail("the rounded modal polytope is not contractive")
    # ±c exactly (the rationalized directions are rescaled copies; keep the exact rows too)
    for c in rows:
        for s in (1, -1):
            r = [s * v for v in c]
            if r not in H:
                H.append(r)
    Hn = np.array([[float(v) for v in r] for r in H])
    scale = max(1e-9, float(np.max(np.abs(Hn @ Bn) @ dn)))
    # start: the modal polytope (offsets 1), with every other normal redundant
    h0 = _start_offsets(Hn, An, hm, cap)
    if h0 is None:
        return fail("the rounded modal polytope is not contractive")
    rounds, last = 0, None
    while True:
        cvec = np.abs(Hn @ Bn) @ dn + 2 * eps * scale
        res = None if h0 is None else _policy_iteration(Hn, An, cvec, h0, cap, verbose=verbose,
                                                          deadline=deadline)
        if res is None:
            if last is None:
                return fail(f"policy iteration failed ({len(H)} facets)")
            if verbose:
                verbose(f"polyhedral: refinement to {len(H)} facets failed numerically; "
                        f"keeping {len(last[0])}")
            H, Hn, Mcur, hf = last
            break
        Mcur, hf = res
        last = (list(H), Hn, Mcur, hf)
        rounds += 1
        if strategy != "adaptive" or len(H) >= facets or \
                (deadline is not None and time.time() > deadline):
            break
        new = _refine(Hn, Mcur, hf, rows_n)
        added = 0
        hnew = list(hf)
        want = max(4, min(facets - len(H), len(H) // 3))
        for v in new:
            if added >= want:
                break
            r = _rat_dir(v, den)
            if r in H or not any(x != 0 for x in r):
                continue
            H.append(r)
            added += 1
        if not added:
            break
        Hn = np.array([[float(v) for v in r] for r in H])
        h0 = _start_offsets(Hn, An, np.array(hnew), cap)
        if verbose:
            verbose(f"  refinement round {rounds}: {len(H)} facets")
    # drop redundant normals (faces that never become active), then re-solve the row LPs
    # without the cap, so every row has an exact LP basis
    for _ in range(5):
        keep, Mf = [], np.zeros((len(H), len(H)))
        HA_n = Hn @ An
        for i in range(len(H)):
            r = _row_lp(Hn, HA_n[i], i, hf)
            if r is not None:
                keep.append(i)
                Mf[i] = r
        if len(keep) == len(H):
            break
        H = [H[i] for i in keep]
        Hn, hf = Hn[keep], hf[keep]
    else:
        return fail("could not remove redundant facets")
    if np.any(Mf @ hf + np.abs(Hn @ Bn) @ dn >= 0):
        return fail("numeric margin lost after removing redundant facets")
    k = len(H)
    t_num = time.time() - t0
    if deadline is not None and time.time() > deadline + time_limit:
        return fail(f"time limit {time_limit}s exceeded")
    # exact M: each row on its LP basis
    HA = exact.matmul(H, A)
    M: Mat = []
    for i in range(k):
        row = _exact_combination(H, HA[i], Mf[i], free=i)
        if row is None:
            return fail(f"exact rounding of row {i} of M failed")
        M.append(row)
    # offsets for this exact M, with a strict margin of ~eps, containing x0
    Mn = np.array([[float(v) for v in r] for r in M])
    h_num = -np.linalg.solve(Mn, np.abs(Hn @ Bn) @ dn + eps * scale * 1.5)
    g = -np.linalg.solve(Mn, np.ones(k))           # ≥ 0: an inflation direction
    Hx0 = Hn @ np.array([float(v) for v in x0])
    beta = max(0.0, float(np.max((Hx0 - h_num) / g)))
    if beta > 0:
        h_num = h_num + (beta * (1 + 1e-6) + 1e-9) * g
    # rounding h up by ≤ 1/hden moves M h by ≤ ‖M‖∞/hden: keep that below a tenth of the margin
    mnorm = float(np.max(np.sum(np.abs(Mn), axis=1)))
    hden = 10 ** max(6, math.ceil(math.log10(10 * mnorm / (eps * scale))))
    h = [_round_up(v, hden) for v in h_num]
    marg = margin(H, h, M, A, B, delta)
    if any(v >= 0 for v in marg) or any(a > b for a, b in zip(exact.matvec(H, x0), h)):
        return fail("exact margin or initial containment failed after rounding h")
    # output bounds by LP duality
    from scipy.optimize import linprog
    hfl = np.array([float(v) for v in h])
    outs = []
    for c in rows:
        ls = []
        for s in (1, -1):
            tgt = [s * v for v in c]
            r = linprog(hfl, A_eq=Hn.T, b_eq=np.array([float(v) for v in tgt]),
                        bounds=[(0, None)] * k, method="highs")
            l = None if r.status != 0 else _exact_combination(H, tgt, r.x, free=None)
            if l is None:  # the facet ±c itself
                l = [Fraction(int(H[j] == tgt)) for j in range(k)]
            ls.append(l)
        b = _nice_upper(max(exact.dot(ls[0], h), exact.dot(ls[1], h)))
        outs.append(OutputBound(c, ls[0], ls[1], b))
    cert = PolyhedralCertificate(H, h, M, delta, outs, {
        "facets": k, "numeric_s": round(t_num, 3), "total_s": round(time.time() - t0, 3),
        "margin_max": float(max(marg)),
    })
    errs = cert.check(A, B, x0)
    if errs:
        raise AssertionError(f"internal: exact re-check failed: {errs}")
    return cert
