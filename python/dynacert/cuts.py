"""Where to tear: coupling graph, cut screening (Proposition 2), and the distributed solve.

The paper's Section VI–VIII, untrusted:

* `coupling_graph`: an edge `j → i` when `ẋᵢ` depends on `xⱼ`. It is *strong* when the exact
  linear part has `Aᵢⱼ ≠ 0` (a first-order coupling) and *weak* when the dependence enters only
  through a residual channel (second order).
* `candidates`: strongly connected components of the strong-edge graph are the proposed blocks
  (tear across weak couplings, keep strong ones inside a block); for comparison every
  bipartition that cuts few strong edges is screened too.
* `screen` (**Proposition 2**): if no block-diagonal `P ≻ 0` gives `AᵀP + PA ≺ 0` on the
  linearization, no static quadratic supply rate certifies a tube across that cut, at any
  disturbance level; one small LMI rejects the cut before any nonlinear analysis.
* `admm`: consensus ADMM over the interface scalars (supply rates and budget shares): each block
  solves its own LMI (9) with a proximal term, a coordinator projects onto
  `{Σ σ_received ≤ σ_sent, Σ budgets ≤ 1}`, and the scaled duals are updated. The certificate
  it finds is checked by the Lean kernel like any other.
"""

from __future__ import annotations

import itertools
import time
from dataclasses import dataclass, field

import numpy as np

from . import sector as S


@dataclass
class Graph:
    states: list
    strong: set          # (j, i): ẋ_i depends on x_j through A
    weak: set            # (j, i): only through a residual channel


def _channel_states(sp_: S.SectorProblem, ch) -> set:
    """States a residual channel depends on (through its atoms and linear variables)."""
    import sympy as sp

    deps = set()
    syms = {v: k for k, v in enumerate(sp_.states)}
    e = sp.sympify(ch.expr)
    for s_ in e.free_symbols:
        name = s_.name
        if name in syms:
            deps.add(syms[name])
        elif name in sp_.lin_alg:
            deps |= {i for i, c in enumerate(sp_.lin_alg[name]) if c != 0}
        else:   # nonlinear algebraic: its atom's arguments
            for a in sp_.atoms:
                if a.alg == name:
                    for i, _, _ in a.args.values():
                        deps |= {k for k, c in enumerate(sp_.coords[i].row) if c != 0}
    return deps


def coupling_graph(sp_: S.SectorProblem) -> Graph:
    n = sp_.n
    strong = {(j, i) for i in range(n) for j in range(n) if i != j and sp_.A[i][j] != 0}
    weak = set()
    for ch in sp_.channels:
        deps = _channel_states(sp_, ch)
        for i in ch.col:
            for j in deps:
                if j != i and (j, i) not in strong:
                    weak.add((j, i))
    return Graph(list(sp_.states), strong, weak)


def sccs(n: int, edges: set) -> list[list[int]]:
    """Strongly connected components (Kosaraju), in a deterministic order."""
    adj = {i: sorted(j for (a, j) in edges if a == i) for i in range(n)}
    radj = {i: sorted(a for (a, j) in edges if j == i) for i in range(n)}
    seen, order = set(), []

    def dfs(v):
        stack = [(v, iter(adj[v]))]
        seen.add(v)
        while stack:
            u, it = stack[-1]
            for w in it:
                if w not in seen:
                    seen.add(w)
                    stack.append((w, iter(adj[w])))
                    break
            else:
                order.append(u)
                stack.pop()

    for v in range(n):
        if v not in seen:
            dfs(v)
    comp, out = {}, []
    for v in reversed(order):
        if v in comp:
            continue
        cur, stack = [], [v]
        comp[v] = len(out)
        while stack:
            u = stack.pop()
            cur.append(u)
            for w in radj[u]:
                if w not in comp:
                    comp[w] = len(out)
                    stack.append(w)
        out.append(sorted(cur))
    return sorted(out, key=lambda c: c[0])


def cut_weight(g: Graph, parts) -> tuple[int, int]:
    owner = {i: b for b, p in enumerate(parts) for i in p}
    s = sum(1 for (j, i) in g.strong if owner[i] != owner[j])
    w = sum(1 for (j, i) in g.weak if owner[i] != owner[j])
    return s, w


def screen(sp_: S.SectorProblem, parts, margin=1e-6) -> bool:
    """Proposition 2: is there a block-diagonal `P ≻ 0` with `AᵀP + PA ≺ 0`?"""
    import cvxpy as cp

    n = sp_.n
    A = np.array([[float(v) for v in r] for r in sp_.A])
    blocks = [cp.Variable((len(p), len(p)), symmetric=True) for p in parts]
    P = cp.Constant(np.zeros((n, n)))
    for p, Pb in zip(parts, blocks):
        E = np.zeros((n, len(p)))
        for k, i in enumerate(p):
            E[i, k] = 1.0
        P = P + E @ Pb @ E.T
    cons = [Pb >> np.eye(Pb.shape[0]) for Pb in blocks]
    cons.append(A.T @ P + P @ A << -margin * np.eye(n))
    prob = cp.Problem(cp.Minimize(0), cons)
    try:
        prob.solve(solver=cp.CLARABEL)
    except Exception:  # noqa: BLE001
        return False
    return prob.status in ("optimal", "optimal_inaccurate")


@dataclass
class Candidate:
    parts: list
    source: str             # "scc" (proposed) | "bipartition" (screened for comparison)
    strong_cut: int
    weak_cut: int
    feasible: bool | None = None

    def label(self, names) -> str:
        return " | ".join(",".join(names[i] for i in p) for p in self.parts)


def candidates(sp_: S.SectorProblem, max_strong: int = 3, screen_all: bool = True):
    """The proposed cut (SCCs of the strong graph) and, for comparison, every bipartition that
    cuts at most `max_strong` strong edges (state pairs); each screened with Proposition 2."""
    g = coupling_graph(sp_)
    n = sp_.n
    out = []
    comps = sccs(n, g.strong)
    if len(comps) > 1:
        s, w = cut_weight(g, comps)
        out.append(Candidate(comps, "scc", s, w))
    if screen_all and n <= 12:
        for mask in range(1, 2 ** (n - 1)):
            a = [i for i in range(n) if mask >> i & 1]
            b = [i for i in range(n) if not mask >> i & 1]
            parts = sorted([a, b], key=lambda p: p[0])
            if any(sorted(map(tuple, c.parts)) == sorted(map(tuple, parts)) for c in out):
                continue
            s, w = cut_weight(g, parts)
            if s <= max_strong:
                out.append(Candidate(parts, "bipartition", s, w))
    for c in out:
        c.feasible = screen(sp_, c.parts)
    out.sort(key=lambda c: (c.source != "scc", not c.feasible, c.strong_cut, c.weak_cut))
    return g, out


def choose(sp_: S.SectorProblem, cands) -> Candidate | None:
    """The automatic choice: the proposed (SCC) cut if Proposition 2 accepts it, else the
    accepted cut with the fewest strong (then weak) edges cut."""
    ok = [c for c in cands if c.feasible]
    if not ok:
        return None
    scc = [c for c in ok if c.source == "scc"]
    return scc[0] if scc else min(ok, key=lambda c: (c.strong_cut, c.weak_cut))


def parse_cut(sp_: S.SectorProblem, text: str) -> list[list[int]]:
    """`"e_x,v_x,theta,q | e_z,v_z"` -> state index blocks."""
    parts = []
    for blk in text.split("|"):
        names = [s.strip() for s in blk.split(",") if s.strip()]
        try:
            parts.append(sorted(sp_.states.index(nm) for nm in names))
        except ValueError as e:
            raise S.SectorError(f"unknown state in cut {text!r}: {e}") from e
    flat = sorted(i for p in parts for i in p)
    if flat != list(range(sp_.n)):
        raise S.SectorError(f"cut {text!r} is not a partition of the states {sp_.states}")
    return sorted(parts, key=lambda p: p[0])


# --- consensus ADMM ------------------------------------------------------------------------------

class _SumT:
    """The objective of the composed member: Σ over the blocks that own the direction."""

    def __init__(self, ts):
        self.value = sum(float(t.value) for t in ts if t is not None)


@dataclass
class AdmmResult:
    member: S.Member | None
    iterations: int
    seconds: float
    history: list = field(default_factory=list)     # (iteration, objective, residual)


def _project(ifaces, z_in, z_out, budgets):
    """Euclidean projection onto {Σ_receivers σ_in ≤ σ_out, σ ≥ 0, Σ budgets ≤ 1, ≥ 0}."""
    import cvxpy as cp

    vi = {k: cp.Variable(nonneg=True) for k in z_in}
    vo = {e: cp.Variable(nonneg=True) for e in z_out}
    vb = [cp.Variable(nonneg=True) for _ in budgets]
    cons = [sum(vb) <= 1]
    for e, I in enumerate(ifaces):
        cons.append(sum(vi[(r, e)] for r in I.receivers) <= vo[e])
    obj = sum(cp.square(vi[k] - z_in[k]) for k in z_in) + \
        sum(cp.square(vo[e] - z_out[e]) for e in z_out) + \
        sum(cp.square(vb[b] - budgets[b]) for b in range(len(budgets)))
    cp.Problem(cp.Minimize(obj), cons).solve(solver=cp.CLARABEL)
    return ({k: float(v.value) for k, v in vi.items()}, {e: float(v.value) for e, v in vo.items()},
            [float(v.value) for v in vb])


def admm(sp_: S.SectorProblem, parts, gains, betas, name, row, alpha, iters=80, rho=1.0,
         verbose=None, margin=1e-3) -> AdmmResult:
    """Consensus ADMM for one objective at a fixed α (paper §VI-C)."""
    t0 = time.time()
    blocks, ifaces = S.build_blocks(sp_, parts)
    B = len(blocks)
    z_in = {(r, e): 1.0 for e, I in enumerate(ifaces) for r in I.receivers}
    z_out = {e: 1.0 for e in range(len(ifaces))}
    z_b = [1.0 / B] * B
    u_in = {k: 0.0 for k in z_in}
    u_out = {e: 0.0 for e in z_out}
    u_b = [0.0] * B
    hist = []
    local = [None] * B
    # objective scale: each block owning the direction alone (full budget, free supply rates);
    # normalizing by it lets one penalty ρ suit every objective
    scale = 0.0
    for b, blk in enumerate(blocks):
        if not any(row[i] != 0 for i in blk.idx):
            continue
        pr0, v0 = S.lmi_blocks(sp_, blocks, ifaces, gains, betas, alpha, row, only=b,
                               margin=margin, budget_split=[1.0] * B)
        if S.solve(pr0) and v0["t"].value is not None:
            pr1, v1 = S.lmi_blocks(sp_, blocks, ifaces, gains, betas, alpha, row, only=b,
                                   margin=margin, budget_split=[1.0] * B,
                                   obj_scale=1.0 / max(float(v0["t"].value), 1e-12))
            scale += float(v1["t"].value) if S.solve(pr1) else float(v0["t"].value)
    scale = scale if scale > 0 else 1.0
    for it in range(iters):
        x_in, x_out, x_b = {}, {}, [0.0] * B
        obj = 0.0
        for b in range(B):
            prox = {"rho": rho, "scale": scale,
                    "sig_in": {k: z_in[k] - u_in[k] for k in z_in if k[0] == b},
                    "sig_out": {e: z_out[e] - u_out[e] for e in z_out if ifaces[e].sender == b},
                    "budget": z_b[b] - u_b[b]}
            prob, var = S.lmi_blocks(sp_, blocks, ifaces, gains, betas, alpha, row, only=b,
                                     prox=prox, margin=margin)
            if not S.solve(prob):
                return AdmmResult(None, it, time.time() - t0, hist)
            local[b] = var
            for k, v in var["sig_in"].items():
                x_in[k] = float(v.value)
            for e, v in var["sig_out"].items():
                x_out[e] = float(v.value)
            x_b[b] = float(var["budget"].value)
            obj += float(var["t"].value) if var["t"] is not None else 0.0
        z_in, z_out, z_b = _project(ifaces, {k: x_in[k] + u_in[k] for k in z_in},
                                    {e: x_out[e] + u_out[e] for e in z_out},
                                    [x_b[b] + u_b[b] for b in range(B)])
        r = 0.0
        for k in z_in:
            u_in[k] += x_in[k] - z_in[k]
            r = max(r, abs(x_in[k] - z_in[k]))
        for e in z_out:
            u_out[e] += x_out[e] - z_out[e]
            r = max(r, abs(x_out[e] - z_out[e]))
        for b in range(B):
            u_b[b] += x_b[b] - z_b[b]
            r = max(r, abs(x_b[b] - z_b[b]))
        hist.append((it, obj, r))
        if verbose and (it % 10 == 0 or it == iters - 1):
            verbose(f"    ADMM {name} iter {it}: objective {obj:.6g}, interconnection residual "
                    f"{r:.2e}")
    # a feasible point, block by block with the consensus supply rates fixed: blocks without
    # the objective take the smallest budget share they need, the rest goes to the others
    owners = [b for b, blk in enumerate(blocks)
              if any(row[i] != 0 for i in blk.idx)]
    split = [0.0] * B
    sub = {}
    for b in range(B):
        if b in owners:
            continue
        prob, var = S.lmi_blocks(sp_, blocks, ifaces, gains, betas, alpha, None, only=b,
                                 margin=margin, fixed_sigma=dict(z_out))
        if not S.solve(prob):
            return AdmmResult(None, iters, time.time() - t0, hist)
        split[b] = float(var["budget"].value) * (1 + 1e-6) + 1e-9
        sub[b] = var
    rest = 1.0 - sum(split)
    if rest <= 0:
        return AdmmResult(None, iters, time.time() - t0, hist)
    tot = sum(z_b[b] for b in owners) or 1.0
    for b in owners:
        split[b] = rest * z_b[b] / tot
    # the owners take the supply rates the other blocks actually used
    fixed = dict(z_out)
    for e, I in enumerate(ifaces):
        if I.sender in sub:
            fixed[e] = float(sub[I.sender]["sig_out"][e].value)
        elif all(r in sub for r in I.receivers):
            fixed[e] = sum(float(sub[r]["sig_in"][(r, e)].value) for r in I.receivers) \
                * (1 + 1e-9) + 1e-12
    for b in owners:
        prob, var = S.lmi_blocks(sp_, blocks, ifaces, gains, betas, alpha, row, only=b,
                                 margin=margin, fixed_sigma=fixed, budget_split=split,
                                 obj_scale=1.0 / scale)
        if not S.solve(prob):
            return AdmmResult(None, iters, time.time() - t0, hist)
        sub[b] = var
    var = {"P": [sub[b]["P"][b] for b in range(B)],
           "gamma": [sub[b]["gamma"][b] for b in range(B)],
           "tau": [sub[b]["tau"][b] for b in range(B)],
           "scale": [sub[b]["scale"][b] for b in range(B)],
           "blocks": blocks,
           "sig_in": {k: v for b in range(B) for k, v in sub[b]["sig_in"].items()},
           "sig_out": {e: v for b in range(B) for e, v in sub[b]["sig_out"].items()},
           "t": _SumT([sub[b]["t"] for b in owners])}
    mb = S._member(name, row, alpha, var)
    return AdmmResult(mb, iters, time.time() - t0, hist)


# --- loop tearing baseline (paper §IV): peak-to-peak small gain across a cut --------------------

def l1_gain(A, b, c, horizon=None, steps=20000) -> float:
    """∫₀^∞ |cᵀ e^{At} b| dt (the peak-to-peak gain of a SISO stable system), by quadrature on
    a horizon of 40 time constants (numerical, untrusted)."""
    from scipy.linalg import expm

    lam = np.linalg.eigvals(A)
    if np.max(lam.real) >= 0:
        return float("inf")
    T = horizon or 40.0 / min(-lam.real)
    dt = T / steps
    E = expm(A * dt)
    x = b.astype(float).copy()
    tot, prev = 0.0, abs(float(c @ x))
    for _ in range(steps):
        x = E @ x
        cur = abs(float(c @ x))
        tot += 0.5 * (prev + cur) * dt
        prev = cur
    return tot


@dataclass
class Tearing:
    parts: list
    signals: list           # (sender block, row) of each interface
    J: np.ndarray           # J[e, f]: peak-to-peak gain from signal f to signal e
    rho: float


def tearing(sp_: S.SectorProblem, parts) -> Tearing:
    """Linear part of the loop-torn bound map: each block treats the linear interface signals it
    receives as bounded disturbances and bounds the ones it sends by their exact peak-to-peak
    gains. The bound map is `F(b) ≥ c + J b`, so a certificate needs `ρ(J) < 1`
    (Collatz–Wielandt); with `ρ(J) ≥ 1` tearing fails at every disturbance level (§IV)."""
    blocks, ifaces = S.build_blocks(sp_, parts)
    k = len(ifaces)
    J = np.zeros((k, k))
    for e, I in enumerate(ifaces):
        sb = blocks[I.sender]
        cvec = np.array([float(I.row[i]) for i in sb.idx])
        for f, If in enumerate(ifaces):
            if I.sender not in If.receivers:
                continue
            pos = sb.signals.index(("iface", f))
            bcol = sb.B[:, pos]
            if not bcol.any():
                continue
            J[e, f] = l1_gain(sb.A, bcol, cvec)
    if not np.isfinite(J).all():
        rho = float("inf")       # a torn block is unstable on its own
    else:
        rho = float(max(abs(np.linalg.eigvals(J)))) if k else 0.0
    return Tearing(parts, [(I.sender, I.row) for I in ifaces], J, rho)
