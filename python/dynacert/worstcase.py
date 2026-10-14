"""Adjoint worst-case search: gradients of an output peak with respect to the disturbance.

To make `±y(t*)` as large as possible over disturbances `|w_j(t)| ≤ δ_j`, linearize along a
trajectory:

    δy(t*) = ∫₀^{t*} σ(s)ᵀ δw(s) ds  (+ ∂g/∂w · δw(t*) for feedthrough),
    σ(s) = B_w(s)ᵀ λ(s),   λ̇ = −A(s)ᵀ λ,   λ(t*) = ∇ₓ g(x(t*), u(t*)),

with `A = ∂f/∂x`, `B_w = ∂f/∂w` along the trajectory. The first-order optimum is bang-bang,
`w_j = δ_j sign σ_j` (Pontryagin), switching where the switching function `σ_j` crosses zero.

The search runs in stages:

1. **scan:** from a base trajectory, one adjoint pass per candidate peak time `t*` and sign,
   with levels set per grid segment to the sign of `∫_segment σ`. For a linear model `A` and
   `B_w` do not depend on the trajectory, so this is the exact worst case on the grid.
2. **refine:** repeat along the best trajectory, with `t*` moved to its current peak, until the
   peak stops growing (local optimum for nonlinear models).
3. **switch:** put the switches at the zero crossings of `σ` (linear interpolation on the
   integration grid) instead of on segment boundaries, and iterate the same way. This removes the
   grid restriction; for a linear model it is the exact continuous-time worst case for `t*`.
4. **multistart:** stages 2–3 from extra starting scenarios (e.g. the worst Monte Carlo runs),
   to escape local optima of nonlinear models.

Jacobians are symbolic derivatives of rumoca's sympy export, the same DAE as the Lean
specification. Untrusted: the result is an achieved scenario, a lower bound on the worst case.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field

import numpy as np
import sympy as sp

from . import analysis as an
from .montecarlo import Scenario, ScenarioSpace, SympyBackend


@dataclass
class Explicit:
    """The model as an explicit ODE `ẋ = f(x, u)` with outputs `y = g(x, u)`, at fixed parameters."""
    xs: list                   # state symbols (model order)
    us: list                   # input symbols (model order)
    ws: list                   # disturbance symbols (spec order)
    f: sp.Matrix
    g: dict                    # output -> expression


def explicit(model, spec, theta: tuple) -> Explicit:
    """Eliminate algebraics from rumoca's sympy export with uncertain parameters at `theta`."""
    unc = {u.name: v for u, v in zip(spec.uncertain, theta)}
    vals = model.param_values(keep=unc)
    vals.update({model.var(n).symbol: sp.Rational(t) for n, t in unc.items()})
    res = an.substitute_params(model.equations_flat(), vals)
    ders = [model.der[v.name] for v in model.states]
    ex = an.eliminate(res, ders, [v.symbol for v in model.algebraics])
    g = {}
    for name in spec.certify:
        v = model.var(name)
        g[name] = v.symbol if v.role == "state" else ex.alg[v.symbol]
    return Explicit([v.symbol for v in model.states], [v.symbol for v in model.inputs],
                    [model.var(d.name).symbol for d in spec.disturbances],
                    sp.Matrix([ex.der[d] for d in ders]), g)


def nominal_theta(model, spec) -> tuple:
    vals = model.param_values()
    return tuple(float(vals[model.var(u.name).symbol]) for u in spec.uncertain)


@dataclass
class _Compiled:
    A: object                  # (x, u) -> ∂f/∂x
    Bw: object                 # (x, u) -> ∂f/∂w
    gx: dict                   # output -> (x, u) -> ∇ₓ g
    gw: dict                   # output -> (x, u) -> ∂g/∂w


@dataclass
class AdjointResult:
    output: str
    value: float               # peak |output| of the best scenario (sympy RK4)
    scenario: Scenario
    tstar: float               # time of the peak
    stage: str                 # stage that produced it: scan, refine, switch, multistart
    candidates: list = field(default_factory=list)   # (stage, value, scenario): best per stage
    simulations: int = 0


class Adjoint:
    def __init__(self, model, spec, space: ScenarioSpace, dt: float | None = None):
        self.model, self.spec, self.space = model, spec, space
        self.fwd = SympyBackend(model, spec, space, dt)
        self.dt = self.fwd.dt
        self._cache = {}
        self.sims = 0

    def applicable(self) -> str | None:
        """None if gradients can be formed, else why not."""
        if not self.spec.disturbances:
            return "no disturbance inputs to optimize"
        try:
            self._compile(nominal_theta(self.model, self.spec))
        except (ValueError, TypeError, NotImplementedError, KeyError) as e:
            return f"cannot form an explicit ODE with derivatives: {e}"
        return None

    def _compile(self, theta: tuple) -> _Compiled:
        theta = tuple(float(v) for v in theta)
        if theta in self._cache:
            return self._cache[theta]
        e = explicit(self.model, self.spec, theta)
        lam = lambda ex: sp.lambdify([e.xs, e.us], ex, "numpy")  # noqa: E731
        gx = {n: lam(sp.Matrix([g]).jacobian(e.xs)) for n, g in e.g.items()}
        gw = {n: lam(sp.Matrix([g]).jacobian(e.ws)) for n, g in e.g.items()}
        c = _Compiled(lam(e.f.jacobian(e.xs)), lam(e.f.jacobian(e.ws)), gx, gw)
        self._cache[theta] = c
        return c

    def _theta(self, scn: Scenario) -> tuple:
        return tuple(scn.theta[u.name] for u in self.spec.uncertain)

    # --- forward and adjoint ----------------------------------------------------------------
    def _forward(self, scn: Scenario):
        self.sims += 1
        return self.fwd.run(scn)

    def _arrays(self, run):
        X = np.column_stack([run.states[v.name] for v in self.model.states])
        U = np.column_stack([run.inputs[v.name] for v in self.model.inputs])
        return X, U

    def adjoint(self, comp: _Compiled, run, output: str, istar: int, sign: float):
        """Backward pass from `t* = ts[istar]` for `sign · y(t*)`. Returns the switching
        function `σ` on `ts[:istar+1]` (shape (istar+1, disturbances), scaled by the bounds) and
        the feedthrough gradient `∂(sign·g)/∂w` at `t*`."""
        X, U = self._arrays(run)
        ts = run.t
        bounds = np.array([b for _, b in self.space.dists])
        nd = len(bounds)
        sigma = np.zeros((istar + 1, nd))
        lam = sign * np.asarray(comp.gx[output](X[istar], U[istar]), float).reshape(-1)
        gw = sign * np.asarray(comp.gw[output](X[istar], U[istar]), float).reshape(-1)
        sigma[istar] = lam @ np.asarray(comp.Bw(X[istar], U[istar]), float)
        A_next = np.asarray(comp.A(X[istar], U[istar]), float)
        for i in range(istar - 1, -1, -1):          # Heun (trapezoid) backward in time
            dt = ts[i + 1] - ts[i]
            Ai = np.asarray(comp.A(X[i], U[i]), float)
            pred = lam + dt * A_next.T @ lam
            lam = lam + 0.5 * dt * (A_next.T @ lam + Ai.T @ pred)
            A_next = Ai
            sigma[i] = lam @ np.asarray(comp.Bw(X[i], U[i]), float)
        return sigma * bounds, gw * bounds

    def _grid_step(self, scn: Scenario, sigma, gw, ts, istar: int) -> Scenario:
        """Levels up to the segment of t* set to the sign of `∫_segment σ` (trapezoid)."""
        sp_ = self.space
        K, h = sp_.dist.segments, sp_.h
        last = min(int(ts[istar] / h), K - 1)
        seg = np.minimum((ts[:istar] / h).astype(int), K - 1)
        base = sp_.regrid(scn)
        levels = {}
        for j, (n, _) in enumerate(sp_.dists):
            G = np.zeros(K)
            np.add.at(G, seg, 0.5 * (sigma[:istar, j] + sigma[1:istar + 1, j]) * np.diff(ts[:istar + 1]))
            G[last] += gw[j]
            lv = base.levels[n].copy()
            g = G[:last + 1]
            lv[:last + 1] = np.where(g > 0, 1.0, np.where(g < 0, -1.0, lv[:last + 1]))
            levels[n] = lv
        return Scenario(dict(scn.theta), levels, {k: v.copy() for k, v in scn.refs.items()})

    def _switch_step(self, scn: Scenario, sigma, gw, ts, istar: int) -> Scenario | None:
        """Bang-bang with switches at the zero crossings of `σ` before t*; after t*, the sign of
        the feedthrough (or the last level). None if there are more pieces than the grid holds."""
        sp_ = self.space
        K, T, tstar = sp_.dist.segments, sp_.T, ts[istar]
        levels, edges = {}, {}
        for j, (n, _) in enumerate(sp_.dists):
            sg = sigma[:istar + 1, j]
            sgn = np.sign(sg)
            for i in range(1, len(sgn)):            # carry the sign through exact zeros
                if sgn[i] == 0:
                    sgn[i] = sgn[i - 1]
            nz = np.flatnonzero(sgn)
            if len(nz) == 0:
                return None
            sgn[:nz[0]] = sgn[nz[0]]
            cross = np.flatnonzero(sgn[:-1] != sgn[1:])
            times = [ts[i] + (ts[i + 1] - ts[i]) * sg[i] / (sg[i] - sg[i + 1]) for i in cross]
            lv = [sgn[0]] + [sgn[i + 1] for i in cross]
            after = np.sign(gw[j]) or lv[-1]
            e = times + [tstar]
            lv = lv + [after]
            if len(lv) > K:
                return None
            pad = K - len(lv)
            levels[n] = np.array(lv + [after] * pad, float)
            edges[n] = np.array(e + [T] * pad, float)
        return Scenario(dict(scn.theta), levels, {k: v.copy() for k, v in scn.refs.items()}, edges)

    def switching_function(self, scn: Scenario, output: str):
        """`(t, σ, t*)` along `scn` for its own peak of `|output|`: `σ[:, j]` is the sensitivity
        of the peak to disturbance `j` at time `t` (scaled by the bound). A bang-bang optimum has
        `w_j = δ_j sign σ_j` wherever `σ_j ≠ 0`."""
        run = self._forward(scn)
        v, i, s = self._peak(run, output)
        sigma, _ = self.adjoint(self._compile(self._theta(scn)), run, output, i, s)
        return run.t[:i + 1], sigma, float(run.t[i])

    # --- search -----------------------------------------------------------------------------
    def thetas(self, max_corners: int = 16) -> list[tuple]:
        """Uncertain-parameter corners (all of them if there are at most `max_corners`)."""
        us = self.spec.uncertain
        if not us:
            return [()]
        if 2 ** len(us) > max_corners:
            return [nominal_theta(self.model, self.spec)]
        return list(itertools.product(*[(float(u.lo), float(u.hi)) for u in us]))

    @staticmethod
    def _peak(run, output):
        y = run.outputs[output]
        i = int(np.argmax(np.abs(y)))
        return float(abs(y[i])), i, float(np.sign(y[i]) or 1.0)

    def _iterate(self, output, scn, run, step: str, iters: int):
        """Repeat a step along its own peak until the peak stops growing."""
        v, i, s = self._peak(run, output)
        comp = self._compile(self._theta(scn))
        for _ in range(iters):
            sigma, gw = self.adjoint(comp, run, output, i, s)
            new = (self._switch_step if step == "switch" else self._grid_step)(
                scn, sigma, gw, run.t, i)
            if new is None:
                break
            run2 = self._forward(new)
            v2, i2, s2 = self._peak(run2, output)
            if v2 <= v * (1 + 1e-9):
                break
            v, scn, run, i, s = v2, new, run2, i2, s2
        return v, scn, run

    def search(self, output: str, *, tstars: int = 10, iters: int = 10,
               starts: list | None = None, refs: dict | None = None, max_corners: int = 16,
               verbose=None) -> AdjointResult:
        """Worst case of `|output|` (see the module docstring for the stages)."""
        sp_ = self.space
        K = sp_.dist.segments
        refs = refs or {n: np.zeros((sp_.dist.harmonics, 3)) for n in sp_.free}
        self.sims = 0
        best = {}                                          # stage -> (value, scenario, run)

        def keep(stage, v, scn, run):
            if stage not in best or v > best[stage][0]:
                best[stage] = (v, scn, run)

        # 1. scan
        for theta in self.thetas(max_corners):
            comp = self._compile(theta)
            th = {u.name: v for u, v in zip(self.spec.uncertain, theta)}
            base = Scenario(th, {n: np.zeros(K) for n, _ in sp_.dists}, refs)
            run0 = self._forward(base)
            ts = run0.t
            cands = np.unique(np.linspace(0, len(ts) - 1, tstars + 1)[1:].round().astype(int))
            for istar in cands:
                for sign in (1.0, -1.0):
                    sigma, gw = self.adjoint(comp, run0, output, int(istar), sign)
                    scn = self._grid_step(base, sigma, gw, ts, int(istar))
                    run = self._forward(scn)
                    keep("scan", self._peak(run, output)[0], scn, run)
        if verbose:
            verbose(f"  adjoint scan: {best['scan'][0]:.6g}")
        # 2-3. refine on the grid, then move the switches
        v, scn, run = self._iterate(output, best["scan"][1], best["scan"][2], "grid", iters)
        keep("refine", v, scn, run)
        v, scn, run = self._iterate(output, scn, run, "switch", iters)
        keep("switch", v, scn, run)
        if verbose:
            verbose(f"  adjoint refine: {best['refine'][0]:.6g}, switching times: "
                    f"{best['switch'][0]:.6g}")
        # 4. multistart
        for s0 in starts or []:
            r0 = self._forward(s0)
            v, scn, run = self._iterate(output, s0, r0, "grid", iters)
            v, scn, run = self._iterate(output, scn, run, "switch", iters)
            keep("multistart", v, scn, run)
        if starts and verbose:
            verbose(f"  adjoint multistart ({len(starts)} starts): {best['multistart'][0]:.6g}")
        stage = max(best, key=lambda k: best[k][0])
        v, scn, run = best[stage]
        tstar = float(run.t[self._peak(run, output)[1]])
        return AdjointResult(output, v, scn, tstar, stage,
                             [(k, b[0], b[1]) for k, b in best.items()], self.sims)
