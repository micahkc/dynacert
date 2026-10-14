"""Direct collocation worst-case search (CasADi + IPOPT) on rumoca's CasADi export.

For a peak time `t*` and sign `s`, solve

    maximize   s · y(t*)
    over       disturbance levels w_k ∈ [−δ, δ] on N intervals of [0, t*],
               uncertain parameters θ ∈ [lo, hi]
    subject to ẋ = f(t, x, u(w, t), θ) at Radau collocation points, x(0) = x₀,

with `f` the `rhs` CasADi function rumoca's `casadi-ode` export builds from its solve IR (an
independent path from the sympy export) and `y = g(x, u)` from the sympy export. Other inputs
(references) are taken from a seed trajectory. IPOPT finds a local optimum; warm-starting from
the adjoint result is the intended use, and parameters are optimized jointly, so interior
parameter worst cases that corner enumeration misses are reachable.

Untrusted: the solution is re-simulated before it is reported, as an achieved scenario.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

import numpy as np
import sympy as sp

from .montecarlo import Scenario, ScenarioSpace
from .worstcase import explicit, nominal_theta

_CASADI_FUNCS = ("sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "exp",
                 "log", "sqrt", "atan2")


def _casadi_module():
    import casadi as ca

    m = {f: getattr(ca, f) for f in _CASADI_FUNCS}
    m.update({"Abs": ca.fabs, "sign": ca.sign, "Min": ca.fmin, "Max": ca.fmax})
    return m


def _plain(name: str) -> str:
    """rumoca's export lists input names as JSON objects ({"name": ..., "dimensions": ...})."""
    if name.startswith("{"):
        return json.loads(name)["name"]
    return name


def available() -> str | None:
    """None if CasADi with IPOPT and the rumoca binding are importable, else why not."""
    try:
        import casadi as ca
    except ImportError:
        return "casadi is not installed"
    if not ca.has_nlpsol("ipopt"):
        return "casadi has no IPOPT"
    try:
        import rumoca  # noqa: F401
    except ImportError:
        return "rumoca Python binding not installed"
    return None


@dataclass
class CollocationResult:
    value: float               # s · y(t*) at the optimum (collocation model)
    scenario: Scenario
    tstar: float
    sign: float
    status: str                # IPOPT return status
    theta: dict


class Collocation:
    def __init__(self, model, spec, space: ScenarioSpace, source: Path, model_name: str,
                 degree: int = 3):
        import casadi as ca
        import rumoca

        self.ca, self.model, self.spec, self.space = ca, model, spec, space
        ex = rumoca.Session(roots=[str(Path(source).resolve())]).load(
            str(Path(source).resolve()), model=model_name).to_casadi()
        self.rhs, self.mod = ex.rhs, ex.module
        self.states = list(ex.state_names)
        self.inputs = [_plain(n) for n in ex.input_names]
        self.params = list(ex.parameter_names)
        want = [v.name for v in model.states]
        if sorted(self.states) != sorted(want):
            raise ValueError(f"rumoca CasADi states {self.states} differ from {want}")
        self.degree = degree
        tau = np.append(0.0, ca.collocation_points(degree, "radau"))
        C, D = np.zeros((degree + 1, degree + 1)), np.zeros(degree + 1)
        for j in range(degree + 1):
            p = np.poly1d([1.0])
            for r in range(degree + 1):
                if r != j:
                    p *= np.poly1d([1.0, -tau[r]]) / (tau[j] - tau[r])
            D[j] = p(1.0)
            dp = np.polyder(p)
            for r in range(degree + 1):
                C[j, r] = dp(tau[r])
        self.tau, self.C, self.D = tau, C, D
        self._g = {}

    def _gfun(self, output: str, theta: tuple):
        key = (output, theta)
        if key not in self._g:
            e = explicit(self.model, self.spec, theta)
            self._g[key] = sp.lambdify([e.xs, e.us], e.g[output], modules=[_casadi_module()])
        return self._g[key]

    def solve(self, output: str, tstar: float, sign: float, seed: Scenario, seed_run,
              intervals: int | None = None, optimize_params: bool = True,
              max_iter: int = 300) -> CollocationResult:
        ca, sp_ = self.ca, self.space
        K, T = sp_.dist.segments, sp_.T
        N = min(intervals or (K - 1), K - 1)
        h = tstar / N
        nx, nd = len(self.states), len(sp_.dists)
        dnames = [n for n, _ in sp_.dists]
        dbound = np.array([b for _, b in sp_.dists])
        sx = [self.states.index(v.name) for v in self.model.states]     # sympy -> rumoca order
        opti = ca.Opti()
        # parameters: model defaults, uncertain ones as bounded decision variables
        P = [float(v) for v in self.mod.init_params(list(self.mod.DEFAULT_P))]
        theta0 = {u.name: float(seed.theta.get(u.name, v)) for u, v in
                  zip(self.spec.uncertain, nominal_theta(self.model, self.spec))}
        pvars = {}
        pvec = []
        for i, name in enumerate(self.params):
            if name in theta0:
                P[i] = theta0[name]
                if optimize_params:
                    u = next(u for u in self.spec.uncertain if u.name == name)
                    v = opti.variable()
                    opti.subject_to(opti.bounded(float(u.lo), v, float(u.hi)))
                    opti.set_initial(v, theta0[name])
                    pvars[name] = v
                    pvec.append(v)
                    continue
            pvec.append(P[i])
        p = ca.vertcat(*pvec)
        x0 = np.array(self.mod.init_state(P), float)
        # exogenous inputs from the seed trajectory
        ts = seed_run.t
        exo = {n: seed_run.inputs[n] for n in seed_run.inputs if n not in dnames}

        def U(t, w):
            parts = []
            for n in self.inputs:
                parts.append(w[dnames.index(n)] if n in dnames
                             else float(np.interp(t, ts, exo[n])) if n in exo else 0.0)
            return ca.vertcat(*parts)

        W = opti.variable(nd, N)
        for j in range(nd):
            opti.subject_to(opti.bounded(-dbound[j], W[j, :], dbound[j]))
        Xs = opti.variable(nx, N + 1)
        Xc = opti.variable(nx, N * self.degree)
        opti.subject_to(Xs[:, 0] == x0)
        d = self.degree
        for k in range(N):
            for j in range(1, d + 1):
                t = (k + self.tau[j]) * h
                xp = self.C[0, j] * Xs[:, k]
                for r in range(1, d + 1):
                    xp = xp + self.C[r, j] * Xc[:, k * d + r - 1]
                opti.subject_to(h * self.rhs(t, Xc[:, k * d + j - 1], U(t, W[:, k]), p) == xp)
            xe = self.D[0] * Xs[:, k]
            for r in range(1, d + 1):
                xe = xe + self.D[r] * Xc[:, k * d + r - 1]
            opti.subject_to(Xs[:, k + 1] == xe)
        g = self._gfun(output, tuple(theta0[u.name] for u in self.spec.uncertain))
        xT = Xs[:, N]
        uT = U(tstar, W[:, N - 1])
        y = g([xT[sx[i]] for i in range(nx)],
              [uT[self.inputs.index(v.name)] for v in self.model.inputs])
        opti.minimize(-sign * y)
        # warm start from the seed
        Xr = np.column_stack([seed_run.states[n] for n in self.states])
        grid = np.linspace(0, tstar, N + 1)
        for i in range(nx):
            opti.set_initial(Xs[i, :], np.interp(grid, ts, Xr[:, i]))
            tc = np.concatenate([(k + self.tau[1:]) * h for k in range(N)])
            opti.set_initial(Xc[i, :], np.interp(tc, ts, Xr[:, i]))
        mid = (np.arange(N) + 0.5) * h
        for j, n in enumerate(dnames):
            f = sp_.disturbance(seed, n)
            opti.set_initial(W[j, :], np.clip([f(t) for t in mid], -dbound[j], dbound[j]))
        opti.solver("ipopt", {"print_time": False},
                    {"print_level": 0, "sb": "yes", "max_iter": max_iter, "tol": 1e-9})
        try:
            sol = opti.solve()
            status = "solved"
        except RuntimeError:
            sol = opti.debug
            status = sol.stats().get("return_status", "failed")
        Wv = np.atleast_2d(sol.value(W)).reshape(nd, N)
        theta = {n: float(sol.value(v)) for n, v in pvars.items()} or dict(theta0)
        levels, edges = {}, {}
        for j, n in enumerate(dnames):
            lv = list(np.clip(Wv[j] / dbound[j], -1, 1)) + [float(np.sign(Wv[j, -1]))]
            e = list(h * np.arange(1, N + 1))
            pad = K - len(lv)
            levels[n] = np.array(lv + [lv[-1]] * pad)
            edges[n] = np.array(e + [T] * pad)
        scn = Scenario(theta, levels, {k: v.copy() for k, v in seed.refs.items()}, edges)
        return CollocationResult(float(sign * sol.value(y)), scn, tstar, sign, status, theta)
