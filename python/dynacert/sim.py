"""Simulate a model from rumoca's sympy export, with admissible inputs.

The simulation runs the model's own equations (the same DAE the Lean theorem is about), not
the derived error coordinates. Inputs are drawn to satisfy the specification:

* disturbances: signals with `|d(t)| ≤ bound` (bang-bang, sinusoid, random steps);
* references: a free top-level signal (e.g. `a_ref`) is a random smooth signal, and
  references with a declared derivative are integrated from their declared start value, so
  `x_ref' = v_ref` etc. hold exactly as the claim assumes;
* uncertain parameters: sampled in their intervals (including the endpoints).

Simulations illustrate the certificate; they are not part of the proof.
"""

from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np
import sympy as sp

from . import analysis as an
from . import model as model_mod
from . import spec as spec_mod


@dataclass
class Run:
    t: np.ndarray
    outputs: dict          # certified output name -> array
    states: dict           # state name -> array
    inputs: dict           # input name -> array
    params: dict           # parameter name -> value used
    label: str = ""


@dataclass
class Simulator:
    model: model_mod.Model
    spec: spec_mod.Spec
    _cache: dict = field(default_factory=dict, repr=False)

    # --- compiled right-hand sides per parameter sample ---------------------------------------
    def _compile(self, theta: tuple):
        if theta in self._cache:
            return self._cache[theta]
        m, sp_ = self.model, self.spec
        unc = {u.name: v for u, v in zip(sp_.uncertain, theta)}
        vals = m.param_values(keep=unc)
        vals.update({m.var(n).symbol: sp.Rational(t) for n, t in unc.items()})
        res = an.substitute_params(m.equations_flat(), vals)
        ders = [m.der[v.name] for v in m.states]
        algs = [v.symbol for v in m.algebraics]
        ex = an.eliminate(res, ders, algs)
        xs = [v.symbol for v in m.states]
        us = [v.symbol for v in m.inputs]
        f = sp.lambdify([xs, us], [ex.der[d] for d in ders], "numpy")
        outs = {}
        for name in sp_.certify:
            v = m.var(name)
            e = v.symbol if v.role == "state" else ex.alg[v.symbol]
            outs[name] = sp.lambdify([xs, us], e, "numpy")
        x0 = []
        for v in m.states:
            st = v.start if v.start is not None else 0
            x0.append(float(sp.sympify(st).subs(vals).subs(vals)))
        self._cache[theta] = (f, outs, np.array(x0))
        return self._cache[theta]

    # --- input generation ---------------------------------------------------------------------
    def _signals(self, rng, T):
        m, sp_ = self.model, self.spec
        dist = {}
        for k, d in enumerate(sp_.disturbances):
            b = float(d.bound)
            kind = rng.integers(3)
            if kind == 0:
                f, ph = rng.uniform(0.1, 2.0), rng.uniform(0, 2 * np.pi)
                dist[d.name] = lambda t, f=f, ph=ph, b=b: b * np.sign(np.sin(2 * np.pi * f * t + ph))
            elif kind == 1:
                f, ph = rng.uniform(0.05, 1.5), rng.uniform(0, 2 * np.pi)
                dist[d.name] = lambda t, f=f, ph=ph, b=b: b * np.sin(2 * np.pi * f * t + ph)
            else:
                knots = rng.uniform(-1, 1, int(T * 2) + 2)
                dist[d.name] = lambda t, kn=knots, b=b: b * kn[min(int(t * 2), len(kn) - 1)]
        # free reference signals (no declared derivative, and not the derivative of nothing)
        derived = {r.name for r in sp_.references if r.derivative}
        free = {}
        for r in sp_.references:
            if not r.derivative:
                amp, f, ph = rng.uniform(0.2, 1.0), rng.uniform(0.05, 0.5), rng.uniform(0, 6.28)
                free[r.name] = lambda t, a=amp, f=f, ph=ph: a * np.sin(2 * np.pi * f * t + ph)
        return dist, derived, free

    def run(self, T: float = 10.0, dt: float = 0.002, seed: int = 0, theta=None) -> Run:
        m, sp_ = self.model, self.spec
        rng = np.random.default_rng(seed)
        if theta is None:
            theta = tuple(float(rng.choice([u.lo, u.hi])) if rng.random() < 0.5
                          else float(rng.uniform(float(u.lo), float(u.hi)))
                          for u in sp_.uncertain)
        dist, _, free = self._signals(rng, T)
        return self.integrate(theta, dist, free, T, dt, label=f"seed {seed}")

    def integrate(self, theta, dist: dict, free: dict, T: float = 10.0, dt: float = 0.002,
                  label: str = "", breaks=None) -> Run:
        """Fixed-step RK4 of the model with uncertain parameters `theta` (spec order),
        disturbance signals `dist` and free reference signals `free` (name -> function of t).
        Disturbances are held over each step (zero-order hold at the step start); a step that
        contains one of the sorted `breaks` (disturbance switching times) is split there, so
        switches between grid points are integrated exactly."""
        m, sp_ = self.model, self.spec
        f, outs, x0 = self._compile(tuple(float(v) for v in theta))
        chain = [r for r in sp_.references if r.derivative]  # integrated references
        r0 = np.array([float(r.start or 0) for r in chain])
        in_names = [v.name for v in m.inputs]

        def inputs_at(t, rstate, td=None):
            td = t if td is None else td  # disturbances are sampled at `td`
            u = {}
            for k, r in enumerate(chain):
                u[r.name] = rstate[k]
            for name, sig in free.items():
                u[name] = sig(t)
            for name, sig in dist.items():
                u[name] = sig(td)
            return np.array([u.get(n, 0.0) for n in in_names], dtype=float), u

        def deriv_refs(t, rstate):
            _, u = inputs_at(t, rstate, td=0.0)
            return np.array([u.get(r.derivative, 0.0) for r in chain], dtype=float)

        def rk4(t0, h, x, r):
            def F(tt, xx, rr):
                uu, _ = inputs_at(tt, rr, td=t0)  # disturbances held over the step (ZOH)
                fr = np.array(f(xx, uu), dtype=float).reshape(-1)
                return fr, deriv_refs(tt, rr)

            k1x, k1r = F(t0, x, r)
            k2x, k2r = F(t0 + h / 2, x + h / 2 * k1x, r + h / 2 * k1r)
            k3x, k3r = F(t0 + h / 2, x + h / 2 * k2x, r + h / 2 * k2r)
            k4x, k4r = F(t0 + h, x + h * k3x, r + h * k3r)
            return (x + h / 6 * (k1x + 2 * k2x + 2 * k3x + k4x),
                    r + h / 6 * (k1r + 2 * k2r + 2 * k3r + k4r))

        bk = np.unique(np.asarray(breaks if breaks is not None else [], float))
        n = int(round(T / dt)) + 1
        ts = np.linspace(0.0, T, n)
        X = np.empty((n, len(x0)))
        R = np.empty((n, len(chain)))
        U = np.empty((n, len(in_names)))
        x, r = x0.astype(float), r0.astype(float)
        for k, t in enumerate(ts):
            X[k], R[k] = x, r
            U[k], _ = inputs_at(t, r)
            if k == n - 1:
                break

            t1 = ts[k + 1]
            cuts = [b for b in bk[np.searchsorted(bk, t, side="right"):
                                  np.searchsorted(bk, t1, side="left")]] if len(bk) else []
            t0 = t
            for tb in [*cuts, t1]:
                x, r = rk4(t0, tb - t0, x, r)
                t0 = tb
        out = {name: np.array([float(fn(X[k], U[k])) for k in range(n)])
               for name, fn in outs.items()}
        return Run(ts, out, {v.name: X[:, i] for i, v in enumerate(m.states)},
                   {nm: U[:, i] for i, nm in enumerate(in_names)},
                   {u.name: th for u, th in zip(sp_.uncertain, theta)},
                   label=label)

    def runs(self, n: int = 20, T: float = 10.0, dt: float = 0.002, seed: int = 0) -> list[Run]:
        return [self.run(T, dt, seed + k) for k in range(n)]
