"""Plots of certified reachable sets against simulated trajectories.

The certified quantities (ellipsoid `xᵀPx ≤ c`, per-output bounds) are read from the
certificate sidecar (`certified.json`), which holds the same exact rationals the Lean kernel
checked. Simulations are illustrations only: they are sampled disturbances, not proofs.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Callable

import numpy as np


def load_sidecar(path) -> dict:
    data = json.loads(Path(path).read_text())

    def f(x):
        return float(Fraction(x))

    data["P_f"] = np.array([[f(v) for v in r] for r in data["P"]])
    data["level_f"] = f(data["level"])
    for o in data["outputs"]:
        o["bound_f"] = f(o["bound"])
    for d in data["disturbances"]:
        d["bound_f"] = f(d["bound"])
    return data


def disturbance_signals(bounds: np.ndarray, n: int, seed: int = 0, T: float = 10.0):
    """Admissible disturbance signals `t ↦ w(t)` with `|wⱼ(t)| ≤ boundsⱼ`."""
    rng = np.random.default_rng(seed)
    m = len(bounds)
    sigs = []
    for k in range(n):
        kind = k % 3
        if kind == 0:  # bang-bang with random switching
            f = rng.uniform(0.2, 3.0, m)
            ph = rng.uniform(0, 2 * np.pi, m)
            sigs.append(lambda t, f=f, ph=ph: bounds * np.sign(np.sin(2 * np.pi * f * t + ph)))
        elif kind == 1:  # sinusoid
            f = rng.uniform(0.05, 2.0, m)
            ph = rng.uniform(0, 2 * np.pi, m)
            sigs.append(lambda t, f=f, ph=ph: bounds * np.sin(2 * np.pi * f * t + ph))
        else:  # random piecewise constant
            knots = rng.uniform(-1, 1, (int(T * 4) + 2, m))
            sigs.append(lambda t, knots=knots: bounds * knots[min(int(t * 4), len(knots) - 1)])
    return sigs


def simulate(rhs: Callable, x0: np.ndarray, w: Callable, T: float, dt: float = 0.005):
    """Fixed-step RK4 (piecewise-constant disturbances are sampled per step)."""
    ts = np.arange(0.0, T + dt / 2, dt)
    xs = np.empty((len(ts), len(x0)))
    x = np.array(x0, dtype=float)
    for k, t in enumerate(ts):
        xs[k] = x
        wk = w(t)
        k1 = rhs(x, wk)
        k2 = rhs(x + dt / 2 * k1, wk)
        k3 = rhs(x + dt / 2 * k2, wk)
        k4 = rhs(x + dt * k3, wk)
        x = x + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return ts, xs


def ellipse_points(P: np.ndarray, c: float, i: int, j: int, n: int = 400):
    """Boundary of the projection of `{xᵀPx ≤ c}` onto coordinates `(i, j)`."""
    Pinv = np.linalg.inv(P)
    S = Pinv[np.ix_([i, j], [i, j])] * c  # projected ellipse {y : yᵀ S⁻¹ y ≤ 1}
    L = np.linalg.cholesky(S)
    th = np.linspace(0, 2 * np.pi, n)
    return L @ np.vstack([np.cos(th), np.sin(th)])


def plot_certificate(sidecar, rhs: Callable, out: str | Path, T: float = 10.0, n_sims: int = 24,
                     x0: np.ndarray | None = None):
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    data = load_sidecar(sidecar) if not isinstance(sidecar, dict) else sidecar
    P, c = data["P_f"], data["level_f"]
    names = data["states"]
    nx = len(names)
    x0 = np.zeros(nx) if x0 is None else x0
    bounds = np.array([d["bound_f"] for d in data["disturbances"]])
    runs = [simulate(rhs, x0, w, T) for w in disturbance_signals(bounds, n_sims, T=T)]

    outs = data["outputs"]
    fig, axes = plt.subplots(1, len(outs) + (1 if nx >= 2 else 0),
                             figsize=(4.2 * (len(outs) + 1), 3.6), squeeze=False)
    axes = axes[0]
    k = 0
    if nx >= 2:
        i, j = data.get("phase", [0, 1])
        ax = axes[0]
        e = ellipse_points(P, c, i, j)
        ax.fill(e[0], e[1], color="tab:blue", alpha=0.12, label="certified set")
        ax.plot(e[0], e[1], color="tab:blue", lw=1.2)
        for _, xs in runs:
            ax.plot(xs[:, i], xs[:, j], color="0.35", lw=0.6, alpha=0.6)
        for o in outs:
            if o.get("state") == i:
                ax.axvline(o["bound_f"], color="tab:red", ls="--", lw=1)
                ax.axvline(-o["bound_f"], color="tab:red", ls="--", lw=1)
            if o.get("state") == j:
                ax.axhline(o["bound_f"], color="tab:red", ls="--", lw=1)
                ax.axhline(-o["bound_f"], color="tab:red", ls="--", lw=1)
        ax.set_xlabel(names[i])
        ax.set_ylabel(names[j])
        ax.set_title("phase plane")
        ax.legend(loc="upper right", fontsize=8)
        k = 1
    for o in outs:
        ax = axes[k]
        k += 1
        coeff = np.array([float(Fraction(v)) for v in o["row"]])
        for ts, xs in runs:
            ax.plot(ts, xs @ coeff, color="0.35", lw=0.6, alpha=0.6)
        ax.axhline(o["bound_f"], color="tab:red", ls="--", lw=1.2, label="certified bound")
        ax.axhline(-o["bound_f"], color="tab:red", ls="--", lw=1.2)
        ax.set_xlabel("t")
        ax.set_title(o["name"])
        ax.legend(loc="upper right", fontsize=8)
    fig.suptitle(f"{data['model']}: {data['method']} certificate "
                 f"(disturbances {', '.join(d['name'] + ' ≤ ' + str(d['bound']) for d in data['disturbances'])})",
                 fontsize=10)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)
    peaks = {o["name"]: max(float(np.max(np.abs(xs @ np.array([float(Fraction(v)) for v in o["row"]]))))
                            for _, xs in runs) for o in outs}
    return peaks



def plot_exceedance(mc, beta: float = 1e-3, figsize=None):
    """Kept for compatibility; see `dynacert.figures.exceedance`."""
    from .figures import exceedance

    return exceedance(mc, beta=beta, figsize=figsize)
