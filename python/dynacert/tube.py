"""Error-frame tubes: the certified set carried along a reference trajectory.

A certificate proves, in the theorem `<Model>.Cert.tube`, that the error-frame state `z` stays
in the ellipsoid `E = {z | zᵀ P z ≤ level}`. The error frame `z = φ(x, r)` is built from the
states `x` and the references `r`, so for any reference trajectory `r(t)` the physical state is
confined to the tube

    X(t) = { x | φ(x, r(t)) ∈ E }.

For the linear frames derived today, `φ(x, r) = F_x x + F_u r`; when `F_x` is invertible,
`X(t) = x̄(t) ⊕ F_x⁻¹ E` with centre `x̄(t) = −F_x⁻¹ F_u r(t)`, an ellipsoid of fixed shape
translated along the reference. A Lie-group frame (`ξ = log(Y⁻¹X)`) plugs in through the same
`ErrorFrame` interface with a nonlinear `to_physical` (the exponential map).

The tube is proved; simulations here only illustrate it and check that the simulator agrees
(`Tube.margin` ≤ 1 along every run).

**Funnels.** When states carry `initialSet` annotations, the certificate also proves
`<Model>.Cert.funnel`: `zᵀPz ≤ ρ(t) = V₀ e^{-αt} + r (1 − e^{-αt})` with `r = Σγⱼδⱼ²/α`.
`Funnel` reads these constants from the sidecar (`"funnel"`); the set at time `t` is the
tube's ellipsoid scaled by `√(ρ(t)/level)`. `Tube.funnel_runs` simulates the certified
error-frame dynamics from the corners of the initial box (illustration only).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Protocol

import numpy as np


class ErrorFrame(Protocol):
    names: list            # error coordinates z
    P: np.ndarray          # z-space ellipsoid zᵀ P z ≤ level
    level: float
    states: list           # physical states `to_physical` reconstructs

    def error(self, states: dict, inputs: dict) -> np.ndarray:
        """z along a run: (len(t), k) from state and input arrays."""

    def to_physical(self, ref: dict, Z: np.ndarray) -> dict:
        """Rows of `Z` mapped to physical states at one time, given that time's inputs."""

    def bounds(self) -> dict:
        """Proved scalar bounds implied by the set."""


def _f(v) -> float:
    return float(Fraction(v))


@dataclass
class Funnel:
    """`zᵀPz ≤ ρ(t) = V₀ e^{-αt} + rate·(1 − e^{-αt})`, proved by `<Model>.Cert.funnel`."""
    V0: float
    alpha: float
    rate: float            # asymptotic level Σγⱼδⱼ²/α
    level: float           # the invariant level of `Cert.tube` (≥ V₀ and ≥ rate)
    theorem: str = ""
    initial: list = field(default_factory=list)   # [{"name", "min", "max"}] annotated states
    centre: np.ndarray | None = None              # z at the centre of the initial box

    @classmethod
    def from_sidecar(cls, side: dict) -> "Funnel | None":
        f = side.get("funnel")
        if f is None:
            return None
        return cls(_f(f["V0"]), _f(f["alpha"]), _f(f["rate"]), _f(f.get("level", side["level"])),
                   f.get("theorem", ""), list(side.get("initial", [])),
                   np.array([_f(v) for v in side.get("x0", [])]) if side.get("x0") else None)

    def rho(self, t) -> np.ndarray:
        """The proved level ρ(t)."""
        e = np.exp(-self.alpha * np.asarray(t, dtype=float))
        return self.V0 * e + self.rate * (1 - e)

    def scale(self, t) -> np.ndarray:
        """Size of the funnel's ellipsoid relative to the tube's, `√(ρ(t)/level)` (≤ 1)."""
        return np.sqrt(self.rho(t) / self.level)


@dataclass
class LinearFrame:
    """`z = F_x x + F_u r` (states `x`, reference inputs `r`), from a certificate sidecar."""
    names: list
    P: np.ndarray
    level: float
    states: list           # all model states, in model order (columns of Fx)
    inputs: list           # reference inputs appearing in the frame (columns of Fu)
    Fx: np.ndarray
    Fu: np.ndarray
    theorem: str = ""
    outputs: dict = field(default_factory=dict)   # certified output bounds
    funnel: Funnel | None = None                  # present when an initial set is annotated
    A: np.ndarray | None = None                   # certified frame dynamics ż = A z + B w
    B: np.ndarray | None = None
    dist_bounds: list = field(default_factory=list)

    @classmethod
    def from_certificate(cls, cert) -> "LinearFrame":
        side = cert.sidecar
        fr = side.get("frame")
        if fr is None:
            raise ValueError(f"{cert.name}: certificate has no error frame; re-run "
                             "`dynacert MODEL.mo lmi` to regenerate it with `Cert.tube`")
        states = [v.name for v in cert.model.states]
        inputs = sorted({t["var"] for c in fr["terms"] for t in c if t["kind"] == "input"},
                        key=[v.name for v in cert.model.inputs].index)
        k = len(fr["coords"])
        Fx, Fu = np.zeros((k, len(states))), np.zeros((k, len(inputs)))
        for i, terms in enumerate(fr["terms"]):
            for t in terms:
                if t["kind"] == "state":
                    Fx[i, states.index(t["var"])] += _f(t["coeff"])
                else:
                    Fu[i, inputs.index(t["var"])] += _f(t["coeff"])
        P = np.array([[_f(v) for v in r] for r in side["P"]])
        A = np.array([[_f(v) for v in r] for r in side["A"]]) if side.get("A") else None
        B = np.array([[_f(v) for v in r] for r in side["B"]]) if side.get("B") else None
        return cls(list(fr["coords"]), P, _f(side["level"]), states, inputs, Fx, Fu,
                   fr.get("theorem", ""), {o["name"]: _f(o["bound"]) for o in side["outputs"]},
                   Funnel.from_sidecar(side), A, B,
                   [_f(d["bound"]) for d in side.get("disturbances", [])])

    @property
    def reconstructs(self) -> bool:
        """True if the frame determines every state (F_x square and invertible)."""
        return (self.Fx.shape[0] == self.Fx.shape[1]
                and abs(np.linalg.det(self.Fx)) > 1e-12)

    @property
    def M(self) -> np.ndarray:
        """Shape map z ↦ x − x̄ (requires `reconstructs`)."""
        return np.linalg.inv(self.Fx)

    def error(self, states: dict, inputs: dict) -> np.ndarray:
        X = np.column_stack([states[s] for s in self.states])
        Z = X @ self.Fx.T
        if self.inputs:
            R = np.column_stack([inputs[r] for r in self.inputs])
            Z = Z + R @ self.Fu.T
        return Z

    def to_physical(self, ref: dict, Z: np.ndarray) -> dict:
        if not self.reconstructs:
            raise ValueError("the error frame does not determine every state")
        r = np.array([ref[n] for n in self.inputs]) if self.inputs else np.zeros(0)
        X = (np.atleast_2d(Z) - (self.Fu @ r if self.inputs else 0.0)) @ self.M.T
        return {s: X[:, i] for i, s in enumerate(self.states)}

    def bounds(self) -> dict:
        """|z_i| ≤ √(level·(P⁻¹)_ii) for the coordinates and, when the frame reconstructs the
        states, |x_i − x̄_i| ≤ √(level·(M P⁻¹ Mᵀ)_ii) (exact projections of the ellipsoid)."""
        Pi = np.linalg.inv(self.P)
        out = {f"|{n}|": float(np.sqrt(self.level * Pi[i, i])) for i, n in enumerate(self.names)}
        if self.reconstructs:
            S = self.M @ Pi @ self.M.T
            for i, s in enumerate(self.states):
                out[f"|{s} − {s}̄|"] = float(np.sqrt(self.level * S[i, i]))
        return out


def sphere(k: int, n: int, rng=None) -> np.ndarray:
    """`n` points on the unit sphere in ℝᵏ (a circle for k = 2, evenly spaced)."""
    if k == 1:
        return np.array([[-1.0], [1.0]])
    if k == 2:
        th = np.linspace(0, 2 * np.pi, n, endpoint=False)
        return np.column_stack([np.cos(th), np.sin(th)])
    rng = rng or np.random.default_rng(0)
    U = rng.standard_normal((n, k))
    return U / np.linalg.norm(U, axis=1, keepdims=True)


@dataclass
class Tube:
    """The certified set along one reference trajectory (`t`, `ref` inputs on `t`)."""
    frame: object
    t: np.ndarray
    ref: dict

    def ref_at(self, i: int) -> dict:
        return {n: float(v[i]) for n, v in self.ref.items()}

    def center(self) -> dict:
        """The state at zero error along the reference (x̄(t))."""
        k = len(self.frame.names)
        pts = [self.frame.to_physical(self.ref_at(i), np.zeros((1, k))) for i in range(len(self.t))]
        return {s: np.array([p[s][0] for p in pts]) for s in self.frame.states}

    def boundary_z(self, n: int = 240) -> np.ndarray:
        """Points on the boundary of `{zᵀPz ≤ level}`."""
        L = np.linalg.cholesky(self.frame.P)            # P = L Lᵀ, z = √level · L⁻ᵀ u
        U = sphere(self.frame.P.shape[0], n)
        return np.sqrt(self.frame.level) * np.linalg.solve(L.T, U.T).T

    @property
    def funnel(self) -> Funnel | None:
        return getattr(self.frame, "funnel", None)

    def level_at(self, i: int | None = None):
        """The proved level at `t[i]` (all times if `i` is None): ρ(t) with a funnel, else the
        constant tube level."""
        tt = self.t if i is None else self.t[i]
        if self.funnel is None:
            return np.full_like(np.asarray(tt, dtype=float), self.frame.level)
        return np.minimum(self.funnel.rho(tt), self.frame.level)

    def section(self, i: int, a: str, b: str, n: int = 240, funnel: bool = True):
        """The set at time `t[i]` projected on physical states `(a, b)`: the exact projected
        ellipse for an affine frame, else the convex hull of mapped boundary samples. With a
        funnel (and `funnel=True`) the set is the funnel's, `{zᵀPz ≤ ρ(t[i])}`."""
        fr = self.frame
        lvl = float(self.level_at(i)) if funnel else fr.level
        if isinstance(fr, LinearFrame):
            ia, ib = fr.states.index(a), fr.states.index(b)
            S = fr.M @ np.linalg.inv(fr.P) @ fr.M.T
            S2 = lvl * S[np.ix_([ia, ib], [ia, ib])]
            th = np.linspace(0, 2 * np.pi, n)
            e = np.linalg.cholesky(S2) @ np.vstack([np.cos(th), np.sin(th)])
            c = fr.to_physical(self.ref_at(i), np.zeros((1, len(fr.names))))
            return c[a][0] + e[0], c[b][0] + e[1]
        pts = fr.to_physical(self.ref_at(i), self.boundary_z(4 * n) * np.sqrt(lvl / fr.level))
        from scipy.spatial import ConvexHull

        P2 = np.column_stack([pts[a], pts[b]])
        h = ConvexHull(P2).vertices
        return P2[np.append(h, h[0]), 0], P2[np.append(h, h[0]), 1]

    def halfwidths(self) -> dict:
        """Per-state half-width of the tube around its centre (affine frames)."""
        fr = self.frame
        S = fr.level * fr.M @ np.linalg.inv(fr.P) @ fr.M.T
        return {s: float(np.sqrt(S[i, i])) for i, s in enumerate(fr.states)}

    def funnel_halfwidths(self) -> dict:
        """Per-state half-width of the funnel over `t` (arrays; the tube's without a funnel)."""
        sc = np.sqrt(self.level_at() / self.frame.level)
        return {s: h * sc for s, h in self.halfwidths().items()}

    def margin(self, run) -> np.ndarray:
        """`zᵀPz / level` along a simulated run (≤ 1 is inside the proved tube)."""
        Z = self.frame.error(run.states, run.inputs)
        return np.einsum("ij,jk,ik->i", Z, self.frame.P, Z) / self.frame.level

    def funnel_margin(self, run) -> np.ndarray:
        """`zᵀPz / ρ(t)` along a run started in the initial set (≤ 1 is inside the funnel)."""
        Z = self.frame.error(run.states, run.inputs)
        V = np.einsum("ij,jk,ik->i", Z, self.frame.P, Z)
        f = self.funnel
        return V / (f.rho(run.t) if f is not None else self.frame.level)

    def funnel_runs(self, adversarial: bool = True) -> list:
        """Illustration: the certified frame dynamics `ż = A z + B w` (nominal `A` for a
        polytope) from each corner of the initial box, along this reference, with the
        disturbance `w = δ·sign(BᵀPz)` that pushes `V` up fastest (or `w = 0`). Returns
        run-like objects (`t`, `states`, `inputs`, `label`). Requires a funnel and a frame
        that reconstructs the states."""
        import itertools
        from types import SimpleNamespace

        from scipy.linalg import expm

        fr, f = self.frame, self.funnel
        if f is None or fr.A is None or not fr.reconstructs:
            return []
        idx = [fr.states.index(b["name"]) for b in f.initial]
        mids = np.array([(_f(b["min"]) + _f(b["max"])) / 2 for b in f.initial])
        half = np.array([(_f(b["max"]) - _f(b["min"])) / 2 for b in f.initial])
        c = f.centre if f.centre is not None else np.zeros(len(fr.names))
        delta = np.array(fr.dist_bounds) if fr.dist_bounds else np.zeros(fr.B.shape[1])
        t = self.t
        runs = []
        for corner in itertools.product(*[(-1.0, 1.0)] * len(idx)):
            e = np.array(corner) * half
            z = c + fr.Fx[:, idx] @ e
            Z = np.empty((len(t), len(z)))
            Z[0] = z
            for k in range(len(t) - 1):
                h = t[k + 1] - t[k]
                w = delta * np.sign(fr.B.T @ fr.P @ z) if adversarial else 0 * delta
                # exact zero-order-hold step of ż = A z + B w
                E = expm(np.block([[fr.A, fr.B @ np.atleast_1d(w)[:, None]],
                                   [np.zeros((1, len(z) + 1))]]) * h)
                z = E[:len(z), :len(z)] @ z + E[:len(z), -1]
                Z[k + 1] = z
            states = {s: np.empty(len(t)) for s in fr.states}
            for k in range(len(t)):
                p = fr.to_physical(self.ref_at(k), Z[k:k + 1])
                for s in fr.states:
                    states[s][k] = p[s][0]
            label = ", ".join(f"{b['name']}₀={m + ci * hh:+.3g}" for b, m, ci, hh in
                              zip(f.initial, mids, corner, half))
            runs.append(SimpleNamespace(t=t, states=states,
                                        inputs={n: np.asarray(v) for n, v in self.ref.items()},
                                        label=label))
        return runs


# --- reference trajectories -------------------------------------------------------------------

def read_reference(path, spec) -> dict:
    """Free reference signals from a CSV with a header `t,<name>,...`; returns name -> f(t).
    Only references without a declared derivative may be given: the others are integrated from
    their declared start values so the claim's hypotheses hold."""
    data = np.genfromtxt(path, delimiter=",", names=True)
    cols = list(data.dtype.names)
    if not cols or cols[0] != "t":
        raise ValueError(f"{path}: first column must be t")
    free = {r.name for r in spec.references if not r.derivative}
    chained = {r.name for r in spec.references if r.derivative}
    sigs = {}
    for c in cols[1:]:
        if c in chained:
            raise ValueError(f"{path}: {c} has a declared derivative; give the free reference "
                             f"({', '.join(sorted(free))}) and dynacert integrates the rest")
        if c not in free:
            raise ValueError(f"{path}: {c} is not a free reference ({', '.join(sorted(free))})")
        t, y = data["t"], data[c]
        sigs[c] = lambda tt, t=t, y=y: float(np.interp(tt, t, y))
    return sigs
