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
        return cls(list(fr["coords"]), P, _f(side["level"]), states, inputs, Fx, Fu,
                   fr.get("theorem", ""), {o["name"]: _f(o["bound"]) for o in side["outputs"]})

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

    def section(self, i: int, a: str, b: str, n: int = 240):
        """The set at time `t[i]` projected on physical states `(a, b)`: the exact projected
        ellipse for an affine frame, else the convex hull of mapped boundary samples."""
        fr = self.frame
        if isinstance(fr, LinearFrame):
            ia, ib = fr.states.index(a), fr.states.index(b)
            S = fr.M @ np.linalg.inv(fr.P) @ fr.M.T
            S2 = fr.level * S[np.ix_([ia, ib], [ia, ib])]
            th = np.linspace(0, 2 * np.pi, n)
            e = np.linalg.cholesky(S2) @ np.vstack([np.cos(th), np.sin(th)])
            c = fr.to_physical(self.ref_at(i), np.zeros((1, len(fr.names))))
            return c[a][0] + e[0], c[b][0] + e[1]
        pts = fr.to_physical(self.ref_at(i), self.boundary_z(4 * n))
        from scipy.spatial import ConvexHull

        P2 = np.column_stack([pts[a], pts[b]])
        h = ConvexHull(P2).vertices
        return P2[np.append(h, h[0]), 0], P2[np.append(h, h[0]), 1]

    def halfwidths(self) -> dict:
        """Per-state half-width of the tube around its centre (affine frames)."""
        fr = self.frame
        S = fr.level * fr.M @ np.linalg.inv(fr.P) @ fr.M.T
        return {s: float(np.sqrt(S[i, i])) for i, s in enumerate(fr.states)}

    def margin(self, run) -> np.ndarray:
        """`zᵀPz / level` along a simulated run (≤ 1 is inside the proved tube)."""
        Z = self.frame.error(run.states, run.inputs)
        return np.einsum("ij,jk,ik->i", Z, self.frame.P, Z) / self.frame.level


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
