"""Notebook-facing API.

    import dynacert
    cert = dynacert.check("examples/ClosedLoop.mo", "ClosedLoop")   # certify (rumoca + Lean)
    cert = dynacert.load("ClosedLoop")                              # or load an existing one
    cert                      # claim, bounds, theorem, axioms (rich display in Jupyter)
    cert.verify()             # re-check the theorem with the Lean kernel
    runs = cert.simulate(30)  # simulations of the Modelica model with admissible inputs
    cert.plot(runs)           # trajectories against the verified bounds

The bounds and the claim come from the Lean files; simulations are illustrations only.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

import numpy as np

from . import model as model_mod
from . import spec as spec_mod


def find_root(start: Path | None = None) -> Path:
    """The dynacert Lean project: `$DYNACERT_ROOT`, else the nearest dir with `lakefile.toml`
    whose package is dynacert (searching up from `start`, the package, and the cwd)."""
    env = os.environ.get("DYNACERT_ROOT")
    if env:
        return Path(env).resolve()
    cands = [start, Path(__file__).resolve(), Path.cwd()]
    for c in cands:
        if c is None:
            continue
        for d in [c, *Path(c).resolve().parents]:
            lf = d / "lakefile.toml"
            if lf.exists() and 'name = "dynacert"' in lf.read_text():
                return d
    raise FileNotFoundError("dynacert Lean project not found; set DYNACERT_ROOT")


def _frac(x) -> Fraction:
    return Fraction(x)


@dataclass
class Certificate:
    """A checked certificate: the Lean claim, the verified bounds, and the model."""
    name: str
    dir: Path
    sidecar: dict
    _model: object = field(default=None, repr=False)
    _spec: object = field(default=None, repr=False)

    # --- verified data --------------------------------------------------------------------------
    @property
    def theorem(self) -> str:
        return self.sidecar["theorem"]

    @property
    def axioms(self) -> list[str]:
        return self.sidecar["axioms"]

    @property
    def bounds(self) -> dict[str, Fraction]:
        """Verified bounds `|output| ≤ b` (exact rationals)."""
        return {o["name"]: _frac(o["bound"]) for o in self.sidecar["outputs"]}

    @property
    def disturbances(self) -> dict[str, Fraction]:
        return {d["name"]: _frac(d["bound"]) for d in self.sidecar["disturbances"]}

    @property
    def spec_lean(self) -> str:
        return (self.dir / "Spec.lean").read_text()

    @property
    def claim(self) -> str:
        """The `Claim` definition from Spec.lean (what the theorem asserts)."""
        src = self.spec_lean
        m = re.search(r"(def Claim.*?)(?:\n\nend )", src, re.S)
        return m.group(1).strip() if m else src

    @property
    def hypotheses(self) -> str:
        """Every definition in Spec.lean other than the claim (disturbances, references...)."""
        src = self.spec_lean
        defs = re.findall(r"(/--.*?-/\ndef (?!Claim).*?)(?=\n\n)", src, re.S)
        return "\n\n".join(d.strip() for d in defs)

    # --- model ----------------------------------------------------------------------------------
    @property
    def model(self) -> model_mod.Model:
        if self._model is None:
            self._model = model_mod.load(self.dir / "model_sympy.py")
        return self._model

    @property
    def spec(self) -> spec_mod.Spec:
        if self._spec is None:
            self._spec = spec_mod.from_model(self.model)
        return self._spec

    # --- checking -------------------------------------------------------------------------------
    def verify(self, verbose=print) -> list[str]:
        """Rebuild the certificate with Lean and audit its axioms. Returns the axioms."""
        from .pipeline import ALLOWED_AXIOMS, CertError, axioms, lake

        root = self.dir.parents[2]
        mod = f"Certs.{self.sidecar['ns']}.Cert"
        lake("build", mod, cwd=root)
        ax = axioms(mod, self.theorem, root=root)
        if not ax <= ALLOWED_AXIOMS:
            raise CertError(f"disallowed axioms: {ax - ALLOWED_AXIOMS}")
        if verbose:
            verbose(f"{self.theorem}: checked by the Lean kernel; axioms {sorted(ax)}")
        return sorted(ax)

    @property
    def source(self) -> Path:
        """The Modelica source the certificate was generated from (for rumoca simulation)."""
        p = self.dir / self.sidecar.get("source", "source.mo")
        if not p.exists():
            raise FileNotFoundError(f"{p}: re-run `dynacert MODEL.mo lmi` to store the model source")
        return p

    # --- Monte Carlo (untrusted; see dynacert.montecarlo) ---------------------------------------
    def montecarlo(self, n: int | None = None, *, eps=None, beta=Fraction(1, 10 ** 6),
                   T: float = 10.0, backend: str = "rumoca", seed: int = 0, dist=None,
                   dt: float | None = None, verbose=None):
        """Simulate `n` i.i.d. admissible scenarios (default: enough for `P(peak > achieved)
        ≤ eps` at confidence `1 - beta`, eps = 1%) and report agreement and tightness."""
        from . import montecarlo

        return montecarlo.run(self, n, eps=eps, beta=beta, T=T, backend_name=backend, seed=seed,
                              dist=dist, dt=dt, verbose=verbose)

    def crosscheck(self, n: int = 20, *, T: float = 10.0, seed: int = 0, dist=None):
        """Same scenarios through rumoca's native solver and the sympy export."""
        from . import montecarlo

        return montecarlo.crosscheck(self, n, T=T, seed=seed, dist=dist)

    def falsify(self, output: str | None = None, *, T: float = 10.0, seed: int = 0, init=None,
                backend: str = "rumoca", verbose=None, **kw):
        """Cross-entropy search for a worst-case scenario (an achieved lower bound)."""
        from . import montecarlo

        return montecarlo.falsify(self, output, T=T, seed=seed, init=init,
                                  backend_name=backend, verbose=verbose, **kw)

    # --- simulation and plots -------------------------------------------------------------------
    def simulate(self, n: int = 20, T: float = 10.0, dt: float = 0.002, seed: int = 0):
        from .sim import Simulator

        return Simulator(self.model, self.spec).runs(n, T, dt, seed)

    def ellipse(self, a: str, b: str, npts: int = 400):
        """Boundary of the certified invariant set projected onto outputs `(a, b)`."""
        P = np.array([[float(_frac(v)) for v in r] for r in self.sidecar["P"]])
        c = float(_frac(self.sidecar["level"]))
        rows = {o["name"]: np.array([float(_frac(v)) for v in o["row"]])
                for o in self.sidecar["outputs"]}
        C = np.vstack([rows[a], rows[b]])
        S = c * C @ np.linalg.inv(P) @ C.T
        L = np.linalg.cholesky(S)
        th = np.linspace(0, 2 * np.pi, npts)
        return L @ np.vstack([np.cos(th), np.sin(th)])

    def plot(self, runs=None, phase: tuple[str, str] | None = None, figsize=None):
        """Simulated outputs against the verified bounds; returns the matplotlib figure."""
        import matplotlib.pyplot as plt

        from .figures import palette

        pal = palette()

        runs = self.simulate() if runs is None else runs
        outs = [o["name"] for o in self.sidecar["outputs"]]
        bnd = {k: float(v) for k, v in self.bounds.items()}
        phase = phase if phase is not None else (tuple(outs[:2]) if len(outs) >= 2 else None)
        ncol = len(outs) + (1 if phase else 0)
        fig, axes = plt.subplots(1, ncol, figsize=figsize or (4.3 * ncol, 3.7), squeeze=False)
        axes = axes[0]
        k = 0
        if phase:
            a, b = phase
            ax = axes[0]
            e = self.ellipse(a, b)
            ax.fill(e[0], e[1], color=pal.series[0], alpha=0.12, label="verified invariant set")
            ax.plot(e[0], e[1], color=pal.series[0], lw=1.2)
            for r in runs:
                ax.plot(r.outputs[a], r.outputs[b], color=pal.muted, lw=0.6, alpha=0.6)
            for v, f in ((bnd[a], ax.axvline), (-bnd[a], ax.axvline),
                         (bnd[b], ax.axhline), (-bnd[b], ax.axhline)):
                f(v, color=pal.ink, ls="--", lw=1)
            ax.set_xlabel(a)
            ax.set_ylabel(b)
            ax.set_title("phase plane")
            ax.legend(loc="upper right", fontsize=8)
            k = 1
        for name in outs:
            ax = axes[k]
            k += 1
            for r in runs:
                ax.plot(r.t, r.outputs[name], color=pal.muted, lw=0.6, alpha=0.6)
            ax.axhline(bnd[name], color=pal.ink, ls="--", lw=1.2, label=f"verified ±{bnd[name]:.4g}")
            ax.axhline(-bnd[name], color=pal.ink, ls="--", lw=1.2)
            ax.set_xlabel("t")
            ax.set_title(name)
            ax.legend(loc="upper right", fontsize=8)
        dist = ", ".join(f"|{n}| ≤ {float(v):g}" for n, v in self.disturbances.items())
        unc = ", ".join(f"{u.name} ∈ [{float(u.lo):g}, {float(u.hi):g}]" for u in self.spec.uncertain)
        fig.suptitle(f"{self.sidecar['model']}: {len(runs)} simulations ({dist}"
                     + (f"; {unc}" if unc else "") + ") vs. Lean-verified bounds", fontsize=10)
        fig.tight_layout()
        return fig

    def peaks(self, runs) -> dict[str, float]:
        return {n: max(float(np.max(np.abs(r.outputs[n]))) for r in runs) for n in self.bounds}

    def table(self, runs=None):
        """Verified bound vs. simulated peak per output (a pandas DataFrame if available)."""
        rows = []
        pk = self.peaks(runs) if runs else {}
        for n, b in self.bounds.items():
            row = {"output": n, "verified bound": f"{b.numerator}/{b.denominator}" if b.denominator != 1
                   else str(b.numerator), "≈": float(b)}
            if runs:
                row["simulated peak"] = pk[n]
                row["peak / bound"] = pk[n] / float(b)
            rows.append(row)
        try:
            import pandas as pd

            return pd.DataFrame(rows).set_index("output")
        except ImportError:
            return rows

    # --- display --------------------------------------------------------------------------------
    def _repr_markdown_(self) -> str:
        bl = "\n".join(f"| `{n}` | `{b}` | {float(b):.6g} |" for n, b in self.bounds.items())
        return (f"**{self.sidecar['model']}**: `{self.theorem} : Spec.Claim ...`, "
                f"checked by the Lean kernel (axioms: {', '.join(self.axioms)})\n\n"
                f"| output | verified bound | ≈ |\n|---|---|---|\n{bl}\n\n"
                f"```lean\n{self.claim}\n```")

    def __repr__(self) -> str:
        b = ", ".join(f"|{n}| ≤ {float(v):.6g}" for n, v in self.bounds.items())
        return f"<Certificate {self.theorem}: {b}>"


def load(name: str, root: str | Path | None = None) -> Certificate:
    """Load an existing certificate from `certs/Certs/<name>`."""
    root = Path(root).resolve() if root else find_root()
    d = root / "certs" / "Certs" / name
    side = json.loads((d / "certified.json").read_text())
    side.setdefault("ns", name)
    return Certificate(name, d, side)


def check(mo: str | Path, model: str, root: str | Path | None = None, verbose=print,
          plots: bool = False) -> Certificate:
    """Certify a Modelica model end to end and return the certificate."""
    from .pipeline import check as _check

    res = _check(Path(mo), model, plots=plots, verbose=verbose or (lambda *_: None),
                 root=Path(root).resolve() if root else find_root(Path(mo).resolve()))
    d = Path(res["dir"])
    return load(d.name, d.parents[2])
