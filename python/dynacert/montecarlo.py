"""Monte Carlo validation of a certificate, simulated by rumoca.

A certificate proves `sup |y| ≤ b` over *every* admissible scenario. Monte Carlo cannot prove
that, but it answers three questions the certificate does not, all untrusted:

1. **Does the simulator agree with the theorem?** Every sampled peak must stay below `b`. A
   sample above `b` is a counterexample to the pipeline (rumoca's transcription, the spec, or
   the simulator), and the report keeps its scenario for replay. A clean run of `N` samples
   shows, with confidence `1 - β`, that disagreements have probability `< ε` under the sampling
   distribution (`Dynacert.Prob.zero_failure_bound`).
2. **How conservative is the bound?** The largest sampled peak `L` is achieved, so
   `L ≤ sup |y| ≤ b`. With confidence `1 - β`, scenarios with a peak above `L` have probability
   at most `ε = 1 - β^{1/N}` (`Dynacert.Prob.scenario_bound`): `L` is a probabilistic bound and
   `b` the worst-case one.
3. **What is the worst case?** `falsify` searches scenarios (cross-entropy method) to raise
   `L`. Its samples are not i.i.d., so it gives a lower bound only, with no probability.

The probabilistic statements are about the sampling distribution `μ` (`Distribution`, recorded
in every report), the horizon `T`, and exact evaluation of the peak; simulation error and the
pseudo-random generator are outside them. They never strengthen or replace the certificate.

Backends simulate the same `Scenario`:

* `rumoca`: rumoca's native solver on a generated Modelica harness that instantiates the model
  and drives its inputs from scenario parameters (an independent path from the Lean export);
* `sympy`: fixed-step RK4 on rumoca's sympy export, the same DAE IR as the Lean specification.

`crosscheck` runs both on the same scenarios, a differential test of the two paths.
"""

from __future__ import annotations

import json
import math
import re
import time
from dataclasses import asdict, dataclass, field
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp

from . import stats
from .sim import Run, Simulator

TWO_PI = 2 * math.pi


# --- array variables ----------------------------------------------------------------------------

class ScalarTarget:
    """A simulation target (a `Problem` or a `Certificate`) seen with array variables as scalar
    components (`scalarize.view`): one signal per component of an array input (Modelica
    `sys.d[1] = …`), one parameter per component, one reported peak per component of an array
    output. Every other attribute is the target's own."""

    def __init__(self, target):
        from . import scalarize

        self._target = target
        self.model, self.spec = scalarize.view(target.model, target.spec)

    def __getattr__(self, name):
        return getattr(self._target, name)


def scalar_target(target):
    """`target` itself when it has no array variables (or is already scalar), else a
    `ScalarTarget`."""
    from . import scalarize

    if isinstance(target, ScalarTarget) or not scalarize.has_arrays(target.model):
        return target
    return ScalarTarget(target)


# --- scenarios ----------------------------------------------------------------------------------

@dataclass
class Distribution:
    """The sampling distribution `μ` over admissible scenarios on `[0, T]`.

    Disturbances are piecewise constant on `segments` equal intervals, held for a random number
    of segments from `holds`. With probability `p_bang` a signal is bang-bang (`±bound`, where
    worst cases of linear systems live), otherwise uniform in `[-bound, bound]`. An uncertain
    parameter is at a random endpoint with probability `p_vertex`, otherwise uniform. Free
    references are sums of `harmonics` sinusoids with uniform amplitude, frequency (Hz) and
    phase; references with a declared derivative are integrated from their start values."""
    segments: int = 40
    holds: tuple = (1, 2, 4, 8)
    p_bang: float = 0.5
    p_vertex: float = 0.5
    harmonics: int = 3
    ref_amp: tuple = (0.0, 1.0)
    ref_freq: tuple = (0.05, 0.5)


@dataclass
class Scenario:
    theta: dict                 # uncertain parameter -> value
    levels: dict                # disturbance -> normalized levels in [-1, 1], one per segment
    refs: dict                  # free reference -> (harmonics, 3) array of amp, freq, phase
    # disturbance -> the K-1 nondecreasing segment boundaries (switching times); absent means
    # the uniform grid `k·T/K`. Worst-case searches use it to place switches exactly.
    edges: dict = field(default_factory=dict)

    def to_json(self) -> dict:
        return {"theta": self.theta, "levels": {k: v.tolist() for k, v in self.levels.items()},
                "refs": {k: v.tolist() for k, v in self.refs.items()},
                "edges": {k: v.tolist() for k, v in self.edges.items()}}

    @staticmethod
    def from_json(d: dict) -> "Scenario":
        return Scenario(dict(d["theta"]), {k: np.array(v) for k, v in d["levels"].items()},
                        {k: np.array(v) for k, v in d["refs"].items()},
                        {k: np.array(v) for k, v in d.get("edges", {}).items()})


class ScenarioSpace:
    """Admissible scenarios of a certificate's specification, and the distribution `μ`."""

    def __init__(self, spec, T: float = 10.0, dist: Distribution | None = None):
        self.spec, self.T = spec, float(T)
        self.dist = dist or Distribution()
        self.h = self.T / self.dist.segments
        self.dists = [(d.name, float(d.bound)) for d in spec.disturbances]
        self.params = [(u.name, float(u.lo), float(u.hi)) for u in spec.uncertain]
        self.free = [r.name for r in spec.references if not r.derivative]

    # sampling from μ
    def sample(self, rng: np.random.Generator) -> Scenario:
        D, K = self.dist, self.dist.segments
        theta = {n: float(rng.choice([lo, hi])) if rng.random() < D.p_vertex
                 else float(rng.uniform(lo, hi)) for n, lo, hi in self.params}
        levels = {}
        for n, _ in self.dists:
            hold = int(rng.choice(D.holds))
            m = -(-K // hold)
            v = rng.choice([-1.0, 1.0], m) if rng.random() < D.p_bang else rng.uniform(-1, 1, m)
            levels[n] = np.repeat(v, hold)[:K]
        refs = {n: np.column_stack([rng.uniform(*D.ref_amp, D.harmonics) / D.harmonics,
                                    rng.uniform(*D.ref_freq, D.harmonics),
                                    rng.uniform(0, TWO_PI, D.harmonics)]) for n in self.free}
        return Scenario(theta, levels, refs)

    # signals
    def edges(self, scn: Scenario, name: str) -> np.ndarray:
        """The K-1 segment boundaries of a disturbance (uniform unless the scenario moves them)."""
        e = scn.edges.get(name)
        return np.asarray(e, float) if e is not None else self.h * np.arange(1, self.dist.segments)

    def disturbance(self, scn: Scenario, name: str):
        b = dict(self.dists)[name]
        lv = scn.levels[name]
        if name in scn.edges:
            e = self.edges(scn, name)
            return lambda t: b * lv[int(np.searchsorted(e, t, side="right"))]
        h, K = self.h, len(lv)
        return lambda t: b * lv[min(int(t / h), K - 1)]

    def regrid(self, scn: Scenario) -> Scenario:
        """The same scenario with disturbances sampled onto the uniform grid (segment midpoints)."""
        if not scn.edges:
            return scn
        mid = self.h * (np.arange(self.dist.segments) + 0.5)
        levels = {}
        for n, _ in self.dists:
            lv = scn.levels[n]
            levels[n] = (lv[np.searchsorted(self.edges(scn, n), mid, side="right")]
                         if n in scn.edges else lv.copy())
        return Scenario(dict(scn.theta), levels, {k: v.copy() for k, v in scn.refs.items()})

    def reference(self, scn: Scenario, name: str):
        c = scn.refs[name]
        return lambda t: float(np.sum(c[:, 0] * np.sin(TWO_PI * c[:, 1] * t + c[:, 2])))

    # flat encoding (for the cross-entropy search), with box bounds
    def box(self) -> tuple[np.ndarray, np.ndarray]:
        D, K = self.dist, self.dist.segments
        lo, hi = [], []
        for _ in self.dists:
            lo += [-1.0] * K
            hi += [1.0] * K
        for _, a, b in self.params:
            lo.append(a)
            hi.append(b)
        for _ in self.free:
            for _ in range(D.harmonics):
                lo += [0.0, D.ref_freq[0], 0.0]
                hi += [D.ref_amp[1] / D.harmonics, D.ref_freq[1], TWO_PI]
        return np.array(lo), np.array(hi)

    def encode(self, scn: Scenario) -> np.ndarray:
        scn = self.regrid(scn)
        parts = [scn.levels[n] for n, _ in self.dists]
        parts.append(np.array([scn.theta[n] for n, _, _ in self.params]))
        parts += [scn.refs[n].reshape(-1) for n in self.free]
        return np.concatenate(parts) if parts else np.zeros(0)

    def decode(self, z: np.ndarray) -> Scenario:
        K, H, k = self.dist.segments, self.dist.harmonics, 0
        levels = {}
        for n, _ in self.dists:
            levels[n] = np.array(z[k:k + K])
            k += K
        theta = {}
        for n, _, _ in self.params:
            theta[n] = float(z[k])
            k += 1
        refs = {}
        for n in self.free:
            refs[n] = np.array(z[k:k + 3 * H]).reshape(H, 3)
            k += 3 * H
        return Scenario(theta, levels, refs)


# --- backends -----------------------------------------------------------------------------------

def _mo(name: str) -> str:
    return re.sub(r"\W", "_", name)


def harness(model, spec, space: ScenarioSpace, model_name: str) -> tuple[str, str]:
    """Modelica source of a wrapper that instantiates `model_name` as `sys` and drives its inputs
    from scenario parameters. Returns `(class name, source)`."""
    D, K, h = space.dist, space.dist.segments, space.h
    cls = f"DynacertMC_{_mo(model_name)}"
    decl, eqs = [], []
    driven = set()
    for n, b in space.dists:
        ps = [f"dw_{_mo(n)}_{k + 1}" for k in range(K)]
        es = [f"de_{_mo(n)}_{k + 1}" for k in range(K - 1)]   # movable segment boundaries
        decl += [f"  parameter Real {p} = 0;" for p in ps]
        decl += [f"  parameter Real {e} = {h * (k + 1)!r};" for k, e in enumerate(es)]
        chain = f"if time < {es[0]} then {ps[0]}" + "".join(
            f" elseif time < {es[k]} then {ps[k]}" for k in range(1, K - 1)) + f" else {ps[-1]}"
        eqs.append(f"  sys.{n} = {b!r} * ({chain});")
        driven.add(n)
    for n in space.free:
        terms = []
        for j in range(D.harmonics):
            a, f, p = (f"dr_{_mo(n)}_{s}{j + 1}" for s in "afp")
            decl.append(f"  parameter Real {a} = 0, {f} = 0, {p} = 0;")
            terms.append(f"{a} * sin({TWO_PI!r} * {f} * time + {p})")
        eqs.append(f"  sys.{n} = {' + '.join(terms)};")
        driven.add(n)
    for r in spec.references:
        if r.derivative:
            s = f"ref_{_mo(r.name)}"
            decl.append(f"  Real {s}(start = {float(r.start or 0)!r}, fixed = true);")
            eqs += [f"  der({s}) = sys.{r.derivative};", f"  sys.{r.name} = {s};"]
            driven.add(r.name)
    from . import scalarize

    for v in model.inputs:   # array inputs: one equation per component (`sys.d[1] = 0`)
        for e in scalarize.elements(v):
            if e.name not in driven:
                eqs.append(f"  sys.{e.name} = 0;")
    # uncertain array parameters: rumoca tunes whole arrays only, so each array with an
    # uncertain component is bound to one wrapper parameter per component (`tunable`)
    mods = []
    unc = {n for n, _, _ in space.params}
    vals = None
    for v in model.params:
        if not isinstance(v, scalarize.ElemVar) or v.name not in unc or \
                any(m_.startswith(f"{v.base} =") for m_ in mods):
            continue
        if vals is None:
            vals = model.param_values()
        es = [e for e in model.params if isinstance(e, scalarize.ElemVar) and e.base == v.base]
        for e in es:
            nominal = float(sp.sympify(e.symbol).subs(vals).subs(vals))
            decl.append(f"  parameter Real {tunable(e.name)} = {nominal!r};")
        shape = max(e.index for e in es)
        if len(shape) == 1:
            lit = "{" + ", ".join(tunable(e.name) for e in es) + "}"
        else:
            rows = [[tunable(e.name) for e in es if e.index[0] == i] for i in range(shape[0] + 1)]
            lit = "{" + ", ".join("{" + ", ".join(r) + "}" for r in rows) + "}"
        mods.append(f"{v.base} = {lit}")
    inst = f"  {model_name} sys" + (f"({', '.join(mods)})" if mods else "") + ";"
    src = "\n".join([f"model {cls}", inst, *decl, "equation", *eqs, f"end {cls};", ""])
    return cls, src


def tunable(name: str) -> str:
    """The harness parameter that sets the model parameter `name`: `sys.c`, or a wrapper
    parameter `th_c_1_` for the component `c[1]` of an array."""
    return f"th_{_mo(name)}" if "[" in name else f"sys.{name}"


class RumocaBackend:
    """rumoca's native solver on the generated harness (one compilation, one solve per run)."""
    name = "rumoca"

    def __init__(self, model, spec, space: ScenarioSpace, source: Path, model_name: str,
                 dt: float | None = None, solver: str | None = None):
        import rumoca

        self.rm, self.space, self.spec, self.mdl = rumoca, space, spec, model
        self.dt = dt or space.h / 50
        self.cls, self.src = harness(model, spec, space, model_name)
        session = rumoca.Session(roots=[str(Path(source).resolve())])
        self.model = session.loads(self.src, model=self.cls, filename=f"{self.cls}.mo")
        self.config = rumoca.SimConfig(solver=solver) if solver else None
        # The same scenario is re-solved with this solver if the first one fails, so failures
        # do not silently bias the sample (skipping them would change μ).
        self.fallback = None if solver == "rk-like" else rumoca.SimConfig(solver="rk-like")
        self.fallbacks = []              # (label, first error) for each re-solved run
        known = set(self.model.parameters.names)
        for n, _, _ in space.params:
            if tunable(n) not in known:
                raise ValueError(f"uncertain parameter {tunable(n)} is not a tunable parameter")

    def params(self, scn: Scenario) -> dict:
        p = {}
        for n, _ in self.space.dists:
            p.update({f"dw_{_mo(n)}_{k + 1}": float(v) for k, v in enumerate(scn.levels[n])})
            p.update({f"de_{_mo(n)}_{k + 1}": float(e)
                      for k, e in enumerate(self.space.edges(scn, n))})
        for n, c in scn.refs.items():
            for j, (a, f, ph) in enumerate(c):
                p.update({f"dr_{_mo(n)}_a{j + 1}": float(a), f"dr_{_mo(n)}_f{j + 1}": float(f),
                          f"dr_{_mo(n)}_p{j + 1}": float(ph)})
        p.update({tunable(n): float(v) for n, v in scn.theta.items()})
        return p

    def run(self, scn: Scenario, label: str = "") -> Run:
        p = self.params(scn)
        try:
            r = self.model.simulate((0.0, self.space.T), dt=self.dt, params=p, config=self.config)
        except self.rm.SimulationError as e:
            if self.fallback is None:
                raise
            self.fallbacks.append((label, str(e)))
            r = self.model.simulate((0.0, self.space.T), dt=self.dt, params=p,
                                    config=self.fallback)
        out = {n: np.asarray(r[f"sys.{n}"], float) for n in self.spec.certify}
        names = set(r.names)
        ins = {v.name: np.asarray(r[f"sys.{v.name}"], float) for v in self.mdl.inputs
               if f"sys.{v.name}" in names}
        sts = {v.name: np.asarray(r[f"sys.{v.name}"], float) for v in self.mdl.states
               if f"sys.{v.name}" in names}
        return Run(np.asarray(r.time, float), out, sts, ins, dict(scn.theta), label)


class SympyBackend:
    """Fixed-step RK4 on rumoca's sympy export (the DAE the Lean theorem is about)."""
    name = "sympy"

    def __init__(self, model, spec, space: ScenarioSpace, dt: float | None = None):
        self.sim, self.space, self.spec = Simulator(model, spec), space, spec
        self.dt = dt or space.h / 50

    def run(self, scn: Scenario, label: str = "") -> Run:
        sp_ = self.space
        dist = {n: sp_.disturbance(scn, n) for n, _ in sp_.dists}
        free = {n: sp_.reference(scn, n) for n in sp_.free}
        theta = [scn.theta[u.name] for u in self.spec.uncertain]
        breaks = [e for n in scn.edges for e in sp_.edges(scn, n)]
        return self.sim.integrate(theta, dist, free, sp_.T, self.dt, label=label, breaks=breaks)


def backend(cert, space: ScenarioSpace, name: str = "rumoca", dt=None, solver=None):
    cert = scalar_target(cert)
    if name == "rumoca":
        return RumocaBackend(cert.model, cert.spec, space, cert.source, cert.model.name, dt, solver)
    if name == "sympy":
        return SympyBackend(cert.model, cert.spec, space, dt)
    raise ValueError(f"unknown backend {name!r} (rumoca, sympy)")


def _peaks(run: Run) -> dict:
    return {n: float(np.max(np.abs(y))) for n, y in run.outputs.items()}


# --- Monte Carlo --------------------------------------------------------------------------------

@dataclass
class MonteCarlo:
    """`N` i.i.d. scenarios from `μ`, their peaks per certified output, and the statistics.
    `bounds` holds the certificate's bounds; it is empty when the model has no certificate, and
    then only the achieved peaks and the `scenario_bound` statement are reported."""
    model: str
    backend: str
    bounds: dict                     # output -> certified bound (Fraction); may be empty
    peaks: dict                      # output -> np.ndarray of sampled peaks
    scenarios: list
    errors: list                     # (index, message) of simulations that failed
    T: float
    seed: int
    distribution: dict
    seconds: float
    rtol: float = 1e-6               # sampled peaks above b·(1 + rtol) count as violations
    fallbacks: list = field(default_factory=list)  # runs re-solved with the fallback solver
    trace_t: np.ndarray | None = field(default=None, repr=False)   # common time grid
    traces: dict = field(default_factory=dict, repr=False)  # output -> (n, len(trace_t)), signed
    _space: object = field(default=None, repr=False)

    @property
    def n(self) -> int:
        return len(self.scenarios) - len(self.errors)

    def margin(self) -> np.ndarray:
        """Normalized performance `g = max_i |y_i| / s_i` per scenario, with `s_i` the certified
        bound (so `g ≤ 1` is certified) or, without a certificate, the largest sampled peak."""
        return np.max([self.peaks[o] / self._scale(o) for o in self.peaks], axis=0)

    def _scale(self, o: str) -> float:
        if o in self.bounds:
            return float(self.bounds[o])
        return max(float(self.peaks[o].max()), 1e-300)

    def violations(self) -> dict:
        return {o: [int(i) for i in np.flatnonzero(self.peaks[o] > float(b) * (1 + self.rtol))]
                for o, b in self.bounds.items()}

    def summary(self, beta=Fraction(1, 10 ** 6)) -> dict:
        """Per output: certified bound, achieved peak, the ε of both Lean-proved statements."""
        n = self.n
        eps = stats.eps_for(n, beta)
        rows = {}
        viol = self.violations()
        for o, pk in self.peaks.items():
            b = self.bounds.get(o)
            rows[o] = {"bound": b, "achieved": float(pk.max()), "argmax": int(pk.argmax()),
                       "ratio": float(pk.max()) / float(b) if b is not None else None,
                       "eps": eps, "beta": Fraction(beta), "violations": len(viol.get(o, []))}
        return {"n": n, "eps": eps, "beta": Fraction(beta), "outputs": rows,
                "conditional": bool(self.errors)}

    def worst(self, output: str | None = None) -> Scenario:
        g = self.margin() if output is None else self.peaks[output]
        return self.scenarios[self._ok()[int(np.argmax(g))]]

    def _ok(self) -> list[int]:
        bad = {i for i, _ in self.errors}
        return [i for i in range(len(self.scenarios)) if i not in bad]

    def table(self, beta=Fraction(1, 10 ** 6)):
        s = self.summary(beta)
        rows = [{"output": o,
                 "certified bound": float(r["bound"]) if r["bound"] is not None else None,
                 "achieved peak": r["achieved"], "achieved / bound": r["ratio"],
                 "P(peak > achieved) ≤": float(r["eps"]), "violations": r["violations"]}
                for o, r in s["outputs"].items()]
        try:
            import pandas as pd

            return pd.DataFrame(rows).set_index("output")
        except ImportError:
            return rows

    def report(self, beta=Fraction(1, 10 ** 6)) -> str:
        s = self.summary(beta)
        eps, b = s["eps"], s["beta"]
        conf = f"confidence 1 - {float(b):.3g}"
        lines = [f"Monte Carlo: {self.model}, {s['n']} i.i.d. scenarios on [0, {self.T:g}] "
                 f"({self.backend}, seed {self.seed}, {self.seconds:.1f} s)"]
        if self.fallbacks:
            lines.append(f"  {len(self.fallbacks)} runs failed in rumoca's default solver and were "
                         "re-solved with rk-like (see .fallbacks)")
        if self.errors:
            lines.append(f"  {len(self.errors)} simulations failed and are excluded: the "
                         "statements below are conditional on simulation success")
        w = max(6, *(len(o) for o in s["outputs"]))
        lines.append(f"  {'output':<{w}}  {'certified':>10}  {'achieved':>10}  {'ratio':>6}  "
                     f"{'violations':>10}")
        for o, r in s["outputs"].items():
            if r["bound"] is None:
                lines.append(f"  {o:<{w}}  {'—':>10}  {r['achieved']:>10.6g}  {'—':>6}  {'—':>10}")
            else:
                lines.append(f"  {o:<{w}}  {float(r['bound']):>10.6g}  {r['achieved']:>10.6g}  "
                             f"{r['ratio']:>6.3f}  {r['violations']:>10d}")
        nviol = sum(r["violations"] for r in s["outputs"].values())
        if not self.bounds:
            lines.append("  No certificate for this model: there is no worst-case bound to "
                         "compare against.")
            lines.append(f"  Per output, P(peak > achieved) ≤ {float(eps):.4g} with {conf} "
                         "[Dynacert.Prob.scenario_bound]; achieved ≤ true sup.")
            lines.append("  Probabilities are under the sampling distribution μ (see "
                         ".distribution); they do not bound the worst case.")
            return "\n".join(lines)
        if nviol:
            lines.append(f"  COUNTEREXAMPLE: {nviol} sampled peaks exceed the certified bound. "
                         "The simulator disagrees with the theorem; replay the scenarios "
                         "(`.violations()`, `.scenarios`) to find out why.")
        else:
            lines.append(f"  No sample exceeds a certified bound: P(peak > bound) ≤ {float(eps):.4g} "
                         f"with {conf} [Dynacert.Prob.zero_failure_bound].")
        lines.append(f"  Per output, P(peak > achieved) ≤ {float(eps):.4g} with {conf} "
                     "[Dynacert.Prob.scenario_bound]; achieved ≤ true sup ≤ certified.")
        lines.append("  Probabilities are under the sampling distribution μ (see .distribution); "
                     "only the certified bound holds for every admissible scenario.")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return self.report()

    def to_json(self, beta=Fraction(1, 10 ** 6)) -> dict:
        s = self.summary(beta)
        q = lambda f: f"{f.numerator}/{f.denominator}"  # noqa: E731
        return {
            "kind": "montecarlo (untrusted)", "model": self.model, "backend": self.backend,
            "T": self.T, "seed": self.seed, "n": s["n"], "distribution": self.distribution,
            "beta": q(s["beta"]), "eps": q(s["eps"]), "errors": self.errors,
            "outputs": {o: {"bound": q(r["bound"]) if r["bound"] is not None else None,
                            "achieved": r["achieved"],
                            "violations": self.violations().get(o, []),
                            "worst": self.worst(o).to_json()}
                        for o, r in s["outputs"].items()},
            "theorems": ["Dynacert.Prob.scenario_bound", "Dynacert.Prob.zero_failure_bound"],
        }

    def plot(self, kind: str = "exceedance", **opts):
        """A figure of this run: exceedance, histogram, envelope, traces, or phase (see
        `dynacert.figures`)."""
        from . import figures

        kinds = {"exceedance": figures.exceedance, "histogram": figures.peak_histogram,
                 "envelope": figures.envelope, "traces": figures.traces, "phase": figures.phase}
        if kind not in kinds:
            raise ValueError(f"unknown plot {kind!r}; choose from {', '.join(kinds)}")
        return kinds[kind](self, **opts)


def _bounds(target, bounds) -> dict:
    return dict(bounds if bounds is not None else (getattr(target, "bounds", None) or {}))


def downsample(t: np.ndarray, y: np.ndarray, grid: np.ndarray) -> np.ndarray:
    """`y` on `len(grid)` bins of `[grid[0], grid[-1]]`, keeping in each bin the value of
    largest magnitude (so peaks survive). Bins without samples take the nearest sample."""
    nb = len(grid)
    T0, T1 = grid[0], grid[-1]
    idx = np.clip(((t - T0) / (T1 - T0) * (nb - 1) + 0.5).astype(int), 0, nb - 1)
    hi = np.full(nb, -np.inf)
    lo = np.full(nb, np.inf)
    np.maximum.at(hi, idx, y)
    np.minimum.at(lo, idx, y)
    out = np.where(np.abs(hi) >= np.abs(lo), hi, lo)
    empty = ~np.isfinite(out)
    if empty.any():
        out[empty] = np.interp(grid[empty], t, y)
    return out


def run(cert, n: int | None = None, *, eps=None, beta=Fraction(1, 10 ** 6), T: float = 10.0,
        backend_name: str = "rumoca", seed: int = 0, dist: Distribution | None = None,
        dt: float | None = None, solver: str | None = None, bounds: dict | None = None,
        trace_points: int = 400, verbose=None) -> MonteCarlo:
    """Simulate `n` i.i.d. scenarios (or enough for `eps` at confidence `1 - beta`).

    `cert` is a `Certificate` or a `problem.Problem` (anything with `.model`, `.spec`,
    `.source`, `.name`); `bounds` defaults to its certified bounds, if any. Each run's outputs
    are kept on a `trace_points` grid for plotting (0: keep peaks only)."""
    cert = scalar_target(cert)
    if n is None:
        n = stats.samples_for(eps if eps is not None else Fraction(1, 100), beta)
    space = ScenarioSpace(cert.spec, T, dist)
    be = backend(cert, space, backend_name, dt, solver)
    rng = np.random.default_rng(seed)
    scns, peaks, errors = [], {o: [] for o in cert.spec.certify}, []
    grid = np.linspace(0.0, float(T), trace_points) if trace_points else None
    traces = {o: [] for o in cert.spec.certify}
    t0 = time.time()
    from . import timing

    timer = timing.phase(f"simulate {n} scenarios ({be.name})")
    timer.__enter__()
    for i in range(n):
        scn = space.sample(rng)
        scns.append(scn)
        try:
            r = be.run(scn, label=str(i))
            pk = _peaks(r)
            if not all(math.isfinite(v) for v in pk.values()):
                raise FloatingPointError("non-finite output")
        except Exception as e:  # noqa: BLE001 - a failed simulation is reported, not raised
            errors.append((i, f"{type(e).__name__}: {e}"))
            continue
        for o in peaks:
            peaks[o].append(pk[o])
            if grid is not None:
                traces[o].append(downsample(r.t, r.outputs[o], grid))
        if verbose and (i + 1) % max(1, n // 10) == 0:
            verbose(f"  {i + 1}/{n} scenarios")
    timer.__exit__(None, None, None)    # per-run failures are caught above, so this always runs
    return MonteCarlo(cert.name, be.name, _bounds(cert, bounds),
                      {o: np.array(v) for o, v in peaks.items()}, scns, errors, space.T, seed,
                      asdict(space.dist), time.time() - t0,
                      fallbacks=list(getattr(be, "fallbacks", [])), trace_t=grid,
                      traces={o: np.array(v) for o, v in traces.items()} if grid is not None
                      else {}, _space=space)


# --- differential test --------------------------------------------------------------------------

@dataclass
class CrossCheck:
    n: int
    diffs: dict                      # output -> |peak_rumoca - peak_sympy| / scale, per scenario
    peaks: dict                      # backend -> output -> peaks
    scale: str = "bound"             # "bound" (certified) or "peak" (largest sampled peak)

    def max_rel(self) -> dict:
        return {o: float(d.max()) for o, d in self.diffs.items()}

    def __repr__(self) -> str:
        m = ", ".join(f"{o}: {v:.2e}" for o, v in self.max_rel().items())
        return (f"<CrossCheck rumoca vs sympy on {self.n} scenarios: "
                f"max |Δpeak| / {self.scale} = {m}>")


def crosscheck(cert, n: int = 20, *, T: float = 10.0, seed: int = 0,
               dist: Distribution | None = None, dt: float | None = None,
               bounds: dict | None = None) -> CrossCheck:
    """Simulate the same scenarios through rumoca's native solver and through the sympy export
    (the Lean-side DAE); large differences point at a transcription or simulator problem."""
    cert = scalar_target(cert)
    space = ScenarioSpace(cert.spec, T, dist)
    bes = [backend(cert, space, "rumoca", dt), backend(cert, space, "sympy", dt)]
    rng = np.random.default_rng(seed)
    scns = [space.sample(rng) for _ in range(n)]
    outs = cert.spec.certify
    pk = {be.name: {o: np.array([_peaks(be.run(s))[o] for s in scns]) for o in outs}
          for be in bes}
    bnd = _bounds(cert, bounds)
    scale = {o: float(bnd[o]) if o in bnd else max(float(np.abs(pk["sympy"][o]).max()), 1e-300)
             for o in outs}
    diffs = {o: np.abs(pk["rumoca"][o] - pk["sympy"][o]) / scale[o] for o in outs}
    return CrossCheck(n, diffs, pk, "bound" if bnd else "peak")


# --- falsification ------------------------------------------------------------------------------

@dataclass
class Falsification:
    """Best scenario found by the cross-entropy search: an achieved (lower) bound only."""
    output: str | None
    value: float                     # achieved peak (or normalized margin if output is None)
    bound: float | None              # certified bound, if any
    scenario: Scenario
    history: list                    # best value per iteration
    evaluations: int

    def __repr__(self) -> str:
        what = f"|{self.output}|" if self.output else "max |y|/b"
        if self.bound is None:
            return (f"<Falsification {what}: achieved {self.value:.6g} (no certificate; "
                    f"{self.evaluations} simulations)>")
        return (f"<Falsification {what}: achieved {self.value:.6g} vs certified {self.bound:.6g} "
                f"(ratio {self.value / self.bound:.4f}, {self.evaluations} simulations)>")


def falsify(cert, output: str | None = None, *, iters: int = 20, pop: int = 60,
            elite: float = 0.1, smoothing: float = 0.7, T: float = 10.0, seed: int = 0,
            backend_name: str = "rumoca", dist: Distribution | None = None,
            dt: float | None = None, init: "MonteCarlo | Scenario | None" = None,
            bounds: dict | None = None,
            verbose=None) -> Falsification:
    """Cross-entropy search for a scenario that maximizes the peak of `output` (or, with a
    certificate, the normalized margin `max |y_i| / b_i` over all outputs).

    Disturbance levels are searched over `±bound` (bang-bang, where worst cases of linear
    systems live): each segment's sign is Bernoulli, and the probabilities are refit to the
    elite frequencies. Uncertain parameters and reference coefficients are independent clipped
    Gaussians refit to the elite mean and spread. `init` (a scenario, or a Monte Carlo run, on the
    same grid) biases the start toward it (its worst scenario)."""
    cert = scalar_target(cert)
    space = ScenarioSpace(cert.spec, T, dist)
    be = backend(cert, space, backend_name, dt)
    lo, hi = space.box()
    nb = space.dist.segments * len(space.dists)          # binary (sign) coordinates come first
    bounds = {o: float(b) for o, b in _bounds(cert, bounds).items()}
    if output is None and not bounds:
        raise ValueError("falsify: name an output (there are no certified bounds to normalize by)")

    def score(z):
        pk = _peaks(be.run(space.decode(z)))
        return pk[output] if output else max(pk[o] / bounds[o] for o in bounds)

    rng = np.random.default_rng(seed)
    if isinstance(init, MonteCarlo):
        init = init.worst(output)
    z0 = space.encode(init if init is not None else space.sample(rng))
    p = np.clip(0.5 + 0.35 * np.sign(z0[:nb]), 0.15, 0.85) if init is not None else np.full(nb, 0.5)
    mu, sigma = z0[nb:], (hi[nb:] - lo[nb:]) / 2
    best_z, best, hist, evals = z0.copy(), score(z0), [], 1
    n_el = max(2, int(round(elite * pop)))
    for it in range(iters):
        signs = np.where(rng.random((pop, nb)) < p, 1.0, -1.0)
        cont = np.clip(mu + sigma * rng.standard_normal((pop, len(mu))), lo[nb:], hi[nb:])
        Z = np.hstack([signs, cont])
        s = np.array([score(z) for z in Z])
        evals += pop
        idx = np.argsort(s)[-n_el:]
        if s[idx[-1]] > best:
            best, best_z = float(s[idx[-1]]), Z[idx[-1]].copy()
        E = Z[idx]
        p = np.clip(smoothing * (E[:, :nb] > 0).mean(0) + (1 - smoothing) * p, 0.01, 0.99)
        mu = smoothing * E[:, nb:].mean(0) + (1 - smoothing) * mu
        sigma = smoothing * E[:, nb:].std(0) + (1 - smoothing) * sigma
        hist.append(best)
        if verbose:
            verbose(f"  iteration {it + 1}/{iters}: best {best:.6g}")
    return Falsification(output, best, bounds.get(output) if output else 1.0,
                         space.decode(best_z),
                         hist, evals)


def save(mc: MonteCarlo, path: str | Path, beta=Fraction(1, 10 ** 6)) -> Path:
    path = Path(path)
    path.write_text(json.dumps(mc.to_json(beta), indent=1))
    return path
