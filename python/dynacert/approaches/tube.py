"""Error-frame tube along a reference trajectory (the set is proved; the runs are validation).

`<Model>.Cert.tube` proves that the error-frame state stays in `{zᵀPz ≤ level}`. This approach
picks a reference trajectory (random, or a CSV of the free reference signals), maps the set to
physical coordinates along it, simulates admissible disturbances on that reference (plus the
adjoint worst cases), and checks that every run stays inside (`zᵀPz/level ≤ 1`).
"""

from __future__ import annotations

import numpy as np

from .. import montecarlo, tube as tube_mod, worstcase
from ..sim import Simulator
from . import VALIDATION, VIEW, Approach, Assessment, register


@register
class TubeApproach(Approach):
    name = "tube"
    kind = VALIDATION
    layer = VIEW                      # an L5 product of the certificate (its runs are evidence)
    classes = ("lti", "lpv")
    claims = ("tube",)
    summary = "the certified error-frame set along a reference trajectory (proved tube, simulated runs)"

    def add_arguments(self, p):
        p.add_argument("--reference", default="random", metavar="random|FILE.csv",
                       help="reference: a random one (default) or a CSV `t,<free reference>,...`")
        p.add_argument("--n", type=int, default=30, help="disturbance scenarios (default 30)")
        p.add_argument("--T", type=float, default=10.0, help="horizon (default 10)")
        p.add_argument("--no-worst", action="store_true",
                       help="skip the adjoint worst case per output")
        p.add_argument("--backend", default="rumoca", choices=["rumoca", "sympy"],
                       help="simulator (a CSV reference always uses sympy)")
        p.add_argument("--seed", type=int, default=0)

    def assess(self, prob) -> Assessment:
        cert = prob.certificate()
        if cert is None:
            return Assessment.no("no current certificate: run `lmi` first")
        if "frame" not in cert.sidecar:
            return Assessment.no("the certificate predates `Cert.tube`: re-run `lmi`")
        fr = tube_mod.LinearFrame.from_certificate(cert)
        where = ("tube in states " + ", ".join(fr.states) if fr.reconstructs
                 else "the frame does not determine every state: error coordinates only")
        return Assessment.yes(f"error frame ({', '.join(fr.names)}) proved by {fr.theorem}", where)

    def run(self, prob, opts, verbose=print):
        prob = montecarlo.scalar_target(prob)   # array variables: per component
        cert = prob.certificate()
        fr = tube_mod.LinearFrame.from_certificate(cert)
        space = montecarlo.ScenarioSpace(prob.spec, opts.T)
        rng = np.random.default_rng(opts.seed)
        csv = opts.reference != "random"
        refscn = space.sample(rng)
        scns = [space.sample(rng) for _ in range(opts.n)]
        for s in scns:
            s.refs = {k: v.copy() for k, v in refscn.refs.items()}
        zero = montecarlo.Scenario(dict(refscn.theta), {n: np.zeros(space.dist.segments)
                                                        for n, _ in space.dists}, refscn.refs)
        if csv:
            free = tube_mod.read_reference(opts.reference, prob.spec)
            sim = Simulator(prob.model, prob.spec)
            dt = space.h / 50

            def simulate(scn, label=""):
                dist = {n: space.disturbance(scn, n) for n, _ in space.dists}
                theta = [scn.theta[u.name] for u in prob.spec.uncertain]
                return sim.integrate(theta, dist, free, opts.T, dt, label=label)
            backend = "sympy"
        else:
            be = montecarlo.backend(prob, space, opts.backend)
            simulate, backend = be.run, opts.backend
        verbose(f"reference: {'CSV ' + opts.reference if csv else 'random'}; {opts.n} runs "
                f"({backend})")
        ref_run = simulate(zero, "reference")
        tb = tube_mod.Tube(fr, ref_run.t, {n: ref_run.inputs[n] for n in fr.inputs})
        runs = [simulate(s, str(i)) for i, s in enumerate(scns)]
        worst = []
        if not opts.no_worst and not csv:
            adj = worstcase.Adjoint(prob.model, prob.spec,
                                    montecarlo.ScenarioSpace(prob.spec, opts.T,
                                                             montecarlo.Distribution(segments=200)))
            if adj.applicable() is None:
                wsp = adj.space
                bes = (montecarlo.backend(prob, wsp, opts.backend) if opts.backend == "rumoca"
                       else None)
                for o in prob.spec.certify:
                    verbose(f"adjoint worst case of |{o}| on this reference")
                    r = adj.search(o, refs=refscn.refs)
                    w = bes.run(r.scenario) if bes is not None else adj.fwd.run(r.scenario)
                    worst.append((o, w))
        margins = [float(tb.margin(r).max()) for r in runs]
        wm = {o: float(tb.margin(w).max()) for o, w in worst}
        viol = [i for i, m in enumerate(margins) if m > 1 + 1e-6]
        viol += [o for o, m in wm.items() if m > 1 + 1e-6]
        lines = [f"Tube: {prob.model.name}, error frame ({', '.join(fr.names)}), proved by "
                 f"{fr.theorem}"]
        lines.append("  set: zᵀ P z ≤ level; proved extents: " + ", ".join(
            f"{k} ≤ {v:.4g}" for k, v in fr.bounds().items()))
        lines.append(f"  {len(runs)} runs on one {'CSV' if csv else 'random'} reference "
                     f"({backend}): max zᵀPz/level = {max(margins):.4f}")
        for o, m in wm.items():
            lines.append(f"  adjoint worst case of |{o}|: max zᵀPz/level = {m:.4f}")
        lines.append("  COUNTEREXAMPLE: a run leaves the proved tube" if viol else
                     "  every run stays inside the proved tube (≤ 1)")
        data = {"frame": fr.names, "theorem": fr.theorem, "bounds": fr.bounds(),
                "max_margin": max(margins), "worst_margin": wm, "violations": viol,
                "reference": opts.reference}
        return self.outcome(not viol, "counterexample" if viol else "validated",
                            "\n".join(lines), data,
                            artifacts={"tube": tb, "runs": runs, "worst": worst,
                                       "model": prob.model.name})

    def figures(self, prob, outcome, opts):
        from .. import figures

        a = outcome.artifacts
        figs = {"tube": lambda: figures.tube(a["tube"], a["runs"], a["worst"], model=a["model"]),
                "tube-margin": lambda: figures.tube_margin(a["tube"], a["runs"], a["worst"],
                                                           model=a["model"])}
        if a["tube"].frame.reconstructs and len(a["tube"].frame.states) >= 2:
            figs["tube-phase"] = lambda: figures.tube_phase(a["tube"], a["runs"], a["worst"],
                                                            model=a["model"])
        return figs
