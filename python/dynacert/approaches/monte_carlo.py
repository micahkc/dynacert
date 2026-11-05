"""Monte Carlo validation (untrusted): i.i.d. admissible scenarios simulated by rumoca.

With a current certificate, checks that no sample exceeds a certified bound and reports how
tight the bounds are. Without one, reports achieved peaks and the probabilistic statement of
`Dynacert.Prob.scenario_bound`. See docs/montecarlo.md.
"""

from __future__ import annotations

import importlib.util
from fractions import Fraction
from pathlib import Path

from .. import montecarlo
from . import VALIDATE, VALIDATION, Approach, Assessment, register


def scenario_inputs(prob) -> list[str]:
    """What a scenario varies: disturbances, uncertain parameters, free references (array
    variables per component)."""
    s = montecarlo.scalar_target(prob).spec
    return ([f"disturbance {d.name}" for d in s.disturbances]
            + [f"parameter {u.name}" for u in s.uncertain]
            + [f"reference {r.name}" for r in s.references if not r.derivative])


def simulation_check(prob, backend: str = "rumoca") -> Assessment | None:
    """Shared preconditions of the simulation approaches; None if they hold."""
    if not prob.spec.certify:
        return Assessment.no("no outputs to observe: annotate them with __Dynacert(certify)")
    if not scenario_inputs(prob):
        return Assessment.no("nothing to sample: no disturbances, uncertain parameters, or free "
                             "references in the spec")
    if backend == "rumoca" and importlib.util.find_spec("rumoca") is None:
        return Assessment.no("rumoca Python binding not installed (use --backend sympy)")
    return None


def certificate_note(prob) -> tuple[str, dict]:
    cert = prob.certificate()
    if cert is not None:
        return f"compares against certificate {cert.theorem}", dict(cert.bounds)
    # no current lmi certificate: the tightest current bounds of the other methods (index)
    try:
        from .. import certindex

        best = (certindex.kept(certindex.load(prob.cert_dir, prob.model.ns)["certificates"],
                               prob.source_hash) if prob.cert_dir.exists() else {})
    except (OSError, ValueError, KeyError):
        best = {}
    if best:
        meths = sorted({b["method"] for b in best.values()})
        return (f"compares against the current {', '.join(meths)} certificate"
                f"{'s' * (len(meths) > 1)} (certificates.json)",
                {o: Fraction(b["bound"]) for o, b in best.items()})
    if (prob.cert_dir / "certified.json").exists():
        return "certificate in certs/ is stale (source differs): no bounds to compare", {}
    return "no certificate: reports achieved peaks and probabilistic bounds only", {}


@register
class MonteCarloApproach(Approach):
    name = "montecarlo"
    kind = VALIDATION
    summary = "i.i.d. scenario sampling: agreement with the certificate, tightness, ε-quantiles"
    layer = VALIDATE
    classes = ("lti", "lpv", "layered", "lie-se23", "nonlinear")
    claims = ("peak",)
    cost = 10

    def add_arguments(self, p):
        p.add_argument("--n", type=int, help="number of scenarios (default: from --eps, --beta)")
        p.add_argument("--eps", default="1/100", help="target P(peak > achieved) (default 1/100)")
        p.add_argument("--beta", default="1/1000000", help="1 - confidence (default 1e-6)")
        p.add_argument("--T", type=float, default=10.0, help="horizon (default 10)")
        p.add_argument("--backend", default="rumoca", choices=["rumoca", "sympy"])
        p.add_argument("--seed", type=int, default=0)
        p.add_argument("--crosscheck", type=int, default=0, metavar="N",
                       help="also compare rumoca with the sympy export on N scenarios")
        p.add_argument("--save", nargs="?", const="", metavar="DIR",
                       help="write montecarlo.json (default: the certificate's directory, "
                            "else the current directory); figures: --plot")

    def assess(self, prob) -> Assessment:
        try:
            prob = montecarlo.scalar_target(prob)   # array variables: per component
        except ValueError as e:
            return Assessment.no(str(e))
        bad = simulation_check(prob)
        if bad:
            return bad
        note, _ = certificate_note(prob)
        return Assessment.yes("samples " + ", ".join(scenario_inputs(prob)), note)

    def run(self, prob, opts, verbose=print):
        prob = montecarlo.scalar_target(prob)   # array variables: per component
        note, bounds = certificate_note(prob)
        verbose(note)
        beta = Fraction(opts.beta)
        mc = montecarlo.run(prob, opts.n, eps=Fraction(opts.eps), beta=beta, T=opts.T,
                            backend_name=opts.backend, seed=opts.seed, bounds=bounds,
                            verbose=verbose)
        text = [mc.report(beta)]
        data = mc.to_json(beta)
        if opts.crosscheck:
            cc = montecarlo.crosscheck(prob, opts.crosscheck, T=opts.T, seed=opts.seed,
                                       bounds=bounds)
            text.append(repr(cc))
            data["crosscheck"] = {"n": cc.n, "scale": cc.scale, "max": cc.max_rel()}
        files = []
        if opts.save is not None:
            d = Path(opts.save) if opts.save else (prob.cert_dir if bounds else Path.cwd())
            stem = "montecarlo" if bounds else f"{prob.name}_montecarlo"
            files = [montecarlo.save(mc, d / f"{stem}.json", beta)]
            text.append("  wrote " + ", ".join(str(f) for f in files))
        viol = sum(len(v) for v in mc.violations().values())
        return self.outcome(viol == 0, "counterexample" if viol else "validated",
                            "\n".join(text), data, files,
                            {"mc": mc, "cert": prob.certificate() if bounds else None})

    def figures(self, prob, outcome, opts):
        from .. import figures

        mc, cert = outcome.artifacts["mc"], outcome.artifacts.get("cert")
        figs = {"exceedance": lambda: figures.exceedance(mc),
                "histogram": lambda: figures.peak_histogram(mc),
                "envelope": lambda: figures.envelope(mc),
                "traces": lambda: figures.traces(mc)}
        if len(mc.traces) >= 2:
            figs["phase"] = lambda: figures.phase(mc, cert=cert)
        if mc.bounds:
            figs["tightness"] = lambda: figures.tightness(
                {o: {"certified": float(b), "montecarlo": float(mc.peaks[o].max())}
                 for o, b in mc.bounds.items()}, model=prob.model.name)
        return figs
