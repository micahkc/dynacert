"""LMI certificates for linear models: dissipation + peak bounds, checked by the Lean kernel.

Feasible when the certified outputs, in error coordinates derived from the model, obey
`ż = A z + B w` with `A` multi-affine in the uncertain parameters and `B` constant, and the
LMI search finds a certificate that survives exact rounding. Running it emits
`Model/Spec/Cert.lean` under `certs/Certs/<Model>/`, builds them, and audits the axioms.
"""

from __future__ import annotations

from fractions import Fraction

import sympy as sp

from .. import analysis as an
from .. import pipeline
from . import CERTIFICATE, Approach, Assessment, register


def nonlinear_terms(prob) -> list[str]:
    """`der(x)` right-hand sides that are not affine in states and inputs (uncertain
    parameters are left symbolic, so products with them are allowed)."""
    m, thetas = prob.model, {m_.symbol for m_ in prob.model.params
                             if m_.name in {u.name for u in prob.spec.uncertain}}
    vals = {k: v for k, v in m.param_values().items() if k not in thetas}
    res = an.substitute_params(m.equations_flat(), vals)
    ex = an.eliminate(res, [m.der[v.name] for v in m.states], [v.symbol for v in m.algebraics])
    xs = {v.symbol for v in m.states} | {v.symbol for v in m.inputs}
    bad = []
    for v in m.states:
        rhs = ex.der[m.der[v.name]]
        dep = sorted({str(s) for x in xs for s in sp.diff(rhs, x).free_symbols & xs})
        if dep:
            bad.append(f"der({v.name}) is nonlinear in {', '.join(dep)}")
    return bad


@register
class LMI(Approach):
    name = "lmi"
    kind = CERTIFICATE
    summary = "LTI / polytopic LMI certificate of peak output bounds (Lean-checked)"

    def add_arguments(self, parser):
        parser.add_argument("--no-plots", action="store_true", help="skip certificate.png")

    def _search(self, prob):
        if "lmi" not in prob.cache:
            pb = pipeline.linear_problem(prob.model, prob.spec, prob.lean_src)
            prob.cache["lmi"] = (pb, pipeline.lti_search(pb))
        return prob.cache["lmi"]

    def assess(self, prob) -> Assessment:
        if not prob.spec.certify:
            return Assessment.no("nothing to certify: annotate outputs with __Dynacert(certify)")
        bad = nonlinear_terms(prob)
        if bad:
            return Assessment.no("the dynamics are not linear: " + "; ".join(bad))
        try:
            pb, cert = self._search(prob)
        except pipeline.CertError as e:
            return Assessment.no(str(e))
        coords = ", ".join(c.name for c in pb.coords)
        shape = (f"polytopic over {len(pb.vertices)} vertices" if pb.vertices is not None
                 else f"{len(pb.dists)} disturbance channel{'s' * (len(pb.dists) != 1)}")
        if cert is None:
            return Assessment.no(f"linear in ({coords}), {shape}, but the LMI search found no "
                                 "certificate (infeasible, or rounding failed)")
        pred = ", ".join(f"|{o.name}| ≤ {float(b.bound):.4g}"
                         for o, b in zip(pb.outputs, cert.boxes))
        return Assessment.yes(f"linear in ({coords}), {shape}",
                              f"candidate found: {pred} (not yet checked by Lean)",
                              predicted={o.name: str(b.bound) for o, b in
                                         zip(pb.outputs, cert.boxes)})

    def run(self, prob, opts, verbose=print):
        pb, cert = self._search(prob)
        verbose(f"search: α = {float(cert.alpha):.4g}, level = {float(cert.level):.6g}")
        res = pipeline.emit_and_check(prob.model, prob.spec, prob.lean_src, prob.py_file,
                                      prob.mo, pb, cert, plots=not opts.no_plots,
                                      verbose=verbose, root=prob.root)
        prob.cache.pop("certificate", None)
        side = res["sidecar"]
        lines = [f"CERTIFIED  {side['theorem']}  (axioms: {', '.join(side['axioms'])})"]
        for o in side["outputs"]:
            peak = res.get("simulated_peaks", {}).get(o["name"])
            extra = f"   (simulated peak {peak:.4g})" if peak is not None else ""
            lines.append(f"  |{o['name']}| ≤ {o['bound']}  ≈ {float(Fraction(o['bound'])):.6g}"
                         f"{extra}")
        lines.append(f"  files: {res['dir']}")
        files = [res["dir"]] + ([res["plot"]] if "plot" in res else [])
        return self.outcome(True, "certified", "\n".join(lines),
                            {"theorem": side["theorem"], "axioms": side["axioms"],
                             "method": side["method"],
                             "bounds": {o["name"]: o["bound"] for o in side["outputs"]},
                             "dir": res["dir"]}, files)

    def figures(self, prob, outcome, opts):
        cert = prob.certificate()
        if cert is None:
            return {}
        return {"certificate": lambda: cert.plot(cert.simulate(24))}
