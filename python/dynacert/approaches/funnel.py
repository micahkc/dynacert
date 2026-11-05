"""Certified finite-horizon funnel for nonlinear tracking (Lean-checked).

Feasible for a model with a `__Dynacert(horizon = T)` annotation, states annotated with their
reference (`__Dynacert(nominal = "...")`, polynomials in time), a closed loop of the form
`ẋ = A x + a sin(x_k) + c(t) + B w` whose reference is an exact undisturbed solution, and
certified outputs equal to one error coordinate. Running it synthesizes the funnel (SDP),
rounds it to an exact certificate, emits `Spec.lean` and `FunnelCert.lean`, builds them and
audits the axioms. The theorem is `Dynacert.Nonlinear.FunnelCert.output_bound`; the method is
Condie, Woodbury, Pant, Goppert (piecewise-polynomial P(t), univariate SOS, α = 0).
"""

from __future__ import annotations

from fractions import Fraction

from .. import funnel as F
from . import CERTIFICATE, Approach, Assessment, register


@register
class Funnel(Approach):
    name = "funnel"
    kind = CERTIFICATE
    layer = "certify"
    classes = ("smooth-nonlinear",)
    claims = ("funnel",)
    cert_file = "FunnelCert.lean"
    sidecar = "funnel.json"
    summary = "finite-horizon funnel: polytopic embedding + piecewise-polynomial P(t), SOS (Lean-checked)"

    def add_arguments(self, parser):
        parser.add_argument("--segments", type=int, default=16)
        parser.add_argument("--degree", type=int, default=3, help="degree of P(t) per segment")

    def assess(self, prob) -> Assessment:
        try:
            fp = F.extract(prob)
        except (F.FunnelError, ValueError, KeyError) as e:
            return Assessment.no(str(e))
        nl = ", ".join(f"{a.kind}({fp.states[a.k]})" for a in fp.atoms) or "none"
        return Assessment.yes(
            f"tracking {', '.join(n for n in fp.nominal_names if n)} over [0, {fp.horizon}]",
            f"nonlinearities {nl}; certifies " + ", ".join(n for n, _ in fp.outputs))

    def run(self, prob, opts, verbose=print):
        from .. import emit_funnel
        res = emit_funnel.run(prob, segments=getattr(opts, "segments", 16),
                              degree=getattr(opts, "degree", 3), verbose=verbose)
        side = res["sidecar"]
        lines = [f"CERTIFIED  {side['theorem']}  (axioms: {', '.join(side['axioms'])})"]
        for n, b in side["bounds"].items():
            lines.append(f"  |{n}| ≤ {b}  ≈ {float(Fraction(b)):.6g}  on [0, {side['horizon']}]")
        lines.append(f"  files: {res['dir']}")
        return self.outcome(True, "certified", "\n".join(lines),
                            {"theorem": side["theorem"], "bounds": side["bounds"],
                             "axioms": side["axioms"], "dir": res["dir"]}, [res["dir"]])
