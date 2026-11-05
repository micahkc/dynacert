"""SE₂(3) log-tube certificate for a body-frame PD controller tracking a coasting reference.

Feasible when `structure` finds a vehicle/reference pair in inverse-square gravity and the
model's equations match the PD pattern `emit_lie.recognize` reads (thrust and rates from
body-frame errors, coasting reference on a circular orbit, certified outputs
`sqrt(Δp·Δp)`, `sqrt(Δv·Δv)`, `sqrt(eR·eR)`). Running it searches for the certificate data,
emits `Spec.lean` and `LieCert.lean`, builds them with Lean and audits the axioms. The proof is
`Dynacert.Lie.pd_spacecraft_components`.
"""

from __future__ import annotations

from fractions import Fraction

from .. import emit_lie, pipeline
from . import CERTIFICATE, Approach, Assessment, register
from .structure import discover


@register
class Lie(Approach):
    name = "lie"
    kind = CERTIFICATE
    layer = "certify"
    classes = ("lie-se23",)
    claims = ("peak", "tube")
    cert_file = "LieCert.lean"
    sidecar = "lie.json"
    summary = "SE₂(3) log-error tube for PD tracking of a circular orbit (Lean-checked)"

    def assess(self, prob) -> Assessment:
        from ..scalarize import NORM2

        for d in prob.spec.disturbances:   # the Lie tube reads bounds per component
            if d.norm == "2" and not prob.model.var(d.name).scalar:
                return Assessment.no(NORM2.format(name=d.name))
        try:
            s = discover(prob)
            pat = emit_lie.recognize(prob, s)
            nums = emit_lie.problem_numbers(prob, pat)
        except (pipeline.CertError, ValueError, KeyError) as e:
            return Assessment.no(str(e))
        g = nums["gains"]
        return Assessment.yes(
            f"vehicle {pat.veh['p'].rsplit('.', 1)[0]} tracks {pat.ref['p'].rsplit('.', 1)[0]} "
            f"(circular orbit, r0 = {nums['r0']}, μ = {nums['mu']})",
            f"PD gains kp = {g['kp']}, kd = {g['kd']}, kR = {g['kR']}; certifies "
            + ", ".join(n for n, _ in pat.outputs))

    def run(self, prob, opts, verbose=print):
        res = emit_lie.run(prob, discover(prob), verbose=verbose)
        side = res["sidecar"]
        lines = [f"CERTIFIED  {side['theorem']}  (axioms: {', '.join(side['axioms'])})"]
        for n, b in side["bounds"].items():
            lines.append(f"  |{n}| ≤ {b}  ≈ {float(Fraction(b)):.6g}")
        lines.append(f"  log-error tube: α = {side['alpha']}, ‖P‖ ≤ {side['pn']}, "
                     f"region ‖ξ‖ ≤ {side['D']}")
        lines.append(f"  files: {res['dir']}")
        return self.outcome(True, "certified", "\n".join(lines),
                            {"theorem": side["theorem"], "bounds": side["bounds"],
                             "axioms": side["axioms"], "dir": res["dir"]}, [res["dir"]])
