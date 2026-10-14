"""Structure discovery and the certificates built on it.

* `structure` (analysis): what the model can be rewritten as (SE₂(3)/SO(3) blocks, gravity
  class, vehicle/reference log error, layers, linearity), and which Lean results consume each
  finding. With `--lean` it also emits and builds the SE₂(3) link (`LieLink.lean`).
* `layered` (certificate): one LTI certificate per Modelica sub-component, the other
  components' states treated as bounded disturbances, composed by mutual first exit
  (`Dynacert.Compose.assume_guarantee`).
"""

from __future__ import annotations

from fractions import Fraction

from .. import emit_layered, lie_link, pipeline
from .. import structure as structure_mod
from . import CERTIFICATE, Approach, Assessment, register

ANALYSIS = "analysis"


def discover(prob):
    if "structure" not in prob.cache:
        prob.cache["structure"] = structure_mod.discover(prob.model, prob.spec)
    return prob.cache["structure"]


@register
class Structure(Approach):
    name = "structure"
    kind = ANALYSIS
    layer = "analyze"
    summary = "find Lie-group, gravity, layer and linear structure (and link SE₂(3) in Lean)"

    def add_arguments(self, parser):
        parser.add_argument("--lean", action="store_true",
                            help="emit and build the SE₂(3) link LieLink.lean")

    def assess(self, prob) -> Assessment:
        try:
            s = discover(prob)
        except ValueError as e:
            return Assessment.no(f"cannot make the equations explicit: {e}")
        if not s.facts:
            return Assessment.yes("no structure recognized")
        return Assessment.yes(*[f.summary for f in s.facts], kinds=s.kinds())

    def run(self, prob, opts, verbose=print):
        s = discover(prob)
        text, data, files = s.describe(), {"facts": s.to_json()}, []
        if getattr(opts, "lean", False) and s.of("se23"):
            res = lie_link.write_and_check(prob, s, verbose=verbose)
            text += "\n\nLean link (checked): " + ", ".join(res["theorems"]) + \
                f"\n  file: {res['file']}"
            data["lean"] = res
            files.append(res["file"])
        return self.outcome(True, "analyzed", text, data, files)


@register
class Layered(Approach):
    name = "layered"
    kind = CERTIFICATE
    layer = "certify"
    classes = ("layered",)
    claims = ("peak",)
    cert_file = "LayeredCert.lean"
    sidecar = "layered.json"
    summary = "per-component LTI certificates composed by assume–guarantee (Lean-checked)"

    def _problem(self, prob):
        if "layered" not in prob.cache:
            pb, layers, signals, out_idx, _ = emit_layered.layered_problem(prob)
            prob.cache["layered"] = (pb, layers, signals, out_idx,
                                     emit_layered.search(pb, layers, signals))
        return prob.cache["layered"]

    def assess(self, prob) -> Assessment:
        if not prob.spec.certify:
            return Assessment.no("nothing to certify: annotate outputs with __Dynacert(certify)")
        try:
            pb, layers, signals, out_idx, found = self._problem(prob)
        except (pipeline.CertError, ValueError) as e:
            return Assessment.no(str(e))
        desc = "; ".join(f"{L.name or '(top)'} reads "
                         f"{', '.join(pb.coords[j].name for j in L.coupling) or 'nothing'}"
                         for L in layers)
        if found is None:
            return Assessment.no(f"layers: {desc}", "no consistent coupling bounds (coupling "
                                 "too strong for peak-bound composition)")
        b, c = found
        return Assessment.yes(f"layers: {desc}", "coupling bounds: " + ", ".join(
            f"|{pb.coords[j].name}| ≤ {float(c[j]):.4g}" for j in signals))

    def run(self, prob, opts, verbose=print):
        res = emit_layered.run(prob, verbose=verbose)
        side = res["sidecar"]
        lines = [f"CERTIFIED  {side['theorem']}  (axioms: {', '.join(side['axioms'])})"]
        mono = side.get("monolithic_bounds") or {}
        for n, b in side["bounds"].items():
            m = f"   (monolithic LMI: {float(Fraction(mono[n])):.6g})" if n in mono else ""
            lines.append(f"  |{n}| ≤ {b}  ≈ {float(Fraction(b)):.6g}{m}")
        lines.append(f"  files: {res['dir']}")
        return self.outcome(True, "certified", "\n".join(lines),
                            {"theorem": side["theorem"], "bounds": side["bounds"],
                             "axioms": side["axioms"], "dir": res["dir"]}, [res["dir"]])
