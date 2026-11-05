"""Polyhedral RPI certificates for LTI models (docs/architecture.md §4.2, "fixed K").

The set is a polytope `{z | H z ≤ h}` in the LMI certificate's error coordinates, certified by
a Metzler `M` with `H A = M H` and `M h + |H B| δ < 0`; output bounds come from LP duality.
Everything is exact rational data checked by `decide +kernel` against
`Dynacert.Linear.PolyCert.invariant` and `PolyOutputCert.abs_le`. The bounds approach the
exact all-time peak (the L1 norm of the impulse response) as the facet count grows.

Requirements (v1): a single LTI model (no uncertain parameters), a fixed initial point, and a
current lmi certificate, whose link proof (`Cert.link`, `Cert.init`, `Cert.out<k>`) the
generated `PolyCert.lean` imports and reuses.
"""

from __future__ import annotations

import json
import time
from fractions import Fraction

from .. import emit_poly, pipeline
from ..methods import polyhedral
from . import CERTIFICATE, CERTIFY, Approach, Assessment, register

DEFAULT_FACETS = 128
PROBE_FACETS = 16      # assess(): a quick, time-capped candidate only
PROBE_SECONDS = 5.0


@register
class Polyhedral(Approach):
    name = "polyhedral"
    kind = CERTIFICATE
    summary = ("polyhedral invariant set (Metzler certificate, LP-duality output bounds), "
               "Lean-checked; tighter than lmi with enough facets")
    layer = CERTIFY
    classes = ("lti",)
    claims = ("peak", "tube")
    cost = 20
    cert_file = "PolyCert.lean"
    sidecar = "polyhedral.json"

    def add_arguments(self, parser):
        parser.add_argument("--facets", type=int, default=DEFAULT_FACETS,
                            help=f"target number of facets (default {DEFAULT_FACETS}); more "
                                 "facets give tighter bounds and a slower kernel check")

    def _problem(self, prob):
        if "polyhedral_pb" not in prob.cache:
            if "lmi" in prob.cache:
                pb = prob.cache["lmi"][0]
            else:
                pb = pipeline.linear_problem(prob.model, prob.spec, prob.lean_src)
            prob.cache["polyhedral_pb"] = pb
        return prob.cache["polyhedral_pb"]

    def _search(self, prob, facets: int, time_limit: float | None = None):
        key = ("polyhedral", facets, time_limit)
        if key not in prob.cache:
            pb = self._problem(prob)
            pc = polyhedral.certify(pb.A, pb.B, pb.dist_bounds, x0=pb.x0,
                                    output_rows=[o.row for o in pb.outputs], facets=facets,
                                    time_limit=time_limit)
            prob.cache[key] = pc
        return prob.cache[key]

    def assess(self, prob) -> Assessment:
        if not prob.spec.certify:
            return Assessment.no("nothing to certify: annotate outputs with __Dynacert(certify)")
        if getattr(prob, "lean_src", None) is None:
            return Assessment.no("rumoca's Lean export failed")
        from .lmi import nonlinear_terms
        try:
            bad = nonlinear_terms(prob)
        except (pipeline.CertError, ValueError) as e:
            return Assessment.no(str(e))
        if bad:
            return Assessment.no("the dynamics are not linear: " + "; ".join(bad))
        try:
            pb = self._problem(prob)
        except pipeline.CertError as e:
            return Assessment.no(str(e))
        if pb.vertices is not None:
            return Assessment.no("uncertain parameters: v1 handles a single LTI model "
                                 "(a polytopic/LPV version needs a common polytope over vertices)")
        lmi = prob.certificate()
        if lmi is None:
            return Assessment.no("needs a current lmi certificate (its link proof is reused); "
                                 "run `certify lmi` first (the portfolio runs lmi first)")
        why = emit_poly.cert_supported((prob.cert_dir / "Cert.lean").read_text())
        if why:
            return Assessment.no(why)
        # a quick probe only; the full search (--facets, default 128) runs in run()
        pc = self._search(prob, PROBE_FACETS, PROBE_SECONDS)
        base = f"LTI in ({', '.join(c.name for c in pb.coords)}), reusing the lmi link"
        if pc is None:
            return Assessment.yes(base, f"quick {PROBE_FACETS}-facet probe found no candidate "
                                  "within 5 s; run() searches with --facets (default "
                                  f"{DEFAULT_FACETS})")
        lb = lmi.bounds
        pred = ", ".join(
            f"|{o.name}| ≤ {float(b.bound):.4g} (lmi {float(lb[o.name]):.4g})"
            if o.name in lb else f"|{o.name}| ≤ {float(b.bound):.4g}"
            for o, b in zip(pb.outputs, pc.outputs))
        return Assessment.yes(
            base,
            f"candidate found with {pc.facets} facets: {pred}; run() refines to --facets "
            f"(default {DEFAULT_FACETS}) for tighter bounds",
            probe={o.name: str(b.bound) for o, b in zip(pb.outputs, pc.outputs)})

    def run(self, prob, opts, verbose=print):
        facets = getattr(opts, "facets", DEFAULT_FACETS)
        pb = self._problem(prob)
        lmi = prob.certificate()
        if lmi is None:
            raise pipeline.CertError("polyhedral needs a current lmi certificate (Cert.lean)")
        t0 = time.time()
        pc = self._search(prob, facets)
        if pc is None:
            raise pipeline.CertError("the polyhedral search failed")
        verbose(f"search: {pc.facets} facets ({pc.stats.get('total_s', time.time() - t0)}s)")
        d = prob.cert_dir
        f = d / self.cert_file
        f.write_text(emit_poly.emit(pb, pc))
        mod = f"Certs.{pb.ns}.PolyCert"
        verbose(f"lean: lake build {mod}")
        t1 = time.time()
        pipeline.lake("build", mod, cwd=prob.root)
        t_lean = time.time() - t1
        thm = f"{pb.ns}.PolyCert.certified"
        ax = pipeline.axioms(mod, thm, root=prob.root)
        tax = pipeline.axioms(mod, f"{pb.ns}.PolyCert.tube", root=prob.root)
        bad = (ax | tax) - pipeline.ALLOWED_AXIOMS
        if bad:
            raise pipeline.CertError(f"polyhedral certificate uses disallowed axioms: {bad}")
        verbose(f"lean: {thm} checked in {t_lean:.1f}s; axioms {sorted(ax)}")
        lb = {k: str(v) for k, v in lmi.bounds.items()}
        side = emit_poly.sidecar(pb, pc, thm, ax, lb)
        side["stats"]["lean_s"] = round(t_lean, 1)
        side["tube_axioms"] = sorted(tax)
        (d / self.sidecar).write_text(json.dumps(side, indent=1))
        lines = [f"CERTIFIED  {thm}  (axioms: {', '.join(sorted(ax))})",
                 f"  polytope with {pc.facets} facets"]
        for o in side["outputs"]:
            extra = (f"   (lmi {float(Fraction(o['lmi_bound'])):.6g})"
                     if "lmi_bound" in o else "")
            lines.append(f"  |{o['name']}| ≤ {o['bound']}  ≈ {float(Fraction(o['bound'])):.6g}"
                         f"{extra}")
        lines.append(f"  files: {f}")
        return self.outcome(True, "certified", "\n".join(lines),
                            {"theorem": thm, "axioms": sorted(ax), "method": "polyhedral",
                             "facets": pc.facets,
                             "bounds": {o["name"]: o["bound"] for o in side["outputs"]},
                             "dir": str(d)}, [str(f), str(d / self.sidecar)])
