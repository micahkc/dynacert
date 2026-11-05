"""Switched linear certificates: `if`-expressions switching between linear modes (Lean-checked).

Applicable when the equations contain `if`-expressions and every mode (one branch of every
switch) is linear in a common error frame: same coordinates, same disturbance matrix `B`, same
output rows; only `A` differs. The search finds one quadratic storage `zᵀPz` that decays in
every mode (`methods.lti.certify_polytopic` over the mode matrices), so the bound holds under
any switching, in particular the model's. Emits `SwitchedCert.lean` against the unchanged
`Spec.lean` (see docs/switching.md).

v1: no uncertain parameters; outputs must be states or given by unswitched equations.
"""

from __future__ import annotations

import json
from fractions import Fraction

from .. import emit_lti, emit_switched, pipeline, switched
from . import CERTIFICATE, CERTIFY, Approach, Assessment, register


@register
class Switched(Approach):
    name = "switched"
    kind = CERTIFICATE
    summary = ("switched linear modes (if-expressions): common quadratic storage over the "
               "modes, Lean-checked")
    layer = CERTIFY
    classes = ("switched-lti",)
    claims = ("peak", "tube")
    cost = 15
    cert_file = "SwitchedCert.lean"
    sidecar = "switched.json"

    def _problem(self, prob):
        if "switched" not in prob.cache:
            from .. import timing

            with timing.phase("switched problem"):
                try:
                    prob.cache["switched"] = switched.switched_problem(
                        prob.model, prob.spec, prob.lean_src)
                except pipeline.CertError as e:
                    prob.cache["switched"] = e
        r = prob.cache["switched"]
        if isinstance(r, Exception):
            raise r
        return r

    def _search(self, prob):
        if "switched_cert" not in prob.cache:
            from .. import timing

            spb = self._problem(prob)
            with timing.phase("switched LMI search"):
                prob.cache["switched_cert"] = switched.search(spb)
        return prob.cache["switched_cert"]

    def assess(self, prob) -> Assessment:
        if not switched.has_switching(prob.model):
            return Assessment.no("no if-expressions in the equations (not a switched model)")
        if not prob.spec.certify:
            return Assessment.no("nothing to certify: annotate outputs with __Dynacert(certify)")
        if prob.lean_src is None:
            return Assessment.no("rumoca's Lean export failed: "
                                 + str(prob.cache.get("lean_error", "")))
        arrays = [v.name for v in prob.model.variables if not v.scalar]
        if arrays:
            return Assessment.no("needs scalar variables; arrays: " + ", ".join(arrays[:6]))
        try:
            spb = self._problem(prob)
        except (pipeline.CertError, ValueError) as e:
            return Assessment.no(str(e))
        coords = ", ".join(c.name for c in spb.base.coords)
        shape = (f"{len(spb.modes)} modes from {len(spb.switches)} switch"
                 f"{'es' * (len(spb.switches) != 1)}, linear in ({coords})")
        cert = self._search(prob)
        if cert is None:
            why = ("no common quadratic Lyapunov function exists for the mode matrices (even "
                   "without disturbances)" if switched.common_lyapunov_infeasible(spb.As)
                   else "the LMI search found no certificate (infeasible at every decay rate "
                   "tried, or rounding failed)")
            unstable = [k for k, A in enumerate(spb.As) if _max_real_eig(A) >= 0]
            if unstable:
                why += "; mode" + ("s " if len(unstable) > 1 else " ") + ", ".join(
                    f"{k} ({spb.mode_text(k)}, max Re λ = {_max_real_eig(spb.As[k]):.3g})"
                    for k in unstable) + " not asymptotically stable"
            return Assessment.no(f"{shape}, but {why}")
        pred = ", ".join(f"|{o.name}| ≤ {float(b.bound):.4g}"
                         for o, b in zip(spb.base.outputs, cert.boxes))
        return Assessment.yes(shape, f"candidate found: {pred} (not yet checked by Lean)",
                              predicted={o.name: str(b.bound) for o, b in
                                         zip(spb.base.outputs, cert.boxes)})

    def run(self, prob, opts, verbose=print):
        spb = self._problem(prob)
        cert = self._search(prob)
        if cert is None:
            raise pipeline.CertError("switched: no common quadratic certificate found")
        verbose(f"search: {len(spb.modes)} modes, α = {float(cert.alpha):.4g}, "
                f"level = {float(cert.level):.6g}")
        res = emit_and_check(prob, spb, cert, verbose)
        side = res["sidecar"]
        lines = [f"CERTIFIED  {side['theorem']}  (axioms: {', '.join(side['axioms'])})",
                 f"  {len(spb.modes)} modes: " + "; ".join(
                     f"[{k}] {spb.mode_text(k)}" for k in range(len(spb.modes)))]
        for o in side["outputs"]:
            lines.append(f"  |{o['name']}| ≤ {o['bound']}  ≈ {float(Fraction(o['bound'])):.6g}")
        lines.append(f"  files: {res['file']}")
        return self.outcome(True, "certified", "\n".join(lines),
                            {"theorem": side["theorem"], "axioms": side["axioms"],
                             "method": "switched-lti", "bounds": side["bounds"],
                             "modes": len(spb.modes), "dir": res["dir"]},
                            [res["file"], res["sidecar_file"]])


def _max_real_eig(A) -> float:
    import numpy as np

    return float(max(np.linalg.eigvals(np.array(A, dtype=float)).real))


def emit_and_check(prob, spb, cert, verbose=print) -> dict:
    """Write Model/Spec/SwitchedCert.lean, build, audit axioms, write `switched.json`."""
    import shutil
    from pathlib import Path

    from .. import timing

    pb = spb.base
    out = prob.cert_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / "Model.lean").write_text(prob.lean_src)
    (out / "Spec.lean").write_text(emit_lti.emit_spec(pb))
    if Path(prob.py_file).resolve() != (out / "model_sympy.py").resolve():
        shutil.copy(prob.py_file, out / "model_sympy.py")
    if Path(prob.mo).resolve() != (out / "source.mo").resolve():
        shutil.copy(prob.mo, out / "source.mo")
    f = out / Switched.cert_file
    f.write_text(emit_switched.emit_cert(spb, cert))
    mod = f"Certs.{pb.ns}.SwitchedCert"
    verbose(f"lean: lake build {mod}")
    with timing.phase("lake build"):
        pipeline.lake("build", mod, cwd=prob.root)
    thm = f"{pb.ns}.SwitchedCert.certified"
    with timing.phase("axioms"):
        ax = pipeline.axioms(mod, thm, root=prob.root)
        tax = pipeline.axioms(mod, f"{pb.ns}.SwitchedCert.tube", root=prob.root)
        fax = (pipeline.axioms(mod, f"{pb.ns}.SwitchedCert.funnel", root=prob.root)
               if pb.init_box is not None else set())
    bad = (ax | tax | fax) - pipeline.ALLOWED_AXIOMS
    if bad:
        raise pipeline.CertError(f"switched certificate uses disallowed axioms: {bad}")
    verbose(f"lean: {thm} checked; axioms {sorted(ax)}")
    side = emit_switched.sidecar(spb, cert, thm, ax, prob.source_hash)
    side["tube_axioms"] = sorted(tax)
    if pb.init_box is not None:
        side["funnel"]["axioms"] = sorted(fax)
    sf = out / Switched.sidecar
    sf.write_text(json.dumps(side, indent=1))
    return {"dir": str(out), "file": str(f), "sidecar_file": str(sf), "sidecar": side}
