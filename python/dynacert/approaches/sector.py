"""Sector-multiplier tube certificates for nonlinear closed loops (Lean-checked).

`sector`: the joint invariant-ellipsoid certificate of "Where to Tear" (Condie), §V: exact
linear part, residual channels with sector multipliers or peak bounds (proved in Lean from Taylor
inequalities on the region), LMI (8), and Algorithm 1's region fixed point with one ellipsoid per
bounded signal (Lemma 1).

`compose`: the same certificate decomposed with quadratic supply rates (§VI, Proposition 1):
the cut is chosen automatically from the coupling structure (strong first-order edges inside
blocks, weak residual edges across) and screened with Proposition 2; the block LMIs are solved
by consensus ADMM. The emitted certificate checks each block LMI separately in Lean.

See docs/sector.md.
"""

from __future__ import annotations

import json
import time
from fractions import Fraction

from .. import pipeline
from . import ANALYSIS, CERTIFICATE, CERTIFY, Approach, Assessment, register


def _problem(prob):
    from .. import sector as S

    if "sector_problem" not in prob.cache:
        try:
            prob.cache["sector_problem"] = S.extract(prob)
        except S.SectorError as e:
            prob.cache["sector_problem"] = e
    sp_ = prob.cache["sector_problem"]
    if isinstance(sp_, Exception):
        raise sp_
    return sp_


def _assess_common(prob):
    from .. import sector as S

    if prob.lean_src is None:
        return None, Assessment.no("rumoca's Lean export failed")
    try:
        sp_ = _problem(prob)
    except (S.SectorError, ValueError, KeyError) as e:
        return None, Assessment.no(str(e))
    if not sp_.channels:
        return None, Assessment.no("the closed loop is linear: no residual channels "
                                   "(use lmi)")
    return sp_, None


def _describe(sp_) -> str:
    sec = [str(c.expr) for c in sp_.channels if c.kind == "sector"]
    bnd = [str(c.expr) for c in sp_.channels if c.kind == "bounded"]
    return (f"{len(sp_.channels)} residual channels: sector {', '.join(sec) or '-'}; "
            f"bounded {', '.join(bnd) or '-'}; region on "
            + ", ".join(c.name for c in sp_.coords))


def _sidecar(prob, sp_, res, cert, thm, ax, tax, stats, extra=None) -> dict:
    from ..certindex import source_hash

    side = {
        "model": sp_.model_name, "ns": sp_.ns, "method": extra.get("method", "sector")
        if extra else "sector",
        "theorem": thm, "tube_theorem": thm.replace("certified", "tube"), "axioms": sorted(ax),
        "tube_axioms": sorted(tax),
        "bounds": {name: str(b.bound) for (name, _, _), b in zip(sp_.outputs, cert.output_boxes)},
        "region": {c.name: str(r) for c, r in zip(sp_.coords, cert.region)},
        "channels": [
            {"kind": ch.kind, "expr": str(ch.expr), "enters": {sp_.states[i]: str(v)
                                                                for i, v in ch.col.items()},
             **({"sector": [str(cert.gains[j][0]), str(cert.gains[j][1])],
                 "q": str(sp_.qexprs[ch.q])} if ch.kind == "sector"
                else {"bound": str(cert.betas[j])})}
            for j, ch in enumerate(sp_.channels)],
        "ellipsoids": [{"objective": em.name, "alpha": str(em.alpha), "level": str(em.level),
                        "outer": str(em.outer), "blocks": [
                            [sp_.states[i] for i in eb.idx] for eb in em.blocks]}
                       for em in cert.members],
        "states": sp_.states,
        "disturbances": [{"name": d, "bound": str(b)} for d, b in zip(sp_.dists,
                                                                       sp_.dist_bounds)],
        "fixed_point": {"iterations": res.iterations, "history": res.history},
        "stats": stats,
        "source_hash": source_hash(prob.mo.read_text(), prob.model.name),
    }
    if extra:
        side.update(extra)
    return side


def _build(prob, sp_, cert, prefix, parts, verbose):
    from .. import emit_sector as E

    out = prob.cert_dir
    ctx, mods = E.write(prob, sp_, cert, prefix, parts, out)
    lean_s = {}
    for mod in mods:
        verbose(f"lean: lake build Certs.{sp_.ns}.{mod}")
        lean_s[mod] = round(E.lake_build(f"Certs.{sp_.ns}.{mod}", prob.root), 1)
    thm = f"{sp_.ns}.{prefix}Cert.certified"
    ax = E.axioms(f"Certs.{sp_.ns}.{prefix}Cert", thm, prob.root)
    tax = E.axioms(f"Certs.{sp_.ns}.{prefix}Cert", f"{sp_.ns}.{prefix}Cert.tube", prob.root)
    bad = (ax | tax) - pipeline.ALLOWED_AXIOMS
    if bad:
        raise pipeline.CertError(f"certificate uses disallowed axioms: {bad}")
    verbose(f"lean: {thm} checked; axioms {sorted(ax)}")
    return thm, ax, tax, lean_s, mods


def _report(thm, ax, sp_, cert, files, extra_lines=()):
    lines = [f"CERTIFIED  {thm}  (axioms: {', '.join(sorted(ax))})"]
    for (name, _, _), b in zip(sp_.outputs, cert.output_boxes):
        lines.append(f"  |{name}| ≤ {b.bound}  ≈ {float(b.bound):.6g}")
    lines.append("  region: " + ", ".join(f"|{c.name}| ≤ {float(r):.4g}"
                                         for c, r in zip(sp_.coords, cert.region)))
    lines += list(extra_lines)
    lines.append(f"  files: {', '.join(str(f) for f in files)}")
    return "\n".join(lines)


@register
class Sector(Approach):
    name = "sector"
    kind = CERTIFICATE
    summary = ("nonlinear tube: exact linear part + residual channels with sector multipliers "
               "(rigorous Lean bounds), LMI (8), region fixed point (Lean-checked)")
    layer = CERTIFY
    classes = ("nonlinear",)
    claims = ("peak", "tube")
    cost = 40
    cert_file = "SectorCert.lean"
    sidecar = "sector.json"
    prefix = "Sector"

    def add_arguments(self, parser):
        parser.add_argument("--max-iter", type=int, default=40,
                            help="region fixed-point iterations (Algorithm 1)")

    def assess(self, prob) -> Assessment:
        sp_, no = _assess_common(prob)
        if no:
            return no
        return Assessment.yes(_describe(sp_),
                              "run() searches the region fixed point (LMI (8), one ellipsoid per "
                              "bounded signal) and checks the result in Lean")

    def _search(self, prob, sp_, parts, opts, verbose):
        from .. import sector as S

        t0 = time.time()
        res = S.region_fixed_point(sp_, parts, max_iter=getattr(opts, "max_iter", 40),
                                   verbose=verbose)
        t_search = time.time() - t0
        if not res.ok:
            raise pipeline.CertError(f"no certificate: {res.message}")
        return res, t_search

    def run(self, prob, opts, verbose=print):
        from .. import sector as S

        sp_ = _problem(prob)
        verbose(f"sector: {_describe(sp_)}")
        parts = [list(range(sp_.n))]
        res, t_search = self._search(prob, sp_, parts, opts, verbose)
        t1 = time.time()
        cert, res = S.certify_grow(sp_, res, parts, verbose=verbose)
        if cert is None:
            raise pipeline.CertError("the certificate did not survive exact rounding")
        t_exact = time.time() - t1
        thm, ax, tax, lean_s, mods = _build(prob, sp_, cert, self.prefix, parts, verbose)
        stats = {"search_s": round(t_search, 1), "exact_s": round(t_exact, 1), "lean_s": lean_s}
        side = _sidecar(prob, sp_, res, cert, thm, ax, tax, stats, {"method": self.name})
        (prob.cert_dir / self.sidecar).write_text(json.dumps(side, indent=1))
        files = [prob.cert_dir / f"{m}.lean" for m in mods] + [prob.cert_dir / self.sidecar]
        return self.outcome(True, "certified", _report(thm, ax, sp_, cert, files[-2:]),
                            {"theorem": thm, "axioms": sorted(ax), "method": self.name,
                             "bounds": side["bounds"], "dir": str(prob.cert_dir)},
                            [str(f) for f in files])


@register
class Compose(Sector):
    name = "compose"
    summary = ("compositional sector certificate: automatic cut (coupling graph + Proposition 2 "
               "screening), block LMIs with quadratic supply rates solved by ADMM (Lean-checked)")
    cost = 45
    cert_file = "ComposeCert.lean"
    sidecar = "compose.json"
    prefix = "Compose"

    def add_arguments(self, parser):
        super().add_arguments(parser)
        parser.add_argument("--cut", default=None,
                            help='blocks of states, e.g. "e_x,v_x,theta,q | e_z,v_z" '
                                 "(default: chosen from the coupling graph)")
        parser.add_argument("--solver", choices=("admm", "central"), default="admm",
                            help="final block LMIs: consensus ADMM (default) or one central SDP")
        parser.add_argument("--admm-iters", type=int, default=80)
        parser.add_argument("--rho", type=float, default=1.0, help="ADMM penalty (objectives are normalized)")

    def _cut(self, prob, sp_, opts):
        from .. import cuts as C

        key = ("compose_cut", getattr(opts, "cut", None) if opts else None)
        if key in prob.cache:
            return prob.cache[key]
        g, cands = C.candidates(sp_)
        if opts is not None and getattr(opts, "cut", None):
            parts = C.parse_cut(sp_, opts.cut)
            s, w = C.cut_weight(g, parts)
            chosen = C.Candidate(parts, "user", s, w, C.screen(sp_, parts))
        else:
            chosen = C.choose(sp_, cands)
        prob.cache[key] = (g, cands, chosen)
        return prob.cache[key]

    def assess(self, prob) -> Assessment:
        sp_, no = _assess_common(prob)
        if no:
            return no
        g, cands, chosen = self._cut(prob, sp_, None)
        names = sp_.states
        lines = [f"{c.label(names)} [{c.source}; cuts {c.strong_cut} strong, {c.weak_cut} weak "
                 f"edges]: Proposition 2 {'accepts' if c.feasible else 'rejects'}"
                 for c in cands[:6]]
        if chosen is None or len(chosen.parts) < 2:
            return Assessment.no("no cut passes Proposition 2 (no block-diagonal P with "
                                 "AᵀP + PA ≺ 0)", *lines)
        return Assessment.yes(f"cut {chosen.label(names)}", *lines,
                              cut=[[names[i] for i in p] for p in chosen.parts])

    def run(self, prob, opts, verbose=print):
        from .. import cuts as C
        from .. import sector as S

        sp_ = _problem(prob)
        g, cands, chosen = self._cut(prob, sp_, opts)
        if chosen is None or len(chosen.parts) < 2:
            raise pipeline.CertError("no cut passes Proposition 2")
        if chosen.feasible is False:
            raise pipeline.CertError(f"cut {chosen.label(sp_.states)} fails Proposition 2: no "
                                     "block-diagonal certificate exists across it")
        parts = chosen.parts
        verbose(f"compose: cut {chosen.label(sp_.states)}")
        res, t_search = self._search(prob, sp_, parts, opts, verbose)
        blocks, ifaces = S.build_blocks(sp_, parts)
        gains, betas = S.constants(sp_, res.region)
        admm_stats = None
        members = None
        if getattr(opts, "solver", "admm") == "admm":
            members, admm_stats = [], []
            for mb in res.members:
                central = S.resolve(sp_, blocks, ifaces, gains, betas, mb, 1e-3)
                r = C.admm(sp_, parts, gains, betas, mb.name, mb.row, mb.alpha,
                           iters=getattr(opts, "admm_iters", 80), rho=getattr(opts, "rho", 1.0),
                           verbose=verbose)
                if r.member is None:
                    verbose(f"  ADMM did not close for {mb.name}: using one central SDP")
                    members, admm_stats = None, None
                    break
                members.append(r.member)
                admm_stats.append({"objective": mb.name, "iterations": r.iterations,
                                   "seconds": round(r.seconds, 2),
                                   "support_admm": r.member.support,
                                   "support_central": central.support if central else None,
                                   "final_residual": r.history[-1][2] if r.history else None})
                verbose(f"  ADMM {mb.name}: support {r.member.support:.6g} (central "
                        f"{central.support if central else float('nan'):.6g}) in "
                        f"{r.seconds:.2f} s")
        t1 = time.time()
        if members is None:
            cert, res = S.certify_grow(sp_, res, parts, verbose=verbose)
        else:
            cert = S.certify_exact(sp_, res, parts, members=members)
        if cert is None:
            raise pipeline.CertError("the certificate did not survive exact rounding")
        t_exact = time.time() - t1
        thm, ax, tax, lean_s, mods = _build(prob, sp_, cert, self.prefix, parts, verbose)
        stats = {"search_s": round(t_search, 1), "exact_s": round(t_exact, 1), "lean_s": lean_s}
        extra = {"method": self.name,
                 "cut": [[sp_.states[i] for i in p] for p in parts],
                 "candidates": [{"cut": c.label(sp_.states), "source": c.source,
                                 "strong_cut": c.strong_cut, "weak_cut": c.weak_cut,
                                 "proposition2": c.feasible} for c in cands],
                 "interfaces": [{"sender": [sp_.states[i] for i in parts[I.sender]],
                                 "row": [str(v) for v in I.row],
                                 "receivers": [[sp_.states[i] for i in parts[r]]
                                               for r in I.receivers]} for I in ifaces],
                 "admm": admm_stats}
        side = _sidecar(prob, sp_, res, cert, thm, ax, tax, stats, extra)
        (prob.cert_dir / self.sidecar).write_text(json.dumps(side, indent=1))
        files = [prob.cert_dir / f"{m}.lean" for m in mods] + [prob.cert_dir / self.sidecar]
        extra_lines = [f"  cut: {chosen.label(sp_.states)} (block LMIs checked separately)"]
        return self.outcome(True, "certified",
                            _report(thm, ax, sp_, cert, files[-2:], extra_lines),
                            {"theorem": thm, "axioms": sorted(ax), "method": self.name,
                             "bounds": side["bounds"], "dir": str(prob.cert_dir),
                             "cut": extra["cut"]},
                            [str(f) for f in files])


@register
class Tear(Approach):
    name = "tearing"
    kind = ANALYSIS
    summary = ("loop tearing baseline (paper §IV): peak-to-peak small gain across each candidate "
               "cut; explains failure by the cycle gain ρ(J) (analysis, not a certificate)")
    layer = "analyze"

    def assess(self, prob) -> Assessment:
        sp_, no = _assess_common(prob)
        if no:
            return no
        return Assessment.yes("cuts that sever linear couplings: cycle gain of the torn loop")

    def run(self, prob, opts, verbose=print):
        import numpy as np

        from .. import cuts as C

        sp_ = _problem(prob)
        g, cands = C.candidates(sp_)
        rows, data = [], []
        for c in cands:
            t = C.tearing(sp_, c.parts)
            if not t.signals:
                continue
            verdict = ("a torn block is unstable on its own: no peak-to-peak bound" if
                       t.rho == float("inf") else
                       "fails at every disturbance level" if t.rho >= 1 else
                       "linear part contracts (the residual interfaces still need bounds)")
            rows.append(f"  {c.label(sp_.states):32s} ρ(J) = {t.rho:.3g}: {verdict}")
            data.append({"cut": c.label(sp_.states), "rho": t.rho if t.rho != float("inf")
                         else "inf", "J": [[x if np.isfinite(x) else "inf" for x in r]
                                           for r in t.J.tolist()]})
        text = "Loop tearing (peak-to-peak interfaces), linear cycle gain per cut:\n" + \
            ("\n".join(rows) if rows else "  no cut severs a linear coupling")
        return self.outcome(True, "analyzed", text, {"cuts": data})
