"""Layered LTI certificates: one certificate per Modelica sub-component, composed by
`Dynacert.Compose.assume_guarantee`.

The model's states are split by component (`structure.layers`). Layer `L` is certified as an
LTI system `ż_L = A_L z_L + B_L w_L` whose disturbance channels are the model's own
disturbances and the states it reads from other layers (the *coupling signals*), with
assumed peak bounds `|s_j| ≤ b_j`. Each layer guarantees strictly tighter bounds `c_j < b_j` on
the coupling signals it owns. Python finds the bounds by fixed-point iteration (a small-gain
condition in disguise); Lean checks every layer certificate and closes the loop by mutual first
exit, which needs no small-gain theorem, only the strict inequalities.

The claim (`Spec.lean`) is the one the monolithic LMI approach would emit for the same model:
it comes from `pipeline.linear_problem` and does not depend on the layering. The certificate
goes to `LayeredCert.lean` next to it.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction

from . import emit_lti as E
from . import lean as lean_mod
from . import pipeline
from .lean import mat, q, vec
from .methods import lti


@dataclass
class Layer:
    name: str               # component
    idx: list[int]          # global coordinate indices it owns
    coupling: list[int]     # global coordinate indices it reads from other layers
    dists: list[int]        # disturbance channels it reads
    A: list
    B: list                 # columns: dists, then coupling
    rows: list[int]         # owned coordinates that get a box bound (signals + outputs)
    cert: object = None


def _component(name: str) -> str:
    return name.split(".", 1)[0] if "." in name else ""


def layered_problem(prob):
    m, sp_ = prob.model, prob.spec
    pb = pipeline.linear_problem(m, sp_, prob.lean_src)
    if pb.refs or pb.vertices is not None:
        raise pipeline.CertError("layered: references and uncertain parameters are not "
                                 "supported yet (use the lmi approach)")
    if any(len(c.terms) != 1 or c.terms[0].kind != "x" or c.terms[0].coeff != 1
           for c in pb.coords):
        raise pipeline.CertError("layered: coordinates must be the states themselves")
    names = [c.name for c in pb.coords]
    comps: dict[str, list[int]] = {}
    for i, n in enumerate(names):
        comps.setdefault(_component(n), []).append(i)
    if len(comps) < 2:
        raise pipeline.CertError("layered: the model has a single component")
    n = len(names)
    owner = {i: c for c, ids in comps.items() for i in ids}
    out_idx = {}
    for k, o in enumerate(pb.outputs):
        if o.kind != "state" or sorted(o.row) != [0] * (n - 1) + [1]:
            raise pipeline.CertError(f"layered: output {o.name} must be a state")
        out_idx[k] = o.row.index(1)
    layers = []
    for c, ids in comps.items():
        coup = sorted({j for i in ids for j in range(n) if j not in ids and pb.A[i][j] != 0})
        dists = sorted({k for i in ids for k in range(len(pb.dists)) if pb.B[i][k] != 0})
        A = [[pb.A[i][j] for j in ids] for i in ids]
        B = [[pb.B[i][k] for k in dists] + [pb.A[i][j] for j in coup] for i in ids]
        layers.append(Layer(c, ids, coup, dists, A, B, []))
    signals = sorted({j for L in layers for j in L.coupling})
    for L in layers:
        L.rows = sorted({j for j in signals if j in L.idx} |
                        {j for j in out_idx.values() if j in L.idx})
    return pb, layers, signals, out_idx, owner


def search(pb, layers, signals, margin=Fraction(21, 20), iters=60):
    """Bounds `b` on the coupling signals with every layer guaranteeing `c_j < b_j`."""
    b = {j: Fraction(0) for j in signals}
    for _ in range(iters):
        c = {}
        for L in layers:
            deltas = [pb.dist_bounds[k] for k in L.dists] + [b[j] for j in L.coupling]
            x0 = [pb.x0[i] for i in L.idx]
            rows = [[Fraction(int(i == j)) for i in L.idx] for j in L.rows]
            L.cert = lti.certify_channels(L.A, L.B, deltas, x0=x0, output_rows=rows)
            if L.cert is None:
                return None
            for j, box in zip(L.rows, L.cert.boxes):
                c[j] = box.bound
        if all(c[j] < b[j] for j in signals):
            return b, c
        b = {j: max(b[j], c[j] * margin) for j in signals}
    return None


def emit_cert(pb, layers, signals, out_idx, b, c) -> str:
    ns = pb.ns
    K = len(signals)
    flds = pb.states
    eh = [f"e{i}" for i in range(pb.n_eqs)]
    pnames, peqs = E._param_hyps(pb)
    out = [f"import {pb.module}.Spec", "import Dynacert.Linear.Channels",
           "import Dynacert.Compose.AssumeGuarantee", ""]
    out += lean_mod.header(f"Layered certificate for `{pb.model_name}`",
                           "dynacert (layered LTI, assume–guarantee)")
    out += E.LINTERS + ["set_option maxRecDepth 10000", "", f"namespace {ns}.LayeredCert", "",
                        f"open Matrix Set Dynacert Dynacert.Linear Dynacert.Compose {ns}", ""]
    lits = []
    for i, s_ in enumerate(pb.literals):
        out.append(f"theorem lit{i} : ({s_} : ℝ) = {q(Fraction(s_))} := by norm_num")
        lits.append(f"lit{i}")
    out.append("")
    rewrite = ", ".join(peqs + lits)
    ch = [f"hc{i}" for i in range(len(flds))]
    dh = [f"hd{i}" for i in range(len(flds))]
    sig_terms = [f"|s.{flds[j]}|" for j in signals]
    out += [
        "/-! ### Coupling signals: the states each layer reads from the others -/", "",
        f"def sig (s : States) : Fin {K} → ℝ := ![{', '.join(sig_terms)}]",
        f"/-- Assumed bounds. -/\ndef Bsig : Fin {K} → ℚ := {vec([b[j] for j in signals])}",
        f"/-- Guaranteed bounds (strictly smaller). -/\ndef Csig : Fin {K} → ℚ := "
        f"{vec([c[j] for j in signals])}",
        "", "theorem Csig_lt : ∀ i, Csig i < Bsig i := by decide +kernel", ""]
    for li, L in enumerate(layers):
        nL, mL = len(L.idx), len(L.dists) + len(L.coupling)
        zf = [f"s.{flds[i]}" for i in L.idx]
        wf = [f"v.{pb.dists[k]}" for k in L.dists] + [f"s.{flds[j]}" for j in L.coupling]
        zs, ws = [f"z {j}" for j in range(nL)], [f"w {k}" for k in range(mL)]
        rows = [" + ".join(p_ for p_ in (E._lin(L.A[i], zs), E._lin(L.B[i], ws)) if p_ != "0")
                or "0" for i in range(nL)]
        cert = L.cert
        Lt, dt = lean_mod.sum_witness(cert.lmi_L, cert.lmi_d, nL, mL)
        deltas = [pb.dist_bounds[k] for k in L.dists] + [b[j] for j in L.coupling]
        x0 = [pb.x0[i] for i in L.idx]
        x0v = vec(x0)
        label = L.name or "(top level)"
        out += [
            f"/-! ### Layer {li}: `{label}` (states {', '.join(f'`{pb.coords[i].name}`' for i in L.idx)};"
            f" reads {', '.join(f'`{pb.coords[j].name}`' for j in L.coupling) or 'nothing'}) -/", "",
            f"def vec{li} (s : States) : Fin {nL} → ℝ := ![{', '.join(zf)}]",
            f"def dist{li} (s : States) (v : Inputs) : Fin {mL} → ℝ := ![{', '.join(wf)}]",
            f"def model{li} : LTIModel {nL} {mL} where",
            f"  A := {mat(L.A)}", f"  B := {mat(L.B)}", "",
            f"theorem f_apply{li} (z : Fin {nL} → ℝ) (w : Fin {mL} → ℝ) :",
            f"    model{li}.toSystem.f z w = ![{', '.join(rows)}] := by",
            "  funext i", "  fin_cases i <;>",
            f"    simp [LTIModel.toSystem, model{li}, toReal, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring",
            "",
            f"theorem link{li} {{p : Params}} (hp : p.Bound) {{u : ℝ → Inputs}} {{x : ℝ → States}}",
            "    {y : ℝ → Algebraics} {T : ℝ} (h : IsSolutionOn p u x y T) :",
            f"    model{li}.toSystem.IsSolution (fun t => vec{li} (x t)) (fun t => dist{li} (x t) (u t)) T := by",
        ]
        if pnames:
            out.append(f"  obtain {E._conj(pnames)} := hp")
        out += [f"  obtain ⟨dx, {', '.join(ch)}, hder⟩ := h",
                "  refine ⟨?_, fun t ht => ?_⟩",
                "  · refine continuousOn_pi.mpr fun i => ?_", "    fin_cases i"]
        for i in L.idx:
            out.append(f"    · exact {ch[i]}")
        out.append(f"  · obtain ⟨{', '.join(dh)}, {E._conj(eh)}⟩ := hder t ht")
        if rewrite:
            out.append(f"    try simp only [{rewrite}] at {' '.join(eh)}")
        out += ["    rw [hasDerivWithinAt_pi]", "    intro i", "    fin_cases i"]
        zt = [f"(x t).{flds[i]}" for i in L.idx]
        wt = [f"(u t).{pb.dists[k]}" for k in L.dists] + [f"(x t).{flds[j]}" for j in L.coupling]
        for r, i in enumerate(L.idx):
            rhs = " + ".join(p_ for p_ in (E._lin(L.A[r], zt), E._lin(L.B[r], wt))
                             if p_ != "0") or "0"
            lc = E._lc(pb.multipliers[i], eh)
            out += [f"    · show HasDerivWithinAt (fun s => (x s).{flds[i]}) _ (Ici t) t",
                    f"      refine {dh[i]}.congr_deriv ?_",
                    f"      rw [f_apply{li}]",
                    f"      show (dx t).{flds[i]} = {rhs}",
                    f"      linear_combination {lc}" if lc else "      ring"]
        out += [
            "",
            f"def P{li} : Matrix (Fin {nL}) (Fin {nL}) ℚ := {mat(cert.P)}",
            f"def α{li} : ℚ := {q(cert.alpha)}",
            f"def γ{li} : Fin {mL} → ℚ := {vec(cert.gammas)}",
            f"def lmiL{li} : Matrix (Fin {nL} ⊕ Fin {mL}) (Fin {nL} ⊕ Fin {mL}) ℚ :=",
            f"  {Lt}",
            f"def lmiD{li} : Fin {nL} ⊕ Fin {mL} → ℚ :=", f"  {dt}",
            f"def cert{li} : ChannelCert model{li} :=",
            f"  ⟨P{li}, α{li}, γ{li}, by decide +kernel, by decide +kernel, by decide +kernel,",
            f"    ⟨lmiL{li}, lmiD{li}, by decide +kernel, by decide +kernel⟩⟩",
            f"def level{li} : ℚ := {q(cert.level)}",
            f"def δ{li} : Fin {mL} → ℚ := {vec(deltas)}", "",
            f"theorem budget_le{li} :",
            f"    (∑ j, (γ{li} j : ℝ) * ((δ{li} j : ℝ) * (δ{li} j : ℝ))) / (α{li} : ℝ) ≤ (level{li} : ℝ) := by",
            f"  have h : (∑ j, γ{li} j * (δ{li} j * δ{li} j)) / α{li} ≤ level{li} := by decide +kernel",
            "  exact_mod_cast h", "",
        ]
        for k, (j, box) in enumerate(zip(L.rows, cert.boxes)):
            row = [Fraction(int(i == j)) for i in L.idx]
            out += [
                f"/-- `|{pb.coords[j].name}| ≤ {q(box.bound)}` on the layer's invariant set. -/",
                f"def box{li}_{k} : LinearBoxCert P{li} level{li} {vec(row)} ({q(box.bound)}) :=",
                "  ⟨by decide +kernel, by decide +kernel,",
                f"    ⟨{mat(box.L)},", f"     {vec(box.d)},",
                "     by decide +kernel, by decide +kernel⟩⟩", ""]
        ih = [f"i{i}" for i in range(pb.n_init)]
        rw0 = ", ".join(peqs + lits + ih)
        out += [
            f"theorem init{li} {{p : Params}} (hp : p.Bound) {{s : States}} (h0 : Initial p s) :",
            f"    vec{li} s = fun i => ((({x0v} : Fin {nL} → ℚ) i : ℚ) : ℝ) := by",
        ]
        if pnames:
            out.append(f"  obtain {E._conj(pnames)} := hp")
        if pb.n_init:
            out.append(f"  obtain {E._conj(ih)} := h0")
        out += ["  funext i", "  fin_cases i <;>",
                f"    simp [vec{li}{', ' + rw0 if rw0 else ''}] <;> norm_num", "",
                f"theorem init_le{li} :",
                f"    quad (toReal P{li}) (fun i => ((({x0v} : Fin {nL} → ℚ) i : ℚ) : ℝ)) ≤ (level{li} : ℝ) := by",
                "  rw [quad_toReal_cast]",
                f"  exact_mod_cast (by decide +kernel : quad P{li} {x0v} ≤ level{li})", ""]
        # guarantee: assumptions on [0, τ) give the layer's invariant on [0, τ]
        sig_of = {j: s for s, j in enumerate(signals)}
        out += [
            f"/-- Layer {li} guarantee: if the coupling signals respect `Bsig` on `[0, τ)`, the",
            f"layer stays in its invariant set on `[0, τ]`. -/",
            f"theorem guar{li} {{p : Params}} {{u : ℝ → Inputs}} {{x : ℝ → States}} {{y : ℝ → Algebraics}}",
            "    {T : ℝ} (hp : p.Bound) (h : IsSolutionOn p u x y T) (hu : Spec.Admissible u T)",
            "    (h0 : Initial p (x 0)) {τ : ℝ} (hτ : τ ≤ T)",
            "    (hA : ∀ j, ∀ t ∈ Ico 0 τ, sig (x t) j ≤ (Bsig j : ℝ)) :",
            f"    ∀ t ∈ Icc 0 τ, quad (toReal P{li}) (vec{li} (x t)) ≤ (level{li} : ℝ) := by",
            f"  have hx := (link{li} hp h).mono hτ",
            f"  have hw : ∀ t ∈ Ico 0 τ, cert{li}.energy (dist{li} (x t) (u t)) ≤",
            f"      ∑ j, (γ{li} j : ℝ) * ((δ{li} j : ℝ) * (δ{li} j : ℝ)) := by",
            "    intro t ht",
            "    have hut := hu t ⟨ht.1, ht.2.trans_le hτ⟩",
        ]
        for j in L.coupling:
            out.append(f"    have ha{sig_of[j]} := hA {sig_of[j]} t ht")
        out += [
            f"    simp only [sig, Bsig] at {' '.join(f'ha{sig_of[j]}' for j in L.coupling)}"
            if L.coupling else "",
            f"    refine cert{li}.energy_le_of_abs_le (δ := δ{li}) fun j => ?_",
            f"    fin_cases j <;> simp [dist{li}, δ{li}] <;> simp_all",
            f"  have h0' : quad (toReal cert{li}.P) (vec{li} (x 0)) ≤ (level{li} : ℝ) := by",
            f"    rw [init{li} hp h0]; exact init_le{li}",
            f"  exact cert{li}.invariant hx hw h0' budget_le{li}", ""]
    # composition
    owner_box = {}
    for li, L in enumerate(layers):
        for k, j in enumerate(L.rows):
            owner_box[j] = (li, k)
    out += [
        "/-! ### Composition -/", "",
        "/-- Every layer's guarantee, as one statement over the coupling signals. -/",
        "theorem guarantee {p : Params} {u : ℝ → Inputs} {x : ℝ → States} {y : ℝ → Algebraics}",
        "    {T : ℝ} (hp : p.Bound) (h : IsSolutionOn p u x y T) (hu : Spec.Admissible u T)",
        "    (h0 : Initial p (x 0)) :",
        "    ∀ τ ∈ Icc 0 T, (∀ j, ∀ t ∈ Ico 0 τ, sig (x t) j ≤ (Bsig j : ℝ)) →",
        "      ∀ i, ∀ t ∈ Icc 0 τ, sig (x t) i ≤ (Csig i : ℝ) := by",
        "  intro τ hτ hA i t ht",
        "  fin_cases i",
    ]
    for s, j in enumerate(signals):
        li, k = owner_box[j]
        out += [f"  · have hb := box{li}_{k}.abs_le (guar{li} hp h hu h0 hτ.2 hA t ht)",
                f"    simp only [vec{li}, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at hb",
                "    simp only [sig, Csig]",
                "    norm_num at hb ⊢",
                "    linarith"]
    out += [
        "",
        "/-- **Mutual first exit.** The coupling signals stay within `Csig` on all of `[0, T]`. -/",
        "theorem signals {p : Params} {u : ℝ → Inputs} {x : ℝ → States} {y : ℝ → Algebraics}",
        "    {T : ℝ} (hp : p.Bound) (h : IsSolutionOn p u x y T) (hu : Spec.Admissible u T)",
        "    (h0 : Initial p (x 0)) : ∀ i, ∀ t ∈ Icc 0 T, sig (x t) i ≤ (Csig i : ℝ) := by",
        "  have hcont : ∀ i, ContinuousOn (fun t => sig (x t) i) (Icc 0 T) := by",
        f"    obtain ⟨dx, {', '.join(ch)}, -⟩ := h",
        "    intro i", "    fin_cases i",
    ]
    for j in signals:
        out.append(f"    · exact continuous_abs.comp_continuousOn {ch[j]}")
    out += [
        "  exact assume_guarantee (s := fun i t => sig (x t) i) hcont",
        "    (fun i => by exact_mod_cast Csig_lt i) (guarantee hp h hu h0)", ""]
    # final claim
    bounds = []
    for k, o in sorted(out_idx.items()):
        li, bk = owner_box[o]
        bounds.append(layers[li].cert.boxes[bk].bound)
    bvec = vec(bounds)
    out += [
        f"/-- **Certified (layered).** The claim of `Spec.lean` holds with the bounds `{bvec}`. -/",
        f"theorem certified : Spec.Claim {bvec} := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  have hS := signals hp h hu h0",
        "  have hA : ∀ j, ∀ t ∈ Ico 0 T, sig (x t) j ≤ (Bsig j : ℝ) := fun j t ht =>",
        "    (hS j t ⟨ht.1, ht.2.le⟩).trans (by exact_mod_cast (Csig_lt j).le)",
    ]
    for li in range(len(layers)):
        out.append(f"  have hV{li} := guar{li} hp h hu h0 le_rfl hA")
    ks = sorted(out_idx)
    out.append("  intro t ht")
    if len(ks) > 1:
        out.append(f"  refine ⟨{', '.join('?_' for _ in ks)}⟩")
    for k in ks:
        li, bk = owner_box[out_idx[k]]
        pre = "  · " if len(ks) > 1 else "  "
        ind = "    " if len(ks) > 1 else "  "
        out += [f"{pre}have hb := box{li}_{bk}.abs_le (hV{li} t ht)",
                f"{ind}simp only [vec{li}, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at hb",
                f"{ind}norm_num at hb ⊢",
                f"{ind}linarith"]
    out += ["", f"end {ns}.LayeredCert", ""]
    return "\n".join(l for l in out if l is not None)


def run(prob, verbose=print) -> dict:
    pb, layers, signals, out_idx, owner = layered_problem(prob)
    verbose(f"layers: " + "; ".join(f"{L.name or '(top)'}: {[pb.coords[i].name for i in L.idx]}"
                                     f" reads {[pb.coords[j].name for j in L.coupling]}"
                                     for L in layers))
    found = search(pb, layers, signals)
    if found is None:
        raise pipeline.CertError("layered: no consistent coupling bounds (the layers are too "
                                 "strongly coupled for peak-bound composition; try lmi)")
    b, c = found
    verbose("coupling bounds: " + ", ".join(
        f"|{pb.coords[j].name}| ≤ {float(c[j]):.4g} (assumed {float(b[j]):.4g})" for j in signals))
    out = prob.cert_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / "Model.lean").write_text(prob.lean_src)
    (out / "Spec.lean").write_text(E.emit_spec(pb))
    (out / "LayeredCert.lean").write_text(emit_cert(pb, layers, signals, out_idx, b, c))
    mod = f"Certs.{pb.ns}.LayeredCert"
    verbose(f"lean: lake build {mod}")
    pipeline.lake("build", mod, cwd=prob.root)
    ax = pipeline.axioms(mod, f"{pb.ns}.LayeredCert.certified", root=prob.root)
    if not ax <= pipeline.ALLOWED_AXIOMS:
        raise pipeline.CertError(f"disallowed axioms: {ax - pipeline.ALLOWED_AXIOMS}")
    bounds = {}
    for k, o in sorted(out_idx.items()):
        L = next(L for L in layers if o in L.idx)
        bounds[pb.outputs[k].name] = L.cert.boxes[L.rows.index(o)].bound
    mono = pipeline.lti_search(pb)
    side = {
        "model": pb.model_name, "method": "layered-lti",
        "theorem": f"{pb.ns}.LayeredCert.certified", "axioms": sorted(ax),
        "layers": [{"component": L.name, "states": [pb.coords[i].name for i in L.idx],
                    "reads": [pb.coords[j].name for j in L.coupling],
                    "level": q(L.cert.level)} for L in layers],
        "coupling": {pb.coords[j].name: {"assumed": q(b[j]), "guaranteed": q(c[j])}
                     for j in signals},
        "bounds": {k: q(v) for k, v in bounds.items()},
        "monolithic_bounds": ({o.name: q(bx.bound) for o, bx in zip(pb.outputs, mono.boxes)}
                              if mono else None),
    }
    (out / "layered.json").write_text(json.dumps(side, indent=1))
    return {"dir": str(out), "sidecar": side, "bounds": bounds}
