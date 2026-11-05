"""Lean emission for switched linear models: `SwitchedCert.lean` (link + proof).

The claim is `Spec.lean` from `emit_lti.emit_spec`, unchanged: the faithful classical-solution
claim of the model's own equations, `if`-expressions included. The certificate is a
`PolytopicCert` over the mode matrices `A_m` (one common storage `zᵀPz`), and the link
proves, at every `t ∈ [0, T)`,

    ż = Σ_m wt t m • (A_m z + B w),   wt t m = 1 if mode m is active at t, else 0,

where the indicator `weights` is written with the model's own conditions, copied verbatim from
rumoca's `Equations` (same binder names), so that one `split_ifs` decides the equations and the
weights together. Each branch is then closed by the active mode's `linear_combination`
multipliers (the generated proof tries each mode's multipliers; any one that `ring` accepts is
a proof). `PolytopicCert.invariant` takes time-varying weights, so the switching signal needs
no new library theorem.
"""

from __future__ import annotations

from fractions import Fraction

from . import emit_lti as E
from . import lean
from .emit_lti import LINTERS, _c, _conj, _coord_expr, _fold, _lc, _lin, _param_hyps
from .lean import mat, q, vec


def _branch_indicator(conds: list[str], j: int) -> str:
    """`if c₀ then v₀ else if c₁ then v₁ else … v_k` with `v_j = 1` and every other `v = 0`."""
    vals = ["(1 : ℝ)" if i == j else "(0 : ℝ)" for i in range(len(conds) + 1)]
    s = vals[-1]
    for c, v in reversed(list(zip(conds, vals))):
        s = f"if {c} then {v} else {s}"
    return f"({s})"


def mode_weight(spb, k: int) -> str:
    parts = [_branch_indicator(sw.conds, j) for sw, j in zip(spb.switches, spb.modes[k])]
    return " * ".join(parts) if parts else "(1 : ℝ)"


def _order(binders: str) -> list[str]:
    """Roles in the order of the `Equations` binders."""
    import re

    out = []
    for names, ty in re.findall(r"\(([^():]+):\s*([^()]+)\)", binders):
        ty = ty.strip()
        role = {"ℝ": ["t"], "Params": ["p"], "Inputs": ["u"], "States": ["x", "dx"],
                "Algebraics": ["y"]}[ty]
        out += role[:len(names.split())]
    return out


def emit_cert(spb, cert) -> str:
    pb = spb.base
    n, m = len(pb.coords), len(pb.dists)
    ns = pb.ns
    K = len(spb.modes)
    nst = len(pb.states)
    names = spb.names
    order = _order(spb.binders)
    pnames, peqs = _param_hyps(pb)
    phyp = "p.Bound"
    eh = [f"e{i}" for i in range(pb.n_eqs)]
    dr = [r for r in pb.refs if r.deriv]
    rs = [r for r in pb.refs if r.start is not None]
    box = pb.init_box
    imp = "{" + "} {".join(spb.binders.strip()[1:-1].split(") (")) + "}"
    args = " ".join(names[r] for r in order)
    targs = " ".join({"t": "t", "p": "p", "u": "(u t)", "x": "(x t)", "dx": "(dx t)",
                      "y": "(y t)"}[r] for r in order)
    X, DX, U = names["x"], names["dx"], names["u"]
    out = [f"import {pb.module}.Spec",
           "import Dynacert.Linear.Funnel" if box is not None else "import Dynacert.Linear.Polytopic",
           ""]
    out += lean.header(f"Switched certificate for `{pb.model_name}`",
                       "dynacert (switched linear modes)")
    out += LINTERS + [
        "set_option maxRecDepth 10000",
        "",
        f"namespace {ns}.SwitchedCert",
        "",
        f"open Matrix Set Dynacert Dynacert.Linear {ns}",
        "",
        "/-! ### Modes",
        "",
        "The if-expressions of `Equations`, grouped into switches by their condition chain; a mode",
        "picks one branch of every switch. In mode `m` the model, in coordinates `z`, is",
        "`ż = A_m z + B w`:",
        "",
    ]
    for k in range(K):
        out.append(f"* mode {k}: `{spb.mode_text(k)}`")
    out += [
        "-/",
        "",
        "/-- Coordinates: " + ", ".join(f"`{c.name}`" for c in pb.coords) + ". -/",
        ("noncomputable " if any(Fraction(tm.coeff).denominator != 1
                                 for c in pb.coords for tm in c.terms) else "")
        + f"def vec (s : States) (v : Inputs) : Fin {n} → ℝ :=",
        "  ![" + ", ".join(E._coord_def(c) for c in pb.coords) + "]",
        "/-- Disturbance channels: " + ", ".join(f"`{d}`" for d in pb.dists) + ". -/",
        f"def dist (v : Inputs) : Fin {m} → ℝ := ![" + ", ".join(f"v.{d}" for d in pb.dists) + "]",
        "",
        "/-- Mode matrices `A_m`. -/",
        f"def As : Fin {K} → Matrix (Fin {n}) (Fin {n}) ℚ :=",
        "  ![" + ",\n    ".join(mat(Av) for Av in spb.As) + "]",
        f"def Bm : Matrix (Fin {n}) (Fin {m}) ℚ := {mat(pb.B)}",
        "",
        "/-- Indicator of the active mode, written with the model's own conditions (verbatim",
        "from `Equations`, same binders). -/",
        f"noncomputable def weights {spb.binders} : Fin {K} → ℝ :=",
        "  ![" + ",\n    ".join(mode_weight(spb, k) for k in range(K)) + "]",
        "",
        f"theorem weights_nonneg {spb.binders} : ∀ i, 0 ≤ weights {args} i := by",
        "  intro i",
        "  fin_cases i",
    ]
    for k in range(K):
        out += [f"  · show (0 : ℝ) ≤ {mode_weight(spb, k)}",
                "    split_ifs <;> norm_num"]
    wsum = " + ".join(mode_weight(spb, k) for k in range(K))
    out += [
        "",
        f"theorem weights_sum {spb.binders} : ∑ i, weights {args} i = 1 := by",
        f"  have h : {wsum} = 1 := by",
        "    split_ifs <;> norm_num",
        "  simpa [weights, Fin.sum_univ_succ, add_assoc] using h",
        "",
    ]
    zs = [f"z {j}" for j in range(n)]
    wsym = [f"w {k}" for k in range(m)]
    rows = []
    for i in range(n):
        parts = [f"wt {sg} * ({_lin(Av[i], zs)})" for sg, Av in enumerate(spb.As)
                 if _lin(Av[i], zs) != "0"]
        bp = _lin(pb.B[i], wsym)
        if bp != "0":
            parts.append(bp)
        rows.append(" + ".join(parts) or "0")
    out += [
        f"theorem f_apply (wt : Fin {K} → ℝ) (z : Fin {n} → ℝ) (w : Fin {m} → ℝ) :",
        "    (∑ i, wt i • toReal (As i)) *ᵥ z + toReal Bm *ᵥ w = ![" + ", ".join(rows) + "] := by",
        "  funext i",
        "  fin_cases i <;>",
        "    simp [As, Bm, toReal, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring",
        "",
    ]
    lits = []
    for i, s_ in enumerate(pb.literals):
        out.append(f"theorem lit{i} : ({s_} : ℝ) = {q(Fraction(s_))} := by norm_num")
        lits.append(f"lit{i}")
    if pb.literals:
        out.append("")
    rewrite = ", ".join(peqs + lits)
    ref_der = {r.fld: r.deriv for r in dr}

    def coord_b(c):     # coordinate in the Equations binders
        return " + ".join(f"{_c(tm.coeff)} * {X if tm.kind == 'x' else U}.{tm.fld}"
                          for tm in c.terms)

    def dval(c, xs, us):
        return " + ".join(f"{_c(tm.coeff)} * {xs}.{tm.fld}" if tm.kind == "x" else
                          f"{_c(tm.coeff)} * {us}.{ref_der[tm.fld]}" for tm in c.terms)

    def rhs(i, wfun, zt, wt):
        parts = [f"({wfun(sg)}) * ({_lin(Av[i], zt)})" for sg, Av in enumerate(spb.As)
                 if _lin(Av[i], zt) != "0"]
        bp = _lin(pb.B[i], wt)
        if bp != "0":
            parts.append(bp)
        return " + ".join(parts) or "0"

    zb = [coord_b(c) for c in pb.coords]
    wb = [f"{U}.{d}" for d in pb.dists]
    concl = [f"{dval(c, DX, U)} = {rhs(i, lambda sg: f'weights {args} {sg}', zb, wb)}"
             for i, c in enumerate(pb.coords)]
    shown = [f"{dval(c, DX, U)} = {rhs(i, lambda sg: mode_weight(spb, sg), zb, wb)}"
             for i, c in enumerate(pb.coords)]

    def lc_try(i):
        cands = []
        for pbk in spb.problems:
            lc = _lc(pbk.multipliers[i], eh)
            t = f"linear_combination {lc}" if lc else "ring"
            if t not in cands:
                cands.append(t)
        return "first | " + " | ".join(cands)

    out += [
        "/-- **Pointwise link.** At one instant, the model's equations give each coordinate",
        "derivative as the active mode's linear right-hand side. The `if`-expressions of the",
        "equations and of `weights` are split together. -/",
        f"theorem step {imp} (hp : {names['p']}.Bound)",
        f"    (h : Equations {args}) :",
        "    " + " ∧\n    ".join(concl) + " := by",
    ]
    if pnames:
        out.append(f"  obtain {_conj(pnames)} := hp")
    if pb.n_eqs:
        out.append(f"  obtain {_conj(eh)} := h")
    out.append("  show " + " ∧\n    ".join(shown))
    hyps = " ".join(f"e{i}" for i in spb.if_eqs)
    out.append(f"  split_ifs at {hyps} ⊢ <;>")
    if rewrite and pb.n_eqs:
        out.append(f"    (try simp only [{rewrite}] at {' '.join(eh)}) <;>")
    if n == 1:
        out.append(f"    ({lc_try(0)})")
    else:
        out.append("    exact ⟨" + ",\n      ".join(f"by {lc_try(i)}" for i in range(n)) + "⟩")
    out.append("")
    # link
    ch = {s_: f"hc{i}" for i, s_ in enumerate(pb.states)}
    dh = {s_: f"hd{i}" for i, s_ in enumerate(pb.states)}
    rc = {r.fld: f"hrc{i}" for i, r in enumerate(dr)}
    rd = {r.fld: f"hrd{i}" for i, r in enumerate(dr)}

    def cont_term(tm):
        h = ch[tm.fld] if tm.kind == "x" else rc[tm.fld]
        return f"(continuousOn_const.mul {h})"

    def der_term(tm):
        h = dh[tm.fld] if tm.kind == "x" else rd[tm.fld]
        return f"({h}.const_mul {_c(tm.coeff)})"

    sh = [f"s{i}" for i in range(n)]
    out += [
        "/-- **Link.** Along a solution, the coordinates obey `ż = Σ_m wt t m • (A_m z + B w)`",
        "with `wt t` the indicator of the mode active at `t`. -/",
        f"theorem link {{p : Params}} (hp : {phyp}) {{u : ℝ → Inputs}} {{x : ℝ → States}}",
        "    {y : ℝ → Algebraics} {T : ℝ} (h : IsSolutionOn p u x y T)",
        "    (hr : Spec.References u T) :",
        f"    ∃ wt : ℝ → Fin {K} → ℝ, (∀ t ∈ Ico 0 T, ∀ i, 0 ≤ wt t i) ∧",
        "      (∀ t ∈ Ico 0 T, ∑ i, wt t i = 1) ∧",
        "      ContinuousOn (fun t => vec (x t) (u t)) (Icc 0 T) ∧ ∀ t ∈ Ico 0 T,",
        "        HasDerivWithinAt (fun t => vec (x t) (u t))",
        "          ((∑ i, wt t i • toReal (As i)) *ᵥ vec (x t) (u t) + toReal Bm *ᵥ dist (u t))",
        "          (Ici t) t := by",
        f"  obtain ⟨dx, {', '.join(ch[s_] for s_ in pb.states)}, hder⟩ := h",
    ]
    if dr:
        out.append(f"  obtain ⟨{', '.join(rc[r.fld] for r in dr)}, hrder⟩ := hr")
    out += [
        f"  refine ⟨fun t => weights {targs}, fun t _ => weights_nonneg {targs},",
        f"    fun t _ => weights_sum {targs}, ?_, fun t ht => ?_⟩",
        "  · refine continuousOn_pi.mpr fun i => ?_",
        "    fin_cases i",
    ]
    for c in pb.coords:
        out += [f"    · show ContinuousOn (fun s => {_coord_expr(c, 's')}) (Icc 0 T)",
                f"      exact {_fold([cont_term(tm) for tm in c.terms], 'add')}"]
    out.append(f"  · obtain ⟨{', '.join(dh[s_] for s_ in pb.states)}, hE⟩ := hder t ht")
    if dr:
        out.append(f"    obtain {_conj([rd[r.fld] for r in dr])} := hrder t ht")
    out += [f"    obtain {_conj(sh)} := step hp hE",
            "    rw [hasDerivWithinAt_pi]", "    intro i", "    fin_cases i"]
    zt = [_coord_expr(c, "t") for c in pb.coords]
    wt = [f"(u t).{d}" for d in pb.dists]
    for i, c in enumerate(pb.coords):
        out += [
            f"    · show HasDerivWithinAt (fun s => {_coord_expr(c, 's')}) _ (Ici t) t",
            f"      refine ({_fold([der_term(tm) for tm in c.terms], 'add')}).congr_deriv ?_",
            "      rw [f_apply]",
            f"      show {dval(c, '(dx t)', '(u t)')} = "
            f"{rhs(i, lambda sg: f'weights {targs} {sg}', zt, wt)}",
            f"      exact s{i}",
        ]
    out.append("")
    # certificate data (as the polytopic branch of emit_lti)
    out += [
        "/-! ### Common storage `V z = zᵀ P z` and per-channel rates for every mode -/",
        "",
        f"def P : Matrix (Fin {n}) (Fin {n}) ℚ := {mat(cert.P)}",
        f"def α : ℚ := {q(cert.alpha)}",
        f"def γ : Fin {m} → ℚ := {vec(cert.gammas)}",
        "",
    ]
    for sg, (Lw, dw) in enumerate(cert.witnesses):
        Lt, dt = lean.sum_witness(Lw, dw, n, m)
        out += [
            f"def lmi{sg} : PSDWitness (channelLmi (As {sg}) Bm P α γ) :=",
            f"  ⟨{Lt},",
            f"   {dt},",
            "   by decide +kernel, by decide +kernel⟩",
            "",
        ]
    out += ["def lmis : ∀ i, PSDWitness (channelLmi (As i) Bm P α γ)"]
    for sg in range(K):
        out.append(f"  | ⟨{sg}, _⟩ => lmi{sg}")
    out += [
        f"  | ⟨n + {K}, h⟩ => absurd h (by omega)",
        "",
        "def cert : PolytopicCert As Bm :=",
        "  ⟨P, α, γ, by decide +kernel, by decide +kernel, by decide +kernel, lmis⟩",
        "",
        "/-- Invariant level `max(Σγⱼδⱼ²/α, V(z₀))`. -/",
        f"def level : ℚ := {q(cert.level)}",
        f"def δ : Fin {m} → ℚ := {vec(pb.dist_bounds)}",
        "",
        "theorem budget_le :",
        "    (∑ j, (γ j : ℝ) * ((δ j : ℝ) * (δ j : ℝ))) / (α : ℝ) ≤ (level : ℝ) := by",
        "  have h : (∑ j, γ j * (δ j * δ j)) / α ≤ level := by decide +kernel",
        "  exact_mod_cast h",
        "",
    ]
    swo = getattr(cert, "switched_boxes", {}) or {}
    for k, (o, b) in enumerate(zip(pb.outputs, cert.boxes)):
        if k in swo:
            bk, mboxes = swo[k]
            for r, bb in _distinct_rows(spb, k, mboxes):
                out += [
                    f"/-- `|{o.name}| ≤ {q(bk)}` on `{{zᵀPz ≤ level}}` where `{o.name}` has the row "
                    f"`{vec(spb.problems[r].outputs[k].row)}` (mode {r}). -/",
                    f"def box{k}_{r} : LinearBoxCert P level {vec(spb.problems[r].outputs[k].row)} "
                    f"({q(bk)}) :=",
                    "  ⟨by decide +kernel, by decide +kernel,",
                    f"    ⟨{mat(bb.L)},",
                    f"     {vec(bb.d)},",
                    "     by decide +kernel, by decide +kernel⟩⟩",
                    "",
                ]
            continue
        out += [
            f"/-- `|{o.name}| ≤ {q(b.bound)}` on `{{zᵀPz ≤ level}}`. -/",
            f"def box{k} : LinearBoxCert P level {vec(o.row)} ({q(b.bound)}) :=",
            "  ⟨by decide +kernel, by decide +kernel,",
            f"    ⟨{mat(b.L)},",
            f"     {vec(b.d)},",
            "     by decide +kernel, by decide +kernel⟩⟩",
            "",
        ]
    ih = [f"i{i}" for i in range(pb.n_init)]
    rh = [f"r{i}" for i in range(len(rs))]
    x0v = vec(pb.x0)
    if box is not None:
        out += E._init_box_lines(pb, cert, box, phyp, pnames, rs, lits, peqs)
    else:
        out += [
            f"theorem init {{p : Params}} (hp : {phyp}) {{s : States}} {{v : Inputs}} (h0 : Initial p s)",
            "    (hr0 : " + (" ∧ ".join(f"v.{r.fld} = {_c(r.start)}" for r in rs) or "True") + ") :",
            f"    vec s v = fun i => ((({x0v} : Fin {n} → ℚ) i : ℚ) : ℝ) := by",
        ]
        if pnames:
            out.append(f"  obtain {_conj(pnames)} := hp")
        if pb.n_init:
            out.append(f"  obtain {_conj(ih)} := h0")
        if rs:
            out.append(f"  obtain {_conj(rh)} := hr0")
        rw0 = ", ".join(peqs + lits + ih + rh)
        out += [
            "  funext i",
            "  fin_cases i <;>",
            f"    simp [vec{', ' + rw0 if rw0 else ''}] <;> norm_num",
            "",
            "theorem init_le :",
            f"    quad (toReal P) (fun i => ((({x0v} : Fin {n} → ℚ) i : ℚ) : ℝ)) ≤ (level : ℝ) := by",
            "  rw [quad_toReal_cast]",
            f"  exact_mod_cast (by decide +kernel : quad P {x0v} ≤ level)",
            "",
        ]
    for k, o in enumerate(pb.outputs):
        if k in swo:
            out += _switched_output(spb, k, o, swo[k], phyp, pnames, eh, rewrite, zt, n, nst)
            continue
        rowv = vec(o.row)
        out += [
            f"theorem out{k} {{p : Params}} (hp : {phyp}) {{u : ℝ → Inputs}} {{x : ℝ → States}}",
            f"    {{y : ℝ → Algebraics}} {{T : ℝ}} (h : IsSolutionOn p u x y T) {{t : ℝ}}",
            f"    (ht : t ∈ {'Icc' if o.kind == 'state' else 'Ico'} 0 T) :",
            f"    {o.lean_term} = (fun i => (({rowv} : Fin {n} → ℚ) i : ℝ)) ⬝ᵥ vec (x t) (u t) := by",
            f"  have hdot : (fun i => (({rowv} : Fin {n} → ℚ) i : ℝ)) ⬝ᵥ vec (x t) (u t) =",
            f"      {_lin(o.row, zt)} := by",
            "    simp [vec, dotProduct, Fin.sum_univ_succ] <;> ring",
            "  rw [hdot]",
        ]
        if o.kind == "algebraic" and _lc(o.mult, eh):
            if pnames:
                out.append(f"  obtain {_conj(pnames)} := hp")
            out.append("  obtain ⟨dx, hder⟩ := h")
            out.append(f"  have hE := (hder{'.2' * nst} t ht){'.2' * nst}")
            out.append(f"  obtain {_conj(eh)} := hE")
            if rewrite:
                out.append(f"  try simp only [{rewrite}] at {' '.join(eh)}")
        lc = _lc(o.mult, eh)
        out.append(f"  linear_combination {lc}" if lc else "  ring")
        out.append("")
    bvec = vec([b.bound for b in cert.boxes])
    coords = ", ".join(f"`{c.name}`" for c in pb.coords)
    out += [
        "/-- **Tube.** Under the hypotheses of `Spec.Claim`, the error-frame state",
        f"`z = vec (x t) (u t)` (coordinates {coords}) stays in the certified ellipsoid",
        "`zᵀ P z ≤ level` on `[0, T]`, whatever the switching. -/",
        "theorem tube : ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics)",
        f"    (T : ℝ), {phyp} → IsSolutionOn p u x y T → Spec.Admissible u T →",
        "    Spec.References u T → Spec.ReferenceStart u → "
        + ("Spec.InitialSet p (x 0) →" if box is not None else "Initial p (x 0) →"),
        "    ∀ t ∈ Icc 0 T, quad (toReal P) (vec (x t) (u t)) ≤ (level : ℝ) := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  obtain ⟨wt, hwt, hsum, hc, hx⟩ := link hp h hr",
        "  have hw : ∀ t ∈ Ico 0 T, cert.energy (dist (u t)) ≤",
        "      ∑ j, (γ j : ℝ) * ((δ j : ℝ) * (δ j : ℝ)) := by",
        "    intro t ht",
        "    have hut := hu t ht",
        "    refine cert.energy_le_of_abs_le (δ := δ) fun j => ?_",
        "    fin_cases j <;> simp [dist, δ] <;> simp_all",
        "  have h0' : quad (toReal cert.P) (vec (x 0) (u 0)) ≤ (level : ℝ) := by",
        ("    exact (init_V0 hp h0 hr0).trans (by exact_mod_cast V0_le)" if box is not None else
         "    rw [init hp h0 hr0]; exact init_le"),
        "  exact cert.invariant (wt := wt) hc hx hwt hsum hw h0' budget_le",
        "",
        f"/-- **Certified.** The claim of `Spec.lean` holds with the bounds `{bvec}`. -/",
        f"theorem certified : Spec.Claim {bvec} := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  have hV := tube p u x y T hp h hu hr hr0 h0",
    ]
    groups = []
    for rng, kind in (("Icc", "state"), ("Ico", "algebraic")):
        ks = [k for k, o in enumerate(pb.outputs) if o.kind == kind]
        if ks:
            groups.append((rng, ks))
    if len(groups) > 1:
        out.append("  refine ⟨?_, ?_⟩")
    for rng, ks in groups:
        ind = "    " if len(groups) > 1 else "  "
        pre = "  · " if len(groups) > 1 else "  "
        tt = "ht" if rng == "Icc" else "⟨ht.1, ht.2.le⟩"
        out.append(f"{pre}intro t ht")
        if len(ks) > 1:
            out.append(f"{ind}refine ⟨{', '.join('?_' for _ in ks)}⟩")
        for k in ks:
            b = f"{ind}· " if len(ks) > 1 else ind
            if k in swo:
                out.append(f"{b}exact out{k} hp h ht (hV t {tt})")
            else:
                out.append(f"{b}rw [out{k} hp h ht]; exact box{k}.abs_le (hV t {tt})")
    if box is not None:
        out += _funnel_lines(pb, cert, phyp)
    out += ["", f"end {ns}.SwitchedCert", ""]
    return "\n".join(out)


def _distinct_rows(spb, k, mboxes):
    """(mode, box) for the first mode of every distinct row of output k."""
    seen, out = [], []
    for r, bb in enumerate(mboxes):
        row = list(spb.problems[r].outputs[k].row)
        if row not in seen:
            seen.append(row)
            out.append((r, bb))
    return out


def _switched_output(spb, k, o, sb, phyp, pnames, eh, rewrite, zt, n, nst) -> list[str]:
    """`|output| ≤ b` from the ellipsoid, splitting the output's own if-expressions: in every
    mode the output is that mode's row in the coordinates."""
    bk, mboxes = sb
    rows = _distinct_rows(spb, k, mboxes)
    out = [
        f"/-- `|{o.name}| ≤ {q(bk)}` on the ellipsoid: in every mode `{o.name}` is that mode's",
        "linear function of the coordinates, each bounded by its own box certificate. -/",
        f"theorem out{k} {{p : Params}} (hp : {phyp}) {{u : ℝ → Inputs}} {{x : ℝ → States}}",
        f"    {{y : ℝ → Algebraics}} {{T : ℝ}} (h : IsSolutionOn p u x y T) {{t : ℝ}}",
        "    (ht : t ∈ Ico 0 T) (hV : quad (toReal P) (vec (x t) (u t)) ≤ (level : ℝ)) :",
        f"    |{o.lean_term}| ≤ (({q(bk)} : ℚ) : ℝ) := by",
    ]
    for r, _ in rows:
        row = spb.problems[r].outputs[k].row
        out += [
            f"  have ob{r} := box{k}_{r}.abs_le hV",
            f"  have od{r} : (fun i => (({vec(row)} : Fin {n} → ℚ) i : ℝ)) ⬝ᵥ vec (x t) (u t) =",
            f"      {_lin(row, zt)} := by",
            "    simp [vec, dotProduct, Fin.sum_univ_succ] <;> ring",
            f"  rw [od{r}] at ob{r}",
        ]
    if pnames:
        out.append(f"  obtain {_conj(pnames)} := hp")
    out += ["  obtain ⟨dx, hder⟩ := h",
            f"  have hE := (hder{'.2' * nst} t ht){'.2' * nst}",
            f"  obtain {_conj(eh)} := hE"]
    hyps = " ".join(f"e{i}" for i in spb.if_eqs)
    out.append(f"  split_ifs at {hyps} <;>")
    if rewrite:
        out.append(f"    (try simp only [{rewrite}] at {' '.join(eh)}) <;>")
    cands = []
    rowidx = {tuple(spb.problems[r].outputs[k].row): r for r, _ in rows}
    for pbm in spb.problems:
        om = pbm.outputs[k]
        r = rowidx[tuple(om.row)]
        lc = _lc(om.mult, eh)
        prf = f"linear_combination {lc}" if lc else "ring"
        c = f"(rw [show {o.lean_term} = {_lin(om.row, zt)} by {prf}]; exact ob{r})"
        if c not in cands:
            cands.append(c)
    out.append("    first\n    | " + "\n    | ".join(cands))
    out.append("")
    return out


def _funnel_lines(pb, cert, phyp) -> list[str]:
    fc = E.funnel_constants(pb, cert)
    V0, a, r, b = (f"(({q(fc[x])} : ℚ) : ℝ)" for x in ("V0", "alpha", "rate", "budget"))
    coords = ", ".join(f"`{c.name}`" for c in pb.coords)
    return [
        "",
        "/-- The disturbance budget `Σⱼ γⱼ δⱼ²`. -/",
        "theorem budget_eq :",
        f"    ∑ j, (γ j : ℝ) * ((δ j : ℝ) * (δ j : ℝ)) = {b} := by",
        f"  have h : ∑ j, γ j * (δ j * δ j) = {q(fc['budget'])} := by decide +kernel",
        "  exact_mod_cast h",
        "",
        "/-- **Funnel.** Under the hypotheses of `Spec.Claim`, the storage of the error-frame",
        f"state `z = vec (x t) (u t)` (coordinates {coords}) obeys",
        "`zᵀPz ≤ V₀ e^{-αt} + (γμ/α)(1 - e^{-αt})` on `[0, T]`, whatever the switching. -/",
        "theorem funnel : ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics)",
        f"    (T : ℝ), {phyp} → IsSolutionOn p u x y T → Spec.Admissible u T →",
        "    Spec.References u T → Spec.ReferenceStart u → Spec.InitialSet p (x 0) →",
        "    ∀ t ∈ Icc 0 T, quad (toReal P) (vec (x t) (u t)) ≤",
        f"      {V0} * Real.exp (-{a} * t) + {r} * (1 - Real.exp (-{a} * t)) := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  obtain ⟨wt, hwt, hsum, hc, hx⟩ := link hp h hr",
        f"  have hw : ∀ t ∈ Ico 0 T, cert.energy (dist (u t)) ≤ {b} := by",
        "    intro t ht",
        "    have hut := hu t ht",
        "    refine (cert.energy_le_of_abs_le (δ := δ) fun j => ?_).trans_eq budget_eq",
        "    fin_cases j <;> simp [dist, δ] <;> simp_all",
        "  exact cert.funnel (wt := wt) hc hx hwt hsum hw (init_V0 hp h0 hr0) (by decide +kernel)",
    ]


def sidecar(spb, cert, theorem: str, axioms, source_hash: str) -> dict:
    pb = spb.base
    side = {
        "model": pb.model_name, "ns": pb.ns, "method": "switched-lti",
        "modes": [{"choice": list(ch), "condition": spb.mode_text(k),
                   "A": [[q(v) for v in r] for r in spb.As[k]]}
                  for k, ch in enumerate(spb.modes)],
        "switches": [{"conditions": sw.conds, "equations": sw.eqs} for sw in spb.switches],
        "coords": [c.name for c in pb.coords],
        "B": [[q(v) for v in r] for r in pb.B],
        "P": [[q(v) for v in r] for r in cert.P], "level": q(cert.level),
        "alpha": q(cert.alpha), "gammas": [q(g) for g in cert.gammas],
        "x0": [q(v) for v in pb.x0],
        "disturbances": [{"name": n_, "bound": q(b)} for n_, b in zip(pb.dists, pb.dist_bounds)],
        "outputs": [{"name": o.name, "row": [q(v) for v in o.row], "bound": q(b.bound)}
                    | ({"rows_by_mode": [[q(v) for v in p_.outputs[k].row] for p_ in spb.problems]}
                       if k in spb.switched_outputs else {})
                    for k, (o, b) in enumerate(zip(pb.outputs, cert.boxes))],
        "bounds": {o.name: q(b.bound) for o, b in zip(pb.outputs, cert.boxes)},
        "theorem": theorem, "tube": theorem.rsplit(".", 1)[0] + ".tube",
        "axioms": sorted(axioms), "source_hash": source_hash,
    }
    if pb.init_box is not None:
        fc = E.funnel_constants(pb, cert)
        side["funnel"] = {k: q(v) for k, v in fc.items()} | {
            "theorem": theorem.rsplit(".", 1)[0] + ".funnel"}
    return side
