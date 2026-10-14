"""SE₂(3) log-tube certificates for a body-frame PD controller tracking a coasting reference.

The Lean theorem is `Dynacert.Lie.pd_spacecraft_components` (in `Lie/PDTube.lean`): a vehicle and
a coasting reference (`ā = 0`, `ω̄ = 0`) on a circular orbit in the field `-μ p/‖p‖³`, the
vehicle under

    a = -kp·R̄ᵀ(p − p̄) − kd·R̄ᵀ(v − v̄) + d,    ω = −kR·½vee(R̄ᵀR − RᵀR̄).

Given rational certificate data (an `LTICert` for the 9-state closed-loop linear part, a
coercivity witness `P ⪰ mI`, an operator-norm witness `‖P‖ ≤ pn`, a region radius `D`, a level
`ρ`, and a decay level `c`), it proves `m‖Δp‖² ≤ c`, `m‖Δv‖² ≤ c` and `m‖eR‖² ≤ c` for all time.

This module recognizes that pattern in rumoca's Lean transcription (`recognize`), searches for
the data (`search`, untrusted), and emits `Spec.lean` and `LieCert.lean`, where each hypothesis
of the theorem is discharged from the model's own equations.
"""

from __future__ import annotations

import json
import math
import re
from dataclasses import dataclass, field
from fractions import Fraction
from types import SimpleNamespace

import numpy as np

from . import emit_lti as E
from . import exact
from . import lean as lean_mod
from . import lie_link, pipeline
from .lean import mat, q, vec
from .methods import lti


class LieError(pipeline.CertError):
    pass


# --- recognizing the pattern -----------------------------------------------------------------

def _strip(s: str) -> str:
    """Drop rumoca's type ascriptions `(e : ℝ)` around parameters and powers."""
    s = re.sub(r"\((p\.\S+?) : ℝ\)", r"\1", s)
    s = re.sub(r"\((\(.*?\) \^ \(1\.5 : ℝ\)) : ℝ\)", r"\1", s)
    return s


@dataclass
class Pattern:
    veh: dict                 # structure se23 block (p, v, R names) of the vehicle
    ref: dict
    eq: dict                  # role -> index into Equations
    fld: dict                 # role -> Lean field (quoted)
    gains: dict               # kp, kd, kR -> parameter field
    dist: str                 # disturbance input field
    outputs: list             # (name, kind) with kind in {"pos", "vel", "att"}
    mu: str                   # vehicle μ parameter field
    mub: str                  # reference μ parameter field
    init: dict = field(default_factory=dict)   # role -> index into Initial


def recognize(prob, structure) -> Pattern:
    les = [f for f in structure.of("log-error") if f.data["vehicle"]["gravity"] == "inverse-square"]
    if not les:
        raise LieError("no vehicle/reference pair in inverse-square gravity "
                       "(this method certifies spacecraft tracking a circular orbit)")
    veh, ref = les[0].data["vehicle"], les[0].data["reference"]
    I = lean_mod.ident
    src = prob.lean_src
    eqs = [_strip(e) for e in lie_link.equations_text(src)]
    inits = lie_link.initial_text(src)
    P, V, R = I(veh["p"]), I(veh["v"]), I(veh["R"])
    Pb, Vb, Rb = I(ref["p"]), I(ref["v"]), I(ref["R"])
    eq: dict = {}
    for role, fld_ in (("p", P), ("v", V), ("R", R), ("pb", Pb), ("vb", Vb), ("Rb", Rb)):
        eq[role] = lie_link._eq_index(eqs, fld_)

    def find(pat, what):
        for k, e in enumerate(eqs):
            m = re.fullmatch(pat, e)
            if m:
                return k, m
        raise LieError(f"the model has no equation of the form {what}")

    # vehicle and reference inputs: dx.v = x.R *ᵥ y.a − …; dx.R = x.R * Rumoca.skew y.w
    a = re.match(rf"dx\.{re.escape(V)} = x\.{re.escape(R)} \*ᵥ y\.(\S+) - ", eqs[eq["v"]])
    w = re.match(rf"dx\.{re.escape(R)} = x\.{re.escape(R)} \* Rumoca\.skew y\.(\S+)$", eqs[eq["R"]])
    ab = re.match(rf"dx\.{re.escape(Vb)} = x\.{re.escape(Rb)} \*ᵥ y\.(\S+) - ", eqs[eq["vb"]])
    wb = re.match(rf"dx\.{re.escape(Rb)} = x\.{re.escape(Rb)} \* Rumoca\.skew y\.(\S+)$",
                  eqs[eq["Rb"]])
    if not (a and w and ab and wb):
        raise LieError("thrust and rates must be algebraic signals `y.a`, `y.w` in "
                       "`der(v) = R*a - …`, `der(R) = R*skew(w)`")
    mu = re.search(r"• (p\.\S+) • x\.", eqs[eq["v"]])
    mub = re.search(r"• (p\.\S+) • x\.", eqs[eq["vb"]])
    fa, fw, fab, fwb = a.group(1), w.group(1), ab.group(1), wb.group(1)
    E_ = re.escape
    eq["ab"], _ = find(rf"y\.{E_(fab)} = !\[0, 0, 0\]", f"{ref['p']}'s thrust = 0")
    eq["wb"], _ = find(rf"y\.{E_(fwb)} = !\[0, 0, 0\]", f"{ref['p']}'s rates = 0")
    eq["a"], ma = find(rf"y\.{E_(fa)} = -\(p\.(\S+) • y\.(\S+)\) - p\.(\S+) • y\.(\S+) \+ u\.(\S+)",
                       "a = -kp*ep - kd*ev + d")
    eq["w"], mw = find(rf"y\.{E_(fw)} = -\(p\.(\S+) • y\.(\S+)\)", "w = -kR*eR")
    kp, ep, kd, ev, dist = ma.groups()
    kR, eR = mw.groups()
    eq["ep"], _ = find(rf"y\.{E_(ep)} = \(x\.{E_(Rb)}\)ᵀ \*ᵥ \(x\.{E_(P)} - x\.{E_(Pb)}\)",
                       "ep = transpose(ref.R)*(p - ref.p)")
    eq["ev"], _ = find(rf"y\.{E_(ev)} = \(x\.{E_(Rb)}\)ᵀ \*ᵥ \(x\.{E_(V)} - x\.{E_(Vb)}\)",
                       "ev = transpose(ref.R)*(v - ref.v)")
    eq["eR"], mR = find(rf"y\.{E_(eR)} = !\[0\.5 \* \(y\.(\S+) 2 1 - y\.\1 1 2\), "
                        r"0\.5 \* \(y\.\1 0 2 - y\.\1 2 0\), 0\.5 \* \(y\.\1 1 0 - y\.\1 0 1\)\]",
                        "eR = {0.5*(Rt[3,2]-Rt[2,3]), …}")
    Rt = mR.group(1)
    eq["Rt"], _ = find(rf"y\.{E_(Rt)} = \(x\.{E_(Rb)}\)ᵀ \* x\.{E_(R)}", "Rt = transpose(ref.R)*R")
    outs = []
    for name in prob.spec.certify:
        o = lean_mod.ident(name)
        kinds = {"pos": rf"y\.{E_(o)} = Real\.sqrt \(\(x\.{E_(P)} - x\.{E_(Pb)}\) ⬝ᵥ \(x\.{E_(P)} - x\.{E_(Pb)}\)\)",
                 "vel": rf"y\.{E_(o)} = Real\.sqrt \(\(x\.{E_(V)} - x\.{E_(Vb)}\) ⬝ᵥ \(x\.{E_(V)} - x\.{E_(Vb)}\)\)",
                 "att": rf"y\.{E_(o)} = Real\.sqrt \(y\.{E_(eR)} ⬝ᵥ y\.{E_(eR)}\)"}
        for kind, pat in kinds.items():
            hit = [k for k, e in enumerate(eqs) if re.fullmatch(pat, e)]
            if hit:
                outs.append((name, kind))
                eq["out:" + name] = hit[0]
                break
        else:
            raise LieError(f"certified output {name} must be sqrt(Δp·Δp), sqrt(Δv·Δv) or "
                           "sqrt(eR·eR)")
    init = {}
    for role, fld_ in (("p", P), ("v", V), ("R", R), ("pb", Pb), ("vb", Vb), ("Rb", Rb)):
        hit = [k for k, s in enumerate(inits) if s.startswith(f"x.{fld_} = ")]
        if not hit:
            raise LieError(f"{fld_} needs a fixed start value")
        init[role] = hit[0]
    fld = dict(p=P, v=V, R=R, pb=Pb, vb=Vb, Rb=Rb, a=fa, w=fw, ab=fab, wb=fwb, ep=ep, ev=ev,
               eR=eR, Rt=Rt)
    return Pattern(veh, ref, eq, fld, {"kp": kp, "kd": kd, "kR": kR}, dist, outs,
                   mu.group(1)[2:], mub.group(1)[2:], init)


# --- numbers ---------------------------------------------------------------------------------

def pd_gain(kp, kd, kR, D, dl):
    return ((kR * D / 2 + kR * D ** 2 / 4) +
            ((kp + kd) * (D / 2 + D ** 2 / 6) + (kR * D + (kp + kd) * D + dl) / 2 +
             D / 8 * ((kp + kd) * D + dl) + kR * D ** 2 / 4) +
            (kR * D ** 2 / 6 + kR * D / 2 + kR * D ** 2 / 8))


def grav_gain(mu, r, D):
    return (1 / (1 - D ** 2 / 16)) * (2 * mu / (r * (r - D) ** 2))


def pd_matrices(kp, kd, kR):
    A = [[Fraction(0)] * 9 for _ in range(9)]
    for i in range(3):
        A[i][i + 3] = Fraction(1)
        A[3 + i][i] = -Fraction(kp)
        A[3 + i][3 + i] = -Fraction(kd)
        A[6 + i][6 + i] = -Fraction(kR)
    B = [[Fraction(int(i == j + 3)) for j in range(3)] for i in range(9)]
    return A, B


@dataclass
class LieCertData:
    P: list
    alpha: Fraction
    gamma: Fraction
    lmi: tuple                # (L, d) for lmiMatrix
    m: Fraction
    Wm: tuple                 # witness for P - m I
    pn: Fraction
    Wn: tuple                 # witness for pn² I - PᵀP
    D: Fraction
    rho: Fraction
    delta: Fraction
    c: Fraction
    kappa: Fraction
    bounds: list              # per output, rational b with m b² ≥ c
    mu: Fraction = Fraction(0)
    r0: Fraction = Fraction(0)


def _sqrt_up(x: Fraction, den=10 ** 6) -> Fraction:
    """A rational ≥ √x."""
    r = Fraction(math.isqrt(int(x * den * den)) + 1, den)
    while r * r < x:
        r += Fraction(1, den)
    return r


def search(kp, kd, kR, mu, r0, delta, alphas=None, Ds=None):
    """Untrusted search; every inequality is re-checked here in exact rationals."""
    import cvxpy as cp

    A, B = pd_matrices(kp, kd, kR)
    Af = np.array(A, dtype=float)
    Bf = np.array(B, dtype=float)
    alphas = alphas or [0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0]
    Ds = Ds or [Fraction(1, 1000) * k for k in (1, 2, 3, 5, 7, 10, 15, 20, 30, 50, 70, 100)]
    best = None
    for a in alphas:
        Pv, g, pn_ = cp.Variable((9, 9), symmetric=True), cp.Variable(), cp.Variable()
        M = cp.bmat([[Af.T @ Pv + Pv @ Af + a * Pv, Pv @ Bf], [Bf.T @ Pv, -g * np.eye(3)]])
        prob = cp.Problem(cp.Minimize(pn_ + g),
                          [M << -1e-6 * np.eye(12), Pv >> np.eye(9), Pv << pn_ * np.eye(9)])
        try:
            prob.solve()
        except Exception:  # noqa: BLE001 - solver failure means no candidate at this α
            continue
        if Pv.value is None:
            continue
        P = [[exact.frac((Pv.value[i][j] + Pv.value[j][i]) / 2, 10 ** 6) for j in range(9)]
             for i in range(9)]
        alpha = exact.frac(a)
        gamma = exact.frac(float(g.value) * 1.01 + 1e-6)
        W = exact.psd_witness(lti.lmi_matrix(A, B, P, alpha, gamma))
        if W is None:
            continue
        ev = np.linalg.eigvalsh(np.array(P, dtype=float))
        m = exact.frac(ev[0] * 0.999, 10 ** 4)
        Wm = exact.psd_witness(exact.sub(P, exact.eye(9, m)))
        pn = exact.frac(ev[-1] * 1.001 + 1e-6, 10 ** 4)
        PtP = exact.matmul(exact.transpose(P), P)
        Wn = exact.psd_witness(exact.sub(exact.eye(9, pn * pn), PtP))
        if Wm is None or Wn is None:
            continue
        for D in Ds:
            if not (D <= 2 and D < r0):
                continue
            ell = pd_gain(Fraction(kp), Fraction(kd), Fraction(kR), D, delta) + \
                grav_gain(Fraction(mu), Fraction(r0), D)
            kappa = alpha - 2 * pn * ell / m
            if kappa <= 0:
                continue
            rho = m * D * D
            if not gamma * delta * delta < kappa * rho:
                continue
            c = gamma * delta * delta / kappa
            c = Fraction(math.ceil(c * 10 ** 12), 10 ** 12)
            b = _sqrt_up(c / m)
            if best is None or b < best.bounds[0]:
                best = LieCertData(P, alpha, gamma, W, m, Wm, pn, Wn, D, rho, delta, c, kappa,
                                   [b], Fraction(mu), Fraction(r0))
    return best


# --- Lean ------------------------------------------------------------------------------------

def spec_problem(prob, pat: Pattern, dbound) -> SimpleNamespace:
    m = prob.model
    outs = [SimpleNamespace(name=n, lean_term=f"(y t).{lean_mod.ident(n)}", kind="algebraic")
            for n, _ in pat.outputs]
    d = m.var(prob.spec.disturbances[0].name)
    dists = [f"{lean_mod.ident(d.name)} {i}" for i in range(d.shape[0])] if not d.scalar \
        else [lean_mod.ident(d.name)]
    return SimpleNamespace(module=f"Certs.{m.ns}", model_name=m.name, ns=m.ns, dists=dists,
                           dist_bounds=[dbound] * len(dists), refs=[], params_ok=None,
                           outputs=outs)


def emit_cert(prob, pat: Pattern, gains, cd: LieCertData) -> str:
    ns = prob.model.ns
    kp, kd, kR = (q(gains[k]) for k in ("kp", "kd", "kR"))
    F, e = pat.fld, pat.eq
    src = prob.lean_src
    eqs = lie_link.equations_text(src)
    inits = lie_link.initial_text(src)
    bnds = lie_link.bound_text(src)
    nst = len(prob.model.states)
    eh = [f"e{i}" for i in range(len(eqs))]
    ih = [f"i{i}" for i in range(len(inits))]
    bh = [f"b{i}" for i in range(len(bnds))]
    idx = {v.lean: i for i, v in enumerate(prob.model.states)}
    sidx = {r: idx[F[r]] for r in ("p", "v", "R", "pb", "vb", "Rb")}
    d_eqs = "⟨" + ", ".join(["-"] * nst + eh) + "⟩"
    bidx = {}
    for i, s_ in enumerate(bnds):
        mm = re.match(r"p\.(\S+) = ", s_)
        if mm:
            bidx[mm.group(1)] = f"b{i}"
    g = {k: bidx[v] for k, v in pat.gains.items()}
    dvar = prob.model.var(prob.spec.disturbances[0].name)
    nd = 1 if dvar.scalar else dvar.shape[0]

    def from_eq(body: str) -> str:
        return f"(fun t ht => by obtain {d_eqs} := hder t ht; {body})"

    def der(role):
        dh = ["-"] * nst
        dh[sidx[role]] = "hD"
        return f"(fun t ht => by obtain ⟨{', '.join(dh)}, -⟩ := hder t ht; exact hD)"

    def bp(which, role):
        return bidx_param(pat, which, bidx, role)

    Lt, dt = lean_mod.sum_witness(cd.lmi[0], cd.lmi[1], 9, 3)
    out = [f"import {pat_module(prob)}.Spec", "import Dynacert.Lie.PDTube", ""]
    out += lean_mod.header(f"SE₂(3) log-tube certificate for `{prob.model.name}`",
                           "dynacert (Lie: PD spacecraft tube)")
    out += E.LINTERS + ["set_option maxRecDepth 100000", "set_option maxHeartbeats 4000000", "",
                        f"namespace {ns}.LieCert", "",
                        f"open Matrix Set Dynacert Dynacert.Linear Dynacert.Lie {ns}", "",
                        "/-! ### Certificate data (rational, checked by `decide +kernel`) -/", "",
                        f"def P : Matrix (Fin 9) (Fin 9) ℚ := {mat(cd.P)}",
                        "def lmiL : Matrix (Fin 9 ⊕ Fin 3) (Fin 9 ⊕ Fin 3) ℚ :=", f"  {Lt}",
                        "def lmiD : Fin 9 ⊕ Fin 3 → ℚ :=", f"  {dt}", "",
                        f"/-- The closed-loop linear part, `kp = {kp}`, `kd = {kd}`, `kR = {kR}`. -/",
                        f"def C : LTICert (pdModel {kp} {kd} {kR}) :=",
                        f"  ⟨P, {q(cd.alpha)}, {q(cd.gamma)}, by decide +kernel, by decide +kernel,",
                        "    by decide +kernel, ⟨lmiL, lmiD, by decide +kernel, by decide +kernel⟩⟩",
                        "", f"/-- `P ⪰ {q(cd.m)} I`. -/",
                        f"def Wm : PSDWitness (C.P - ({q(cd.m)} : ℚ) • 1) :=",
                        f"  ⟨{mat(cd.Wm[0])},", f"   {vec(cd.Wm[1])},",
                        "   by decide +kernel, by decide +kernel⟩", "",
                        f"/-- `‖P‖ ≤ {q(cd.pn)}`. -/",
                        f"def Wn : PSDWitness (({q(cd.pn)} : ℚ) ^ 2 • 1 - C.Pᵀ * C.P) :=",
                        f"  ⟨{mat(cd.Wn[0])},", f"   {vec(cd.Wn[1])},",
                        "   by decide +kernel, by decide +kernel⟩", ""]
    kap = (f"((C.α : ℝ) - 2 * (({q(cd.pn)} : ℚ) : ℝ) * (pdGain (({kp} : ℚ) : ℝ) (({kd} : ℚ) : ℝ) "
           f"(({kR} : ℚ) : ℝ) ({q(cd.D)} : ℝ) ({q(cd.delta)} : ℝ) + gravGain ({q(cd.mu)} : ℝ) "
           f"({q(cd.r0)} : ℝ) ({q(cd.D)} : ℝ)) / (({q(cd.m)} : ℚ) : ℝ))")
    num = f"(C.γ : ℝ) * ({q(cd.delta)} : ℝ) ^ 2"
    for name, rel, lvl in (("budget", "<", cd.rho), ("decay", "≤", cd.c)):
        out += [f"theorem {name} : {num} {rel} {kap} * ({q(lvl)} : ℝ) := by",
                f"  have hα : C.α = {q(cd.alpha)} := rfl",
                f"  have hγ : C.γ = {q(cd.gamma)} := rfl",
                "  rw [hα, hγ]",
                "  simp only [pdGain, gravGain]",
                "  norm_num", ""]
    bounds = cd.bounds * len(pat.outputs)
    bvec = vec(bounds)
    init_R = lambda role: (f"(by beta_reduce; rw [i{pat.init[role]}]; ext i j; "
                           "fin_cases i <;> fin_cases j <;> rfl)")
    sv = lambda r: f"(fun s => (x s).{F[r]})"
    dv_ = lambda r: f"(fun s => (dx s).{F[r]})"
    yv = lambda r: f"(fun s => (y s).{F[r]})"
    hu_pat = E._conj([f"h{i}" for i in range(nd)])
    out += [
        f"/-- **Certified.** The claim of `Spec.lean` holds with the bounds `{bvec}`. -/",
        f"theorem certified : Spec.Claim {bvec} := by",
        "  intro p u x y T hp h hu _ _ h0",
        f"  obtain {E._conj(bh)} := hp",
        f"  obtain ⟨dx, {', '.join(f'c{i}' for i in range(nst))}, hder⟩ := h",
        f"  obtain {E._conj(ih)} := h0",
        f"  have hmu : p.{pat.mu} = {q(cd.mu)} := by rw [{bidx[pat.mu]}]; norm_num",
        f"  have hmub : p.{pat.mub} = p.{pat.mu} := by rw [{bidx[pat.mub]}, {bidx[pat.mu]}]",
        f"  have key := pd_spacecraft_components (kp := {kp}) (kd := {kd}) (kR := {kR})",
        f"    (p := {sv('p')}) (v := {sv('v')}) (R := {sv('R')})",
        f"    (pb := {sv('pb')}) (vb := {sv('vb')}) (Rb := {sv('Rb')})",
        f"    (dp := {dv_('p')}) (dv := {dv_('v')}) (dR := {dv_('R')})",
        f"    (dpb := {dv_('pb')}) (dvb := {dv_('vb')}) (dRb := {dv_('Rb')})",
        f"    (a := {yv('a')}) (w := {yv('w')}) (ab := {yv('ab')}) (wb := {yv('wb')})",
        f"    (ep := {yv('ep')}) (ev := {yv('ev')}) (eR := {yv('eR')})",
        f"    (d := fun s => (u s).{pat.dist}) (μ := p.{pat.mu}) (μb := p.{pat.mub})",
        f"    (r0 := {q(cd.r0)}) (D := {q(cd.D)}) (δ := {q(cd.delta)}) (ρ := {q(cd.rho)})",
        f"    (c := {q(cd.c)}) (m := {q(cd.m)}) (pn := {q(cd.pn)})",
        "    C Wm Wn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
        f"    c{sidx['p']} c{sidx['v']} c{sidx['R']} c{sidx['pb']} c{sidx['vb']} c{sidx['Rb']}",
        *[f"    {der(r)}" for r in ("p", "v", "R", "pb", "vb", "Rb")],
        *[f"    {from_eq(f'exact e{e[r]}')}" for r in ("p", "v", "R", "pb", "vb", "Rb", "ep", "ev")],
        f"    {from_eq(f'beta_reduce; rw [e{e['eR']}, e{e['Rt']}]; ext i; fin_cases i <;> simp [attErr] <;> norm_num')}",
        f"    {from_eq(f'beta_reduce; rw [e{e['a']}, {g['kp']}, {g['kd']}]; norm_num')}",
        f"    {from_eq(f'beta_reduce; rw [e{e['w']}, {g['kR']}]; norm_num')}",
        f"    {from_eq(f'beta_reduce; rw [e{e['ab']}]; ext i; fin_cases i <;> rfl')}",
        f"    {from_eq(f'beta_reduce; rw [e{e['wb']}]; ext i; fin_cases i <;> rfl')}",
        f"    (fun t ht => by",
        f"      obtain {hu_pat} := hu t ht",
        f"      refine enorm_le_of_abs_le (b := {q(prob.spec.disturbances[0].bound)}) ?_ (by norm_num) (by norm_num)",
        "      intro i; fin_cases i <;> [" + "; ".join(f"exact h{i}" for i in range(nd)) + "])",
        "    (by rw [hmu]; norm_num) hmub (by norm_num)",
        f"    (by beta_reduce; rw [i{pat.init['p']}, i{pat.init['pb']}, {bp('p0', 'p')}, {bp('p0', 'pb')}])",
        f"    (by beta_reduce; rw [i{pat.init['v']}, i{pat.init['vb']}, {bp('v0', 'p')}, {bp('v0', 'pb')}])",
        f"    {init_R('R')} {init_R('Rb')}",
        f"    (by beta_reduce; rw [i{pat.init['pb']}, {bp('p0', 'pb')}, ← sqrt_dot_self]; "
        "norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])",
        f"    (by beta_reduce; rw [i{pat.init['vb']}, {bp('v0', 'pb')}, ← sqrt_dot_self, "
        "Real.sq_sqrt (by norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]), hmu]; "
        "norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])",
        f"    (by beta_reduce; rw [i{pat.init['pb']}, i{pat.init['vb']}, {bp('p0', 'pb')}, "
        f"{bp('v0', 'pb')}]; norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])",
        "    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)",
        "    (by rw [hmu]; exact budget) (by norm_num) (by rw [hmu]; exact decay)",
        "  obtain ⟨kPV, kAtt⟩ := key",
        "  intro t ht",
    ]
    parts = []
    for (name, kind) in pat.outputs:
        k = e["out:" + name]
        src_ = {"pos": "(kPV t ⟨ht.1, ht.2.le⟩).1", "vel": "(kPV t ⟨ht.1, ht.2.le⟩).2",
                "att": "(kAtt t ht)"}[kind]
        parts.append(
            f"(by obtain {d_eqs} := hder t ht; "
            f"rw [e{k}, sqrt_dot_self, abs_of_nonneg (GNC.enorm_nonneg _)]; "
            f"exact le_of_sq_bound (m := (({q(cd.m)} : ℚ) : ℝ)) (c := {q(cd.c)}) (by norm_num)"
            f" (GNC.enorm_nonneg _) (by norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]) {src_} (by norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]))")
    out.append("  exact ⟨" + ",\n    ".join(parts) + "⟩")
    out += ["", f"end {ns}.LieCert", ""]
    return "\n".join(out)


def _rat(x) -> Fraction:
    import sympy as sp
    x = sp.nsimplify(sp.sympify(x), rational=True)
    return Fraction(int(x.p), int(x.q))


def problem_numbers(prob, pat: Pattern) -> dict:
    """Gains, μ, reference radius from the model's parameter values; checks the circular
    start and that the vehicle starts on the reference."""
    from . import structure as st
    vals = st.param_values(prob.model)
    byname = {str(k): v for k, v in vals.items()}
    unq = lie_link.unq
    gains = {k: _rat(byname[unq(v)]) for k, v in pat.gains.items()}
    mu, mub = _rat(byname[unq(pat.mu)]), _rat(byname[unq(pat.mub)])
    if mu != mub:
        raise LieError("vehicle and reference must orbit the same body (equal μ)")

    def start(body, which):
        return [_rat(byname[f"{body}.{which}[{i}]"]) for i in (1, 2, 3)]

    vb_, rb_ = pat.veh["p"].rsplit(".", 1)[0], pat.ref["p"].rsplit(".", 1)[0]
    p0, v0 = start(rb_, "p0"), start(rb_, "v0")
    if start(vb_, "p0") != p0 or start(vb_, "v0") != v0:
        raise LieError("the vehicle must start on the reference (zero initial error)")
    r2 = sum(x * x for x in p0)
    r0 = Fraction(math.isqrt(r2.numerator), math.isqrt(r2.denominator))
    if r0 * r0 != r2:
        raise LieError("the reference radius |p0| must be rational")
    if sum(x * x for x in v0) * r0 != mu or sum(a * b for a, b in zip(p0, v0)) != 0:
        raise LieError("the reference must start on a circular orbit (|v0|² = μ/|p0|, p0·v0 = 0)")
    return dict(gains=gains, mu=mu, r0=r0)


def run(prob, structure, verbose=print) -> dict:
    pat = recognize(prob, structure)
    nums = problem_numbers(prob, pat)
    if len(prob.spec.disturbances) != 1:
        raise LieError("exactly one (vector) disturbance input is supported")
    d0 = Fraction(prob.spec.disturbances[0].bound)
    delta = _sqrt_up(3 * d0 * d0)
    g = nums["gains"]
    verbose(f"lie: PD gains kp={g['kp']}, kd={g['kd']}, kR={g['kR']}; μ={nums['mu']}, "
            f"r0={nums['r0']}; ‖d‖ ≤ {float(delta):.4g}")
    cd = search(g["kp"], g["kd"], g["kR"], nums["mu"], nums["r0"], delta)
    if cd is None:
        raise LieError("no certificate: the residual sectors exceed the decay rate for every "
                       "α and region radius tried (gains too low against the gravity gradient, "
                       "or the disturbance too large)")
    verbose(f"search: α={float(cd.alpha):.3g}, ‖P‖≤{float(cd.pn):.3g}, m={float(cd.m):.3g}, "
            f"D={float(cd.D)}, κ={float(cd.kappa):.3g}, bound {float(cd.bounds[0]):.4g}")
    out = prob.cert_dir
    out.mkdir(parents=True, exist_ok=True)
    spb = spec_problem(prob, pat, d0)
    (out / "Model.lean").write_text(prob.lean_src)
    (out / "Spec.lean").write_text(E.emit_spec(spb))
    (out / "LieCert.lean").write_text(emit_cert(prob, pat, g, cd))
    mod = f"Certs.{prob.model.ns}.LieCert"
    verbose(f"lean: lake build {mod}")
    pipeline.lake("build", mod, cwd=prob.root)
    ax = pipeline.axioms(mod, f"{prob.model.ns}.LieCert.certified", root=prob.root)
    if not ax <= pipeline.ALLOWED_AXIOMS:
        raise LieError(f"disallowed axioms: {ax - pipeline.ALLOWED_AXIOMS}")
    side = {"model": prob.model.name, "method": "lie-pd-tube",
            "theorem": f"{prob.model.ns}.LieCert.certified", "axioms": sorted(ax),
            "vehicle": pat.veh["p"].rsplit(".", 1)[0], "reference": pat.ref["p"].rsplit(".", 1)[0],
            "gains": {k: q(v) for k, v in g.items()}, "mu": q(nums["mu"]), "r0": q(nums["r0"]),
            "alpha": q(cd.alpha), "gamma": q(cd.gamma), "m": q(cd.m), "pn": q(cd.pn),
            "D": q(cd.D), "rho": q(cd.rho), "delta": q(cd.delta), "c": q(cd.c),
            "kappa": float(cd.kappa), "P": [[q(v) for v in r] for r in cd.P],
            "bounds": {n: q(cd.bounds[0]) for n, _ in pat.outputs}}
    (out / "lie.json").write_text(json.dumps(side, indent=1))
    return {"dir": str(out), "sidecar": side}


def pat_module(prob) -> str:
    return f"Certs.{prob.model.ns}"


def bidx_param(pat, which, bidx, role):
    """The `Params.Bound` hypothesis for a body's start parameter (`sc.p0`, `ref.v0`, …)."""
    body = (pat.veh if role == "p" else pat.ref)["p"].rsplit(".", 1)[0]
    key = lean_mod.ident(f"{body}.{which}")
    if key not in bidx:
        raise LieError(f"start value of {body} must be the parameter {body}.{which}")
    return bidx[key]
