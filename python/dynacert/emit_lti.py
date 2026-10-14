"""Lean emission for linear models: `Spec.lean` (the claim) and `Cert.lean` (link + proof).

The generated proof composes library theorems:

* `link`: rumoca's `IsSolutionOn` (plus the reference hypotheses of the spec) ⇒
  `model.toSystem.IsSolution` for coordinates `z = M x + N r` (states and reference
  inputs). Each coordinate derivative is built with `HasDerivWithinAt` combinators and
  matched to the LTI right-hand side by `linear_combination` of the model's own equations
  (multipliers computed by `analysis.py`), after rewriting parameters by `Params.Bound` and
  decimal literals by exact rationals.
* `ChannelCert.invariant`: the invariant ellipsoid.
* `LinearBoxCert`: output bounds; each output is tied to the coordinates by
  `linear_combination` of the equations.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from fractions import Fraction

from . import lean
from .lean import mat, q, vec

DEC_LIT = re.compile(r"(?<![\w.])(\d+\.\d+(?:[eE][+-]?\d+)?|\d+[eE][+-]?\d+)(?![\w.])")


def decimal_literals(lean_src: str) -> list[str]:
    """Every decimal literal in rumoca's Model.lean (they need exact rewriting for `ring`)."""
    body = lean_src.split("namespace", 1)[-1]
    seen = []
    for m in DEC_LIT.finditer(body):
        if m.group(1) not in seen:
            seen.append(m.group(1))
    return seen


@dataclass
class Term:
    coeff: Fraction
    kind: str   # "x" (state) or "u" (reference input)
    fld: str    # Lean field name


@dataclass
class Coord:
    name: str
    terms: list[Term]


@dataclass
class Reference:
    fld: str                 # Lean field of the reference input
    deriv: str | None        # Lean field of its derivative input
    start: Fraction | None   # value at t = 0


@dataclass
class Output:
    name: str                # Modelica name
    lean_term: str           # e.g. "(x t).e" or "(y t).e"
    kind: str                # "state" (claim on Icc) | "algebraic" (claim on Ico)
    row: list                # coefficients over the coordinates
    mult: list               # (eq index, λ) proving lean_term = row · z


@dataclass
class LinearProblem:
    model_name: str
    ns: str
    module: str
    states: list[str]                 # all state fields, declaration order
    coords: list[Coord]
    dists: list[str]
    dist_bounds: list[Fraction]
    refs: list[Reference]
    A: list
    B: list
    n_bound: int
    n_eqs: int
    n_init: int
    multipliers: list                 # per coordinate
    x0: list
    literals: list[str] = field(default_factory=list)
    outputs: list[Output] = field(default_factory=list)
    # polytopic variant (uncertain parameters): None for a single LTI model
    params_ok: list | None = None     # ("eq", fld, value) | ("range", fld, lo, hi), Bound order
    vertices: list | None = None      # vertex matrices A_σ
    weights: list | None = None       # list of factor lists [(fld, lo, hi, "up"|"down")]


# --- small helpers ------------------------------------------------------------------------------

def _conj(names: list[str]) -> str:
    if not names:
        return "-"
    if len(names) == 1:
        return names[0]
    return "⟨" + ", ".join(names) + "⟩"


def _c(x) -> str:
    return f"({q(x)} : ℝ)"


def _term(tm: Term, s: str) -> str:
    src = f"(x {s})" if tm.kind == "x" else f"(u {s})"
    return f"{_c(tm.coeff)} * {src}.{tm.fld}"


def _coord_expr(c: Coord, s: str) -> str:
    return " + ".join(_term(tm, s) for tm in c.terms)


def _coord_def(c: Coord) -> str:
    return " + ".join(f"{_c(tm.coeff)} * {'s' if tm.kind == 'x' else 'v'}.{tm.fld}"
                      for tm in c.terms)


def _lin(coeffs, exprs) -> str:
    parts = [f"{_c(a)} * ({e})" for a, e in zip(coeffs, exprs) if Fraction(a) != 0]
    return " + ".join(parts) if parts else "0"


def _coef(cf) -> str:
    return cf if isinstance(cf, str) else _c(cf)


def _lc(mult, eh) -> str | None:
    s = " + ".join(f"{_coef(cf)} * {eh[e]}" for e, cf in mult
                   if isinstance(cf, str) or cf != 0)
    return s or None


def _factor(f) -> str:
    fld, lo, hi, d = f
    num = f"p.{fld} - {_c(lo)}" if d == "up" else f"{_c(hi)} - p.{fld}"
    return f"(({num}) / {_c(Fraction(hi) - Fraction(lo))})"


def _weight(factors) -> str:
    return " * ".join(_factor(f) for f in factors) if factors else "(1 : ℝ)"


def _param_hyps(pb) -> tuple[list[str], list[str]]:
    """Names for the conjuncts of the parameter hypothesis, and the equality ones."""
    if pb.params_ok is None:
        bh = [f"hb{i}" for i in range(pb.n_bound)]
        return bh, bh
    names, eqs = [], []
    for i, e in enumerate(pb.params_ok):
        if e[0] == "eq":
            names.append(f"hb{i}")
            eqs.append(f"hb{i}")
        else:
            names += [f"hl{i}", f"hh{i}"]
    return names, eqs


def _fold(items: list[str], op: str) -> str:
    acc = items[0]
    for it in items[1:]:
        acc = f"({acc}).{op} {it}"
    return acc


LINTERS = [
    "set_option linter.style.setOption false",
    "set_option linter.style.longLine false",
    "set_option linter.unusedSimpArgs false",
    "set_option linter.unusedTactic false",
    "set_option linter.unreachableTactic false",
    "set_option linter.unnecessarySeqFocus false",
    "set_option linter.flexible false",
    "set_option linter.unusedVariables false",
    "set_option linter.style.show false",
]


# --- Spec ---------------------------------------------------------------------------------------

def emit_spec(pb: LinearProblem) -> str:
    out = [f"import {pb.module}.Model", ""]
    out += [
        "/-!",
        f"# Specification for `{pb.model_name}`",
        "",
        "GENERATED by `dynacert` from the model and its `__Dynacert` annotations only; the",
        "certificate method and its numbers do not affect this file. Read this file to know",
        "what `Cert.certified` proves.",
        "-/",
        "",
        "set_option linter.style.setOption false",
        "set_option linter.style.longLine false",
        "",
        f"namespace {pb.ns}.Spec",
        "",
        f"open Set {pb.ns}",
        "",
    ]
    if pb.dists:
        conds = " ∧ ".join(f"|(u t).{d}| ≤ {_c(b)}" for d, b in zip(pb.dists, pb.dist_bounds))
        out += ["/-- Admissible disturbances: componentwise peak bounds. -/",
                "def Admissible (u : ℝ → Inputs) (T : ℝ) : Prop :=",
                f"  ∀ t ∈ Ico 0 T, {conds}", ""]
    else:
        out += ["def Admissible (u : ℝ → Inputs) (T : ℝ) : Prop := True", ""]
    dr = [r for r in pb.refs if r.deriv]
    if dr:
        cont = [f"ContinuousOn (fun s => (u s).{r.fld}) (Icc 0 T)" for r in dr]
        der = [f"HasDerivWithinAt (fun s => (u s).{r.fld}) (u t).{r.deriv} (Ici t) t" for r in dr]
        out += ["/-- Reference signals: continuous on `[0, T]` with the declared right",
                "derivatives on `[0, T)`. -/",
                "def References (u : ℝ → Inputs) (T : ℝ) : Prop :=",
                "  " + " ∧\n  ".join(cont) + " ∧",
                "  ∀ t ∈ Ico 0 T, " + " ∧\n    ".join(der), ""]
    else:
        out += ["def References (u : ℝ → Inputs) (T : ℝ) : Prop := True", ""]
    rs = [r for r in pb.refs if r.start is not None]
    if rs:
        out += ["/-- Reference values at `t = 0`. -/",
                "def ReferenceStart (u : ℝ → Inputs) : Prop :=",
                "  " + " ∧ ".join(f"(u 0).{r.fld} = {_c(r.start)}" for r in rs), ""]
    else:
        out += ["def ReferenceStart (u : ℝ → Inputs) : Prop := True", ""]
    phyp = "p.Bound"
    if pb.params_ok is not None:
        conds = []
        for e in pb.params_ok:
            if e[0] == "eq":
                conds.append(f"p.{e[1]} = {_c(e[2])}")
            else:
                conds.append(f"{_c(e[2])} ≤ p.{e[1]} ∧ p.{e[1]} ≤ {_c(e[3])}")
        out += ["/-- Parameter values: the model's bindings, with the uncertain parameters",
                "ranging over their annotated intervals. -/",
                "def ParamsOK (p : Params) : Prop :=",
                "  " + " ∧\n  ".join(conds), ""]
        phyp = "ParamsOK p"
    k = len(pb.outputs)
    groups = []
    for rng, kind in (("Icc", "state"), ("Ico", "algebraic")):
        cs = [f"|{o.lean_term}| ≤ (b {i} : ℝ)" for i, o in enumerate(pb.outputs) if o.kind == kind]
        if cs:
            groups.append(f"(∀ t ∈ {rng} 0 T, " + " ∧ ".join(cs) + ")")
    names = ", ".join(f"`{o.name}`" for o in pb.outputs)
    out += [
        "/-- **The claim.** Every solution with admissible parameter values, admissible",
        "disturbances, the declared references, and the model's initial condition keeps",
        f"{names} within the bounds `b`. -/",
        f"def Claim (b : Fin {k} → ℚ) : Prop :=",
        "  ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics) (T : ℝ),",
        f"    {phyp} → IsSolutionOn p u x y T → Admissible u T → References u T →",
        "    ReferenceStart u → Initial p (x 0) →",
        "    " + " ∧\n    ".join(groups),
        "",
        f"end {pb.ns}.Spec",
        "",
    ]
    return "\n".join(out)


# --- Cert ---------------------------------------------------------------------------------------

def emit_cert(pb: LinearProblem, cert) -> str:
    n, m = len(pb.coords), len(pb.dists)
    ns = pb.ns
    nst = len(pb.states)
    poly = pb.vertices is not None
    K = len(pb.vertices) if poly else 0
    pnames, peqs = _param_hyps(pb)
    phyp = "Spec.ParamsOK p" if pb.params_ok is not None else "p.Bound"
    eh = [f"e{i}" for i in range(pb.n_eqs)]
    dr = [r for r in pb.refs if r.deriv]
    rs = [r for r in pb.refs if r.start is not None]
    out = [f"import {pb.module}.Spec",
           "import Dynacert.Linear.Polytopic" if poly else "import Dynacert.Linear.Channels", ""]
    out += lean.header(f"Certificate for `{pb.model_name}`",
                       "dynacert (" + ("polytopic, " if poly else "LTI, ") + "per-channel)")
    out += LINTERS + [
        "set_option maxRecDepth 10000",
        "",
        f"namespace {ns}.Cert",
        "",
        f"open Matrix Set Dynacert Dynacert.Linear {ns}",
        "",
        "/-! ### Link: the rumoca model, in coordinates `z`, is `ż = A z + B w` -/",
        "",
        "/-- Coordinates: " + ", ".join(f"`{c.name}`" for c in pb.coords) + ". -/",
        f"def vec (s : States) (v : Inputs) : Fin {n} → ℝ :=",
        "  ![" + ", ".join(_coord_def(c) for c in pb.coords) + "]",
        "/-- Disturbance channels: " + ", ".join(f"`{d}`" for d in pb.dists) + ". -/",
        f"def dist (v : Inputs) : Fin {m} → ℝ := ![" + ", ".join(f"v.{d}" for d in pb.dists) + "]",
        "",
    ]
    zs = [f"z {j}" for j in range(n)]
    wsym = [f"w {k}" for k in range(m)]
    if poly:
        out += [f"/-- Vertex matrices of the polytope of systems (corners of the parameter box). -/",
                f"def As : Fin {K} → Matrix (Fin {n}) (Fin {n}) ℚ :=",
                "  ![" + ",\n    ".join(mat(Av) for Av in pb.vertices) + "]",
                f"def Bm : Matrix (Fin {n}) (Fin {m}) ℚ := {mat(pb.B)}",
                "",
                "/-- Interpolation weights of the actual parameters. -/",
                f"noncomputable def weights (p : Params) : Fin {K} → ℝ :=",
                "  ![" + ", ".join(_weight(f) for f in pb.weights) + "]",
                ""]
        rows = []
        for i in range(n):
            parts = [f"wt {sg} * ({_lin(Av[i], zs)})" for sg, Av in enumerate(pb.vertices)
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
    else:
        out += [f"def model : LTIModel {n} {m} where",
                f"  A := {mat(pb.A)}",
                f"  B := {mat(pb.B)}",
                ""]
        rows = [" + ".join(p for p in (_lin(pb.A[i], zs), _lin(pb.B[i], wsym)) if p != "0") or "0"
                for i in range(n)]
        out += [
            f"theorem f_apply (z : Fin {n} → ℝ) (w : Fin {m} → ℝ) :",
            "    model.toSystem.f z w = ![" + ", ".join(rows) + "] := by",
            "  funext i",
            "  fin_cases i <;>",
            "    simp [LTIModel.toSystem, model, toReal, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring",
            "",
        ]
    lits = []
    for i, s_ in enumerate(pb.literals):
        out.append(f"theorem lit{i} : ({s_} : ℝ) = {q(Fraction(s_))} := by norm_num")
        lits.append(f"lit{i}")
    if pb.literals:
        out.append("")
    rewrite = ", ".join(peqs + lits)
    # hypothesis names by index: field names may be quoted («plant.x»)
    ch = {s_: f"hc{i}" for i, s_ in enumerate(pb.states)}
    dh = {s_: f"hd{i}" for i, s_ in enumerate(pb.states)}
    rc = {r.fld: f"hrc{i}" for i, r in enumerate(dr)}
    rd = {r.fld: f"hrd{i}" for i, r in enumerate(dr)}
    ref_der = {r.fld: r.deriv for r in dr}

    def cont_term(tm: Term) -> str:
        h = ch[tm.fld] if tm.kind == "x" else rc[tm.fld]
        return f"(continuousOn_const.mul {h})"

    def der_term(tm: Term) -> str:
        h = dh[tm.fld] if tm.kind == "x" else rd[tm.fld]
        return f"({h}.const_mul {_c(tm.coeff)})"

    def der_value(tm: Term) -> str:
        if tm.kind == "x":
            return f"{_c(tm.coeff)} * (dx t).{tm.fld}"
        return f"{_c(tm.coeff)} * (u t).{ref_der[tm.fld]}"

    def close(mult, ind):
        lc = _lc(mult, eh)
        return f"{ind}linear_combination {lc}" if lc else f"{ind}ring"

    if poly:
        out += [
            f"theorem weights_nonneg {{p : Params}} (hp : {phyp}) : ∀ i, 0 ≤ weights p i := by",
            f"  obtain {_conj(pnames)} := hp",
            "  intro i",
            "  fin_cases i",
        ]
        for f in pb.weights:
            facs = [f"(div_nonneg (by linarith) (by norm_num))" for _ in f]
            term = facs[0] if facs else "zero_le_one"
            for fc in facs[1:]:
                term = f"(mul_nonneg {term} {fc})"
            out += [f"  · show (0 : ℝ) ≤ {_weight(f)}", f"    exact {term}"]
        out += [
            "",
            f"theorem weights_sum (p : Params) : ∑ i, weights p i = 1 := by",
            "  simp [weights, Fin.sum_univ_succ]",
            "  ring",
            "",
        ]
        concl = ("    ContinuousOn (fun t => vec (x t) (u t)) (Icc 0 T) ∧ ∀ t ∈ Ico 0 T,\n"
                 "      HasDerivWithinAt (fun t => vec (x t) (u t))\n"
                 "        ((∑ i, weights p i • toReal (As i)) *ᵥ vec (x t) (u t) + toReal Bm *ᵥ dist (u t))\n"
                 "        (Ici t) t := by")
    else:
        concl = "    model.toSystem.IsSolution (fun t => vec (x t) (u t)) (fun t => dist (u t)) T := by"
    out += [
        f"theorem link {{p : Params}} (hp : {phyp}) {{u : ℝ → Inputs}} {{x : ℝ → States}}",
        "    {y : ℝ → Algebraics} {T : ℝ} (h : IsSolutionOn p u x y T)",
        "    (hr : Spec.References u T) :",
        concl,
    ]
    if pnames:
        out.append(f"  obtain {_conj(pnames)} := hp")
    out.append(f"  obtain ⟨dx, {', '.join(ch[s_] for s_ in pb.states)}, hder⟩ := h")
    if dr:
        out.append(f"  obtain ⟨{', '.join(rc[r.fld] for r in dr)}, hrder⟩ := hr")
    out += [
        "  refine ⟨?_, fun t ht => ?_⟩",
        "  · refine continuousOn_pi.mpr fun i => ?_",
        "    fin_cases i",
    ]
    for c in pb.coords:
        out += [f"    · show ContinuousOn (fun s => {_coord_expr(c, 's')}) (Icc 0 T)",
                f"      exact {_fold([cont_term(tm) for tm in c.terms], 'add')}"]
    out.append(f"  · obtain ⟨{', '.join(dh[s_] for s_ in pb.states)}, "
               f"{_conj(eh) if pb.n_eqs else '-'}⟩ := hder t ht")
    if dr:
        out.append(f"    obtain {_conj([rd[r.fld] for r in dr])} := hrder t ht")
    if rewrite and pb.n_eqs:
        out.append(f"    try simp only [{rewrite}] at {' '.join(eh)}")
    out += ["    rw [hasDerivWithinAt_pi]", "    intro i", "    fin_cases i"]
    zt = [_coord_expr(c, "t") for c in pb.coords]
    wt = [f"(u t).{d}" for d in pb.dists]
    for i, c in enumerate(pb.coords):
        dval = " + ".join(der_value(tm) for tm in c.terms)
        if poly:
            parts = [f"({_weight(f)}) * ({_lin(Av[i], zt)})"
                     for f, Av in zip(pb.weights, pb.vertices) if _lin(Av[i], zt) != "0"]
            bp = _lin(pb.B[i], wt)
            if bp != "0":
                parts.append(bp)
            rhs = " + ".join(parts) or "0"
        else:
            rhs = " + ".join(p for p in (_lin(pb.A[i], zt), _lin(pb.B[i], wt)) if p != "0") or "0"
        out += [
            f"    · show HasDerivWithinAt (fun s => {_coord_expr(c, 's')}) _ (Ici t) t",
            f"      refine ({_fold([der_term(tm) for tm in c.terms], 'add')}).congr_deriv ?_",
            "      rw [f_apply]",
            f"      show {dval} = {rhs}",
            close(pb.multipliers[i], "      "),
        ]
    out.append("")
    # certificate data
    idx = f"Fin {n} ⊕ Fin {m}"
    out += [
        "/-! ### Storage function `V z = zᵀ P z` and per-channel rates -/",
        "",
        f"def P : Matrix (Fin {n}) (Fin {n}) ℚ := {mat(cert.P)}",
        f"def α : ℚ := {q(cert.alpha)}",
        f"def γ : Fin {m} → ℚ := {vec(cert.gammas)}",
        "",
    ]
    if poly:
        for sg, (Lw, dw) in enumerate(cert.witnesses):
            Lt, dt = lean.sum_witness(Lw, dw, n, m)
            out += [
                f"def lmi{sg} : PSDWitness (channelLmi (As {sg}) Bm P α γ) :=",
                f"  ⟨{Lt},",
                f"   {dt},",
                "   by decide +kernel, by decide +kernel⟩",
                "",
            ]
        out += [
            f"def lmis : ∀ i, PSDWitness (channelLmi (As i) Bm P α γ)",
        ]
        for sg in range(K):
            out.append(f"  | ⟨{sg}, _⟩ => lmi{sg}")
        out += [
            f"  | ⟨n + {K}, h⟩ => absurd h (by omega)",
            "",
            "def cert : PolytopicCert As Bm :=",
            "  ⟨P, α, γ, by decide +kernel, by decide +kernel, by decide +kernel, lmis⟩",
            "",
        ]
    else:
        Lt, dt = lean.sum_witness(cert.lmi_L, cert.lmi_d, n, m)
        out += [
            f"def lmiL : Matrix ({idx}) ({idx}) ℚ :=",
            f"  {Lt}",
            f"def lmiD : {idx} → ℚ :=",
            f"  {dt}",
            "",
            "def cert : ChannelCert model :=",
            "  ⟨P, α, γ, by decide +kernel, by decide +kernel, by decide +kernel,",
            "    ⟨lmiL, lmiD, by decide +kernel, by decide +kernel⟩⟩",
            "",
        ]
    out += [
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
    for k, (o, b) in enumerate(zip(pb.outputs, cert.boxes)):
        out += [
            f"/-- `|{o.name}| ≤ {q(b.bound)}` on `{{zᵀPz ≤ level}}`. -/",
            f"def box{k} : LinearBoxCert P level {vec(o.row)} ({q(b.bound)}) :=",
            "  ⟨by decide +kernel, by decide +kernel,",
            f"    ⟨{mat(b.L)},",
            f"     {vec(b.d)},",
            "     by decide +kernel, by decide +kernel⟩⟩",
            "",
        ]
    # initial condition
    ih = [f"i{i}" for i in range(pb.n_init)]
    rh = [f"r{i}" for i in range(len(rs))]
    x0v = vec(pb.x0)
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
    # output identities
    for k, o in enumerate(pb.outputs):
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
        out.append(close(o.mult, "  "))
        out.append("")
    # the tube: the certified ellipsoid in the error frame, then the claim from it
    bvec = vec([b.bound for b in cert.boxes])
    coords = ", ".join(f"`{c.name}`" for c in pb.coords)
    out += [
        "/-- **Tube.** Under the hypotheses of `Spec.Claim`, the error-frame state",
        f"`z = vec (x t) (u t)` (coordinates {coords}) stays in the certified ellipsoid",
        "`zᵀ P z ≤ level` on `[0, T]`. With a reference trajectory this is a tube around it:",
        "the physical state lies in the reference plus this ellipsoid. -/",
        "theorem tube : ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics)",
        f"    (T : ℝ), {phyp} → IsSolutionOn p u x y T → Spec.Admissible u T →",
        "    Spec.References u T → Spec.ReferenceStart u → Initial p (x 0) →",
        "    ∀ t ∈ Icc 0 T, quad (toReal P) (vec (x t) (u t)) ≤ (level : ℝ) := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  have hx := link hp h hr",
        "  have hw : ∀ t ∈ Ico 0 T, cert.energy (dist (u t)) ≤",
        "      ∑ j, (γ j : ℝ) * ((δ j : ℝ) * (δ j : ℝ)) := by",
        "    intro t ht",
        "    have hut := hu t ht",
        "    refine cert.energy_le_of_abs_le (δ := δ) fun j => ?_",
        "    fin_cases j <;> simp [dist, δ] <;> simp_all",
        "  have h0' : quad (toReal cert.P) (vec (x 0) (u 0)) ≤ (level : ℝ) := by",
        "    rw [init hp h0 hr0]; exact init_le",
    ]
    if poly:
        out += [
            "  exact cert.invariant (wt := fun _ => weights p) hx.1 hx.2",
            "    (fun _ _ => weights_nonneg hp) (fun _ _ => weights_sum p) hw h0' budget_le",
        ]
    else:
        out += ["  exact cert.invariant hx hw h0' budget_le"]
    out += [
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
            out.append(f"{b}rw [out{k} hp h ht]; exact box{k}.abs_le (hV t {tt})")
    out += ["", f"end {ns}.Cert", ""]
    return "\n".join(out)
