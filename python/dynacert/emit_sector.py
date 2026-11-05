"""Lean emission for sector-multiplier certificates (`sector.py`).

Files under `certs/Certs/<Model>/` (prefix `Sector` for the joint certificate, `Compose` for the
compositional one):

* `<P>Link.lean`: the link to rumoca's equations. Coordinates `z` (the states), the residual
  channels `pᵢ` as real functions of the model's variables, the exact identity
  `ż = A z + B w` (by `linear_combination` of the equations), and `facts`: on the region box,
  every sector channel is `δ·q` with `δ ∈ [ℓ, u]` and every bounded channel is `|p| ≤ β`, proved
  from the lemmas of `Dynacert/Sector/Atoms.lean`.
* `<P>M<k>.lean`, one per ellipsoid (Lemma 1): the LMI data of each block, its
  `SectorCert` (dominance witness, `decide +kernel`), `diss`: `V̇ ≤ -α V + α c` wherever the
  facts hold, and the box certificates read from this ellipsoid.
* `<P>Cert.lean`: first exit (`region_invariant`) and the claim of `Spec.lean`.
"""

from __future__ import annotations

from fractions import Fraction

import sympy as sp

from . import lean as L
from .lean import q
from .sector import ExactCert, SectorProblem

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
    "set_option linter.style.multiGoal false",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 4000000",
]


def _r(x) -> str:
    """A rational literal at type ℝ."""
    return f"({q(Fraction(x))} : ℝ)"


def _qv(v) -> str:
    return "![" + ", ".join(q(x) for x in v) + "]"


def _rows(R) -> str:
    return "![" + ", ".join(_qv(r) for r in R) + "]" if R else "![]"


def _mat(X, r: int, c: int) -> str:
    if r == 0 or c == 0:
        return f"(0 : Matrix (Fin {r}) (Fin {c}) ℚ)"
    return L.mat(X)


def _sumrow(row, n, m) -> str:
    """A row over `Fin n ⊕ Fin m`."""
    a, b = row[:n], row[n:]
    sa = _qv(a) if n else "![]"
    sb = _qv(b) if m else "![]"
    return f"Sum.elim {sa} {sb}"


class Renderer:
    """sympy expressions in model symbols → Lean ℝ terms over `s : States`, `a : Algebraics`,
    `v : Inputs` (or other variable names)."""

    def __init__(self, prob, s="s", a="a", v="v"):
        self.extra = {"_delta": "δ"}
        self.roles = {}
        for var in prob.model.variables:
            if var.role == "state":
                self.roles[var.name] = (s, var.lean)
            elif var.role in ("algebraic", "output"):
                self.roles[var.name] = (a, var.lean)
            elif var.role == "input":
                self.roles[var.name] = (v, var.lean)

    def __call__(self, e) -> str:
        e = sp.sympify(e)
        if e.is_Rational:
            return _r(Fraction(int(e.p), int(e.q)))
        if e.is_Symbol:
            if e.name in self.extra:
                return self.extra[e.name]
            obj, fld = self.roles[e.name]
            return f"{obj}.{fld}"
        if e.is_Add:
            return "(" + " + ".join(self(t) for t in e.args) + ")"
        if e.is_Mul:
            return "(" + " * ".join(self(t) for t in e.args) + ")"
        if e.is_Pow and e.exp.is_Integer and e.exp > 0:
            return f"({self(e.base)} ^ {int(e.exp)})"
        if e.is_Pow and e.exp == sp.Rational(1, 2):
            return f"(Real.sqrt {self(e.base)})"
        if isinstance(e, sp.sin):
            return f"(Real.sin {self(e.args[0])})"
        if isinstance(e, sp.cos):
            return f"(Real.cos {self(e.args[0])})"
        if isinstance(e, sp.atan2):
            return f"(Rumoca.atan2 {self(e.args[0])} {self(e.args[1])})"
        raise ValueError(f"cannot render {e}")


def _placeholders(exprs, extra=()):
    """Replace functions (sin, cos, sqrt, atan2) by symbols, consistently."""
    rep = {}
    out = []
    for e in exprs:
        e = sp.sympify(e)
        for f in sorted(e.atoms(sp.Function, sp.Pow), key=sp.srepr):
            if isinstance(f, sp.Pow) and not (f.exp == sp.Rational(1, 2)):
                continue
            if f not in rep:
                rep[f] = sp.Symbol(f"_f{len(rep)}")
        out.append(e.xreplace(rep))
    return out, rep


def _lin_comb(target, divisors, gens):
    """Polynomial multipliers λₖ with target = Σ λₖ divisorₖ, by multivariate division with the
    leading generators first; raises if the remainder is not zero."""
    gens = list(dict.fromkeys(gens))
    qs, r = sp.reduced(sp.expand(target), [sp.expand(d) for d in divisors], *gens, order="lex")
    if sp.expand(r) != 0:
        raise ValueError(f"identity is not a combination of the equations (remainder {r})")
    return qs


class Ctx:
    """Shared emission context for one model."""

    def __init__(self, prob, sp_: SectorProblem, cert: ExactCert, prefix: str):
        self.prob, self.sp, self.cert, self.prefix = prob, sp_, cert, prefix
        m = prob.model
        self.ns = sp_.ns
        self.mod = f"Certs.{sp_.ns}"
        self.R = Renderer(prob)
        self.eqs = sp_.eqs                  # residuals lhs - rhs, params substituted
        self.n = sp_.n
        self.nch = len(sp_.channels)
        self.M = self.nch + len(sp_.dists)  # joint signal count
        self.params = [v for v in m.params if v.binding is not None]
        self.der = m.der
        self.state_syms = [m.var(nm).symbol for nm in sp_.states]
        self.alg_syms = [v.symbol for v in m.algebraics]
        self.lin_algs = [m.var(nm).symbol for nm in sp_.lin_alg]

    # --- names -----------------------------------------------------------------------------
    @property
    def link(self) -> str:
        return f"{self.prefix}Link"

    def member(self, k: int) -> str:
        return f"{self.prefix}M{k}"


# --- the Link file -------------------------------------------------------------------------------

def _pvals(ctx: Ctx):
    """(names, statements) of the parameter-value facts used to rewrite the equations."""
    names, stmts = [], []
    for k, v in enumerate(ctx.params):
        val = ctx.sp.param_values.get(v.name)
        if val is None:
            continue
        names.append(f"pv{k}")
        stmts.append(f"p.{v.lean} = {_r(val)}")
    return names, stmts


def _eq_names(ctx):
    return [f"e{k}" for k in range(len(ctx.eqs))]


def _q_expr(row, z="z") -> str:
    parts = [f"{_r(c)} * {z} {i}" for i, c in enumerate(row) if c != 0]
    return " + ".join(parts) if parts else "0"


def _region_conj(ctx) -> list[str]:
    return [f"|{ctx.R(c.expr)}| ≤ {_r(ctx.cert.region[i])}" for i, c in enumerate(ctx.sp.coords)]


def emit_link(ctx: Ctx) -> str:
    sp_, c, R = ctx.sp, ctx.cert, ctx.R
    n, M, nch = ctx.n, ctx.M, ctx.nch
    out = [f"import {ctx.mod}.Model", "import Dynacert.Sector.Cert", "import Dynacert.Sector.Atoms",
           ""]
    out += L.header(f"Sector link for `{sp_.model_name}`", "dynacert (sector multipliers)")
    out += LINTERS + ["", f"namespace {ctx.ns}.{ctx.link}", "",
                      f"open Matrix Set Real Dynacert Dynacert.Linear Dynacert.Sector {ctx.ns}",
                      ""]
    out += [f"/-- Coordinates: the states `{', '.join(sp_.states)}`. -/",
            f"def vec (s : States) : Fin {n} → ℝ := ![" + ", ".join(f"s.{f}" for f in sp_.sfields)
            + "]", ""]
    # channels
    for j, ch in enumerate(sp_.channels):
        kind = "sector" if ch.kind == "sector" else "bounded"
        out += [f"/-- Residual channel {j} ({kind}): `{ch.expr}`. -/",
                f"noncomputable def ch{j} (s : States) (a : Algebraics) : ℝ := {R(ch.expr)}", ""]
    sig = [f"ch{j} s a" for j in range(nch)] + [f"v.{f}" for f in sp_.dist_fields]
    out += ["/-- The signals `w`: residual channels, then disturbances. -/",
            f"noncomputable def sig (s : States) (a : Algebraics) (v : Inputs) : Fin {M} → ℝ :=",
            "  ![" + ", ".join(sig) + "]", ""]
    B = [[ch.col.get(i, Fraction(0)) for ch in sp_.channels] + list(sp_.Bw[i]) for i in range(n)]
    ctx.B = B
    out += ["/-- Exact linear part and channel input matrix: `ż = A z + B w`. -/",
            f"def A : Matrix (Fin {n}) (Fin {n}) ℚ := {L.mat(sp_.A)}",
            f"def B : Matrix (Fin {n}) (Fin {M}) ℚ := {L.mat(B)}", ""]
    rows = []
    for i in range(n):
        parts = [f"{_r(sp_.A[i][j])} * z {j}" for j in range(n) if sp_.A[i][j] != 0]
        parts += [f"{_r(B[i][j])} * w {j}" for j in range(M) if B[i][j] != 0]
        rows.append(" + ".join(parts) if parts else "0")
    out += [f"theorem field_apply (z : Fin {n} → ℝ) (w : Fin {M} → ℝ) :",
            "    toReal A *ᵥ z + toReal B *ᵥ w = ![" + ", ".join(rows) + "] := by",
            "  funext i",
            "  fin_cases i <;> simp [A, B, toReal, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring",
            ""]
    # q forms
    for k, row in enumerate(sp_.qforms):
        out += [f"/-- Sector variable {k}: `{sp_.qexprs[k]}`. -/",
                f"noncomputable def Q{k} (z : Fin {n} → ℝ) : ℝ := {_q_expr(row)}", ""]
    # facts
    facts = []
    for j, ch in enumerate(sp_.channels):
        if ch.kind == "sector":
            lo, hi = c.gains[j]
            facts.append(f"(∃ δ ∈ Icc {_r(lo)} {_r(hi)}, w {j} = δ * Q{ch.q} z)")
        else:
            facts.append(f"|w {j}| ≤ {_r(c.betas[j])}")
    for d, b in enumerate(sp_.dist_bounds):
        facts.append(f"|w {nch + d}| ≤ {_r(b)}")
    ctx.n_facts = len(facts)
    out += ["/-- What the certificate needs of the signals on the region: sector channels are",
            "`δ q` with `δ ∈ [ℓ, u]`, the other channels and the disturbances are bounded. -/",
            f"def Facts (z : Fin {n} → ℝ) (w : Fin {M} → ℝ) : Prop :=",
            "  " + " ∧\n  ".join(facts), ""]
    # parameter values
    pn, ps = _pvals(ctx)
    bh = [f"hb{i}" for i in range(len(ctx.params))]
    out += ["theorem pvals {p : Params} (hp : p.Bound) :",
            "    " + " ∧ ".join(ps) + " := by",
            f"  obtain {_conj(bh)} := hp",
            "  refine " + _conj(["?_"] * len(ps)) + " <;> norm_num [" + ", ".join(bh) + "]", ""]
    ctx.pnames = pn
    # link: derivatives
    m = ctx.prob.model
    states = [m.var(nm) for nm in sp_.states]
    hc = [f"hc{i}" for i in range(n)]
    hd = [f"hd{i}" for i in range(n)]
    eh = _eq_names(ctx)
    simp_eq = f"try simp only [{', '.join(pn)}] at {' '.join(eh)}" if pn else ""
    lines = [
        "/-- **Link.** Along a solution, `z = vec x` is continuous and `ż = A z + B w`. -/",
        "theorem link {p : Params} (hp : p.Bound) {u : ℝ → Inputs} {x : ℝ → States}",
        "    {y : ℝ → Algebraics} {T : ℝ} (h : IsSolutionOn p u x y T) :",
        "    ContinuousOn (fun t => vec (x t)) (Icc 0 T) ∧",
        "    ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => vec (x t))",
        "      (toReal A *ᵥ vec (x t) + toReal B *ᵥ sig (x t) (y t) (u t)) (Ici t) t := by",
        f"  obtain {_conj(pn)} := pvals hp" if pn else "",
        f"  obtain ⟨dx, {', '.join(hc)}, hder⟩ := h",
        "  refine ⟨?_, fun t ht => ?_⟩",
        "  · refine continuousOn_pi.mpr fun i => ?_",
        "    fin_cases i",
    ]
    lines += [f"    · exact {hc[i]}" for i in range(n)]
    lines += [f"  · obtain ⟨{', '.join(hd)}, {_conj(eh)}⟩ := hder t ht",
              f"    {simp_eq}" if simp_eq else "",
              "    rw [field_apply, hasDerivWithinAt_pi]",
              "    intro i",
              "    fin_cases i"]
    # identities
    Rt = Renderer(ctx.prob, s="(x t)", a="(y t)", v="(u t)")
    zsyms = ctx.state_syms
    chex = [ch.expr for ch in sp_.channels]
    wsyms = [m.var(d).symbol for d in sp_.dists]
    for i, v in enumerate(states):
        dsym = m.der[v.name]
        rhs = sum((sp.Rational(sp_.A[i][j].numerator, sp_.A[i][j].denominator) * zsyms[j]
                   for j in range(n)), sp.Integer(0))
        rhs += sum((sp.Rational(B[i][j].numerator, B[i][j].denominator) *
                    (chex[j] if j < nch else wsyms[j - nch]) for j in range(M)), sp.Integer(0))
        lc = _identity(ctx, dsym, rhs, [_der_eq(ctx, v.name)], Rt)
        rhs_lean = _row_lean(ctx, i, Rt)
        lines += [f"    · show HasDerivWithinAt (fun s => (x s).{v.lean}) _ (Ici t) t",
                  f"      refine {hd[i]}.congr_deriv ?_",
                  f"      show (dx t).{v.lean} = {rhs_lean}",
                  f"      linear_combination {lc}"]
    out += [ln for ln in lines if ln != ""] + [""]
    out += ["theorem eqs_at {p : Params} {u : ℝ → Inputs} {x : ℝ → States} {y : ℝ → Algebraics}",
            "    {T : ℝ} (h : IsSolutionOn p u x y T) {t : ℝ} (ht : t ∈ Ico 0 T) :",
            "    ∃ ds : States, Equations t p (u t) (x t) ds (y t) := by",
            f"  obtain ⟨dx, {', '.join(hc)}, hder⟩ := h",
            f"  obtain ⟨{', '.join(hd)}, hE⟩ := hder t ht",
            "  exact ⟨dx t, hE⟩", ""]
    # initial
    out += _init_lines(ctx)
    # coordinates as linear forms of z
    out += _coord_lines(ctx)
    # facts from the region
    out += _facts_lines(ctx)
    out += [f"end {ctx.ns}.{ctx.link}", ""]
    return "\n".join(out)


def _conj(names):
    if not names:
        return "⟨⟩"
    return names[0] if len(names) == 1 else "⟨" + ", ".join(names) + "⟩"


def _der_eq(ctx, state_name) -> int:
    m = ctx.prob.model
    d = m.der[state_name]
    for k, e in enumerate(m.equations):
        if e.lhs == d:
            return k
    raise ValueError(state_name)


def _row_lean(ctx, i, Rt) -> str:
    sp_, B = ctx.sp, ctx.B
    parts = [f"{_r(sp_.A[i][j])} * (x t).{sp_.sfields[j]}" for j in range(ctx.n)
             if sp_.A[i][j] != 0]
    for j in range(ctx.M):
        if B[i][j] == 0:
            continue
        if j < ctx.nch:
            parts.append(f"{_r(B[i][j])} * {Rt(sp_.channels[j].expr)}")
        else:
            parts.append(f"{_r(B[i][j])} * (u t).{sp_.dist_fields[j - ctx.nch]}")
    return " + ".join(parts) if parts else "0"


def _identity(ctx, lhs_sym, rhs, extra_eqs, Rt, eqnames=None, coef_syms=()) -> str:
    """`linear_combination` argument proving `lhs_sym = rhs` from equation `extra_eqs` (with
    multiplier found by division) and the linear-algebraic equations."""
    sp_ = ctx.sp
    eqnames = eqnames or _eq_names(ctx)
    lin_idx = [sp_.alg_eq[nm] for nm in sp_.lin_alg]
    # polynomial algebraics are eliminated outermost first (lex order: each defining equation
    # leads with its own variable)
    poly = list(reversed(sp_.poly_alg))
    idx = list(extra_eqs) + [sp_.alg_eq[nm] for nm in poly] + lin_idx
    divs = [ctx.eqs[k] for k in idx]
    (target, *divs), rep = _placeholders([sp.sympify(lhs_sym) - rhs] + divs)
    gens = ([sp.sympify(lhs_sym)] if lhs_sym is not None and lhs_sym != 0 else []) + \
        [ctx.prob.model.var(nm).symbol for nm in poly] + [s for s in ctx.lin_algs]
    others = sorted((target.free_symbols | set().union(*[d.free_symbols for d in divs]))
                    - set(gens), key=str)
    qs = _lin_comb(target, divs, gens + others)
    inv = {v: k for k, v in rep.items()}
    parts = []
    for k, lam in zip(idx, qs):
        lam = sp.expand(lam).xreplace(inv)
        if lam == 0:
            continue
        parts.append(f"({Rt(lam)}) * {eqnames[k]}")
    return " + ".join(parts) if parts else "0"


def _init_lines(ctx) -> list[str]:
    m = ctx.prob.model
    st = [m.var(nm) for nm in ctx.sp.states]
    inits = [v for v in m.states if v.start is not None]
    ih = [f"i{k}" for k in range(len(inits))]
    return [
        "theorem init {p : Params} (hp : p.Bound) {s : States} (h0 : Initial p s) :",
        f"    vec s = 0 := by",
        f"  obtain {_conj(_pvals(ctx)[0])} := pvals hp" if _pvals(ctx)[0] else "  skip",
        f"  obtain {_conj(ih)} := h0",
        "  funext i",
        f"  fin_cases i <;> simp [vec, {', '.join(ih)}]",
        "",
    ]


def _coord_lines(ctx) -> list[str]:
    """`coord_k : expr = row · z` for every region coordinate."""
    out = []
    Rs = Renderer(ctx.prob)
    pn = _pvals(ctx)[0]
    eh = _eq_names(ctx)
    for k, c in enumerate(ctx.sp.coords):
        z = ctx.state_syms
        rhs = sum((sp.Rational(v.numerator, v.denominator) * z[i] for i, v in enumerate(c.row)),
                  sp.Integer(0))
        lc = _identity(ctx, c.expr, rhs, [], Rs)
        out += [f"theorem coord{k} {{p : Params}} (hp : p.Bound) {{t : ℝ}} {{v : Inputs}}",
                "    {s ds : States} {a : Algebraics} (hE : Equations t p v s ds a) :",
                f"    {Rs(c.expr)} = {_q_expr(c.row, 'vec s')} := by",
                f"  obtain {_conj(pn)} := pvals hp" if pn else "  skip",
                f"  obtain {_conj(eh)} := hE",
                f"  try simp only [{', '.join(pn)}] at {' '.join(eh)}" if pn else "  skip",
                "  simp only [vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]",
                f"  linear_combination {lc}", ""]
    return out


def _atom_hyps(ctx, a, Rs) -> list[str]:
    """`have` lines giving the defining equation of an atom in canonical form and the
    hypotheses of its lemma (argument ranges) on the region."""
    out = []
    reg = ctx.cert.region
    if a.alg is not None:
        k = ctx.sp.alg_eq[a.alg]
        out.append(f"  have hdef_{a.alg} : a.{ctx.prob.model.var(a.alg).lean} = {Rs(a.expr)} := by")
        out.append(f"    rw [e{k}]; try ring_nf")
    return out


def _arg_abs(ctx, a, key, Rs) -> tuple[str, str, Fraction]:
    """(name, have-line, bound) for `|arg| ≤ bound` of an atom argument from the region."""
    i, lam, c0 = a.args[key]
    arg = a.lean_args[key] if key != "L" else a.expr.args[0]
    b = abs(lam) * ctx.cert.region[i]
    nm = f"hA{ctx.atoms.index(a)}{key}"
    line = (f"  have {nm} : |{Rs(arg)}| ≤ {_r(b)} := abs_le.mpr ⟨by linarith [(abs_le.mp hR{i}).1,"
            f" (abs_le.mp hR{i}).2], by linarith [(abs_le.mp hR{i}).1, (abs_le.mp hR{i}).2]⟩")
    return nm, line, b


def _h_icc(ctx, a, Rs):
    i, lam, c0 = a.args["h"]
    c = abs(lam) * ctx.cert.region[i]
    h0, h1 = a.h0 - c, a.h0 + c
    nm = f"hA{ctx.atoms.index(a)}h"
    line = (f"  have {nm} : {Rs(a.lean_args['h'])} ∈ Icc {_r(h0)} {_r(h1)} := ⟨by linarith "
            f"[(abs_le.mp hR{i}).1, (abs_le.mp hR{i}).2], by linarith [(abs_le.mp hR{i}).1, "
            f"(abs_le.mp hR{i}).2]⟩")
    return nm, line, h0, h1


def _facts_lines(ctx) -> list[str]:
    """`facts`: the region and the equations give `Facts (vec s) (sig s a v)`."""
    sp_, c = ctx.sp, ctx.cert
    Rs = Renderer(ctx.prob)
    ctx.atoms = sp_.atoms
    pn = _pvals(ctx)[0]
    eh = _eq_names(ctx)
    hR = [f"hR{i}" for i in range(len(sp_.coords))]
    hw = [f"hw{d}" for d in range(len(sp_.dists))]
    wb = " ∧ ".join(f"|v.{f}| ≤ {_r(b)}" for f, b in zip(sp_.dist_fields, sp_.dist_bounds))
    out = ["/-- **Rigorous residual bounds.** On the region box, every channel satisfies its",
           "sector or peak bound (lemmas of `Dynacert/Sector/Atoms.lean`). -/",
           "theorem facts {p : Params} (hp : p.Bound) {t : ℝ} {v : Inputs} {s ds : States}",
           "    {a : Algebraics} (hE : Equations t p v s ds a)",
           "    (hR : " + " ∧ ".join(_region_conj(ctx)) + ")",
           f"    (hw : {wb}) :" if wb else "    (hw : True) :",
           "    Facts (vec s) (sig s a v) := by",
           f"  obtain {_conj(pn)} := pvals hp" if pn else "  skip",
           f"  obtain {_conj(eh)} := hE",
           f"  try simp only [{', '.join(pn)}] at {' '.join(eh)}" if pn else "  skip",
           f"  obtain {_conj(hR)} := hR",
           f"  obtain {_conj(hw)} := hw" if hw else "  skip"]
    used = set()
    for j, ch in enumerate(sp_.channels):
        rule = ch.rule
        if rule[0] == "poly":
            atoms = [t[3] for t in rule[1] if t[2]]
        elif rule[0] in ("sinrem", "atan2rem", "prod_gain"):
            atoms = [rule[1]]
        else:
            atoms = [f[1] for f in rule[1]]
        for a in atoms:
            if id(a) not in used:
                used.add(id(a))
                out += _atom_hyps(ctx, a, Rs)
                if a.kind == "unit":
                    out += _unit_hyp(ctx, a, Rs)
                elif a.kind in ("sin", "cos"):
                    out.append(_arg_abs(ctx, a, "L", Rs)[1])
                elif a.kind in ("norm",):
                    out.append(_arg_abs(ctx, a, "s", Rs)[1])
                    out.append(_h_icc(ctx, a, Rs)[1])
                elif a.kind == "atan2":
                    out.append(_arg_abs(ctx, a, "y", Rs)[1])
                    out.append(_h_icc(ctx, a, Rs)[1])
    conj = []
    for j, ch in enumerate(sp_.channels):
        conj.append(_fact_proof(ctx, j, ch, Rs))
    for d in range(len(sp_.dists)):
        conj.append([f"    simpa [sig] using hw{d}"])
    out.append("  refine " + _conj(["?_"] * len(conj)))
    for pr in conj:
        out.append("  ·" + pr[0][3:])
        out += pr[1:]
    out += [""]
    return out


def _unit_hyp(ctx, a, Rs) -> list[str]:
    """`|q0 - 1| ≤ X/(2 - X)` on the region (`sqrt_one_sub_sub_one_le`)."""
    from .sector import unit_rho_bound
    ai = ctx.atoms.index(a)
    reg = ctx.cert.region
    xs = [a.lean_args[k] for k in sorted(a.args)]
    hs, X = [], Fraction(0)
    for k in sorted(a.args):
        i, lam, _ = a.args[k]
        if a.lean_args[k] != ctx.sp.coords[i].expr or lam != 1:
            raise ValueError(f"quaternion chart argument {a.lean_args[k]} is not a coordinate")
        hs.append(f"sq_le_of_abs_le hR{i}")
        X += reg[i] ** 2
    rho = unit_rho_bound(a, reg)
    lhs = f"a.{ctx.prob.model.var(a.alg).lean}"
    ssum = " + ".join(f"{Rs(x)} ^ 2" for x in xs)
    return [
        f"  have hU{ai} : |{lhs} - 1| ≤ {_r(rho)} := by",
        f"    rw [hdef_{a.alg}, show {Rs(a.expr.base)} = 1 - ({ssum}) by ring]",
        f"    exact (sqrt_one_sub_sub_one_le (X := {_r(X)}) (by positivity) "
        f"(by linarith [{', '.join(hs)}]) (by norm_num)).trans (by norm_num)"]


def _poly_proof(ctx, j, ch, Rs) -> list[str]:
    """Fact `j` for a grouped polynomial channel: `δ = Σ c·Π factors·(q0 - 1)ʲ`, each term bounded
    by the region (`abs_mul_le_of`), summed (`abs_add_le_of`)."""
    sp_, c = ctx.sp, ctx.cert
    terms = ch.rule[1]
    k_atom = {id(a): i for i, a in enumerate(sp_.atoms)}
    tstr, tprf = [], []
    for coef, others, jj, unit in terms:
        fs, hs = [], []
        for f, ci, lam in others:
            if f != sp_.coords[ci].expr or lam != 1:
                raise ValueError(f"product factor {f} is not a region coordinate")
            fs.append(Rs(f))
            hs.append(f"hR{ci}")
        for _ in range(jj):
            fs.append(f"(a.{ctx.prob.model.var(unit.alg).lean} - 1)")
            hs.append(f"hU{k_atom[id(unit)]}")
        cabs = abs(coef)
        hc = f"(abs_le.mpr ⟨by norm_num, by norm_num⟩ : |{_r(coef)}| ≤ {_r(cabs)})"
        acc = hs[0]
        for h in hs[1:]:
            acc = f"(abs_mul_le_of {acc} {h})"
        tstr.append(f"({_r(coef)} * ({' * '.join(fs)}))")
        tprf.append(f"(abs_mul_le_of {hc} {acc})")
    dsum = " + ".join(tstr)
    acc = tprf[0]
    for h in tprf[1:]:
        acc = f"(abs_add_le_of {acc} {h})"
    out = [f"    have habs := {acc}"]
    unfold = f"simp only [sig, ch{j}, " + (f"Q{ch.q}, " if ch.q is not None else "") + \
        "vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]"
    delta = sum((sp.Rational(t[0].numerator, t[0].denominator) *
                 sp.Mul(*[f for f, _, _ in t[1]]) *
                 (ctx.prob.model.var(t[3].alg).symbol - 1) ** t[2] if t[2] else
                 sp.Rational(t[0].numerator, t[0].denominator) * sp.Mul(*[f for f, _, _ in t[1]])
                 for t in terms), sp.Integer(0))
    if ch.kind == "sector":
        lo, hi = c.gains[j]
        Q = sum((sp.Rational(v.numerator, v.denominator) * ctx.state_syms[i]
                 for i, v in enumerate(sp_.qforms[ch.q])), sp.Integer(0))
        lc = _lin_comb_eqs(ctx, ch.expr - delta * Q, Rs, None)
        return out + [
            f"    refine ⟨{dsum}, gain_of_abs habs (by norm_num) (by norm_num), ?_⟩",
            f"    {unfold}",
            f"    linear_combination {lc}"]
    return out + [
        f"    have heq : sig s a v {j} = {dsum} := by",
        f"      {unfold}",
        "      ring",
        "    rw [heq]",
        "    exact habs.trans (by norm_num)"]


def _qfun(ctx, k) -> str:
    return f"Q{k} (vec s)"


def _fact_proof(ctx, j, ch, Rs) -> list[str]:
    """Lines (indented by 4) proving fact `j` for `w = sig s a v`, `z = vec s`."""
    sp_, c = ctx.sp, ctx.cert
    kind = ch.rule[0]
    if kind == "poly":
        return _poly_proof(ctx, j, ch, Rs)
    eh = _eq_names(ctx)
    k_atom = {id(a): i for i, a in enumerate(sp_.atoms)}
    unfold = f"simp only [sig, ch{j}, Q{ch.q} , vec, Matrix.cons_val_zero, Matrix.cons_val_one, " \
             "Matrix.cons_val, Fin.isValue]" if ch.q is not None else ""
    if kind in ("sinrem", "prod_gain", "atan2rem"):
        a = ch.rule[1]
        lo, hi = c.gains[j]
        ai = k_atom[id(a)]
        delta = sp.Symbol("_delta")
        if kind == "sinrem":
            L_ = a.expr.args[0]
            aa = _arg_abs(ctx, a, "L", Rs)[2]
            get = [f"    obtain ⟨δ, hδ, hk⟩ := sin_sub_self_gain (lo := {_r(lo)}) (hi := {_r(hi)}) "
                   f"hA{ai}L (by norm_num) (by norm_num)"]
            hk = sp.sin(L_) - L_ - delta * L_
            dterm = delta
        elif kind == "prod_gain":
            L_ = a.expr.args[0]
            get = [f"    have hδ : Real.sin {Rs(L_)} ∈ Icc {_r(lo)} {_r(hi)} := gain_of_abs "
                   f"(abs_sin_le_of hA{ai}L) (by norm_num) (by norm_num)"]
            hk = sp.Integer(0)
            dterm = sp.sin(L_)
        else:
            y, h = a.lean_args["y"], a.lean_args["h"]
            b = _arg_abs(ctx, a, "y", Rs)[2]
            _, _, h0, h1 = _h_icc(ctx, a, Rs)
            k = 1 / a.h0
            get = [f"    obtain ⟨δ, hδ, hk⟩ := atan2_sub_gain (h0 := {_r(h0)}) (h1 := {_r(h1)}) "
                   f"(b := {_r(b)}) (k := {_r(k)}) (lo := {_r(lo)}) (hi := {_r(hi)}) (by norm_num) "
                   f"hA{ai}h hA{ai}y (by norm_num) (by norm_num) (by norm_num)"]
            hk = sp.atan2(y, h) - sp.Rational(k.numerator, k.denominator) * y - delta * y
            dterm = delta
        # identity: ch - δ Q = hk + Σ λ (equations)
        Q = sum((sp.Rational(v.numerator, v.denominator) * ctx.state_syms[i]
                 for i, v in enumerate(sp_.qforms[ch.q])), sp.Integer(0))
        hk_name = "hk" if hk != 0 else None
        target = ch.expr - dterm * Q - hk
        lc = _lin_comb_eqs(ctx, target, Rs, a)
        if hk_name:
            lc = "hk" + (" + " + lc if lc != "0" else "")
        dlean = "δ" if dterm is delta else f"Real.sin {Rs(a.expr.args[0])}"
        return [f"    {get[0].strip()}"] + get[1:] + [
            f"    refine ⟨{dlean}, hδ, ?_⟩",
            f"    {unfold}",
            f"    linear_combination {lc}"]
    # bounded: product of factors
    fs, bnds, haves = [], [], []
    for t, (fk, a) in enumerate(ch.rule[1]):
        ai = k_atom[id(a)]
        nm = f"hf{t}"
        if a.kind == "norm":
            s_ = a.lean_args["s"]
            h = a.lean_args["h"]
            b = _arg_abs(ctx, a, "s", Rs)[2]
            _, _, h0, h1 = _h_icc(ctx, a, Rs)
            lhs = f"a.{ctx.prob.model.var(a.alg).lean}"
            if fk == "rho":
                e = f"{lhs} - {Rs(h)}"
                val = b * b / (2 * h0)
                pr = (f"(by rw [hdef_{a.alg}]; exact (abs_sqrt_sub_le (b := {_r(b)}) "
                      f"(h0 := {_r(h0)}) (by norm_num) hA{ai}h.1 hA{ai}s).trans (by norm_num))")
            else:
                e = lhs
                val = h1 + b * b / (2 * h0)
                pr = (f"(by rw [hdef_{a.alg}]; exact (abs_sqrt_le (b := {_r(b)}) (h0 := {_r(h0)}) "
                      f"(h1 := {_r(h1)}) (by norm_num) hA{ai}h hA{ai}s).trans (by norm_num))")
        elif a.kind == "cos":
            L_ = a.expr.args[0]
            aa = _arg_abs(ctx, a, "L", Rs)[2]
            if fk == "rho":
                e = f"Real.cos {Rs(L_)} - 1"
                val = aa * aa / 2
                pr = f"((abs_cos_sub_one_le hA{ai}L).trans (by norm_num))"
            else:
                e = f"Real.cos {Rs(L_)}"
                val = Fraction(1)
                pr = f"(abs_cos_le_one _)"
        elif a.kind == "sin" and fk == "atom":
            L_ = a.expr.args[0]
            aa = _arg_abs(ctx, a, "L", Rs)[2]
            e = f"Real.sin {Rs(L_)}"
            val = aa
            pr = f"((abs_sin_le_of hA{ai}L).trans (by norm_num))"
        else:
            raise ValueError(f"no Lean bound for {fk} of {a.kind}")
        from .sector import up
        val = up(val)
        haves.append(f"    have {nm} : |{e}| ≤ {_r(val)} := {pr}")
        fs.append(e)
        bnds.append(nm)
    prod = " * ".join(f"({e})" for e in fs)
    acc = bnds[0]
    for b in bnds[1:]:
        acc = f"(abs_mul_le_of {acc} {b})"
    return haves + [
        f"    have heq : sig s a v {j} = {prod} := by",
        f"      simp only [sig, ch{j}, Matrix.cons_val_zero, Matrix.cons_val_one, "
        "Matrix.cons_val, Fin.isValue]",
        f"      ring",
        f"    rw [heq]",
        f"    exact {acc}.trans (by norm_num)"]


def _lin_comb_eqs(ctx, target, Rs, atom) -> str:
    """Multipliers of the linear-algebraic equations (and the atom's defining equation) that
    prove `target = 0`."""
    sp_ = ctx.sp
    lin_idx = [sp_.alg_eq[nm] for nm in sp_.lin_alg]
    idx = list(lin_idx)
    names = [f"e{k}" for k in idx]
    divs = [ctx.eqs[k] for k in idx]
    if atom is not None and atom.alg is not None:
        sym = ctx.prob.model.var(atom.alg).symbol
        divs.append(sym - atom.expr)
        names.append(f"hdef_{atom.alg}")
    (t2, *d2), rep = _placeholders([target] + divs)
    gens = [ctx.prob.model.var(atom.alg).symbol] if atom is not None and atom.alg else []
    gens += list(ctx.lin_algs)
    others = sorted((t2.free_symbols | set().union(*[d.free_symbols for d in d2])) - set(gens),
                    key=str)
    qs = _lin_comb(t2, d2, gens + others)
    inv = {v: k for k, v in rep.items()}
    parts = []
    for nm, lam in zip(names, qs):
        lam = sp.expand(lam).xreplace(inv)
        if lam != 0:
            parts.append(f"({_render_delta(Rs, lam)}) * {nm}")
    return " + ".join(parts) if parts else "0"


def _render_delta(Rs, e):
    return Rs(e)


# --- member files --------------------------------------------------------------------------------

def _iface_expr(ctx, row) -> str:
    return _q_expr(row, "z")


def emit_member(ctx: Ctx, k: int, blocks, ifaces) -> str:
    """One ellipsoid (Lemma 1 family member): LMI data and witnesses per block, `diss`, boxes."""
    sp_, c = ctx.sp, ctx.cert
    em = c.members[k]
    n, M = ctx.n, ctx.M
    ns = f"{ctx.ns}.{ctx.member(k)}"
    out = [f"import {ctx.mod}.{ctx.link}", ""]
    out += L.header(f"Sector certificate data for `{sp_.model_name}`: ellipsoid {k} "
                    f"(objective `{em.name}`)", "dynacert (sector multipliers)")
    out += LINTERS + ["", f"namespace {ns}", "",
                      f"open Matrix Set Dynacert Dynacert.Linear Dynacert.Sector {ctx.ns} "
                      f"{ctx.ns}.{ctx.link}", ""]
    nb_all = len(em.blocks)
    for b, (eb, blk) in enumerate(zip(em.blocks, blocks)):
        nb, mb, sb, kb = len(eb.idx), len(eb.signals), len(eb.ch), len(eb.sigma)
        ws = []
        for kind, j in eb.signals:
            if kind == "chan":
                ws.append(f"w {j}")
            elif kind == "dist":
                ws.append(f"w {ctx.nch + j}")
            else:
                ws.append(f"({_iface_expr(ctx, ifaces[j].row)})")
        N = nb + mb
        Lw, dw = L.sum_witness(eb.L, eb.d, nb, mb)
        out += [f"/-! ### Block {b}: states " + ", ".join(sp_.states[i] for i in eb.idx) + " -/",
                "",
                f"def idx{b} : Fin {nb} → Fin {n} := ![" + ", ".join(map(str, eb.idx)) + "]",
                f"noncomputable def wsel{b} (z : Fin {n} → ℝ) (w : Fin {M} → ℝ) : Fin {mb} → ℝ :=",
                "  ![" + ", ".join(ws) + "]",
                f"def D{b} : SectorData {nb} {mb} {sb} {kb} where",
                f"  A := {_mat(eb.A, nb, nb)}",
                f"  B := {_mat(eb.B, nb, mb)}",
                f"  q := " + ("![" + ", ".join(_sumrow(r, nb, mb) for r in eb.q) + "]"
                              if sb else "![]"),
                f"  ch := ![" + ", ".join(map(str, eb.ch)) + "]",
                f"  lo := {_qv(eb.lo) if sb else '![]'}",
                f"  hi := {_qv(eb.hi) if sb else '![]'}",
                f"  γ := {_qv(eb.gamma)}",
                f"  σ := {_qv(eb.sigma) if kb else '![]'}",
                f"  r := " + ("![" + ", ".join(_sumrow(r, nb, mb) for r in eb.r) + "]"
                              if kb else "![]"),
                f"  P := {L.mat(eb.P)}",
                f"  α := {q(eb.alpha)}",
                f"  τ := {_qv(eb.tau) if sb else '![]'}",
                "",
                f"/-- LMI (8)/(9) for block {b}, checked by the kernel. -/",
                f"def C{b} : SectorCert D{b} where",
                "  hα := by decide +kernel",
                "  hτ := by decide +kernel",
                "  hγ := by decide +kernel",
                "  P_symm := by decide +kernel",
                f"  lmi := ⟨{Lw},",
                f"    {dw}, by decide +kernel, by decide +kernel⟩",
                "",
                f"def Ppsd{b} : DomWitness D{b}.P :=",
                f"  ⟨{L.mat(eb.PL)}, {L.vec(eb.Pd)}, by decide +kernel, by decide +kernel⟩",
                "",
                f"def δ{b} : Fin {mb} → ℚ := "
                + _qv([eb.deltas.get(pos, Fraction(0)) for pos in range(mb)]),
                "",
                f"theorem field{b} (z : Fin {n} → ℝ) (w : Fin {M} → ℝ) :",
                f"    sel idx{b} (toReal A *ᵥ z + toReal B *ᵥ w) =",
                f"      toReal D{b}.A *ᵥ sel idx{b} z + toReal D{b}.B *ᵥ wsel{b} z w := by",
                "  funext i",
                f"  fin_cases i <;> simp [sel, idx{b}, wsel{b}, D{b}, A, B, toReal, mulVec, "
                "dotProduct, Fin.sum_univ_succ] <;> ring",
                ""]
    Vs = " + ".join(f"quad (toReal D{b}.P) (sel idx{b} z)" for b in range(nb_all))
    Vds = " + ".join(f"quadDeriv (toReal D{b}.P) (sel idx{b} z) (sel idx{b} z')"
                     for b in range(nb_all))
    out += ["/-- The storage of this ellipsoid (block-diagonal for a composition). -/",
            f"noncomputable def V (z : Fin {n} → ℝ) : ℝ := {Vs}",
            f"noncomputable def V' (z z' : Fin {n} → ℝ) : ℝ := {Vds}",
            f"def α : ℚ := {q(em.alpha)}",
            f"/-- Certified level `c ≥ Σ γ δ² / α`. -/",
            f"def level : ℚ := {q(em.level)}",
            f"/-- Region level `b > c`: the region box contains `{{V ≤ b}}`. -/",
            f"def outer : ℚ := {q(em.outer)}", ""]
    for b in range(nb_all):
        others = [f"Ppsd{o}.quad_nonneg (sel idx{o} z)" for o in range(nb_all) if o != b]
        out += [f"theorem quad_le_V{b} (z : Fin {n} → ℝ) : quad (toReal D{b}.P) (sel idx{b} z) ≤ V z"
                " := by",
                "  simp only [V]",
                f"  linarith [{', '.join(others)}]" if others else "  exact le_rfl", ""]
    # dissipation
    out += _diss_lines(ctx, k, blocks, ifaces)
    # boxes
    for ci, bx in enumerate(c.region_boxes):
        if bx.member != k:
            continue
        out += _box_lines(ctx, f"boxR{ci}", bx, "outer", sp_.coords[ci].row)
    for oi, bx in enumerate(c.output_boxes):
        if bx.member != k:
            continue
        out += _box_lines(ctx, f"boxO{oi}", bx, "level", sp_.outputs[oi][1])
    out += [f"end {ns}", ""]
    return "\n".join(out)


def _box_lines(ctx, name, bx, lvl, full_row) -> list[str]:
    nb = len(bx.row)
    return [f"def {name} : LinearBoxDom D{bx.block}.P {lvl} {_qv(bx.row)} {L.qp(bx.bound)} :=",
            f"  ⟨by decide +kernel, by decide +kernel,",
            f"    ⟨{L.mat(bx.L)}, {L.vec(bx.d)}, by decide +kernel, by decide +kernel⟩⟩",
            "",
            f"theorem {name}_row (z : Fin {ctx.n} → ℝ) :",
            f"    (fun i => ((({_qv(bx.row)} : Fin {nb} → ℚ) i : ℚ) : ℝ)) ⬝ᵥ sel idx{bx.block} z ="
            f" {_q_expr(full_row, 'z')} := by",
            f"  simp [sel, idx{bx.block}, dotProduct, Fin.sum_univ_succ]",
            "  try ring",
            "",
            f"theorem {name}_le {{z : Fin {ctx.n} → ℝ}} (h : V z ≤ ({lvl} : ℝ)) :",
            f"    |{_q_expr(full_row, 'z')}| ≤ {_r(bx.bound)} := by",
            f"  rw [← {name}_row]",
            f"  exact ({name}.abs_le ((quad_le_V{bx.block} z).trans h)).trans (by norm_num)",
            ""]


def _diss_lines(ctx, k, blocks, ifaces) -> list[str]:
    sp_, c = ctx.sp, ctx.cert
    em = c.members[k]
    n, M = ctx.n, ctx.M
    nfacts = ctx.n_facts
    fn = [f"f{j}" for j in range(nfacts)]
    out = ["/-- **Dissipation (Theorem 1 / Proposition 1).** Wherever the facts hold,",
           "`V̇ ≤ -α V + α c` along `ż = A z + B w`. -/",
           f"theorem diss (z : Fin {n} → ℝ) (w : Fin {M} → ℝ) (hF : Facts z w) :",
           "    V' z (toReal A *ᵥ z + toReal B *ᵥ w) ≤ -(α : ℝ) * V z + (α : ℝ) * level := by",
           f"  obtain {_conj(fn)} := hF"]
    for j, ch in enumerate(sp_.channels):
        if ch.kind == "sector":
            lo, hi = c.gains[j]
            out.append(f"  have s{j} : 0 ≤ (w {j} - {_r(lo)} * Q{ch.q} z) * ({_r(hi)} * Q{ch.q} z"
                       f" - w {j}) := by obtain ⟨δ, hδ, hw⟩ := f{j}; exact sector_nonneg hw hδ")
    simps = ("rv, eW, secU, secV, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, sel, "
             "Pi.single_apply")
    Es = []
    sup = []
    for b, eb in enumerate(em.blocks):
        sb = len(eb.ch)
        lines = [f"  have hb{b} := C{b}.supply (sel idx{b} z) (wsel{b} z w) (by"]
        if sb == 0:
            lines.append("    intro i; exact Fin.elim0 i)")
        else:
            lines.append("    intro i")
            lines.append("    fin_cases i")
            for i_, pos in enumerate(eb.ch):
                j = eb.signals[pos][1]
                ch = sp_.channels[j]
                lines.append(f"    · have := s{j}")
                lines.append(f"      simp [D{b}, wsel{b}, idx{b}, Q{ch.q}, {simps}] at this ⊢")
                lines.append("      ring_nf at this ⊢")
                lines.append("      linarith)" if i_ == sb - 1 else "      linarith")
        lines.append(f"  rw [← field{b}] at hb{b}")
        # energy
        mb = len(eb.signals)
        cases = []
        for pos, (kind, j) in enumerate(eb.signals):
            if eb.gamma[pos] == 0:
                cases.append(f"      · simp [D{b}] at hj")
            else:
                f = j if kind == "chan" else ctx.nch + j
                cases.append(f"      · simpa [wsel{b}, δ{b}] using f{f}")
        lines += [f"  have he{b} := energy_le (δ := δ{b}) C{b}.hγ (w := wsel{b} z w) (by",
                  "    intro j hj",
                  "    fin_cases j"] + [c_.replace("      ·", "    ·") for c_ in cases]
        lines[-1] = lines[-1] + ")"
        Es.append(f"(∑ j, D{b}.γ j * (δ{b} j * δ{b} j))")
        sup.append(f"(∑ i, (D{b}.σ i : ℝ) * ((rv (D{b}.r i) ⬝ᵥ Sum.elim (sel idx{b} z) "
                   f"(wsel{b} z w)) * (rv (D{b}.r i) ⬝ᵥ Sum.elim (sel idx{b} z) (wsel{b} z w))))")
        out += lines
    # supply sum
    hints = ", ".join(f"sq_nonneg ({_iface_expr(ctx, I.row)})" for I in ifaces)
    out += [f"  have hs : {' + '.join(sup)} ≤ 0 := by"]
    if ifaces:
        out += [f"    simp [{', '.join(f'D{b}, wsel{b}, idx{b}' for b in range(len(em.blocks)))}, "
                f"{simps}]",
                f"    nlinarith [{hints}]"]
    else:
        out += ["    simp"]
    out += [f"  have hE : (({' + '.join(Es)} : ℚ) : ℝ) ≤ (α : ℝ) * level := by",
            f"    exact_mod_cast (by decide +kernel : ({' + '.join(Es)} : ℚ) ≤ α * level)",
            "  have hα : ∀ b : ℚ, b = α → ((b : ℚ) : ℝ) = (α : ℝ) := fun b h => by rw [h]",
            "  simp only [V, V']"]
    # α in each block equals the member α (decide)
    for b in range(len(em.blocks)):
        out.append(f"  have ha{b} : ((D{b}.α : ℚ) : ℝ) = (α : ℝ) := by norm_num [D{b}, α]")
        out.append(f"  rw [ha{b}] at hb{b}")
    out += ["  push_cast at hE he0" + "".join(f" he{b}" for b in range(1, len(em.blocks))),
            "  linarith", ""]
    return out


# --- assembly ------------------------------------------------------------------------------------

def emit_cert(ctx: Ctx, blocks) -> str:
    sp_, c = ctx.sp, ctx.cert
    K = len(c.members)
    n = ctx.n
    ns = f"{ctx.ns}.{ctx.prefix}Cert"
    mods = [ctx.member(k) for k in range(K)]
    out = [f"import {ctx.mod}.Spec"] + [f"import {ctx.mod}.{m}" for m in mods] + [""]
    out += L.header(f"{ctx.prefix} certificate for `{sp_.model_name}`",
                    "dynacert (sector multipliers)")
    out += LINTERS + ["", f"namespace {ns}", "",
                      f"open Matrix Set Dynacert Dynacert.Linear Dynacert.Sector {ctx.ns} "
                      f"{ctx.ns}.{ctx.link}", ""]
    V = f"{ctx.link}.vec "
    F = f"(toReal A *ᵥ {V}(x t) + toReal B *ᵥ sig (x t) (y t) (u t))"
    out += [f"noncomputable def vs (x : ℝ → States) : Fin {K} → ℝ → ℝ :=",
            "  ![" + ", ".join(f"fun t => {m}.V ({V}(x t))" for m in mods) + "]",
            f"noncomputable def vs' (x : ℝ → States) (y : ℝ → Algebraics) (u : ℝ → Inputs) :"
            f" Fin {K} → ℝ → ℝ :=",
            "  ![" + ", ".join(f"fun t => {m}.V' ({V}(x t)) {F}" for m in mods) + "]",
            f"def αs : Fin {K} → ℚ := ![" + ", ".join(f"{m}.α" for m in mods) + "]",
            f"def levels : Fin {K} → ℚ := ![" + ", ".join(f"{m}.level" for m in mods) + "]",
            f"def outers : Fin {K} → ℚ := ![" + ", ".join(f"{m}.outer" for m in mods) + "]", ""]
    # region from the boxes
    hR = []
    for ci, bx in enumerate(c.region_boxes):
        m = mods[bx.member]
        hR.append(f"(by rw [coord{ci} hp hE]; exact_mod_cast {m}.boxR{ci}_le (hall {bx.member}))")
    nb = lambda k: len(c.members[k].blocks)
    cont = []
    der = []
    for k in range(K):
        m = mods[k]
        terms = [f"((quad_continuous _).comp_continuousOn (sel_continuousOn {m}.idx{b} hcont))"
                 for b in range(nb(k))]
        acc = terms[0]
        for t_ in terms[1:]:
            acc = f"({acc}.add {t_})"
        cont.append(acc)
        dterms = [f"(quad_hasDirDeriv _ _ _ _ _ (sel_hasDerivWithinAt {m}.idx{b} (hder t ht)))"
                  for b in range(nb(k))]
        acc = dterms[0]
        for t_ in dterms[1:]:
            acc = f"({acc}.add {t_})"
        der.append(acc)
    out += [
        "/-- **Tube.** Every certified ellipsoid `{V_k ≤ c_k}` is invariant: the trajectory never",
        "reaches the boundary of the region on which the sector bounds were proved (Lemma 1). -/",
        "theorem tube : ∀ (p : Params) (u : ℝ → Inputs) (x : ℝ → States) (y : ℝ → Algebraics)",
        "    (T : ℝ), p.Bound → IsSolutionOn p u x y T → Spec.Admissible u T →",
        "    Spec.References u T → Spec.ReferenceStart u → Initial p (x 0) →",
        f"    ∀ k : Fin {K}, ∀ t ∈ Icc 0 T, vs x k t ≤ (levels k : ℝ) := by",
        "  intro p u x y T hp h hu hr hr0 h0",
        "  obtain ⟨hcont, hder⟩ := link hp h",
        "  refine region_invariant (v := vs x) (v' := vs' x y u) (α := fun k => (αs k : ℝ))",
        "    (c := fun k => (levels k : ℝ)) (b := fun k => (outers k : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_",
        "  · intro k; fin_cases k <;> norm_num [αs, " + ", ".join(f"{m}.α" for m in mods) + "]",
        "  · intro k; fin_cases k <;> norm_num [levels, outers, "
        + ", ".join(f"{m}.level, {m}.outer" for m in mods) + "]",
        "  · intro k; fin_cases k"]
    out += [f"    · exact {cont[k]}" for k in range(K)]
    out += ["  · intro k t ht; fin_cases k"]
    out += [f"    · exact {der[k]}" for k in range(K)]
    out += ["  · intro k; fin_cases k <;> simp [vs, levels, init hp h0, "
            + ", ".join(f"{m}.V, {m}.level" for m in mods) + "] <;> norm_num",
            "  · intro t ht hall",
            "    obtain ⟨ds, hE⟩ := eqs_at h ht"]
    for k in range(K):
        out.append(f"    have hv{k} : {mods[k]}.V ({V}(x t)) ≤ ({mods[k]}.outer : ℝ) := hall {k}")
    for ci, bx in enumerate(c.region_boxes):
        m = mods[bx.member]
        out.append(f"    have hR{ci} : |{ctx.R(sp_.coords[ci].expr).replace('s.', '(x t).').replace('a.', '(y t).')}| ≤ "
                   f"{_r(c.region[ci])} := by")
        out.append(f"      rw [coord{ci} hp hE]; exact {m}.boxR{ci}_le hv{bx.member}")
    out += ["    have hF := facts hp hE " + _conj([f"hR{ci}" for ci in range(len(c.region_boxes))])
            + " (hu t ht)",
            "    intro k; fin_cases k"]
    out += [f"    · exact {mods[k]}.diss _ _ hF" for k in range(K)]
    out += [""]
    # the claim
    bounds = [bx.bound for bx in c.output_boxes]
    ctx.bounds = bounds
    out += [f"/-- **Certified.** The claim of `Spec.lean` holds with the bounds `{_qv(bounds)}`. -/",
            f"theorem certified : Spec.Claim {_qv(bounds)} := by",
            "  intro p u x y T hp h hu hr hr0 h0",
            "  have hV := tube p u x y T hp h hu hr hr0 h0",
            "  intro t ht",
            "  refine " + _conj(["?_"] * len(bounds))]
    for oi, bx in enumerate(c.output_boxes):
        m = mods[bx.member]
        name, row, fld = sp_.outputs[oi]
        out += [f"  · have hk : {m}.V ({V}(x t)) ≤ ({m}.level : ℝ) := hV {bx.member} t ht",
                f"    have := {m}.boxO{oi}_le hk",
                f"    simp only [{ctx.link}.vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,"
                " Fin.isValue] at this",
                f"    show |(x t).{fld}| ≤ (({L.qp(bx.bound)} : ℚ) : ℝ)",
                "    norm_num at this ⊢",
                "    exact this"]
    out += ["", f"end {ns}", ""]
    return "\n".join(out)


def spec_problem(prob, sp_: SectorProblem):
    """The `LinearProblem` fields `emit_lti.emit_spec` reads, for the same `Spec.lean` as every
    other method."""
    from .emit_lti import LinearProblem, Output

    outs = [Output(name, f"(x t).{fld}", "state", row, []) for name, row, fld in sp_.outputs]
    return LinearProblem(
        model_name=sp_.model_name, ns=sp_.ns, module=f"Certs.{sp_.ns}", states=sp_.sfields,
        coords=[], dists=sp_.dist_fields, dist_bounds=sp_.dist_bounds, refs=[], A=sp_.A, B=[],
        n_bound=prob.model.n_bound, n_eqs=len(sp_.eqs), n_init=prob.model.n_init,
        multipliers=[], x0=[Fraction(0)] * sp_.n, outputs=outs)


# --- build and write ------------------------------------------------------------------------------

def lean_cmd(args, root):
    """`lake …` under a memory cap and low priority when `systemd-run` is available
    (DYNACERT_LEAN_MEMORY, default 6G; set it to 0 to run uncapped)."""
    import os
    import shutil

    cap = os.environ.get("DYNACERT_LEAN_MEMORY", "6G")
    cmd = ["lake", *args]
    if cap not in ("", "0") and shutil.which("systemd-run"):
        cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={cap}",
               "-p", "MemorySwapMax=0", "nice", "-n", "10"] + cmd
    return cmd


def lake_build(module: str, root) -> float:
    import subprocess
    import time

    from .pipeline import CertError

    t0 = time.time()
    r = subprocess.run(lean_cmd(["build", module], root), cwd=root, capture_output=True,
                       text=True)
    if r.returncode != 0:
        errs = "\n".join(l_ for l_ in (r.stdout + r.stderr).splitlines()
                         if "error" in l_)
        raise CertError(f"lake build {module} failed:\n{errs[-4000:]}")
    return time.time() - t0


def axioms(module: str, decl: str, root) -> set:
    import re
    import subprocess
    import tempfile
    from pathlib import Path

    from .pipeline import CertError

    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=root, delete=False) as f:
        f.write(f"import {module}\n#print axioms {decl}\n")
        tmp = Path(f.name)
    try:
        r = subprocess.run(lean_cmd(["env", "lean", tmp.name], root), cwd=root,
                           capture_output=True, text=True)
    finally:
        tmp.unlink()
    out = r.stdout + r.stderr
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    if "does not depend on any axioms" in out:
        return set()
    if not m:
        raise CertError(f"could not read axioms:\n{out}")
    return {a.strip() for a in m.group(1).split(",") if a.strip()}


def write(prob, sp_, cert, prefix, parts, out_dir):
    """Write Model/Spec and the certificate files; returns (ctx, module names in build order)."""
    import shutil

    from . import emit_lti, sector as S

    blocks, ifaces = S.build_blocks(sp_, parts)
    ctx = Ctx(prob, sp_, cert, prefix)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "Model.lean").write_text(prob.lean_src)
    (out_dir / "Spec.lean").write_text(emit_lti.emit_spec(spec_problem(prob, sp_)))
    if prob.py_file and prob.py_file.exists():
        shutil.copy(prob.py_file, out_dir / "model_sympy.py")
    if prob.mo.resolve() != (out_dir / "source.mo").resolve():
        shutil.copy(prob.mo, out_dir / "source.mo")
    files = {f"{prefix}Link": emit_link(ctx)}
    for k in range(len(cert.members)):
        files[ctx.member(k)] = emit_member(ctx, k, blocks, ifaces)
    files[f"{prefix}Cert"] = emit_cert(ctx, blocks)
    for stale in out_dir.glob(f"{prefix}M*.lean"):
        if stale.stem not in files:
            stale.unlink()
    for name, src in files.items():
        (out_dir / f"{name}.lean").write_text(src)
    return ctx, list(files)
