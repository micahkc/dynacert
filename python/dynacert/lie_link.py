"""Lean emission of the SE₂(3) link: rumoca's equations ⇒ `SpacecraftSolution`.

For every SE₂(3) block that `structure.py` finds, this writes a theorem

    se23_<R> : IsSolutionOn p u x y T → Initial p (x 0) →
      SpacecraftSolution (ofScalars p v R) a ω g T

where `a`, `ω`, `g` are the model's own Lean terms, read from rumoca's `Equations`
(`dx.v = x.R *ᵥ a ± g`, `dx.R = x.R * Rumoca.skew ω`), so each kinematic identity is closed by
`exact` on the corresponding equation. The proof is `Dynacert.Lie.spacecraft_of_components`,
which also proves that `R` stays in SO(3).

For a vehicle/reference pair (`log-error` fact) it adds the gravity facts the residual lemmas
need: equal constant gravity (`gravity_residual_const`) or the inverse-square field
`Gravity.field3 μ p` with equal `μ` (`gravity_residual_inverse_square`).

Untrusted: if the generated file does not build, nothing is claimed.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

import sympy as sp

from . import lean as lean_mod


class LinkError(Exception):
    pass


def _conj(names: list[str]) -> str:
    return names[0] if len(names) == 1 else "⟨" + ", ".join(names) + "⟩"


def equations_text(lean_src: str) -> list[str]:
    """The conjuncts of rumoca's `Equations`, one string each, in order."""
    m = re.search(r"def Equations[^\n]*:=\n(.*?)\n\n", lean_src, re.S)
    if not m:
        raise LinkError("no `Equations` definition in the Lean model")
    body = m.group(1)
    parts, cur = [], []
    for line in body.splitlines():
        s = line.strip()
        if s.startswith("∧ ") and cur:
            parts.append(" ".join(cur))
            cur = [s[2:]]
        else:
            cur.append(s)
    if cur:
        parts.append(" ".join(cur))
    return parts


def initial_text(lean_src: str) -> list[str]:
    m = re.search(r"def Initial[^\n]*:=\n(.*?)\n\n", lean_src, re.S)
    if not m:
        return []
    out = []
    for line in m.group(1).splitlines():
        s = line.strip()
        out.append(s[2:] if s.startswith("∧ ") else s)
    return [s for s in out if s]


def bound_text(lean_src: str) -> list[str]:
    m = re.search(r"def Params\.Bound[^\n]*:=\n(.*?)\n\n", lean_src, re.S)
    if not m:
        return []
    out = []
    for line in m.group(1).splitlines():
        s = line.strip()
        out.append(s[2:] if s.startswith("∧ ") else s)
    return [s for s in out if s]


def _top_split(s: str):
    """Split `A + G` / `A - G` at the first top-level binary + or -."""
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and s[i:i + 3] in (" + ", " - "):
            return s[:i].strip(), s[i + 1], s[i + 3:].strip()
    return s.strip(), None, None


def _at_t(term: str) -> str:
    """`x.f` → `(x t).f` (and `y.`, `u.`); parameters `p.` stay."""
    return re.sub(r"(?<![\w.»])([xyu])\.", r"(\1 t).", term)


@dataclass
class SE23Link:
    name: str          # theorem suffix
    p: str
    v: str
    R: str
    a: str             # Lean term in t
    w: str
    g: str
    eq_p: int
    eq_v: int
    eq_R: int
    v_sign: str        # '+' or '-' (dx.v = R a ± G)
    init_R: int | None


def _eq_index(eqs: list[str], fld: str) -> int:
    pre = f"dx.{fld} = "
    for k, e in enumerate(eqs):
        if e.startswith(pre):
            return k
    raise LinkError(f"no equation `{pre}…` in the Lean model")


def block_link(eqs, inits, blk: dict) -> SE23Link:
    P, V, R = (lean_mod.ident(blk[k]) for k in ("p", "v", "R"))
    ip, iv, iR = _eq_index(eqs, P), _eq_index(eqs, V), _eq_index(eqs, R)
    if eqs[ip] != f"dx.{P} = x.{V}":
        raise LinkError(f"`{eqs[ip]}` is not `dx.{P} = x.{V}`")
    rhs = eqs[iv].split(" = ", 1)[1]
    pre = f"x.{R} *ᵥ "
    if not rhs.startswith(pre):
        raise LinkError(f"`{eqs[iv]}` is not of the form `x.{R} *ᵥ a ± g`")
    a, sign, G = _top_split(rhs[len(pre):])
    rrhs = eqs[iR].split(" = ", 1)[1]
    pre_r = f"x.{R} * Rumoca.skew "
    if not rrhs.startswith(pre_r):
        raise LinkError(f"`{eqs[iR]}` is not of the form `x.{R} * Rumoca.skew ω`")
    w = rrhs[len(pre_r):]
    if sign is None:
        g = "0"
    else:
        g = _at_t(G) if sign == "+" else f"-({_at_t(G)})"
    init_R = None
    ident = "Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]"
    for k, s in enumerate(inits):
        if s == f"x.{R} = {ident}":
            init_R = k
    name = re.sub(r"\W", "_", blk["R"])
    return SE23Link(name, P, V, R, _at_t(a), _at_t(w), g, ip, iv, iR, sign or "+", init_R)


def emit(prob, structure) -> tuple[str, list[str]]:
    """The `LieLink.lean` source for every SE₂(3) block, and the names of the theorems."""
    m, src = prob.model, prob.lean_src
    eqs = equations_text(src)
    if len(eqs) != len(m.equations):
        raise LinkError(f"parsed {len(eqs)} equations, the sympy view has {len(m.equations)}")
    inits = initial_text(src)
    bounds = bound_text(src)
    links = [block_link(eqs, inits, f.data) for f in structure.of("se23")]
    if not links:
        raise LinkError("no SE₂(3) block to link")
    ns = m.ns
    states = [v for v in m.states]
    k = len(states)
    ch = [f"c{i}" for i in range(k)]
    dh = [f"d{i}" for i in range(k)]
    eh = [f"e{i}" for i in range(len(eqs))]
    ih = [f"i{i}" for i in range(len(inits))]
    idx = {v.name: i for i, v in enumerate(states)}
    out = [f"import Certs.{ns}.Model", "import Dynacert.Lie.Link", ""]
    out += lean_mod.header(f"SE₂(3) link for `{m.name}`", "dynacert (structure → Lie link)")
    out += ["set_option linter.style.setOption false", "set_option linter.style.longLine false",
            "set_option linter.unusedVariables false", "", f"namespace {ns}.LieLink", "",
            f"open Set Dynacert.Lie {ns}", ""]
    names = []
    for L in links:
        pi, vi, Ri = (idx[n] for n in (unq(L.p), unq(L.v), unq(L.R)))
        hv = f"e{L.eq_v}" if L.v_sign == "+" else f"(e{L.eq_v}.trans (sub_eq_add_neg _ _))"
        r0 = (f"(by rw [{ih[L.init_R]}]; exact identity_mem_SO3)" if L.init_R is not None
              else "hR0")
        extra = "" if L.init_R is not None else \
            f"\n    (hR0 : (x 0).{L.R} ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)"
        thm = f"se23_{L.name}"
        names.append(thm)
        der = (f"(fun t ht => by obtain ⟨{', '.join(dh)}, -⟩ := hder t ht; exact d{{}})")
        out += [
            f"/-- `({L.p}, {L.v}, {L.R})` is an SE₂(3) trajectory: `a = {L.a}`, `ω = {L.w}`,",
            f"`g = {L.g}`. -/",
            f"theorem {thm} {{p : Params}} {{u : ℝ → Inputs}} {{x : ℝ → States}}",
            "    {y : ℝ → Algebraics} {T : ℝ} (h : IsSolutionOn p u x y T)"
            + (f" (h0 : Initial p (x 0))" if L.init_R is not None else "") + extra + " :",
            "    SpacecraftSolution",
            f"      (ofScalars (fun t => (x t).{L.p}) (fun t => (x t).{L.v}) (fun t => (x t).{L.R}))",
            f"      (fun t => {L.a}) (fun t => {L.w}) (fun t => {L.g}) T := by",
            f"  obtain ⟨dx, {', '.join(ch)}, hder⟩ := h",
        ]
        if L.init_R is not None:
            out.append(f"  obtain {_conj(ih)} := h0")
        out += [
            "  refine spacecraft_of_components",
            f"    (dp := fun t => (dx t).{L.p}) (dv := fun t => (dx t).{L.v})",
            f"    (dR := fun t => (dx t).{L.R}) c{pi} c{vi} c{Ri}",
            "    " + der.format(pi), "    " + der.format(vi), "    " + der.format(Ri),
        ]
        for e_, rhs in ((L.eq_p, f"e{L.eq_p}"), (L.eq_v, hv), (L.eq_R, f"e{L.eq_R}")):
            out.append(f"    (fun t ht => by obtain ⟨{', '.join(dh)}, {_conj(eh)}⟩ := hder t ht; "
                       f"exact {rhs})")
        out += [f"    {r0}", ""]
    # gravity facts for vehicle/reference pairs
    bidx = {}
    for i, b in enumerate(bounds):
        mm = re.match(r"p\.(\S+) = ", b)
        if mm:
            bidx[mm.group(1)] = i
    bh = [f"b{i}" for i in range(len(bounds))]
    by_R = {f.data["R"]: L for f, L in zip(structure.of("se23"), links)}
    for f in structure.of("log-error"):
        veh, ref = f.data["vehicle"], f.data["reference"]
        X, Y = by_R[veh["R"]], by_R[ref["R"]]
        if veh["gravity"] == "constant":
            names.append(f"gravity_eq_{X.name}")
            out += [
                f"/-- Vehicle and reference feel the same gravity: `{X.g} = {Y.g}`, so the",
                "gravity term of the log-error field vanishes (`gravity_residual_const`). -/",
                f"theorem gravity_eq_{X.name} {{p : Params}} (hp : p.Bound) {{x : ℝ → States}}"
                " (t : ℝ) :",
                f"    (fun t => {X.g}) t = (fun t => {Y.g}) t := by",
                f"  obtain {_conj(bh)} := hp",
                f"  simp only [{', '.join(bh)}]", ""]
        elif veh["gravity"] == "inverse-square":
            for L in (X, Y):
                mm = re.search(r"• \(?(p\.[^\s)]+)(?: : ℝ\))? • \(x t\)\.(\S+)\)$", L.g)
                if not mm:
                    raise LinkError(f"cannot read μ from `{L.g}`")
                mu, pf = mm.group(1), mm.group(2)
                names.append(f"gravity_field_{L.name}")
                out += [
                    f"/-- `{L.g}` is gnc's inverse-square field `Gravity.field3 μ p`. -/",
                    f"theorem gravity_field_{L.name} {{p : Params}} {{x : ℝ → States}} (t : ℝ) :",
                    f"    (fun t => {L.g}) t = GNC.Gravity.field3 {mu} ((x t).{pf}) :=",
                    "  rumoca_inverse_square _ _", ""]
            mx = re.search(r"• \(?(p\.[^\s)]+)(?: : ℝ\))? •", X.g).group(1)
            my = re.search(r"• \(?(p\.[^\s)]+)(?: : ℝ\))? •", Y.g).group(1)
            names.append(f"mu_eq_{X.name}")
            out += [
                f"/-- Vehicle and reference orbit the same body: `{mx} = {my}`. -/",
                f"theorem mu_eq_{X.name} {{p : Params}} (hp : p.Bound) : {mx} = {my} := by",
                f"  obtain {_conj(bh)} := hp",
                f"  rw [{bh[bidx[mx[2:]]]}, {bh[bidx[my[2:]]]}]", ""]
    out += [f"end {ns}.LieLink", ""]
    return "\n".join(out), names


def unq(fld: str) -> str:
    return fld[1:-1] if fld.startswith("«") else fld


def write_and_check(prob, structure, verbose=print) -> dict:
    """Write `certs/Certs/<Model>/{Model,LieLink}.lean`, build, and audit the axioms."""
    from . import pipeline

    src, names = emit(prob, structure)
    out = prob.cert_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / "Model.lean").write_text(prob.lean_src)
    (out / "LieLink.lean").write_text(src)
    mod = f"Certs.{prob.model.ns}.LieLink"
    verbose(f"lean: lake build {mod}")
    pipeline.lake("build", mod, cwd=prob.root)
    axioms = {}
    for n in names:
        ax = pipeline.axioms(mod, f"{prob.model.ns}.LieLink.{n}", root=prob.root)
        if not ax <= pipeline.ALLOWED_AXIOMS:
            raise pipeline.CertError(f"{n} depends on disallowed axioms: "
                                     f"{ax - pipeline.ALLOWED_AXIOMS}")
        axioms[n] = sorted(ax)
    verbose(f"lean: {len(names)} theorems checked")
    return {"file": str(out / "LieLink.lean"), "theorems": names, "axioms": axioms}
