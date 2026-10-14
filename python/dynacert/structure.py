"""Structure discovery: what a model can be rewritten as, before any reachability analysis.

    s = structure.discover(prob.model, prob.spec)
    print(s.describe())
    s.of("se23")            # the SE₂(3) blocks found, with their witnesses

Discovery runs on rumoca's sympy view of the model (the same DAE IR as the Lean
transcription), after eliminating algebraic variables to `der(x) = f(x, u)`. It looks for:

* `linear`: `f` linear in states and inputs (constant coefficients, or multi-affine in the
  uncertain parameters);
* `integrator`: states that no right-hand side reads (bounded by integrating their derivative);
* `layers`: the strongly connected components of the state-dependency graph (a cascade when
  there are several) and, inside a component, the Modelica sub-components that couple;
* `so3`: a 3×3 block `R` with `Ṙ = R·skew(ω)` (body rates) or `Ṙ = skew(ω)·R` (spatial rates);
* `quaternion`: a 4-vector `q` with `q̇ = Ω q`, `Ω` skew (unit norm is invariant);
* `se23`: `ṗ = v`, `v̇ = R a + g`, `Ṙ = R·skew(ω)`, with `g` classified as constant,
  exogenous, isotropic-linear, inverse-square or other. Constant and isotropic-linear gravity
  are group-affine (gnc `group_affine_iff`, `affine_defect`): the log-error dynamics are exact;
* `se3`: `ṗ = R u`, `Ṙ = R·skew(ω)` (pose kinematics with body velocity);
* `log-error`: a vehicle SE₂(3) block paired with a reference block in the same gravity, with
  the residuals its log-error field will carry.

Everything here is untrusted. A fact only selects which proof is attempted; each one that a
certificate uses is re-proved in Lean from rumoca's `Equations` (see `lie_link.py`). Each fact
names the Lean results that consume it, and says whether all of them are proved
(`usable`) or the fact is report-only until a lemma is added.
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass, field

import sympy as sp

from . import analysis as an


# --- facts ------------------------------------------------------------------------------------

@dataclass
class Fact:
    kind: str
    summary: str
    data: dict = field(default_factory=dict)
    lean: list[str] = field(default_factory=list)   # Lean results that consume this fact
    usable: bool = True                              # every one of them is proved
    missing: str = ""                                # what is not proved yet

    def line(self) -> str:
        mark = "usable" if self.usable else "report-only"
        s = f"[{self.kind}] {self.summary}  ({mark})"
        if self.lean:
            s += "\n      Lean: " + ", ".join(self.lean)
        if self.missing:
            s += "\n      missing: " + self.missing
        return s


@dataclass
class Structure:
    model: str
    facts: list[Fact]
    der: dict = field(repr=False, default_factory=dict)       # scalar state symbol -> rhs
    blocks: dict = field(repr=False, default_factory=dict)    # name -> Block

    def of(self, kind: str) -> list[Fact]:
        return [f for f in self.facts if f.kind == kind]

    def kinds(self) -> list[str]:
        return [f.kind for f in self.facts]

    def describe(self) -> str:
        lines = [f"structure of {self.model}:"]
        lines += ["  " + f.line().replace("\n", "\n  ") for f in self.facts] or ["  (none)"]
        return "\n".join(lines)

    def to_json(self) -> list[dict]:
        def clean(v):
            if isinstance(v, dict):
                return {str(k): clean(x) for k, x in v.items()}
            if isinstance(v, (list, tuple)):
                return [clean(x) for x in v]
            if isinstance(v, (bool, int, float, str)) or v is None:
                return v
            return str(v)
        return [{"kind": f.kind, "summary": f.summary, "usable": f.usable, "lean": f.lean,
                 "missing": f.missing, "data": clean(f.data)} for f in self.facts]


# --- the explicit system ----------------------------------------------------------------------

@dataclass
class Block:
    """A state variable, or a group of scalar states recognized as a vector or matrix."""
    name: str
    shape: tuple
    syms: sp.Matrix      # state symbols, shaped
    der: sp.Matrix       # right-hand sides, fully eliminated (states and inputs only)
    component: str       # Modelica sub-component ('' at top level)
    der_open: sp.Matrix = None   # right-hand sides as written: algebraics kept as signals


def _component(name: str) -> str:
    return name.split(".", 1)[0] if "." in name else ""


def _flat(x) -> list:
    return list(x) if isinstance(x, sp.MatrixBase) else [x]


def scalar_residuals(model) -> list:
    """`lhs - rhs` for every scalar equation (array equations expanded elementwise)."""
    out = []
    for eq in model.equations_flat():
        lhs, rhs = (eq.lhs, eq.rhs) if isinstance(eq, sp.Equality) else (eq, 0)
        if isinstance(lhs, sp.MatrixBase) or isinstance(rhs, sp.MatrixBase):
            L = lhs if isinstance(lhs, sp.MatrixBase) else sp.Matrix([lhs])
            R = rhs if isinstance(rhs, sp.MatrixBase) else sp.Matrix([rhs])
            out += [a - b for a, b in zip(L, R)]
        else:
            out.append(lhs - rhs)
    return out


def explicit(residuals, unknowns) -> dict:
    """Solve the equations for `unknowns` (derivatives and algebraics). Equations that are
    linear in a single remaining unknown are solved by substitution, which handles rumoca's
    mostly explicit equations quickly; any rest is handed to `sympy.solve`."""
    unknowns = list(unknowns)
    U = set(unknowns)
    res = [sp.sympify(r) for r in residuals]
    sol: dict = {}
    progress = True
    while res and progress:
        progress = False
        for k, r in enumerate(res):
            us = r.free_symbols & U
            if len(us) != 1:
                continue
            (u,) = us
            a = sp.diff(r, u)
            if u in a.free_symbols or a == 0:
                continue
            val = sp.together(-r.subs(u, 0) / a)
            sol = {k_: v.subs(u, val) for k_, v in sol.items()}
            sol[u] = val
            U.discard(u)
            res = [rr.subs(u, val) for i, rr in enumerate(res) if i != k]
            res = [rr for rr in res if sp.simplify(rr) != 0 or rr.free_symbols & U]
            progress = True
            break
    if U:
        rest = [r for r in res if r.free_symbols & U]
        if not rest:
            raise ValueError(f"underdetermined: {sorted(map(str, U))}")
        found = sp.solve(rest, sorted(U, key=str), dict=True)
        if len(found) != 1 or set(found[0]) != U:
            raise ValueError("equations do not determine derivatives and algebraics uniquely")
        sub = found[0]
        sol = {k_: v.subs(sub) for k_, v in sol.items()}
        sol.update(sub)
    return sol


_MAT = re.compile(r"^(?P<base>.*?)[_\[]?(?P<i>[1-3])[,_]?(?P<j>[1-3])\]?$")
_VEC = re.compile(r"^(?P<base>.*?)[_\[]?(?P<c>[xyz1-3])\]?$")


def _group_scalars(scalars: list) -> list[Block]:
    """Recognize groups of scalar states named like `R11 … R33` / `R_1_1` and `p_x, p_y, p_z`
    / `p1 … p3` as matrices and vectors (array states need no grouping)."""
    blocks, taken = [], set()
    by = {}
    for name, sym, rhs, ro in scalars:
        m = _MAT.match(name)
        if m:
            by.setdefault(("m", m["base"]), {})[(int(m["i"]) - 1, int(m["j"]) - 1)] = \
                (sym, rhs, name, ro)
    for (_, base), cells in by.items():
        if len(cells) == 9:
            S = sp.Matrix(3, 3, lambda i, j: cells[(i, j)][0])
            D = sp.Matrix(3, 3, lambda i, j: cells[(i, j)][1])
            O = sp.Matrix(3, 3, lambda i, j: cells[(i, j)][3])
            blocks.append(Block(base or "R", (3, 3), S, D, _component(cells[(0, 0)][2]), O))
            taken |= {c[2] for c in cells.values()}
    by = {}
    for name, sym, rhs, ro in scalars:
        if name in taken:
            continue
        m = _VEC.match(name)
        if m:
            c = {"x": 0, "y": 1, "z": 2}.get(m["c"], None)
            c = int(m["c"]) - 1 if c is None else c
            by.setdefault(m["base"], {})[c] = (sym, rhs, name, ro)
    for base, cells in by.items():
        if len(cells) == 3 and base:
            blocks.append(Block(base, (3,), sp.Matrix([cells[i][0] for i in range(3)]),
                                sp.Matrix([cells[i][1] for i in range(3)]),
                                _component(cells[0][2]),
                                sp.Matrix([cells[i][3] for i in range(3)])))
    return blocks


@dataclass
class System:
    der: dict                 # scalar state symbol -> rhs (states, inputs, kept parameters)
    alg: dict                 # algebraic symbol -> expression
    blocks: list[Block]       # every state variable (arrays shaped), plus recognized groups
    states: set
    inputs: set
    params: set               # parameters left symbolic (uncertain)


def param_values(model, keep=()) -> dict:
    """Scalar parameter symbol -> bound value, with array parameters expanded elementwise."""
    return model.param_values(keep)


def system(model, spec=None) -> System:
    """`der(x) = f(x, u)` with parameter values substituted (uncertain ones kept symbolic)."""
    unc = {u.name for u in (spec.uncertain if spec else [])}
    thetas = {v.symbol for v in model.params if v.name in unc}
    vals = param_values(model, keep=unc)
    res = an.substitute_params(scalar_residuals(model), vals)
    ders = [d for v in model.states for d in _flat(model.der[v.name])]
    algs = [s for v in model.algebraics for s in _flat(v.symbol)]
    sol = explicit(res, ders + algs)
    # derivatives as written: each equation with a single derivative, solved for it, with
    # algebraic variables kept as signals (closed-loop rates must not hide `R·skew(ω)`)
    open_: dict = {}
    dset = set(ders)
    for r in res:
        us = r.free_symbols & dset
        if len(us) == 1:
            (u,) = us
            a = sp.diff(r, u)
            if a != 0 and u not in a.free_symbols and u not in open_:
                open_[u] = sp.expand(-r.subs(u, 0) / a)
    der, blocks, scalars = {}, [], []
    for v in model.states:
        syms, dsyms = _flat(v.symbol), _flat(model.der[v.name])
        rhs = [sp.expand(sol[d]) for d in dsyms]
        ro = [open_.get(d, r_) for d, r_ in zip(dsyms, rhs)]
        der.update(zip(syms, rhs))
        if v.scalar:
            scalars.append((v.name, v.symbol, rhs[0], ro[0]))
            blocks.append(Block(v.name, (), sp.Matrix([v.symbol]), sp.Matrix([rhs[0]]),
                                _component(v.name), sp.Matrix([ro[0]])))
        else:
            shape = tuple(v.shape)
            mk = (lambda xs: sp.Matrix(*v.symbol.shape, xs)) if len(shape) == 2 else sp.Matrix
            blocks.append(Block(v.name, shape, v.symbol, mk(rhs), _component(v.name), mk(ro)))
    blocks += _group_scalars(scalars)
    states = set(der)
    inputs = {s for v in model.inputs for s in _flat(v.symbol)}
    return System(der, {a: sol[a] for a in algs}, blocks, states, inputs, thetas)


# --- detectors --------------------------------------------------------------------------------

def _zero(e) -> bool:
    e = sp.sympify(e)
    if e == 0:
        return True
    e = sp.expand(e)
    return e == 0 or sp.simplify(e) == 0


def _zeros(M) -> bool:
    return all(_zero(x) for x in M)


def linear(sys_: System) -> Fact | None:
    xs = sys_.states | sys_.inputs
    for rhs in sys_.der.values():
        for x in xs & rhs.free_symbols:
            if sp.diff(rhs, x).free_symbols & xs:
                return None
    unc = bool(sys_.params & set().union(*[r.free_symbols for r in sys_.der.values()]))
    kind = "affine in the uncertain parameters" if unc else "constant coefficients"
    return Fact("linear", f"der(x) = A x + B u with {kind}",
                {"states": len(sys_.states), "inputs": len(sys_.inputs)},
                ["Linear.Polytopic" if unc else "Linear.Channels"])


def integrators(sys_: System) -> list[Fact]:
    read = set().union(*[r.free_symbols for r in sys_.der.values()]) if sys_.der else set()
    out = []
    for b in sys_.blocks:
        if b.shape == () and b.syms[0] not in read:
            out.append(Fact("integrator", f"{b.name} is read by no derivative: it integrates "
                            f"der({b.name}) = {b.der[0]}", {"state": b.name},
                            ["integrate a certified bound on der(" + b.name + ")"], False,
                            "a bound-integration lemma"))
    return out


def _scc(nodes: list, edges: dict) -> list[list]:
    """Tarjan's strongly connected components, in reverse topological order."""
    index, low, stack, on, out, counter = {}, {}, [], set(), [], [0]

    def visit(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in edges.get(v, ()):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(comp)

    for v in nodes:
        if v not in index:
            visit(v)
    return out


def layers(model, sys_: System) -> list[Fact]:
    """State variables as nodes; `u → v` when `der(v)` reads `u`."""
    vars_ = [b for b in sys_.blocks if b.name in {v.name for v in model.states}]
    owner = {s: b.name for b in vars_ for s in b.syms}
    reads = {b.name: sorted({owner[s] for d in b.der for s in d.free_symbols if s in owner}
                            - {b.name}) for b in vars_}
    feeds = {b.name: [v for v in reads if b.name in reads[v]] for b in vars_}
    comps = _scc([b.name for b in vars_], feeds)[::-1]          # sources first
    out = []
    comp_of = {b.name: b.component for b in vars_}
    if len(comps) > 1:
        order = [sorted(c) for c in comps]
        # merge consecutive layers inside one sub-component for the summary
        shown: list[list] = []
        for c in order:
            cs = {comp_of[v] for v in c}
            if shown and len(cs) == 1 and cs == {comp_of[v] for v in shown[-1]} and cs != {""}:
                shown[-1] = shown[-1] + c
            else:
                shown.append(list(c))
        out.append(Fact("layers", "cascade: " + " → ".join("{" + ", ".join(c) + "}"
                                                           for c in shown),
                        {"order": order, "reads": reads},
                        ["Compose.assume_guarantee (one-way: each layer's bounds feed the next)"]))
    for c in comps:
        parts = sorted({comp_of[v] for v in c})
        if len(parts) > 1:
            coupling = {p: sorted({r for v in c if comp_of[v] == p for r in reads[v]
                                   if comp_of[r] != p}) for p in parts}
            out.append(Fact(
                "layers", "coupled sub-components " + ", ".join(p or "(top)" for p in parts)
                + " (feedback): certify each with the others' signals as bounded disturbances",
                {"components": parts, "coupling": coupling},
                ["Compose.assume_guarantee (mutual first exit)",
                 "gnc CoupledTube (joint weighted energy, alternative)"]))
    return out


def _skew_vec(S) -> sp.Matrix:
    return sp.Matrix([S[2, 1], S[0, 2], S[1, 0]])


def so3_rates(R: sp.Matrix, F: sp.Matrix, side: str = "right"):
    """ω with `F = R·skew(ω)` (side='right') or `F = skew(ω)·R` ('left'), with ω free of R;
    None otherwise."""
    Rs = set(R)
    S = sp.zeros(3, 3)
    for k, j in itertools.product(range(3), range(3)):
        if side == "right":   # F[i,j] = Σ_k R[i,k] S[k,j]: S[k,j] = ∂F[i,j]/∂R[i,k] for every i
            cands = {sp.expand(sp.diff(F[i, j], R[i, k])) for i in range(3)}
        else:                 # F[k,j'] = Σ_j S[k,j] R[j,j']: S[k,j] = ∂F[k,j']/∂R[j,j'] for every j'
            cands = {sp.expand(sp.diff(F[k, jj], R[j, jj])) for jj in range(3)}
        if len(cands) != 1:
            return None
        S[k, j] = cands.pop()
        if S[k, j].free_symbols & Rs:
            return None
    resid = F - (R * S if side == "right" else S * R)
    if not _zeros(resid) or not _zeros(S + S.T):
        return None
    return _skew_vec(S).applyfunc(sp.expand)


def quaternion_rates(q: sp.Matrix, F: sp.Matrix):
    qs = set(q)
    Om = sp.Matrix(4, 4, lambda i, j: sp.expand(sp.diff(F[i], q[j])))
    if any(e.free_symbols & qs for e in Om) or not _zeros(F - Om * q) or not _zeros(Om + Om.T):
        return None
    w = (2 * sp.Matrix([Om[1, 0], Om[2, 0], Om[3, 0]])).applyfunc(sp.expand)
    side = "body" if _zero(Om[1, 2] - w[2] / 2) else "spatial"
    return w, side


def _gravity_kind(g: sp.Matrix, p: sp.Matrix, sys_: System):
    """Classify the non-thrust acceleration `g` of an SE₂(3) block (algebraics expanded)."""
    g = g.subs(sys_.alg).applyfunc(sp.expand)
    fs = set().union(*[e.free_symbols for e in g])
    if not fs & sys_.states:
        if not fs & sys_.inputs:
            return "constant", {"g": list(g)}
        return "exogenous", {"g": list(g), "inputs": sorted(map(str, fs & sys_.inputs))}
    if fs & sys_.states - set(p):
        return "other", {"g": list(g)}
    J = g.jacobian(p)
    if all(not (e.free_symbols & set(p)) for e in J) and _zeros(g - J * p - g.subs(
            {s: 0 for s in p})):
        if _zeros(J - J[0, 0] * sp.eye(3)) and not _zeros(J):
            return "isotropic-linear", {"c": J[0, 0], "g0": list(g.subs({s: 0 for s in p}))}
    r2 = sum(s ** 2 for s in p)
    mu = sp.simplify(-g[0] * r2 ** sp.Rational(3, 2) / p[0])
    if not (mu.free_symbols & sys_.states) and _zeros(g + mu * p / r2 ** sp.Rational(3, 2)):
        return "inverse-square", {"mu": mu}
    return "other", {"g": list(g)}


GROUP_AFFINE = {"constant", "isotropic-linear"}


def lie(sys_: System) -> tuple[list[Fact], list[dict]]:
    facts, se23s = [], []
    mats = [b for b in sys_.blocks if b.shape == (3, 3)]
    vecs = [b for b in sys_.blocks if b.shape == (3,)]
    quats = [b for b in sys_.blocks if b.shape == (4,)]
    rights = []
    for b in mats:
        for side in ("right", "left"):
            w = so3_rates(b.syms, b.der_open, side)
            if w is None:
                w = so3_rates(b.syms, b.der, side)
            if w is not None:
                facts.append(Fact(
                    "so3", f"{b.name}: d{b.name}/dt = " + (f"{b.name}·skew(ω)" if side == "right"
                                                           else f"skew(ω)·{b.name}")
                    + f", ω = {list(w)}", {"R": b.name, "side": side, "omega": list(w)},
                    ["Lie.SO3.rotation_mem_SO3"] if side == "right" else [],
                    side == "right", "" if side == "right" else
                    "left-invariant SO(3) invariance (transpose of the right-invariant proof)"))
                if side == "right":
                    rights.append((b, w))
                break
    for b in quats:
        qr = quaternion_rates(b.syms, b.der_open) or quaternion_rates(b.syms, b.der)
        if qr:
            w, side = qr
            facts.append(Fact("quaternion", f"{b.name}: dq/dt = Ω q, Ω skew ({side} rates "
                              f"ω = {list(w)}); |q| is invariant",
                              {"q": b.name, "omega": list(w), "side": side}, [], False,
                              "quaternion → rotation-matrix link"))
    for R, w in rights:
        Rs = set(R.syms)
        for p, v in itertools.permutations(vecs, 2):
            if not _zeros(p.der_open - v.syms):
                continue
            a = sp.Matrix([sp.expand(sp.diff(v.der_open[0], R.syms[0, k])) for k in range(3)])
            if _zeros(a) or any(e.free_symbols & Rs for e in a):
                continue
            a = a.applyfunc(sp.simplify)
            g = (v.der_open - R.syms * a).applyfunc(sp.expand)
            if any(e.free_symbols & Rs for e in g):
                continue
            kind, gdata = _gravity_kind(g, p.syms, sys_)
            ga = kind in GROUP_AFFINE
            blk = {"R": R.name, "p": p.name, "v": v.name, "a": list(a), "omega": list(w),
                   "gravity": kind, **gdata, "group_affine": ga,
                   "component": R.component}
            se23s.append(blk)
            facts.append(Fact(
                "se23", f"({p.name}, {v.name}, {R.name}) on SE₂(3): a = {list(a)}, "
                f"gravity {kind}" + (" (group-affine)" if ga else " (not group-affine)"),
                blk, ["Lie.ofScalars_solution", "Lie.log_error_tube",
                      "Lie.physical_output_bounds"]))
        for p in vecs:
            if any(blk["p"] == p.name for blk in se23s):
                continue
            u = sp.Matrix([sp.expand(sp.diff(p.der_open[0], R.syms[0, k])) for k in range(3)])
            if any(e.free_symbols & Rs for e in u) or _zeros(u):
                continue
            if _zeros(p.der_open - R.syms * u):
                facts.append(Fact("se3", f"({p.name}, {R.name}) on SE(3): d{p.name}/dt = "
                                  f"{R.name}·{list(u)}", {"R": R.name, "p": p.name,
                                                          "u": list(u)}, [], False,
                                  "SE(3) log tube (gnc has SE₂(3) only)"))
    return facts, se23s


def log_errors(se23s: list[dict], sys_: System) -> list[Fact]:
    """Pair a closed-loop vehicle block with an open-loop reference block in the same field."""
    def driven(b):  # rates or thrust read any state: a feedback loop closes through it
        fs = set().union(*[sp.sympify(e).subs(sys_.alg).free_symbols
                           for e in b["a"] + b["omega"]])
        return bool(fs & sys_.states)

    out = []
    for veh, ref in itertools.permutations(se23s, 2):
        if not driven(veh) or driven(ref) or veh["gravity"] != ref["gravity"]:
            continue
        if veh["gravity"] == "inverse-square" and not _zero(veh["mu"] - ref["mu"]):
            continue
        res, lean, missing = [], ["Lie.log_tube_of_residuals"], []
        res.append("control (a − ā, ω − ω̄ through J⁻¹(ξ))")
        missing.append("controller decomposition lemma (hdecomp/hres for this control law)")
        kind = veh["gravity"]
        if kind == "constant":
            res.append("gravity: identically zero")
            lean.append("Lie.gravity_residual_const")
        elif kind == "inverse-square":
            res.append("gravity: sector ‖·‖ ≤ J(Rc)·2μ/(r_min(r_min−D)²)·‖ξ‖")
            lean.append("Lie.gravity_residual_inverse_square")
        elif kind == "isotropic-linear":
            res.append("gravity: exactly linear in ξ_p (into A)")
            missing.append("isotropic-linear gravity lemma")
        else:
            res.append(f"gravity ({kind}): no bound lemma")
            missing.append(f"a residual bound for {kind} gravity")
        out.append(Fact(
            "log-error", f"vehicle ({veh['p']}, {veh['v']}, {veh['R']}) vs reference "
            f"({ref['p']}, {ref['v']}, {ref['R']}): ξ = log(Y⁻¹X); residuals: " + "; ".join(res),
            {"vehicle": veh, "reference": ref, "residuals": res}, lean, False,
            "; ".join(missing)))
    return out


def error_coordinates(model, spec, sys_: System) -> Fact | None:
    """Certified outputs linear in states and declared references (the LTI error-coordinate
    change `pipeline.linear_problem` proves)."""
    if not spec or not spec.certify or not spec.references:
        return None
    refs = {model.var(r.name).symbol for r in spec.references}
    forms = []
    for name in spec.certify:
        v = model.var(name)
        e = v.symbol if v.role == "state" else sys_.alg.get(v.symbol)
        if e is None or not v.scalar:
            return None
        e = sp.expand(e)
        if e.free_symbols - sys_.states - refs:
            return None
        if any(sp.diff(e, s).free_symbols for s in e.free_symbols):
            return None
        forms.append(f"{name} = {e}")
    return Fact("error-coordinates", "certified outputs are linear in states and references: "
                + "; ".join(forms), {"forms": forms}, ["Linear link (linear_combination)"])


def discover(model, spec=None) -> Structure:
    sys_ = system(model, spec)
    facts = []
    lin = linear(sys_)
    if lin:
        facts.append(lin)
    ec = error_coordinates(model, spec, sys_)
    if ec:
        facts.append(ec)
    facts += integrators(sys_)
    facts += layers(model, sys_)
    lf, se23s = lie(sys_)
    facts += lf
    facts += log_errors(se23s, sys_)
    return Structure(model.name, facts, sys_.der, {b.name: b for b in sys_.blocks})
