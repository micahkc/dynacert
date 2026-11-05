"""Switched linear models: `if`-expressions in the equations, linear dynamics in every mode.

A *switch* is one `if c₀ then e₀ else if c₁ then e₁ else e₂` chain of rumoca's Lean `Equations`
(every if-expression with the same condition chain belongs to the same switch, so it picks the
same branch). A *mode* picks one branch of every switch. For each mode this module builds a copy
of the model whose equations have every if-expression replaced by the chosen branch (same
equation count and order, so Lean conjunct indices still match) and runs the LTI analysis of
`pipeline.linear_problem` on it. The model is a switched linear system when every mode is linear
in the same error coordinates, with the same disturbance matrix `B`, output rows and initial
data; only `A` may differ.

The Lean side (`emit_switched.py`) reads the switch conditions verbatim from rumoca's
`Equations` text, so the mode weights (indicators of the active mode) are defined with the
model's own conditions. Everything here is untrusted; Lean re-checks each identity.
"""

from __future__ import annotations

import dataclasses
import itertools
import re
from dataclasses import dataclass, field
from fractions import Fraction

import sympy as sp

from . import analysis as an
from . import emit_lti
from .pipeline import CertError

MAX_MODES = 32


@dataclass
class Chain:
    """One Lean `if c₀ then e₀ else if c₁ then e₁ else eₖ` occurrence."""
    eq: int                  # conjunct index
    conds: list[str]         # condition texts (k of them; k + 1 branches)
    branches: list[str]      # branch texts

    @property
    def key(self) -> tuple:
        return tuple(self.conds)


@dataclass
class Switch:
    conds: list[str]                    # Lean condition texts (Equations binders)
    atoms: list = field(default_factory=list)   # sympy Piecewise atoms it governs
    eqs: list = field(default_factory=list)     # conjunct indices containing it

    @property
    def n_branches(self) -> int:
        return len(self.conds) + 1


@dataclass
class SwitchedProblem:
    base: emit_lti.LinearProblem        # mode 0's linear problem (coords, B, outputs, x0, ...)
    switches: list[Switch]
    modes: list[tuple]                  # branch index per switch
    problems: list[emit_lti.LinearProblem]   # one per mode
    binders: str                        # Equations binder text, e.g. "(t : ℝ) (p : Params) ..."
    names: dict                         # role -> binder name: t p u x dx y
    if_eqs: list[int]                   # conjunct indices containing an if-expression
    switched_outputs: list = field(default_factory=list)  # output indices with per-mode rows

    @property
    def As(self) -> list:
        return [pb.A for pb in self.problems]

    def mode_text(self, k: int) -> str:
        """Human-readable condition of mode `k` (Lean texts)."""
        parts = []
        for sw, j in zip(self.switches, self.modes[k]):
            if j < len(sw.conds):
                neg = [f"¬({c})" for c in sw.conds[:j]]
                parts.append(" ∧ ".join(neg + [sw.conds[j]]))
            else:
                parts.append(" ∧ ".join(f"¬({c})" for c in sw.conds))
        return " ∧ ".join(parts) if parts else "True"


# --- Lean text --------------------------------------------------------------------------------

_EQ_HEAD = re.compile(r"def Equations\s*(.*?)\s*:\s*Prop\s*:=\s*\n", re.S)


def equations_text(lean_src: str) -> tuple[str, list[str]]:
    """The binder text of rumoca's `Equations` and its conjuncts, in order."""
    m = _EQ_HEAD.search(lean_src)
    if not m:
        raise CertError("no `Equations` definition in the Lean model")
    rest = lean_src[m.end():]
    body = rest.split("\n\n", 1)[0]
    lines = body.split("\n")
    conj, cur = [], None
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        if s.startswith("∧ ") and ln.startswith("  ∧ "):
            conj.append(cur)
            cur = s[2:]
        elif cur is None:
            cur = s
        else:
            cur += " " + s
    if cur is not None:
        conj.append(cur)
    return m.group(1), conj


def binder_names(binders: str) -> dict:
    """Role -> name for `(t : ℝ) (p : Params) (u : Inputs) (x dx : States) (y : Algebraics)`."""
    groups = re.findall(r"\(([^():]+):\s*([^()]+)\)", binders)
    out = {}
    for names, ty in groups:
        ns, ty = names.split(), ty.strip()
        if ty == "ℝ":
            out["t"] = ns[0]
        elif ty == "Params":
            out["p"] = ns[0]
        elif ty == "Inputs":
            out["u"] = ns[0]
        elif ty == "States":
            out["x"], out["dx"] = ns[0], ns[1]
        elif ty == "Algebraics":
            out["y"] = ns[0]
    if set(out) != {"t", "p", "u", "x", "dx", "y"}:
        raise CertError(f"unexpected Equations binders: {binders}")
    return out


_OPEN, _CLOSE = "([{", ")]}"


def _scan(s: str, i: int, stops: list[str]) -> tuple[int, str | None]:
    """First index ≥ i at bracket depth 0 where one of `stops` begins (or a closing bracket
    ends the enclosing group: returns (index, None))."""
    depth = 0
    while i < len(s):
        c = s[i]
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            if depth == 0:
                return i, None
            depth -= 1
        elif depth == 0:
            for st in stops:
                if s.startswith(st, i):
                    return i, st
        i += 1
    return i, None


_IF = re.compile(r"(?<![\w.'«])if ")


def if_chains(conjuncts: list[str]) -> list[Chain]:
    """Every if-chain of the conjuncts, in textual order. Nested if-expressions (in a condition
    or a branch) are rejected."""
    out = []
    for k, s in enumerate(conjuncts):
        pos = 0
        while True:
            m = _IF.search(s, pos)
            if not m:
                break
            i = m.end()
            conds, branches = [], []
            while True:
                j, st = _scan(s, i, [" then "])
                if st is None:
                    raise CertError(f"cannot parse if-expression in equation {k}: {s}")
                conds.append(s[i:j].strip())
                i = j + len(" then ")
                j, st = _scan(s, i, [" else "])
                if st is None:
                    raise CertError(f"cannot parse if-expression in equation {k}: {s}")
                branches.append(s[i:j].strip())
                i = j + len(" else ")
                if s.startswith("if ", i):
                    i += 3
                    continue
                j, _ = _scan(s, i, [" then ", " else "])
                branches.append(s[i:j].strip())
                pos = j
                break
            for t in conds + branches:
                if _IF.search(t):
                    raise CertError("nested if-expressions are not supported by the switched "
                                    f"method (equation {k})")
            out.append(Chain(k, conds, branches))
    return out


_REF = re.compile(r"(?<![\w.'])(dx|[pxyu])\.(«[^»]+»|[A-Za-z_][\w']*)")


def _lean_refs(text: str, names: dict) -> set:
    inv = {v: k for k, v in names.items()}
    return {(inv.get(a, a), f) for a, f in _REF.findall(text)}


def _sympy_refs(cond, m) -> set:
    out = set()
    by_sym = {v.symbol: v for v in m.variables if v.scalar}
    der_of = {d: m.var(n) for n, d in m.der.items()}
    for s in sp.sympify(cond).free_symbols:
        if s in der_of:
            out.add(("dx", der_of[s].lean))
        elif s in by_sym:
            v = by_sym[s]
            kind = {"parameter": "p", "constant": "p", "input": "u", "state": "x"}.get(v.role, "y")
            out.add((kind, v.lean))
        elif str(s) == "t":
            out.add(("t", "t"))
    return out


# --- switches and modes -----------------------------------------------------------------------

def find_switches(m, lean_src: str) -> tuple[list[Switch], str, dict, list[int]]:
    """Match rumoca's Lean if-chains with the sympy Piecewise atoms, equation by equation, and
    group them into switches by condition text."""
    binders, conj = equations_text(lean_src)
    names = binder_names(binders)
    if len(conj) != len(m.equations):
        raise CertError(f"Lean has {len(conj)} equations, sympy {len(m.equations)}")
    chains = if_chains(conj)
    switches: dict[tuple, Switch] = {}
    seen_atoms = {}
    for k, eq in enumerate(m.equations):
        if not isinstance(eq, sp.Equality):
            if chains and any(c.eq == k for c in chains):
                raise CertError("if-expressions inside structured (array/for) equations are "
                                "not supported")
            continue
        atoms = an.piecewise_atoms([eq.lhs - eq.rhs])
        lc = [c for c in chains if c.eq == k]
        # deduplicate Lean chains by text within the equation (sympy merges equal atoms)
        uniq = []
        for c in lc:
            if all((c.conds, c.branches) != (u.conds, u.branches) for u in uniq):
                uniq.append(c)
        if len(uniq) != len(atoms):
            raise CertError(f"equation {k}: {len(uniq)} if-expressions in Lean, {len(atoms)} "
                            "Piecewise in sympy (a branch or condition was simplified away)")
        for pw in atoms:
            if pw.args[-1][1] != sp.true:
                raise CertError(f"equation {k}: Piecewise without an else branch")
            sig = (len(pw.args) - 1,
                   frozenset().union(*[_sympy_refs(c, m) for _, c in pw.args[:-1]]))
            cands = [c for c in uniq if (len(c.conds), frozenset().union(
                *[_lean_refs(t, names) for t in c.conds])) == sig]
            if len(cands) != 1:
                if len(uniq) == 1 and len(uniq[0].conds) == sig[0]:
                    cands = uniq
                else:
                    raise CertError(f"equation {k}: cannot match its if-expressions between "
                                    "Lean and sympy (split the equation)")
            c = cands[0]
            sw = switches.setdefault(c.key, Switch(list(c.conds)))
            if pw in seen_atoms and seen_atoms[pw] is not sw:
                raise CertError("the same if-expression is rendered with different conditions")
            seen_atoms[pw] = sw
            if pw not in sw.atoms:
                sw.atoms.append(pw)
            if k not in sw.eqs:
                sw.eqs.append(k)
    if_eqs = sorted({c.eq for c in chains})
    return list(switches.values()), binders, names, if_eqs


def mode_model(m, switches: list[Switch], choice: tuple):
    """A copy of the model with every if-expression replaced by the chosen branch."""
    rep = {}
    for sw, j in zip(switches, choice):
        for pw in sw.atoms:
            rep[pw] = pw.args[j][0]
    eqs = []
    for e in m.equations:
        if isinstance(e, sp.Equality):
            e = sp.Eq(e.lhs.xreplace(rep), e.rhs.xreplace(rep), evaluate=False)
        eqs.append(e)
    return dataclasses.replace(m, equations=eqs)


def has_switching(m) -> bool:
    eqs = [e for e in m.equations_flat() if isinstance(e, sp.Equality)]
    return bool(an.piecewise_atoms([e.lhs - e.rhs for e in eqs]))


def _same(a, b) -> bool:
    return [[Fraction(v) for v in r] for r in a] == [[Fraction(v) for v in r] for r in b]


def switched_problem(m, sp_, lean_src: str) -> SwitchedProblem:
    """Build the per-mode linear problems and check that they share the error frame."""
    from . import pipeline

    if not has_switching(m):
        raise CertError("no if-expressions: the model is not switched (use lmi)")
    if sp_.uncertain:
        raise CertError("uncertain parameters are not supported by the switched method (v1): "
                        "the vertices would be (mode × parameter corner) and the weights a "
                        "product of indicator and interpolation weights")
    switches, binders, names, if_eqs = find_switches(m, lean_src)
    combos = list(itertools.product(*[range(sw.n_branches) for sw in switches]))
    if len(combos) > MAX_MODES:
        raise CertError(f"{len(combos)} modes (more than {MAX_MODES})")
    probs = []
    for ch in combos:
        mm = mode_model(m, switches, ch)
        try:
            probs.append(pipeline.linear_problem(mm, sp_, lean_src))
        except (CertError, ValueError) as e:
            raise CertError(f"mode {ch} is not linear in a common frame: {e}") from None
    base = probs[0]
    for ch, pb in zip(combos[1:], probs[1:]):
        what = None
        if [c.name for c in pb.coords] != [c.name for c in base.coords] or any(
                [(t.coeff, t.kind, t.fld) for t in c.terms] !=
                [(t.coeff, t.kind, t.fld) for t in d.terms]
                for c, d in zip(pb.coords, base.coords)):
            what = "error coordinates"
        elif not _same(pb.B, base.B):
            what = "disturbance matrix B"
        elif [list(o.row) for o in pb.outputs if o.kind == "state"] != \
                [list(o.row) for o in base.outputs if o.kind == "state"]:
            what = "state output rows"
        elif list(pb.x0) != list(base.x0):
            what = "initial coordinates"
        if what:
            raise CertError(f"modes {combos[0]} and {ch} differ in their {what}; the switched "
                            "method needs one frame for all modes (only A may differ)")
    # switched outputs: algebraic outputs whose row in the coordinates depends on the mode, or
    # whose identity uses an equation with an if-expression (proved per mode in Lean)
    sw_out = []
    for k, o in enumerate(base.outputs):
        rows = [list(pb.outputs[k].row) for pb in probs]
        used = {e for pb in probs for e, cf in pb.outputs[k].mult if cf != 0}
        if any(r != rows[0] for r in rows) or used & set(if_eqs):
            if o.kind != "algebraic":
                raise CertError(f"output {o.name}: a state output must have one row")
            sw_out.append(k)
    return SwitchedProblem(base, switches, combos, probs, binders, names, if_eqs, sw_out)


def search(spb: SwitchedProblem):
    """Common quadratic storage over the mode matrices (untrusted numeric search)."""
    from .methods import lti

    pb = spb.base
    box = pb.init_box
    kw = {} if box is None else {"init_box": (box.G, box.rho)}
    cert = lti.certify_polytopic(spb.As, pb.B, pb.dist_bounds, x0=pb.x0,
                                 output_rows=[o.row for o in pb.outputs], **kw)
    if cert is not None:
        cert.switched_boxes = switched_boxes(spb, cert)
    return cert


def switched_boxes(spb: SwitchedProblem, cert) -> dict:
    """For each switched output: one bound `b` (the largest of the per-mode bounds) and, per
    mode, a `LinearBoxCert` witness for that mode's row at `b`."""
    from . import exact
    from .methods import lti

    out = {}
    P, c = cert.P, cert.level
    for k in spb.switched_outputs:
        rows = [pb.outputs[k].row for pb in spb.problems]
        b = max(lti.box_bound(P, c, r).bound for r in rows)
        boxes = []
        for r in rows:
            v = [Fraction(x) for x in r]
            M = [[b * b * P[i][j] - c * v[i] * v[j] for j in range(len(P))]
                 for i in range(len(P))]
            W = exact.psd_witness(M)
            if W is None:
                raise CertError(f"no box witness for output {spb.base.outputs[k].name}")
            boxes.append(lti.BoxBound(-1, b, W[0], W[1]))
        out[k] = (b, boxes)
        cert.boxes[k] = boxes[0]      # carries the bound b reported for the output
    return out


def common_lyapunov_infeasible(As, eps: float = 1e-7) -> bool:
    """True when no common `P ≻ 0` with `AᵢᵀP + PAᵢ ≺ 0` exists (numeric, untrusted): the
    certificate this method searches for cannot exist at any decay rate."""
    import cvxpy as cp
    import numpy as np

    n = len(As[0])
    P = cp.Variable((n, n), symmetric=True)
    cons = [P >> np.eye(n)]
    for A in As:
        Af = np.array(A, dtype=float)
        cons.append(Af.T @ P + P @ Af << -eps * np.eye(n))
    pr = cp.Problem(cp.Minimize(0), cons)
    try:
        pr.solve(solver=cp.CLARABEL if "CLARABEL" in cp.installed_solvers() else cp.SCS)
    except Exception:
        return True
    return pr.status not in ("optimal", "optimal_inaccurate")
