"""The LMI pipeline: Modelica → rumoca → search → Lean → kernel check → plots (see
`approaches/lmi.py` for the CLI approach)."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path

import sympy as sp

from . import analysis as an
from . import emit_lti, model as model_mod, spec as spec_mod
from . import lean as lean_mod
from .lean import q
from .methods import lti

REPO = Path(__file__).resolve().parents[2]
DEFAULT_TARGETS = Path(os.environ.get(
    "DYNACERT_TARGETS",
    "/home/micah/Research/development/rumoca/rumoca-dynacert/examples/codegen"))
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class CertError(Exception):
    pass


DEFAULT_RUMOCA = "/home/micah/Research/development/rumoca/rumoca-dynacert-target/release/rumoca"


def rumoca_bin() -> str:
    b = os.environ.get("DYNACERT_RUMOCA")
    if not b and Path(DEFAULT_RUMOCA).exists():
        b = DEFAULT_RUMOCA  # rumoca with vendor-annotation pass-through (branch dynacert-lean)
    b = b or shutil.which("rumoca")
    if not b:
        raise CertError("rumoca not found (set DYNACERT_RUMOCA)")
    return b


def run_rumoca(mo: Path, model: str, target: Path, out: Path):
    cmd = [rumoca_bin(), "compile", str(mo), "--model", model, "--target", str(target),
           "--output", str(out)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise CertError(f"rumoca failed ({target.name}):\n{r.stdout}\n{r.stderr}")


def export(mo: Path, model: str, work: Path, targets: Path = DEFAULT_TARGETS, root: Path = REPO):
    """Render the Lean specification and the sympy model from one DAE IR."""
    lean_out, py_out = work / "lean", work / "py"
    run_rumoca(mo, model, targets / "lean_dae", lean_out)
    run_rumoca(mo, model, targets / "sympy_dae", py_out)
    prelude = (lean_out / "Rumoca" / "Prelude.lean").read_text()
    ours = (root / "Rumoca" / "Prelude.lean").read_text()
    if prelude != ours:
        raise CertError("rumoca's Rumoca/Prelude.lean differs from dynacert's copy; update "
                        "Rumoca/Prelude.lean deliberately before certifying")
    leans = [p for p in lean_out.glob("*.lean")]
    pys = [p for p in py_out.glob("*.py")]
    if len(leans) != 1 or len(pys) != 1:
        raise CertError(f"unexpected rumoca output: {leans} {pys}")
    return leans[0], pys[0]


# --- linear problems ---------------------------------------------------------------------------

def linear_problem(m: model_mod.Model, sp_: spec_mod.Spec, lean_src: str):
    """Coordinates, LTI matrices, and proof multipliers for a linear model."""
    E = emit_lti
    if any(not v.scalar for v in m.variables):
        raise CertError("the linear method currently needs scalar variables")
    if not sp_.certify:
        raise CertError("nothing to certify: annotate outputs with __Dynacert(certify)")
    eqs = []
    for e in m.equations:
        if not isinstance(e, sp.Equality):
            raise CertError("structured (array/for) equations are not supported by this method")
        eqs.append(e)
    states = m.states
    xs = [v.symbol for v in states]
    ders = [m.der[v.name] for v in states]
    for d in sp_.disturbance_names:
        if m.var(d).role != "input":
            raise CertError(f"disturbance {d} is not an input")
    ws = [m.var(d).symbol for d in sp_.disturbance_names]
    refs = {r.name: r for r in sp_.references}
    for r in sp_.references:
        if m.var(r.name).role != "input" or (r.derivative and m.var(r.derivative).role != "input"):
            raise CertError(f"reference {r.name}: references and their derivatives must be inputs")
    unc = {u.name: u for u in sp_.uncertain}
    for u in sp_.uncertain:
        if m.var(u.name).role not in ("parameter", "constant"):
            raise CertError(f"uncertain {u.name} is not a parameter")
    thetas = [m.var(u.name).symbol for u in sp_.uncertain]
    pvals = {k_: v_ for k_, v_ in m.param_values().items() if k_ not in thetas}
    res = an.substitute_params(eqs, pvals)
    try:
        ex = an.eliminate(res, ders, [v.symbol for v in m.algebraics])
    except ValueError as err:
        raise CertError(str(err)) from err
    subs_x = dict(ex.alg)

    def expr_of(name):  # output as an expression in states and inputs
        v = m.var(name)
        if v.role == "state":
            return v.symbol
        if v.role in ("algebraic", "output"):
            return sp.expand(subs_x[v.symbol])
        raise CertError(f"cannot certify {name} (role {v.role})")

    ref_syms = [m.var(r).symbol for r in refs]
    in_syms = {v.symbol for v in m.inputs}
    out_exprs = {n: expr_of(n) for n in sp_.certify}
    uses_refs = any(sp.expand(e).free_symbols & in_syms for e in out_exprs.values())

    # coordinates: linear forms in states and reference inputs
    if not uses_refs:
        forms = [(v.name, {v.symbol: sp.Integer(1)}) for v in states]
    else:
        forms = []
        for n_, e in out_exprs.items():
            bad = e.free_symbols - set(xs) - set(ref_syms)
            if bad:
                raise CertError(f"output {n_} depends on {bad}, which are neither states nor "
                                "declared references")
            co = {s: sp.diff(e, s) for s in list(xs) + ref_syms}
            if any(c.free_symbols for c in co.values()) or sp.expand(
                    e - sum(c * s for s, c in co.items())) != 0:
                raise CertError(f"output {n_} is not linear in states and references")
            forms.append((n_, {s: c for s, c in co.items() if c != 0}))
    zexpr = [sum(c * s for s, c in f.items()) for _, f in forms]
    # derivative of each coordinate
    sym_der = {x: ex.der[d] for x, d in zip(xs, ders)}
    sym_der_lean = {x: d for x, d in zip(xs, ders)}
    for r in refs.values():
        if r.derivative:
            sym_der[m.var(r.name).symbol] = m.var(r.derivative).symbol
            sym_der_lean[m.var(r.name).symbol] = m.var(r.derivative).symbol
    zdot, zdot_lean = [], []
    for _, f in forms:
        for s in f:
            if s not in sym_der:
                raise CertError(f"reference {s} has no declared derivative")
        zdot.append(sp.expand(sum(c * sym_der[s] for s, c in f.items())))
        zdot_lean.append(sum(c * sym_der_lean[s] for s, c in f.items()))
    # solve ż = A z + B w as an identity in states and inputs
    k, mm = len(forms), len(ws)
    Asym = sp.Matrix(k, k, lambda i, j: sp.Symbol(f"_A{i}_{j}"))
    Bsym = sp.Matrix(k, mm, lambda i, j: sp.Symbol(f"_B{i}_{j}"))
    A, B = [], []
    for i in range(k):
        ident_ = sp.expand(zdot[i] - sum(Asym[i, j] * zexpr[j] for j in range(k))
                           - sum(Bsym[i, j] * ws[j] for j in range(mm)))
        unknowns = list(Asym.row(i)) + list(Bsym.row(i))
        syms = sorted(ident_.free_symbols - set(unknowns) - set(thetas), key=str)
        coeffs = sp.Poly(ident_, *syms).coeffs() if syms else [ident_]
        sol = sp.linsolve(coeffs, unknowns)
        if not sol:
            raise CertError(f"coordinates {[n for n, _ in forms]} are not closed under the "
                            "dynamics (certify more outputs, or the model is not LTI in them)")
        (vals,) = sol
        free = {s: 0 for v in vals for s in sp.sympify(v).free_symbols if s not in thetas}
        vals = [sp.simplify(sp.sympify(v).subs(free)) for v in vals]
        A.append(vals[:k])
        B.append(vals[k:])
    # B must not depend on uncertain parameters; A must be multi-affine in them
    for row in B:
        for b in row:
            if b.free_symbols:
                raise CertError(f"input matrix depends on uncertain parameters ({b})")
    B = [[an.to_fraction(b) for b in row] for row in B]
    vertices = weights = None
    if thetas:
        for row in A:
            for a in row:
                num, den = sp.fraction(sp.together(a))
                if den.free_symbols:
                    raise CertError(f"A depends non-polynomially on uncertain parameters ({a})")
                pa = sp.Poly(sp.expand(a), *thetas)
                if any(d > 1 for mono in pa.monoms() for d in mono):
                    raise CertError(f"A is not multi-affine in the uncertain parameters ({a})")
        import itertools
        corners = list(itertools.product(*[(unc[str_name].lo, unc[str_name].hi)
                                           for str_name in [u.name for u in sp_.uncertain]]))
        vertices = [[[an.to_fraction(sp.sympify(a).subs(dict(zip(thetas, map(an.rat, cor)))))
                      for a in row] for row in A] for cor in corners]
        weights = []
        for cor in corners:
            f = []
            for u, val in zip(sp_.uncertain, cor):
                f.append((m.var(u.name).lean, u.lo, u.hi, "up" if val == u.hi else "down"))
            weights.append(f)
        Aexpr = A  # symbolic in θ
        nominal = {th: v_ for th, v_ in m.param_values().items() if th in thetas}
        A = [[an.to_fraction(sp.nsimplify(sp.sympify(a).subs(nominal), rational=True))
              for a in row] for row in Aexpr]
    else:
        A = [[an.to_fraction(a) for a in row] for row in A]
        Aexpr = [[an.rat(a) for a in row] for row in A]
    theta_names = {th: f"p.{m.var(u.name).lean}" for th, u in zip(thetas, sp_.uncertain)}
    mult = []
    for i in range(k):
        tgt = zdot_lean[i] - (sum(sp.sympify(a) * z for a, z in zip(Aexpr[i], zexpr))
                              + sum(an.rat(b) * w for b, w in zip(B[i], ws)))
        mu = an.multipliers(res, sp.expand(tgt), params=thetas)
        mult.append([(e, cf if isinstance(cf, Fraction) else lean_mod.sympy_to_lean(cf, theta_names))
                     for e, cf in mu])
    # initial coordinates
    vals = m.param_values()
    init = {}
    for v in states:
        if v.start is not None:
            init[v.symbol] = sp.nsimplify(sp.sympify(v.start).subs(vals).subs(vals), rational=True)
    for r in refs.values():
        if r.start is not None:
            init[m.var(r.name).symbol] = an.rat(r.start)
    x0 = []
    for (n_, f), z in zip(forms, zexpr):
        missing = [s for s in f if s not in init]
        if missing:
            raise CertError(f"coordinate {n_} needs initial values for {missing} (fixed start "
                            "values, or reference(start = ...))")
        x0.append(an.to_fraction(sp.expand(z.subs(init))))
    # outputs: express each in the coordinates
    zs = sp.symbols(f"_z0:{k}")
    outputs = []
    for name in sp_.certify:
        v = m.var(name)
        e = out_exprs[name]
        rsym = sp.symbols(f"_r0:{k}")
        ident_ = sp.expand(e - sum(rr * z for rr, z in zip(rsym, zexpr)))
        syms = sorted(ident_.free_symbols - set(rsym), key=str)
        coeffs = sp.Poly(ident_, *syms).coeffs() if syms else [ident_]
        sol = sp.linsolve(coeffs, rsym)
        if not sol:
            raise CertError(f"output {name} is not a linear function of the coordinates")
        (row,) = sol
        free = {s: 0 for rr in row for s in sp.sympify(rr).free_symbols}
        row = [an.to_fraction(sp.sympify(rr).subs(free)) for rr in row]
        tgt = v.symbol - sum(an.rat(rr) * z for rr, z in zip(row, zexpr))
        mo = an.multipliers(res, tgt, params=thetas) if v.role != "state" else []
        mo = [(e, cf if isinstance(cf, Fraction) else lean_mod.sympy_to_lean(cf, theta_names))
              for e, cf in mo]
        if v.role == "state" and sp.expand(tgt) != 0:
            raise CertError(f"state output {name} must be a combination of coordinates")
        kind = "state" if v.role == "state" else "algebraic"
        term = f"(x t).{v.lean}" if kind == "state" else f"(y t).{v.lean}"
        outputs.append(E.Output(name, term, kind, row, mo))

    def terms(f):
        out = []
        for s, c in f.items():
            var = next(vv for vv in m.variables if vv.symbol == s)
            out.append(E.Term(an.to_fraction(c), "x" if var.role == "state" else "u", var.lean))
        return out

    coords = [E.Coord(n_, terms(f)) for n_, f in forms]
    erefs = [E.Reference(m.var(r.name).lean,
                         m.var(r.derivative).lean if r.derivative else None, r.start)
             for r in sp_.references]
    params_ok = None
    if thetas:
        params_ok = []
        allv = m.param_values()
        for v in m.params:
            if v.binding is None:
                continue
            if v.name in unc:
                params_ok.append(("range", v.lean, unc[v.name].lo, unc[v.name].hi))
            else:
                val = sp.nsimplify(sp.sympify(v.binding).subs(pvals).subs(pvals), rational=True)
                params_ok.append(("eq", v.lean, an.to_fraction(val)))
    return E.LinearProblem(
        params_ok=params_ok, vertices=vertices, weights=weights,
        model_name=m.name, ns=m.ns, module=f"Certs.{m.ns}",
        states=[v.lean for v in states], coords=coords,
        dists=[m.var(d).lean for d in sp_.disturbance_names],
        dist_bounds=[d.bound for d in sp_.disturbances], refs=erefs, A=A, B=B,
        n_bound=m.n_bound, n_eqs=len(eqs), n_init=m.n_init, multipliers=mult, x0=x0,
        literals=E.decimal_literals(lean_src), outputs=outputs)


# --- Lean ---------------------------------------------------------------------------------------

def lake(*args, cwd=REPO, check=True):
    r = subprocess.run(["lake", *args], cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        errs = "\n".join(l for l in (r.stdout + r.stderr).splitlines()
                         if l.startswith("error") or "error:" in l)
        raise CertError(f"lake {' '.join(args)} failed:\n{errs[-4000:]}")
    return r


def axioms(module: str, decl: str, root: Path = REPO) -> set[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=root, delete=False) as f:
        f.write(f"import {module}\n#print axioms {decl}\n")
        tmp = Path(f.name)
    try:
        r = lake("env", "lean", tmp.name, check=False, cwd=root)
    finally:
        tmp.unlink()
    out = r.stdout + r.stderr
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    if "does not depend on any axioms" in out:
        return set()
    if not m:
        raise CertError(f"could not read axioms:\n{out}")
    return {a.strip() for a in m.group(1).split(",") if a.strip()}


# --- driver -------------------------------------------------------------------------------------

def lti_search(pb):
    """Numeric search (untrusted) for the LTI certificate of a linear problem, or None."""
    rows = [o.row for o in pb.outputs]
    if pb.vertices is not None:
        return lti.certify_polytopic(pb.vertices, pb.B, pb.dist_bounds, x0=pb.x0, output_rows=rows)
    return lti.certify_channels(pb.A, pb.B, pb.dist_bounds, x0=pb.x0, output_rows=rows)


def emit_and_check(m, sp_, lean_src: str, py_file: Path, mo: Path, pb, cert, plots: bool = True,
                   verbose=print, root: Path = REPO) -> dict:
    """Write Model/Spec/Cert.lean, build them with Lean, audit axioms, write the sidecar."""
    out = root / "certs" / "Certs" / m.ns
    out.mkdir(parents=True, exist_ok=True)
    (out / "Model.lean").write_text(lean_src)
    (out / "Spec.lean").write_text(emit_lti.emit_spec(pb))
    (out / "Cert.lean").write_text(emit_lti.emit_cert(pb, cert))
    shutil.copy(py_file, out / "model_sympy.py")
    if Path(mo).resolve() != (out / "source.mo").resolve():
        shutil.copy(mo, out / "source.mo")  # for simulation by rumoca (Monte Carlo)
    verbose(f"lean: lake build Certs.{m.ns}.Cert")
    lake("build", f"Certs.{m.ns}.Cert", cwd=root)
    ax = axioms(f"Certs.{m.ns}.Cert", f"{m.ns}.Cert.certified", root=root)
    if not ax <= ALLOWED_AXIOMS:
        raise CertError(f"certificate depends on disallowed axioms: {ax - ALLOWED_AXIOMS}")
    verbose(f"lean: {m.ns}.Cert.certified checked; axioms {sorted(ax)}")
    tax = axioms(f"Certs.{m.ns}.Cert", f"{m.ns}.Cert.tube", root=root)
    if not tax <= ALLOWED_AXIOMS:
        raise CertError(f"tube theorem depends on disallowed axioms: {tax - ALLOWED_AXIOMS}")
    lean_names = {v.lean: v.name for v in m.variables}
    side = {
        "model": m.name, "ns": m.ns,
        "method": "lti-polytopic" if pb.vertices is not None else "lti-channel", "states": [c.name for c in pb.coords],
        "P": [[q(v) for v in r] for r in cert.P], "level": q(cert.level),
        "alpha": q(cert.alpha), "gammas": [q(g) for g in cert.gammas],
        "x0": [q(v) for v in pb.x0],
        "disturbances": [{"name": d.name, "bound": q(d.bound)} for d in sp_.disturbances],
        "coords": [c.name for c in pb.coords],
        "outputs": [{"name": o.name, "row": [q(v) for v in o.row],
                     "state": (o.row.index(1) if sorted(o.row) == [0] * (len(o.row) - 1) + [1]
                               else None),
                     "bound": q(b.bound)} for o, b in zip(pb.outputs, cert.boxes)],
        "A": [[q(v) for v in r] for r in pb.A], "B": [[q(v) for v in r] for r in pb.B],
        "theorem": f"{m.ns}.Cert.certified", "axioms": sorted(ax),
        "source": "source.mo",
        # the error frame z = Σ coeff·var (states and reference inputs) in which `Cert.tube`
        # proves zᵀ P z ≤ level
        "frame": {"coords": [c.name for c in pb.coords],
                  "terms": [[{"coeff": q(tm.coeff),
                              "kind": "state" if tm.kind == "x" else "input",
                              "var": lean_names[tm.fld]} for tm in c.terms]
                            for c in pb.coords],
                  "theorem": f"{m.ns}.Cert.tube"},
    }
    (out / "certified.json").write_text(json.dumps(side, indent=1))
    result = {"dir": str(out), "sidecar": side}
    if plots:
        from . import plot
        import numpy as np
        A = np.array([[float(v) for v in r] for r in pb.A])
        B = np.array([[float(v) for v in r] for r in pb.B])
        peaks = plot.plot_certificate(out / "certified.json", lambda x, w: A @ x + B @ w,
                                      out / "certificate.png",
                                      x0=np.array([float(v) for v in pb.x0]))
        result["plot"] = str(out / "certificate.png")
        result["simulated_peaks"] = peaks
        verbose(f"plot: {out / 'certificate.png'}")
    return result


def check(mo: Path, model: str, plots: bool = True, verbose=print, root: Path = REPO) -> dict:
    """The LMI approach end to end (kept for the Python API; the CLI goes through
    `dynacert.approaches`)."""
    mo = Path(mo).resolve()
    root = Path(root)
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        verbose(f"rumoca: exporting {model} (lean-dae, sympy-dae)")
        lean_file, py_file = export(mo, model, work, root=root)
        m = model_mod.load(py_file)
        lean_src = lean_file.read_text()
        sp_ = spec_mod.from_model(m)
        verbose(f"spec: disturbances {[(d.name, str(d.bound)) for d in sp_.disturbances]}, "
                f"certify {sp_.certify}")
        pb = linear_problem(m, sp_, lean_src)
        verbose(f"model: LTI, n = {len(pb.coords)}, m = {len(pb.dists)}")
        cert = lti_search(pb)
        if cert is None:
            raise CertError("no certificate found (LMI infeasible or rounding failed)")
        verbose(f"search: α = {float(cert.alpha):.4g}, level = {float(cert.level):.6g}")
        return emit_and_check(m, sp_, lean_src, py_file, mo, pb, cert, plots, verbose, root)
