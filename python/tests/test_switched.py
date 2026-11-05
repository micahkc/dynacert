"""Switched linear certificates (`if`-expressions): Lean text parsing, mode expansion, the common
storage search, emission, and an end-to-end Lean build when `lake` is available."""

import shutil
from fractions import Fraction as F
from pathlib import Path

import pytest

from dynacert import approaches, emit_switched, model as model_mod, pipeline, problem
from dynacert import spec as spec_mod, switched
from dynacert.methods import lti

ROOT = Path(__file__).resolve().parents[2]


def committed(name: str) -> problem.Problem:
    d = ROOT / "certs" / "Certs" / name
    m = model_mod.load(d / "model_sympy.py")
    return problem.Problem(d / "source.mo", name, m, spec_mod.from_model(m),
                           (d / "Model.lean").read_text(), d / "model_sympy.py", ROOT)


def test_if_chains_parse_rumoca_text():
    conj = ["y.u = -(p.kp * x.x) - p.ki * x.z",
            "dx.z = (if |y.u| > p.ulim then 0 else x.x)",
            "dx.v = -((if x.v > p.a then p.c else if x.v < -p.a then (p.d + 1) else p.e) * x.v)"
            " + (if |x.x| > p.b then p.k else 0) * x.x"]
    ch = switched.if_chains(conj)
    assert [(c.eq, c.conds, c.branches) for c in ch] == [
        (1, ["|y.u| > p.ulim"], ["0", "x.x"]),
        (2, ["x.v > p.a", "x.v < -p.a"], ["p.c", "(p.d + 1)", "p.e"]),
        (2, ["|x.x| > p.b"], ["p.k", "0"])]
    with pytest.raises(pipeline.CertError):
        switched.if_chains(["dx.z = (if x.a > 0 then (if x.b > 0 then 1 else 2) else 3)"])


def test_binders_and_branch_indicators():
    names = switched.binder_names("(t : ℝ) (p : Params) (u : Inputs) (x dx : States) "
                                  "(y : Algebraics)")
    assert names == {"t": "t", "p": "p", "u": "u", "x": "x", "dx": "dx", "y": "y"}
    assert emit_switched._branch_indicator(["a", "b"], 1) == \
        "(if a then (0 : ℝ) else if b then (1 : ℝ) else (0 : ℝ))"
    assert emit_switched._branch_indicator(["a"], 1) == "(if a then (0 : ℝ) else (1 : ℝ))"


def test_mode_expansion_keeps_the_frame():
    prob = committed("SwitchedPILeak")
    spb = switched.switched_problem(prob.model, prob.spec, prob.lean_src)
    assert [sw.conds for sw in spb.switches] == [["|y.u| > p.ulim"]]
    assert spb.modes == [(0,), (1,)] and spb.if_eqs == [2]
    assert spb.As == [[[-3, -1], [0, F(-1, 2)]], [[-3, -1], [1, 0]]]
    assert all(pb.B == [[1], [0]] for pb in spb.problems)
    assert [c.name for c in spb.base.coords] == ["x", "z"]
    # the expanded modes have the same equation count (Lean conjunct indices still match)
    assert all(pb.n_eqs == 3 for pb in spb.problems)
    assert spb.mode_text(1) == "¬(|y.u| > p.ulim)"


def test_mode_dependent_output_row():
    prob = committed("GainScheduledPI")
    spb = switched.switched_problem(prob.model, prob.spec, prob.lean_src)
    assert spb.switched_outputs == [2]
    rows = [pb.outputs[2].row for pb in spb.problems]
    assert rows == [[-4, -2], [F(-3, 2), -2]]


def test_search_on_the_switched_pi_matrices():
    # conditional integration with bleed-off: a common storage exists
    As = [[[-3, -1], [0, F(-1, 2)]], [[-3, -1], [1, 0]]]
    c = lti.certify_polytopic(As, [[1], [0]], [F(1, 5)], output_rows=[[1, 0], [0, 1]])
    assert c is not None and len(c.witnesses) == 2
    # pure conditional integration: the integrator is frozen in the saturated mode
    frozen = [[[-3, -1], [0, 0]], [[-3, -1], [1, 0]]]
    assert switched.common_lyapunov_infeasible(frozen)
    assert lti.certify_polytopic(frozen, [[1], [0]], [F(1, 5)]) is None
    # two stable oscillators switched by quadrant: no common quadratic storage
    quad = [[[F(-1, 10), -1], [2, F(-1, 10)]], [[F(-1, 10), -2], [1, F(-1, 10)]]]
    assert switched.common_lyapunov_infeasible(quad)


def test_emission_text():
    prob = committed("SwitchedPILeak")
    spb = switched.switched_problem(prob.model, prob.spec, prob.lean_src)
    c = switched.search(spb)
    assert c is not None
    txt = emit_switched.emit_cert(spb, c)
    assert "import Certs.SwitchedPILeak.Spec" in txt
    assert "noncomputable def weights (t : ℝ) (p : Params) (u : Inputs) (x dx : States) " \
           "(y : Algebraics) : Fin 2 → ℝ :=" in txt
    assert "(if |y.u| > p.ulim then (1 : ℝ) else (0 : ℝ))" in txt
    assert "split_ifs at e2 ⊢" in txt
    assert "theorem certified : Spec.Claim" in txt and "theorem tube" in txt
    assert "cert.invariant (wt := wt)" in txt
    assert "sorry" not in txt and "by native_decide" not in txt


def test_assessment():
    a = approaches.get("switched")
    assert a.layer == approaches.CERTIFY and a.classes == ("switched-lti",) and a.cost == 15
    v = a.assess(committed("SwitchedPILeak"))
    assert v.feasible and "2 modes" in v.notes[0]
    v = a.assess(committed("ClosedLoop"))
    assert not v.feasible and "no if-expressions" in v.notes[0]


@pytest.mark.skipif(shutil.which("lake") is None, reason="needs lake")
def test_lean_end_to_end():
    prob = committed("SwitchedPILeak")
    spb = switched.switched_problem(prob.model, prob.spec, prob.lean_src)
    c = switched.search(spb)
    f = prob.cert_dir / "SwitchedCertTest.lean"
    f.write_text(emit_switched.emit_cert(spb, c))
    try:
        pipeline.lake("build", "Certs.SwitchedPILeak.SwitchedCertTest", cwd=ROOT)
        for thm in ("certified", "tube"):
            ax = pipeline.axioms("Certs.SwitchedPILeak.SwitchedCertTest",
                                 f"SwitchedPILeak.SwitchedCert.{thm}", root=ROOT)
            assert ax <= pipeline.ALLOWED_AXIOMS
    finally:
        f.unlink()
        for p in (ROOT / ".lake" / "build").rglob("SwitchedCertTest.*"):
            p.unlink()
