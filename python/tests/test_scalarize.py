"""Array variables as scalar coordinates (scalarize.py) in the linear methods and the Monte Carlo
harness. The fixtures in `fixtures/` are compiled with rumoca; one end-to-end kernel check runs
when `lake` is available."""

import re
import shutil
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import pytest

from dynacert import emit_layered, emit_lti, montecarlo, pipeline, problem, scalarize
from dynacert.approaches import get

ROOT = Path(__file__).resolve().parents[2]
FIX = Path(__file__).resolve().parent / "fixtures"


def _have_rumoca() -> bool:
    try:
        pipeline.rumoca_bin()
    except pipeline.CertError:
        return False
    return pipeline.DEFAULT_TARGETS.exists()


needs_rumoca = pytest.mark.skipif(not _have_rumoca(), reason="needs the rumoca export toolchain")
_CACHE = {}


def load(name: str) -> problem.Problem:
    if name not in _CACHE:
        _CACHE[name] = problem.load(FIX / f"{name}.mo", name, root=ROOT)
    return _CACHE[name]


def write_model(tmp_path, name: str, body: str) -> problem.Problem:
    f = tmp_path / f"{name}.mo"
    f.write_text(f"model {name}\n{body}\nend {name};\n")
    return problem.load(f, name, root=ROOT)


# --- pure units ---------------------------------------------------------------------------------

def test_binders_of_lean_for_loops():
    assert scalarize.binders("(∀ i : Fin 3, p.m * dx.v i = u.d i)") == [("fin", 3)]
    assert scalarize.binders("(∀ i : Fin 2, ∀ j : Fin 2, dx.M i j = -x.M i j)") == \
        [("fin", 2), ("fin", 2)]
    assert scalarize.binders("(∀ i j : Fin 2, dx.M i j = 0)") == [("fin", 2), ("fin", 2)]
    assert scalarize.binders("(∀ i : ℕ, 2 ≤ i → i ≤ 3 → Rumoca.at1 dx.q i = 0)") == \
        [("nat", 2, 3)]
    assert scalarize.binders("dx.x = x.v") == []


def test_simp_set_matches_the_lean_examples():
    """The `simp only` set the generator emits is the one Dynacert/Linear/Scalar.lean tests."""
    src = (ROOT / "Dynacert" / "Linear" / "Scalar.lean").read_text()
    sets = re.findall(r"simp only \[(.*?)\]", src, re.S)
    want = {s.strip() for s in scalarize.SIMPS.split(",")}
    assert sets and all({s.strip() for s in x.split(",")} == want for x in sets)


def test_models_without_arrays_are_unchanged():
    from test_approaches import committed

    prob = committed("ClosedLoop")
    m, s = scalarize.view(prob.model, prob.spec, prob.lean_src)
    assert m is prob.model and s is prob.spec
    pb = pipeline.linear_problem(prob.model, prob.spec, prob.lean_src)
    assert pb.eq_handles is None and pb.state_hyps is None
    assert emit_lti.emit_spec(pb) == (ROOT / "certs/Certs/ClosedLoop/Spec.lean").read_text()


# --- scalar view --------------------------------------------------------------------------------

@needs_rumoca
def test_scalar_view_names_terms_and_handles():
    prob = load("ArrayMSD")
    m = scalarize.model(prob.model, prob.lean_src)
    x2, K12 = m.var("x[2]"), m.var("K[1,2]")
    assert (x2.lean, x2.role, K12.lean, K12.binding) == ("x 1", "state", "K 0 1", F(1, 10))
    assert m.var("x[3]").start is not None and m.n_bound == 4 and m.n_init == 2
    # der(x) = v (vector), a for loop over Fin 3, e = 2 x (vector)
    assert m.eq_handles == ["(congrFun eq0 0)", "(congrFun eq0 1)", "(congrFun eq0 2)",
                            "(eq1 0)", "(eq1 1)", "(eq1 2)",
                            "(congrFun eq2 0)", "(congrFun eq2 1)", "(congrFun eq2 2)"]
    assert m.state_hyps["v[3]"] == (1, " 2")


@needs_rumoca
def test_annotations_per_component():
    s = load("ArrayTracking").scalar[1]
    assert [(d.name, d.bound) for d in s.disturbances] == [("d[1]", F(1)), ("d[2]", F(1, 2))]
    assert s.certify == ["e[1]", "e[2]", "ev[1]", "ev[2]"]
    assert [(r.name, r.derivative, r.start) for r in s.references[:4]] == [
        ("x_ref[1]", "v_ref[1]", F(0)), ("x_ref[2]", "v_ref[2]", F(0)),
        ("v_ref[1]", "a_ref[1]", F(0)), ("v_ref[2]", "a_ref[2]", F(0))]
    u = load("ArrayUncertain").scalar[1]
    assert [(x.name, x.lo, x.hi) for x in u.uncertain] == [("c[1]", F(4, 5), F(6, 5)),
                                                          ("c[2]", F(4, 5), F(9, 5))]
    assert [b.name for b in u.initial] == ["x[1]", "x[2]"]


@needs_rumoca
def test_euclidean_norm_is_rejected(tmp_path):
    prob = write_model(tmp_path, "NormBall", """
  input Real d[2] annotation(__Dynacert(disturbance(bound = 1, norm = "2")));
  Real x[2](each start = 0, each fixed = true) annotation(__Dynacert(certify));
equation
  der(x) = -x + d;""")
    assert prob.spec.disturbances[0].norm == "2"
    for name in ("lmi", "montecarlo"):
        v = get(name).assess(prob)
        assert not v.feasible and 'norm = "2"' in v.notes[0], (name, v.notes)


@needs_rumoca
def test_arrays_in_a_nonlinear_part_are_reported_as_nonlinear(tmp_path):
    prob = write_model(tmp_path, "ArrayNonlinear", """
  parameter Real k[2] = {1, 2};
  input Real d annotation(__Dynacert(disturbance(bound = 1)));
  Real q[2](each start = 0, each fixed = true) annotation(__Dynacert(certify));
equation
  der(q[1]) = -k[1] * q[1] + q[1] * q[2] + d;
  der(q[2]) = -k[2] * q[2];""")
    v = get("lmi").assess(prob)
    assert not v.feasible and "not linear" in v.notes[0] and "der(q[1])" in v.notes[0]
    assert "array" not in v.notes[0]


# --- linear problems and emitted Lean -----------------------------------------------------------

@needs_rumoca
def test_linear_problem_and_spec_per_component():
    prob = load("ArrayTracking")
    pb = pipeline.linear_problem(prob.model, prob.spec, prob.lean_src)
    assert [c.name for c in pb.coords] == ["e[1]", "e[2]", "ev[1]", "ev[2]"]
    assert pb.dists == ["d 0", "d 1"] and pb.dist_bounds == [F(1), F(1, 2)]
    assert pb.states == ["x", "v"] and pb.n_conj == len(prob.model.equations)
    spec = emit_lti.emit_spec(pb)
    assert "|(u t).d 0| ≤ (1 : ℝ) ∧ |(u t).d 1| ≤ (1/2 : ℝ)" in spec
    assert "HasDerivWithinAt (fun s => (u s).x_ref 1) ((u t).v_ref 1) (Ici t) t" in spec
    assert "|(y t).e 0| ≤ (b 0 : ℝ)" in spec and "|(y t).ev 1| ≤ (b 3 : ℝ)" in spec
    cert = pipeline.lti_search(pb)
    src = emit_lti.emit_cert(pb, cert)
    assert "import Dynacert.Linear.Scalar" in src and "fin_mk_ofNat" in src
    assert "(continuousOn_const.mul (hc0 1))" in src and "have e0 := " in src


@needs_rumoca
def test_layered_coordinates_are_array_elements():
    prob = load("ArrayLayered")
    pb, layers, signals, out_idx, _ = emit_layered.layered_problem(prob)
    assert [L.name for L in layers] == ["a", "b"]
    assert [pb.coords[j].name for j in signals] == ["a.x[1]", "a.x[2]", "b.x[1]", "b.x[2]"]
    b, c = emit_layered.search(pb, layers, signals)
    src = emit_layered.emit_cert(pb, layers, signals, out_idx, b, c)
    assert "def sig (s : States) : Fin 4 → ℝ := ![|s.«a.x» 0|, |s.«a.x» 1|" in src
    assert "continuous_abs.comp_continuousOn (hc2 1)" in src


# --- Monte Carlo harness ------------------------------------------------------------------------

@needs_rumoca
def test_harness_drives_each_component():
    prob = montecarlo.scalar_target(load("ArrayUncertain"))
    space = montecarlo.ScenarioSpace(prob.spec, 2.0)
    cls, src = montecarlo.harness(prob.model, prob.spec, space, "ArrayUncertain")
    assert "  sys.d[1] = 0.3 * (" in src and "  sys.d[2] = 0.3 * (" in src
    assert "ArrayUncertain sys(c = {th_c_1_, th_c_2_});" in src
    assert "parameter Real th_c_2_ = 1.5;" in src
    assert montecarlo.tunable("c[2]") == "th_c_2_" and montecarlo.tunable("k") == "sys.k"


@needs_rumoca
def test_sympy_backend_samples_per_component():
    prob = load("ArrayMSD")
    mc = montecarlo.run(prob, 4, T=2.0, backend_name="sympy", trace_points=0, bounds={})
    assert sorted(mc.peaks) == ["e[1]", "e[2]", "e[3]"] and not mc.errors
    scn = mc.scenarios[0]
    assert sorted(scn.levels) == ["d[1]", "d[2]", "d[3]"]
    assert all(np.all(np.abs(v) <= 1) for v in scn.levels.values())


# --- end to end ---------------------------------------------------------------------------------

@needs_rumoca
@pytest.mark.skipif(shutil.which("lake") is None, reason="needs lake")
def test_lean_end_to_end_with_array_references():
    prob = load("ArrayTracking")
    out = ROOT / "certs" / "Certs" / prob.model.ns
    if out.exists():
        pytest.skip(f"{out} exists (left from a manual run?)")
    pb = pipeline.linear_problem(prob.model, prob.spec, prob.lean_src)
    cert = pipeline.lti_search(pb)
    try:
        res = pipeline.emit_and_check(prob.model, prob.spec, prob.lean_src, prob.py_file,
                                      prob.mo, pb, cert, plots=False, verbose=lambda *_: None,
                                      root=ROOT)
        side = res["sidecar"]
        assert set(side["axioms"]) <= pipeline.ALLOWED_AXIOMS
        assert [o["name"] for o in side["outputs"]] == ["e[1]", "e[2]", "ev[1]", "ev[2]"]
        assert [d["name"] for d in side["disturbances"]] == ["d[1]", "d[2]"]
    finally:
        shutil.rmtree(out, ignore_errors=True)
        for p in (ROOT / ".lake" / "build").rglob(prob.model.ns):
            shutil.rmtree(p, ignore_errors=True) if p.is_dir() else p.unlink()
