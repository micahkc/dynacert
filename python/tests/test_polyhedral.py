"""Polyhedral RPI certificates (methods/polyhedral.py, emit_poly.py, approaches/polyhedral.py).

The search output is re-verified exactly here (no Lean needed); one end-to-end kernel check
runs when `lake` is available."""

import shutil
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import pytest

from dynacert import exact, model as model_mod, pipeline, problem, spec as spec_mod
from dynacert.methods import polyhedral as P

ROOT = Path(__file__).resolve().parents[2]

MODELS = {
    # name: (A, B, δ, exact all-time peak of |e| = Σ δ ∫|c e^{As} b| ds, lmi bound of |e|)
    "ClosedLoop": ([[0, 1], [-3, -1]], [[0], [1]], [1], 0.75566, F(5649, 6695)),
    "ClosedLoopComposed": ([[0, 1], [-11, F(-11, 5)]], [[0], [1]], [1], 0.18102, F(17, 84)),
}
ROWS = [[1, 0], [0, 1]]


def independent_check(c, A, B, x0):
    """The Lean fields, re-checked from scratch with Fractions."""
    A, B = exact.to_mat(A), exact.to_mat(B)
    k = len(c.H)
    assert all(c.M[i][j] >= 0 for i in range(k) for j in range(k) if i != j)
    assert exact.matmul(c.H, A) == exact.matmul(c.M, c.H)
    HB = exact.matmul(c.H, B)
    for i in range(k):
        assert sum(c.M[i][j] * c.h[j] for j in range(k)) + \
            sum(abs(HB[i][j]) * c.delta[j] for j in range(len(c.delta))) < 0
    assert all(sum(c.H[i][j] * x0[j] for j in range(len(x0))) <= c.h[i] for i in range(k))
    for o in c.outputs:
        assert min(o.lp) >= 0 and min(o.lm) >= 0
        for j in range(len(o.row)):
            assert sum(o.lp[i] * c.H[i][j] for i in range(k)) == o.row[j]
            assert sum(o.lm[i] * c.H[i][j] for i in range(k)) == -o.row[j]
        assert exact.dot(o.lp, c.h) <= o.bound and exact.dot(o.lm, c.h) <= o.bound


@pytest.mark.parametrize("name", list(MODELS))
def test_search_is_exact_and_sound(name):
    A, B, d, peak, _ = MODELS[name]
    c = P.certify(A, B, d, x0=[0, 0], output_rows=ROWS, facets=48)
    assert c is not None and c.facets <= 48
    assert c.check(exact.to_mat(A), exact.to_mat(B), [F(0), F(0)]) == []
    independent_check(c, A, B, [0, 0])
    # a sound bound is never below the exact all-time peak
    assert float(c.outputs[0].bound) >= peak


def test_more_facets_beat_the_ellipsoid():
    A, B, d, peak, lmi = MODELS["ClosedLoop"]
    c = P.certify(A, B, d, x0=[0, 0], output_rows=ROWS, facets=128)
    assert c is not None
    independent_check(c, A, B, [0, 0])
    assert peak <= float(c.outputs[0].bound) < float(lmi)


def test_nonzero_initial_point_is_inside():
    A, B, d, _, _ = MODELS["ClosedLoop"]
    x0 = [F(3, 2), F(-1)]
    c = P.certify(A, B, d, x0=x0, output_rows=ROWS, facets=32)
    assert c is not None
    independent_check(c, A, B, x0)
    assert c.outputs[0].bound >= F(3, 2)


def test_trajectories_stay_in_the_polytope():
    A, B, d, _, _ = MODELS["ClosedLoopComposed"]
    c = P.certify(A, B, d, x0=[0, 0], output_rows=ROWS, facets=32)
    H = np.array([[float(v) for v in r] for r in c.H])
    h = np.array([float(v) for v in c.h])
    An = np.array([[float(v) for v in r] for r in exact.to_mat(A)])
    rng = np.random.default_rng(1)
    for _ in range(5):
        z, dt = np.zeros(2), 1e-3
        ws = rng.choice([-1.0, 1.0], size=4000 // 50 + 1)
        for s in range(4000):
            z = z + dt * (An @ z + np.array([0.0, ws[s // 50]]))
            assert np.all(H @ z <= h + 1e-6)


def test_unstable_or_defective_models_fail_cleanly():
    assert P.certify([[1, 0], [0, -1]], [[1], [0]], [1], output_rows=ROWS) is None


# --- approach and Lean ---------------------------------------------------------------------------

def committed(name: str) -> problem.Problem:
    d = ROOT / "certs" / "Certs" / name
    m = model_mod.load(d / "model_sympy.py")
    return problem.Problem(d / "source.mo", name, m, spec_mod.from_model(m),
                           (d / "Model.lean").read_text(), d / "model_sympy.py", ROOT)


def test_approach_is_registered_and_assesses():
    from dynacert import approaches
    from dynacert.approaches import polyhedral  # noqa: F401  (until auto-discovery)

    a = approaches.get("polyhedral")
    assert a.classes == ("lti",) and a.cost == 20
    prob = committed("ClosedLoopUncertain")
    v = a.assess(prob)
    assert not v.feasible and "uncertain" in v.notes[0]


@pytest.mark.skipif(shutil.which("lake") is None, reason="needs lake")
def test_lean_end_to_end():
    from dynacert import emit_poly

    prob = committed("ClosedLoop")
    pb = pipeline.linear_problem(prob.model, prob.spec, prob.lean_src)
    c = P.certify(pb.A, pb.B, pb.dist_bounds, x0=pb.x0,
                  output_rows=[o.row for o in pb.outputs], facets=24)
    assert c is not None
    f = prob.cert_dir / "PolyCertTest.lean"
    f.write_text(emit_poly.emit(pb, c))
    try:
        pipeline.lake("build", "Certs.ClosedLoop.PolyCertTest", cwd=ROOT)
        ax = pipeline.axioms("Certs.ClosedLoop.PolyCertTest", "ClosedLoop.PolyCert.certified",
                             root=ROOT)
        assert ax <= pipeline.ALLOWED_AXIOMS
    finally:
        f.unlink()
        for p in (ROOT / ".lake" / "build").rglob("PolyCertTest.*"):
            p.unlink()
