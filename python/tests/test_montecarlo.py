"""Monte Carlo validation (untrusted): exact statistics, scenarios, both backends."""

import importlib.util
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import pytest

import dynacert
from dynacert import montecarlo as M
from dynacert import stats

ROOT = Path(__file__).resolve().parents[2]
has_rumoca = importlib.util.find_spec("rumoca") is not None


def test_samples_for_is_minimal_and_exact():
    n = stats.samples_for(F(1, 100), F(1, 10 ** 6))
    assert n == 1375
    assert (1 - F(1, 100)) ** n <= F(1, 10 ** 6) < (1 - F(1, 100)) ** (n - 1)


def test_eps_for_rounds_up():
    for n in (10, 200, 1375, 5000):
        eps = stats.eps_for(n, F(1, 1000))
        assert stats.confidence_failure(n, eps) <= F(1, 1000)
        assert float(eps) < 1.01 * -np.expm1(np.log(1e-3) / n) + 1e-4


def test_wilks_reduces_to_scenario_bound():
    assert stats.wilks_confidence_failure(50, 0, F(1, 20)) == (1 - F(1, 20)) ** 50
    assert stats.wilks_confidence_failure(50, 2, F(1, 20)) > stats.confidence_failure(50, F(1, 20))


def test_clopper_pearson_and_dkw():
    lo, hi = stats.clopper_pearson(0, 100, 0.05)
    assert lo == 0 and 0.03 < hi < 0.05
    assert abs(stats.dkw(1000, 0.05) - 0.0429) < 1e-3


def test_scenarios_are_admissible_and_roundtrip():
    cert = dynacert.load("ClosedLoopUncertain", root=ROOT)
    space = M.ScenarioSpace(cert.spec, T=5.0)
    lo, hi = space.box()
    rng = np.random.default_rng(0)
    for _ in range(20):
        s = space.sample(rng)
        z = space.encode(s)
        assert np.all(lo <= z) and np.all(z <= hi)
        assert np.allclose(space.encode(space.decode(z)), z)
        d = space.disturbance(s, "d")
        assert all(abs(d(t)) <= 1.0 for t in np.linspace(0, 5, 101))
        assert 0.1 <= s.theta["c"] <= 0.3


def test_harness_drives_every_input():
    cert = dynacert.load("ClosedLoop", root=ROOT)
    space = M.ScenarioSpace(cert.spec, T=5.0)
    cls, src = M.harness(cert.model, cert.spec, space, "ClosedLoop")
    for u in ("d", "a_ref", "x_ref", "v_ref"):
        assert f"sys.{u} = " in src
    assert "der(ref_x_ref) = sys.v_ref;" in src and src.startswith(f"model {cls}")


def test_sympy_backend_within_bounds():
    cert = dynacert.load("ClosedLoopUncertain", root=ROOT)
    mc = cert.montecarlo(8, T=4.0, backend="sympy", seed=3)
    assert mc.n == 8 and not mc.errors
    assert not any(mc.violations().values())
    s = mc.summary(F(1, 1000))
    assert s["eps"] == stats.eps_for(8, F(1, 1000))
    assert np.all(mc.margin() <= 1.0)
    assert "zero_failure_bound" in mc.report()


@pytest.mark.skipif(not has_rumoca, reason="rumoca Python binding not installed")
def test_rumoca_agrees_with_sympy_export():
    cert = dynacert.load("ClosedLoop", root=ROOT)
    cc = cert.crosscheck(4, T=4.0)
    assert max(cc.max_rel().values()) < 1e-3
    mc = cert.montecarlo(6, T=4.0)
    assert mc.n == 6 and not any(mc.violations().values())


def test_adjoint_reaches_the_exact_lti_worst_case():
    """For an LTI model the adjoint step is exact on the grid: compare with the L1 value
    ∫₀ᵀ |C e^{As} B| ds (the supremum of |e(T)| from rest)."""
    import scipy.linalg as la
    from scipy.integrate import quad

    from dynacert import worstcase

    cert = dynacert.load("ClosedLoop", root=ROOT)
    T = 6.0
    A = np.array([[float(F(v)) for v in r] for r in cert.sidecar["A"]])
    B = np.array([float(F(r[0])) for r in cert.sidecar["B"]])
    exact = quad(lambda s: abs((la.expm(A * s) @ B)[0]), 0, T, limit=500)[0]
    space = M.ScenarioSpace(cert.spec, T, M.Distribution(segments=120))
    r = worstcase.Adjoint(cert.model, cert.spec, space, dt=0.005).search("e", tstars=4)
    assert 0.995 * exact <= r.value <= exact * (1 + 1e-3)
    assert set(np.unique(r.scenario.levels["d"])) <= {-1.0, 0.0, 1.0}


def test_switching_times_beat_the_grid():
    """Moving switches to the zero crossings of the switching function closes the grid gap."""
    import scipy.linalg as la
    from scipy.integrate import quad

    from dynacert import worstcase

    cert = dynacert.load("ClosedLoop", root=ROOT)
    T = 6.0
    A = np.array([[float(F(v)) for v in r] for r in cert.sidecar["A"]])
    B = np.array([float(F(r[0])) for r in cert.sidecar["B"]])
    exact = quad(lambda s: abs((la.expm(A * s) @ B)[1]), 0, T, limit=500)[0]
    space = M.ScenarioSpace(cert.spec, T, M.Distribution(segments=30))
    r = worstcase.Adjoint(cert.model, cert.spec, space, dt=0.005).search("ev", tstars=4)
    vals = {stage: v for stage, v, _ in r.candidates}
    assert vals["switch"] > vals["scan"]
    assert vals["switch"] >= 0.9995 * exact
    assert r.scenario.edges            # switches placed off the grid


@pytest.mark.skipif(not has_rumoca or importlib.util.find_spec("casadi") is None,
                    reason="needs rumoca and casadi")
def test_collocation_matches_adjoint_on_lti():
    from dynacert import collocation, worstcase

    if collocation.available():
        pytest.skip(collocation.available())
    cert = dynacert.load("ClosedLoop", root=ROOT)
    space = M.ScenarioSpace(cert.spec, 6.0, M.Distribution(segments=60))
    adj = worstcase.Adjoint(cert.model, cert.spec, space, dt=0.005)
    a = adj.search("e", tstars=4)
    col = collocation.Collocation(cert.model, cert.spec, space, cert.source, "ClosedLoop")
    zero = M.Scenario({}, {"d": np.zeros(60)}, {"a_ref": np.zeros((3, 3))})
    c = col.solve("e", 6.0, 1.0, zero, adj.fwd.run(zero))   # cold start: an LP on its grid
    assert c.status == "solved"
    v = M._peaks(M.SympyBackend(cert.model, cert.spec, space, dt=0.002).run(c.scenario))["e"]
    assert 0.995 * a.value <= v <= a.value * (1 + 1e-3)
