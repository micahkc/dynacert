"""Initial sets (`initialSet`) and funnels (`Cert.funnel`): spec parsing, emission (unchanged
without an initial set), the exact box bound, the sidecar constants, and the figures."""

import itertools
import shutil
import tempfile
from fractions import Fraction as F
from pathlib import Path
from types import SimpleNamespace

import matplotlib

matplotlib.use("Agg")

import numpy as np
import pytest

import dynacert
from dynacert import emit_lti, exact, figures, pipeline, spec, tube
from dynacert import model as model_mod
from dynacert.methods import lti

ROOT = Path(__file__).resolve().parents[2]


def _var(name, role, ann=None):
    return SimpleNamespace(name=name, role=role,
                           annotations={"__Dynacert": ann} if ann is not None else None)


def test_spec_reads_initial_set():
    m = SimpleNamespace(annotations=None, variables=[
        _var("x", "state", {"initialSet": {"min": -0.5, "max": 1.5}}),
        _var("v", "state"),
        _var("d", "input", {"disturbance": {"bound": 1.0}}),
    ])
    s = spec.from_model(m)
    assert [(b.name, b.lo, b.hi) for b in s.initial] == [("x", F(-1, 2), F(3, 2))]
    # spelled `initial` where a parser allows it
    m.variables[0].annotations = {"__Dynacert": {"initial": {"min": 0, "max": 1}}}
    assert spec.from_model(m).initial[0].hi == 1
    m.variables[0].annotations = {"__Dynacert": {"initialSet": {"min": 0}}}
    with pytest.raises(ValueError):
        spec.from_model(m)
    m.variables[0] = _var("d2", "input", {"initialSet": {"min": 0, "max": 1}})
    with pytest.raises(ValueError):
        spec.from_model(m)


def test_box_bound_covers_vertices_and_is_exact_for_two_states():
    P = [[F(3), F(-1, 2)], [F(-1, 2), F(1)]]
    c, G, rho = [F(0), F(0)], [[F(1), F(0)], [F(0), F(1)]], [F(1), F(2)]
    b = lti.box_bound_value(P, c, G, rho)
    verts = [exact.quad(P, [s0 * rho[0], s1 * rho[1]])
             for s0, s1 in itertools.product((-1, 1), repeat=2)]
    assert b == max(verts)
    # off-centre, sheared box: still an upper bound
    c, G, rho = [F(1, 3), F(-2)], [[F(1), F(2)], [F(-1), F(1)]], [F(1, 2), F(1, 4)]
    b = lti.box_bound_value(P, c, G, rho)
    for s in itertools.product((-1, 1), repeat=2):
        z = [c[i] + sum(G[i][j] * s[j] * rho[j] for j in range(2)) for i in range(2)]
        assert exact.quad(P, z) <= b


def test_emit_spec_accepts_namespace_without_initial_set():
    """The Lie and layered generators call `emit_spec` with a bare namespace."""
    pb = SimpleNamespace(module="Certs.X", model_name="X", ns="X", dists=["d 0"],
                         dist_bounds=[F(1)], refs=[], params_ok=None,
                         outputs=[SimpleNamespace(name="e", lean_term="(x t).e", kind="state")])
    out = emit_lti.emit_spec(pb)
    assert "Initial p (x 0)" in out and "InitialSet" not in out


@pytest.mark.skipif(shutil.which("rumoca") is None
                    and not any(Path(p).exists() for p in pipeline.DEFAULT_RUMOCAS),
                    reason="rumoca not available")
@pytest.mark.parametrize("name", ["ClosedLoop", "ClosedLoopUncertain", "ClosedLoopComposed"])
def test_default_emission_is_byte_identical(name):
    with tempfile.TemporaryDirectory() as tmp:
        lean, py = pipeline.export(ROOT / "examples" / f"{name}.mo", name, Path(tmp), root=ROOT)
        m = model_mod.load(py)
        sp_ = spec.from_model(m)
        assert not sp_.initial
        pb = pipeline.linear_problem(m, sp_, lean.read_text())
        assert pb.init_box is None
        cert = pipeline.lti_search(pb)
    d = ROOT / "certs" / "Certs" / name
    assert emit_lti.emit_spec(pb) == (d / "Spec.lean").read_text()
    assert emit_lti.emit_cert(pb, cert) == (d / "Cert.lean").read_text()


def test_funnel_sidecar_and_theorem():
    cert = dynacert.load("ClosedLoopInitial", root=ROOT)
    side = cert.sidecar
    f = {k: F(v) for k, v in side["funnel"].items() if k not in ("theorem", "axioms")}
    assert f["level"] == F(side["level"]) == max(f["V0"], f["rate"])
    assert f["rate"] == f["budget"] / f["alpha"] and f["alpha"] == F(side["alpha"])
    assert f["V0"] > f["rate"]                       # the funnel shrinks
    assert set(side["funnel"]["axioms"]) <= pipeline.ALLOWED_AXIOMS
    assert side["funnel"]["theorem"] == "ClosedLoopInitial.Cert.funnel"
    assert [b["name"] for b in side["initial"]] == ["x", "v"]
    src = (ROOT / "certs" / "Certs" / "ClosedLoopInitial" / "Cert.lean").read_text()
    assert "theorem funnel" in src and "Real.exp" in src and "Spec.InitialSet p (x 0)" in src
    spec_src = (ROOT / "certs" / "Certs" / "ClosedLoopInitial" / "Spec.lean").read_text()
    assert "def InitialSet" in spec_src and "InitialSet p (x 0)" in spec_src
    # V0 = boxBound at the certified P (the Lean `init_box` fact, recomputed)
    P = [[F(v) for v in r] for r in side["P"]]
    x0 = [F(v) for v in side["x0"]]
    G = [[F(1), F(0)], [F(0), F(1)]]
    assert lti.box_bound_value(P, x0, G, [F(1), F(1)]) <= f["V0"]
    assert "funnel" not in dynacert.load("ClosedLoop", root=ROOT).sidecar


def _funnel_tube(T=6.0, n=301):
    cert = dynacert.load("ClosedLoopInitial", root=ROOT)
    fr = tube.LinearFrame.from_certificate(cert)
    t = np.linspace(0, T, n)
    ref = {"x_ref": 0.2 * t, "v_ref": np.full_like(t, 0.2)}
    return tube.Tube(fr, t, ref)


def test_funnel_level_and_corner_runs():
    tb = _funnel_tube()
    fun = tb.funnel
    assert fun is not None and abs(fun.rho(0.0) - fun.V0) < 1e-12
    lv = tb.level_at()
    assert np.all(np.diff(lv) <= 1e-12) and lv[-1] < lv[0]        # shrinking
    assert np.all(fun.scale(tb.t) <= 1 + 1e-12)
    runs = tb.funnel_runs()
    assert len(runs) == 4
    for r in runs:                                   # admissible runs stay in the proved funnel
        assert tb.funnel_margin(r).max() <= 1 + 1e-6
        assert tb.margin(r).max() <= 1 + 1e-6
    hw = tb.funnel_halfwidths()
    assert hw["x"][0] >= hw["x"][-1]


def test_funnel_figures_render_headless():
    tb = _funnel_tube()
    figs = {"tube": figures.tube(tb, [], model="ClosedLoopInitial"),
            "phase": figures.tube_phase(tb, [], model="ClosedLoopInitial"),
            "margin": figures.tube_margin(tb, [], model="ClosedLoopInitial")}
    for f in figs.values():
        assert f.axes
    with tempfile.TemporaryDirectory() as tmp:
        assert len(figures.save(figs, tmp)) == 3
    figures.close(figs)
