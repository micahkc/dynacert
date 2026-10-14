"""Error-frame tubes: the frame from the sidecar, the physical map, and containment of runs."""

import argparse
from pathlib import Path

import numpy as np

import dynacert
from dynacert import approaches, montecarlo as M, tube

ROOT = Path(__file__).resolve().parents[2]


def test_cert_exports_tube_theorem():
    for name in ("ClosedLoop", "ClosedLoopComposed", "ClosedLoopUncertain"):
        src = (ROOT / "certs" / "Certs" / name / "Cert.lean").read_text()
        assert "theorem tube" in src and "have hV := tube" in src
        assert dynacert.load(name, root=ROOT).sidecar["frame"]["theorem"] == f"{name}.Cert.tube"


def test_linear_frame_roundtrip():
    cert = dynacert.load("ClosedLoop", root=ROOT)
    fr = tube.LinearFrame.from_certificate(cert)
    assert fr.names == ["e", "ev"] and fr.reconstructs
    assert fr.inputs == ["x_ref", "v_ref"]
    rng = np.random.default_rng(0)
    X = rng.standard_normal((5, 2))
    ref = {"x_ref": 0.3, "v_ref": -0.2}
    Z = fr.error({"x": X[:, 0], "v": X[:, 1]}, {k: np.full(5, v) for k, v in ref.items()})
    back = fr.to_physical(ref, Z)
    assert np.allclose(back["x"], X[:, 0]) and np.allclose(back["v"], X[:, 1])
    b = fr.bounds()
    assert abs(b["|e|"] - float(cert.bounds["e"])) < 1e-3       # box from the same ellipsoid


def test_runs_stay_in_tube_and_sections_are_on_the_boundary():
    cert = dynacert.load("ClosedLoopUncertain", root=ROOT)
    fr = tube.LinearFrame.from_certificate(cert)
    space = M.ScenarioSpace(cert.spec, 4.0)
    be = M.SympyBackend(cert.model, cert.spec, space, dt=0.005)
    rng = np.random.default_rng(2)
    runs = [be.run(space.sample(rng)) for _ in range(4)]
    tb = tube.Tube(fr, runs[0].t, {n: runs[0].inputs[n] for n in fr.inputs})
    assert all(tb.margin(r).max() <= 1.0 for r in runs)
    xa, xb = tb.section(len(tb.t) // 2, "x", "v")
    # the projected section's extreme x matches the proved half-width
    c = tb.center()
    i = len(tb.t) // 2
    assert abs((xa.max() - c["x"][i]) - tb.halfwidths()["x"]) < 1e-3


def test_tube_approach_runs():
    from test_approaches import committed

    prob = committed("ClosedLoop")
    a = approaches.get("tube")
    assert a.assess(prob).feasible
    p = argparse.ArgumentParser()
    a.add_arguments(p)
    out = a.run(prob, p.parse_args(["--n", "3", "--T", "3", "--backend", "sympy", "--no-worst"]),
                verbose=lambda *_: None)
    assert out.ok and out.data["max_margin"] <= 1.0
    assert {"tube", "tube-margin", "tube-phase"} <= set(a.figures(prob, out, None))
