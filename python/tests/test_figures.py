"""Every figure renders (headless) in every theme, and the CLI writes the files it is asked for."""

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import numpy as np  # noqa: E402
import pytest  # noqa: E402

import dynacert  # noqa: E402
from dynacert import approaches, figures, montecarlo as M, worstcase  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def mc():
    cert = dynacert.load("ClosedLoop", root=ROOT)
    return cert, cert.montecarlo(12, T=3.0, backend="sympy", seed=1)


@pytest.mark.parametrize("theme", sorted(figures.THEMES))
def test_monte_carlo_figures(mc, theme):
    cert, run = mc
    assert run.traces["e"].shape == (12, len(run.trace_t))
    with figures.theme(theme):
        figs = {k: run.plot(k) for k in ("exceedance", "histogram", "envelope", "traces")}
        figs["phase"] = figures.phase(run, cert=cert)
        figs["tightness"] = figures.tightness(
            {o: {"certified": float(b), "montecarlo": float(run.peaks[o].max()), "exact": None}
             for o, b in run.bounds.items()}, model="ClosedLoop")
    assert all(f.axes for f in figs.values())
    figures.close(figs)


def test_downsample_keeps_peaks():
    t = np.linspace(0, 1, 1001)
    y = np.sin(40 * t)
    y[537] = -3.0
    g = np.linspace(0, 1, 50)
    d = M.downsample(t, y, g)
    assert d.min() == -3.0 and len(d) == 50


def test_worstcase_figure_and_files(mc, tmp_path):
    cert, _ = mc
    space = M.ScenarioSpace(cert.spec, 3.0, M.Distribution(segments=20))
    adj = worstcase.Adjoint(cert.model, cert.spec, space, dt=0.01)
    r = adj.search("e", tstars=2)
    found = [(v, f"adjoint/{s}", scn) for s, v, scn in r.candidates]
    with figures.theme("paper"):
        fig = figures.worstcase(found, "e", adj.fwd.run, bound=float(cert.bounds["e"]),
                                space=space, adjoint=adj, model="ClosedLoop")
    paths = figures.save({"w": fig}, tmp_path, formats=("png", "svg"))
    pdf = figures.report({"w": fig}, tmp_path / "r.pdf")
    assert all(p.stat().st_size > 1000 for p in [*paths, pdf])
    figures.close({"w": fig})


def test_approach_figure_names():
    from test_approaches import committed

    prob = committed("ClosedLoop")
    a = approaches.get("montecarlo")
    p = argparse.ArgumentParser()
    a.add_arguments(p)
    out = a.run(prob, p.parse_args(["--n", "4", "--T", "2", "--backend", "sympy"]),
                verbose=lambda *_: None)
    names = set(a.figures(prob, out, None))
    assert {"exceedance", "histogram", "envelope", "traces", "phase", "tightness"} <= names
