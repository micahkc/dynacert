"""Approach registry and CLI. Problems are built from committed certificates (no rumoca export)
unless the rumoca export toolchain is available."""

import argparse
from fractions import Fraction as F
from pathlib import Path

import pytest

from dynacert import approaches, cli, model as model_mod, pipeline, problem, spec as spec_mod

ROOT = Path(__file__).resolve().parents[2]
have_export = pipeline.DEFAULT_TARGETS.exists()


def committed(name: str) -> problem.Problem:
    d = ROOT / "certs" / "Certs" / name
    m = model_mod.load(d / "model_sympy.py")
    return problem.Problem(d / "source.mo", name, m, spec_mod.from_model(m),
                           (d / "Model.lean").read_text(), d / "model_sympy.py", ROOT)


def test_registry_has_the_builtin_approaches():
    assert list(approaches.REGISTRY)[:3] == ["lmi", "montecarlo", "falsify"]
    assert approaches.get("lmi").kind == approaches.CERTIFICATE
    with pytest.raises(KeyError):
        approaches.get("nope")


def test_lmi_assessment_predicts_the_certified_bounds():
    prob = committed("ClosedLoopUncertain")
    a = approaches.assess("lmi", prob)
    assert a.feasible and "polytopic" in a.notes[0]
    cert = prob.certificate()
    assert cert is not None
    assert {k: F(v) for k, v in a.details["predicted"].items()} == cert.bounds


def test_simulation_approaches_find_the_certificate():
    prob = committed("ClosedLoop")
    for name in ("montecarlo", "falsify"):
        a = approaches.assess(name, prob)
        if a.feasible:
            assert any("ClosedLoop.Cert.certified" in n for n in a.notes)
        else:
            assert "binding" in a.notes[0]
    assert approaches.assess("falsify", prob).details.get("adjoint") in (True, None)


def test_montecarlo_approach_runs_on_sympy_backend():
    prob = committed("ClosedLoop")
    a = approaches.get("montecarlo")
    p = argparse.ArgumentParser()
    a.add_arguments(p)
    opts = p.parse_args(["--n", "5", "--T", "3", "--backend", "sympy"])
    out = a.run(prob, opts, verbose=lambda *_: None)
    assert out.ok and out.status == "validated" and out.data["n"] == 5


def test_infer_model_takes_the_last_model():
    assert problem.infer_model(ROOT / "examples" / "ClosedLoopComposed.mo") == "ClosedLoopComposed"


def test_cli_usage_errors(capsys):
    assert cli.main(["--list"]) == cli.EXIT_OK
    assert "montecarlo" in capsys.readouterr().out
    assert cli.main(["examples/ClosedLoop.mo", "nope"]) == cli.EXIT_USAGE
    assert cli.main([]) == cli.EXIT_USAGE


@pytest.mark.skipif(not have_export, reason="rumoca dynacert-lean export targets not available")
def test_cli_assess_and_infeasible(capsys):
    mo = str(ROOT / "examples" / "PendulumPD.mo")
    assert cli.main([mo, "-q"]) == cli.EXIT_OK
    out = capsys.readouterr().out
    assert "der(omega) is nonlinear in theta" in out
    assert cli.main([mo, "lmi", "-q"]) == cli.EXIT_INFEASIBLE
