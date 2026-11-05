"""Layered CLI (docs/architecture.md §7) and certificate bookkeeping (§8 A1, A2). Problems come
from committed certificates (no rumoca export, no Lean build)."""

import argparse
import json
import shutil
from pathlib import Path

import pytest

from dynacert import approaches, certindex, cli, model as model_mod, problem, spec as spec_mod

ROOT = Path(__file__).resolve().parents[2]


def committed(name: str, root: Path = ROOT) -> problem.Problem:
    d = root / "certs" / "Certs" / name
    m = model_mod.load(d / "model_sympy.py")
    return problem.Problem(d / "source.mo", name, m, spec_mod.from_model(m),
                           (d / "Model.lean").read_text(), d / "model_sympy.py", root)


def copied(tmp_path: Path, name: str = "ClosedLoop") -> problem.Problem:
    """A committed certificate copied under a temporary project root."""
    dst = tmp_path / "certs" / "Certs" / name
    # only the lmi certificate: other methods' files (PolyCert, layered, the index) would make
    # these tests depend on what else has been certified in the working tree
    shutil.copytree(ROOT / "certs" / "Certs" / name, dst,
                    ignore=shutil.ignore_patterns("__pycache__", "plots", "PolyCert.lean",
                                                  "polyhedral.json", "LayeredCert.lean",
                                                  "layered.json", "certificates.json",
                                                  "montecarlo.json"))
    return committed(name, tmp_path)


# --- discovery and layers ------------------------------------------------------------------------

def test_discovery_order():
    assert approaches.module_order(["zeta", "tube", "base", "falsify", "alpha", "lmi",
                                    "monte_carlo", "_private"]) == \
        ["lmi", "monte_carlo", "falsify", "tube", "alpha", "zeta"]
    assert list(approaches.REGISTRY)[:4] == ["lmi", "montecarlo", "falsify", "tube"]


def test_layers_and_defaults():
    R = approaches.REGISTRY
    assert R["lmi"].layer == "certify" and R["lmi"].cost < 100 and "lti" in R["lmi"].classes
    assert R["montecarlo"].layer == R["falsify"].layer == "validate"
    assert R["tube"].layer == "view"
    # declared only `kind` (approaches/structure.py): the layer follows it
    assert R["structure"].layer == "analyze" and R["layered"].layer == "certify"

    class Dummy(approaches.Approach):
        name = "dummy-test-certify"
        kind = approaches.CERTIFICATE

    try:
        approaches.register(Dummy)
        assert R["dummy-test-certify"].layer == "certify"
        assert R["dummy-test-certify"].cost == 100
    finally:
        R.pop("dummy-test-certify", None)


def test_list_is_grouped(capsys):
    assert cli.main(["--list"]) == cli.EXIT_OK
    out = capsys.readouterr().out
    assert out.index("L3 certify") < out.index("\n  lmi ") < out.index("L4 validate") \
        < out.index("\n  montecarlo ") < out.index("L5 view") < out.index("\n  tube ")


# --- the CLI on a committed problem --------------------------------------------------------------

@pytest.fixture
def closed_loop(monkeypatch):
    prob = committed("ClosedLoop")
    monkeypatch.setattr(problem, "load", lambda *a, **k: prob)
    return prob


def test_grouped_assessment(closed_loop, capsys):
    assert cli.main(["examples/ClosedLoop.mo", "-q"]) == cli.EXIT_OK
    out = capsys.readouterr().out
    for title in ("L2 analyze", "L3 certify", "L4 validate", "L5 view"):
        assert title in out
    assert out.index("L3 certify") < out.index("  lmi ") < out.index("L4 validate")
    assert "layered     no" in out                  # with its reason
    assert "certify     portfolio: lmi" in out


def test_legacy_form_still_runs(closed_loop, capsys):
    rc = cli.main(["examples/ClosedLoop.mo", "montecarlo", "--n", "3", "--T", "2",
                   "--backend", "sympy", "-q"])
    assert rc == cli.EXIT_OK
    assert "Monte Carlo" in capsys.readouterr().out
    assert cli.main(["examples/ClosedLoop.mo", "nope"]) == cli.EXIT_USAGE


def test_validate_verb(closed_loop, capsys):
    rc = cli.main(["examples/ClosedLoop.mo", "validate", "--sample", "--n", "3", "--T", "2",
                   "--backend", "sympy", "-q"])
    assert rc == cli.EXIT_OK
    assert "Monte Carlo" in capsys.readouterr().out
    assert cli.main(["examples/ClosedLoop.mo", "validate", "--bogus"]) == cli.EXIT_USAGE


def test_verb_selection():
    sel = lambda verb, names, toks=(): [a.name for a in cli._select(verb, names, list(toks))]
    assert sel("validate", []) == ["montecarlo", "falsify"]
    assert sel("validate", [], ["--search"]) == ["falsify"]
    assert sel("validate", [], ["--search", "--sample"]) == ["montecarlo", "falsify"]
    assert sel("certify", [])[0] == "lmi"            # cheapest first
    assert sel("view", ["tube"]) == ["tube"] and sel("view", ["plots"]) == ["tube"]
    for bad in (("view", []), ("certify", ["montecarlo"]), ("view", ["tube", "plots"])):
        with pytest.raises(ValueError):
            cli._select(*bad, [])


# --- staleness (A1) ------------------------------------------------------------------------------

def test_source_hash_staleness(tmp_path):
    prob = copied(tmp_path)
    side = prob.cert_dir / "certified.json"
    assert prob.source_hash == certindex.source_hash(prob.mo.read_text(), "ClosedLoop")
    s = json.loads(side.read_text())
    s["source_hash"] = prob.source_hash
    side.write_text(json.dumps(s))
    assert prob.is_current(side) and prob.certificate() is not None
    s["source_hash"] = "0" * 64                     # recorded hash differs: stale
    side.write_text(json.dumps(s))
    assert not prob.is_current(side)
    del s["source_hash"]                            # old sidecar: compare source.mo text
    side.write_text(json.dumps(s))
    assert prob.is_current(side)
    prob.mo = tmp_path / "edited.mo"
    prob.mo.write_text((prob.cert_dir / "source.mo").read_text() + "\n// edited\n")
    assert not prob.is_current(side)


def test_invalidate_removes_only_certificates_of_the_old_spec(tmp_path):
    d = tmp_path / "M"
    d.mkdir()
    for f, text in {"Model.lean": "", "Spec.lean": "import Certs.M.Model\n",
                    "Cert.lean": "import Certs.M.Spec\n", "certified.json": "{}",
                    "certificate.png": "", "LayeredCert.lean": "import Certs.M.Spec\n",
                    "layered.json": "{}", "PolyCert.lean": "import Certs.M.Spec\nimport X\n",
                    "LieLink.lean": "import Certs.M.Model\n", "source.mo": "model M end M;"
                    }.items():
        (d / f).write_text(text)
    idx = {"model": "M", "certificates": [
        {"method": "lmi", "file": "Cert.lean", "bounds": {"y": "1"}, "source_hash": "h"},
        {"method": "poly", "file": "PolyCert.lean", "sidecar": "poly.json",
         "bounds": {"y": "1/2"}, "source_hash": "h"},
        {"method": "layered", "file": "LayeredCert.lean", "bounds": {"y": "2"},
         "source_hash": "h"}]}
    (d / "poly.json").write_text("{}")
    certindex.save(d, idx, "h")
    said = []
    gone = certindex.invalidate(d, "M", {"LayeredCert.lean"}, say=said.append)
    assert {p.name for p in gone} == {"Cert.lean", "certified.json", "certificate.png",
                                      "PolyCert.lean", "poly.json"}
    left = {p.name for p in d.iterdir()}
    assert {"Model.lean", "Spec.lean", "source.mo", "LieLink.lean", "LayeredCert.lean",
            "layered.json"} <= left
    idx = json.loads((d / certindex.INDEX).read_text())
    assert [e["method"] for e in idx["certificates"]] == ["layered"]
    assert idx["kept"] == {"y": {"bound": "2", "method": "layered"}}
    assert len(said) == 5 and all(s.startswith("!!") for s in said)


# --- the index (A2) ------------------------------------------------------------------------------

class FakeMethod(approaches.Approach):
    """A certify method that writes `FakeCert.lean` against a new Spec."""
    name = "fake"
    kind = approaches.CERTIFICATE
    layer = "certify"
    sidecar = "fake.json"

    def __init__(self, bounds, spec_text):
        self.bounds, self.spec_text = bounds, spec_text

    def assess(self, prob):
        return approaches.Assessment.yes("always")

    def run(self, prob, opts, verbose=print):
        d = prob.cert_dir
        (d / "Spec.lean").write_text(self.spec_text)
        (d / "FakeCert.lean").write_text(f"import Certs.{prob.model.ns}.Spec\n")
        (d / "fake.json").write_text(json.dumps({"axioms": ["propext"]}))
        return self.outcome(True, "certified", "CERTIFIED fake",
                            {"theorem": f"{prob.model.ns}.FakeCert.certified",
                             "bounds": self.bounds})


def _run_certify(prob, methods, capsys):
    per, common, unknown = cli._parse("M.mo", "certify", methods, ["-q"])
    assert not unknown
    rc = cli._certify(prob, methods, per, common, named=True, say=lambda *a: None)
    return rc, capsys.readouterr()


def test_index_keeps_the_tightest_bound(tmp_path, capsys):
    prob = copied(tmp_path)
    d = prob.cert_dir
    spec = (d / "Spec.lean").read_text()
    rc, out = _run_certify(prob, [FakeMethod({"e": "1/2", "ev": "100"}, spec)], capsys)
    assert rc == cli.EXIT_OK
    idx = json.loads((d / certindex.INDEX).read_text())
    by = {e["method"]: e for e in idx["certificates"]}
    assert set(by) == {"lmi", "fake"}                 # lmi bootstrapped from certified.json
    fake = by["fake"]
    assert fake["file"] == "FakeCert.lean" and fake["axioms"] == ["propext"]
    assert fake["source_hash"] == prob.source_hash
    assert json.loads((d / "fake.json").read_text())["source_hash"] == prob.source_hash
    assert idx["kept"]["e"] == {"bound": "1/2", "method": "fake"}
    assert idx["kept"]["ev"]["method"] == "lmi"
    assert "fake" in out.out and "kept:" in out.out
    assert (d / "Cert.lean").exists()                 # Spec unchanged: nothing removed


def test_changed_spec_removes_the_other_certificates(tmp_path, capsys):
    prob = copied(tmp_path)
    d = prob.cert_dir
    rc, out = _run_certify(prob, [FakeMethod({"e": "1"}, "-- a new claim\n")], capsys)
    assert rc == cli.EXIT_OK
    assert not (d / "Cert.lean").exists() and not (d / "certified.json").exists()
    assert (d / "FakeCert.lean").exists() and (d / "Model.lean").exists()
    assert (d / "source.mo").exists() and (d / "Spec.lean").exists()
    assert "Spec.lean of ClosedLoop changed" in out.err and "removed stale" in out.err
    idx = json.loads((d / certindex.INDEX).read_text())
    assert [e["method"] for e in idx["certificates"]] == ["fake"]


def test_portfolio_continues_after_a_failure(tmp_path, capsys):
    prob = copied(tmp_path)
    spec = (prob.cert_dir / "Spec.lean").read_text()

    class Broken(FakeMethod):
        name = "broken"

        def run(self, prob, opts, verbose=print):
            raise ValueError("no luck")

    rc, out = _run_certify(prob, [Broken({}, spec), FakeMethod({"e": "1"}, spec)], capsys)
    assert rc == cli.EXIT_OK
    assert "broken failed: no luck" in out.err and "failed: no luck" in out.out
