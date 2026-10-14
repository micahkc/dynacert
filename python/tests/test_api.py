"""The notebook API on a committed certificate (no rumoca or Lean needed)."""

from pathlib import Path

import dynacert

ROOT = Path(__file__).resolve().parents[2]


def test_load_simulate_within_bounds():
    cert = dynacert.load("ClosedLoop", root=ROOT)
    assert cert.theorem == "ClosedLoop.Cert.certified"
    assert set(cert.axioms) <= {"propext", "Classical.choice", "Quot.sound"}
    assert "def Claim" in cert.claim
    runs = cert.simulate(4, T=4, dt=0.005)
    for name, peak in cert.peaks(runs).items():
        assert peak <= float(cert.bounds[name])
