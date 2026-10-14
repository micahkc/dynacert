"""The SE₂(3) PD-tube generator: pattern recognition and the certificate search (no rumoca
or Lean; the kernel re-checks everything in `LieCert.lean`)."""

from fractions import Fraction as F
from types import SimpleNamespace

from dynacert import emit_lie, exact, structure
from dynacert.methods import lti

from test_structure import central_g, tracking

LEAN = """def Initial (p : Params) (x : States) : Prop :=
  x.«veh.p» = p.«veh.p0»
  ∧ x.«veh.v» = p.«veh.v0»
  ∧ x.«veh.R» = Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
  ∧ x.«ref.p» = p.«ref.p0»
  ∧ x.«ref.v» = p.«ref.v0»
  ∧ x.«ref.R» = Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

def Equations (t : ℝ) (p : Params) (u : Inputs) (x dx : States) (y : Algebraics) : Prop :=
  y.pos_err = Real.sqrt ((x.«veh.p» - x.«ref.p») ⬝ᵥ (x.«veh.p» - x.«ref.p»))
  ∧ dx.«veh.p» = x.«veh.v»
  ∧ dx.«veh.v» = x.«veh.R» *ᵥ y.«veh.a» - ((x.«veh.p» ⬝ᵥ x.«veh.p») ^ (1.5 : ℝ) : ℝ)⁻¹ • (p.«veh.mu» : ℝ) • x.«veh.p»
  ∧ dx.«veh.R» = x.«veh.R» * Rumoca.skew y.«veh.w»
  ∧ dx.«ref.p» = x.«ref.v»
  ∧ dx.«ref.v» = x.«ref.R» *ᵥ y.«ref.a» - ((x.«ref.p» ⬝ᵥ x.«ref.p») ^ (1.5 : ℝ) : ℝ)⁻¹ • (p.«ref.mu» : ℝ) • x.«ref.p»
  ∧ dx.«ref.R» = x.«ref.R» * Rumoca.skew y.«ref.w»
  ∧ y.Rt = (x.«ref.R»)ᵀ * x.«veh.R»
  ∧ y.ep = (x.«ref.R»)ᵀ *ᵥ (x.«veh.p» - x.«ref.p»)
  ∧ y.ev = (x.«ref.R»)ᵀ *ᵥ (x.«veh.v» - x.«ref.v»)
  ∧ y.eR = ![0.5 * (y.Rt 2 1 - y.Rt 1 2), 0.5 * (y.Rt 0 2 - y.Rt 2 0), 0.5 * (y.Rt 1 0 - y.Rt 0 1)]
  ∧ y.«ref.a» = ![0, 0, 0]
  ∧ y.«ref.w» = ![0, 0, 0]
  ∧ y.«veh.a» = -((p.kp : ℝ) • y.ep) - (p.kd : ℝ) • y.ev + u.d
  ∧ y.«veh.w» = -((p.kR : ℝ) • y.eR)

"""


def test_recognize_pd_pattern():
    s = structure.discover(tracking(central_g))
    prob = SimpleNamespace(lean_src=LEAN, spec=SimpleNamespace(certify=["pos_err"]))
    pat = emit_lie.recognize(prob, s)
    assert pat.gains == {"kp": "kp", "kd": "kd", "kR": "kR"}
    assert pat.dist == "d" and pat.outputs == [("pos_err", "pos")]
    assert pat.eq["a"] == 13 and pat.eq["eR"] == 10 and pat.eq["ab"] == 11
    assert (pat.mu, pat.mub) == ("«veh.mu»", "«ref.mu»")


def test_recognize_rejects_other_laws():
    s = structure.discover(tracking(central_g))
    bad = LEAN.replace("-((p.kR : ℝ) • y.eR)", "-((p.kR : ℝ) • y.eR) + y.ep")
    prob = SimpleNamespace(lean_src=bad, spec=SimpleNamespace(certify=["pos_err"]))
    try:
        emit_lie.recognize(prob, s)
    except emit_lie.LieError as e:
        assert "w = -kR*eR" in str(e)
    else:
        raise AssertionError("a non-PD rate law was accepted")


def test_search_spacecraft_numbers_check_exactly():
    delta = emit_lie._sqrt_up(3 * F(1, 200) ** 2)
    cd = emit_lie.search(4, 4, 1, F(1, 100), 1, delta, alphas=[1.25])
    assert cd is not None
    A, B = emit_lie.pd_matrices(4, 4, 1)
    assert exact.check_witness(lti.lmi_matrix(A, B, cd.P, cd.alpha, cd.gamma), *cd.lmi)
    assert exact.check_witness(exact.sub(cd.P, exact.eye(9, cd.m)), *cd.Wm)
    ell = emit_lie.pd_gain(F(4), F(4), F(1), cd.D, delta) + emit_lie.grav_gain(F(1, 100), F(1), cd.D)
    kappa = cd.alpha - 2 * cd.pn * ell / cd.m
    assert cd.gamma * delta ** 2 < kappa * cd.rho and cd.gamma * delta ** 2 <= kappa * cd.c
    assert cd.m * cd.bounds[0] ** 2 >= cd.c
