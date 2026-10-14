"""Structure discovery, the SE₂(3) link parser, and the layered search (no rumoca or Lean)."""

from fractions import Fraction as F

import sympy as sp

from dynacert import emit_layered, lie_link, structure
from dynacert.model import Model, Var


def _sym(name, shape):
    if shape == ():
        return sp.Symbol(name, real=True)
    if len(shape) == 1:
        return sp.Matrix([sp.Symbol(f"{name}[{i + 1}]", real=True) for i in range(shape[0])])
    return sp.Matrix(shape[0], shape[1],
                     lambda i, j: sp.Symbol(f"{name}[{i + 1},{j + 1}]", real=True))


class Builder:
    """A model in the shape `model.load` returns, written directly in sympy."""

    def __init__(self, name="M"):
        self.name, self.vars, self.eqs, self.der = name, [], [], {}

    def add(self, name, role, shape=(), binding=None):
        s = _sym(name, shape)
        self.vars.append(Var(name, role, shape, s, binding, None, None, None, None, None))
        if role == "state":
            self.der[name] = _sym(f"der_{name}", shape)
        return s

    def eq(self, lhs, rhs):
        self.eqs.append([sp.Eq(lhs, rhs, evaluate=False)])

    def model(self):
        return Model(self.name, self.vars, self.eqs, self.der, None)


def skew(w):
    return sp.Matrix([[0, -w[2], w[1]], [w[2], 0, -w[0]], [-w[1], w[0], 0]])


def rigid_body(b, prefix, gravity):
    p = b.add(f"{prefix}.p", "state", (3,))
    v = b.add(f"{prefix}.v", "state", (3,))
    R = b.add(f"{prefix}.R", "state", (3, 3))
    a = b.add(f"{prefix}.a", "algebraic", (3,))
    w = b.add(f"{prefix}.w", "algebraic", (3,))
    b.eq(b.der[f"{prefix}.p"], v)
    b.eq(b.der[f"{prefix}.v"], R * a + gravity(p))
    b.eq(b.der[f"{prefix}.R"], R * skew(w))
    return p, v, R, a, w


def tracking(gravity):
    """Vehicle + reference rigid bodies, body-frame attitude feedback (ω depends on R)."""
    b = Builder("Tracking")
    w_ref = b.add("w_ref", "input", (3,))
    a_ref = b.add("a_ref", "input", (3,))
    p, v, R, a, w = rigid_body(b, "veh", gravity)
    pr, vr, Rr, ar, wr = rigid_body(b, "ref", gravity)
    Rt = Rr.T * R
    eR = sp.Rational(1, 2) * sp.Matrix([Rt[2, 1] - Rt[1, 2], Rt[0, 2] - Rt[2, 0],
                                        Rt[1, 0] - Rt[0, 1]])
    b.eq(ar, a_ref)
    b.eq(wr, w_ref)
    b.eq(a, a_ref - sp.Rational(1, 10) * Rr.T * (p - pr))
    b.eq(w, w_ref - 3 * eR)
    return b.model()


def const_g(p):
    return sp.Matrix([0, 0, -sp.Rational(981, 100)])


def central_g(p):
    return -p / (p.dot(p)) ** sp.Rational(3, 2)


def test_so3_rates_right_and_left():
    R = _sym("R", (3, 3))
    w = sp.Matrix(sp.symbols("w1:4"))
    assert structure.so3_rates(R, R * skew(w), "right") == w
    assert structure.so3_rates(R, skew(w) * R, "right") is None
    assert structure.so3_rates(R, skew(w) * R, "left") == w
    assert structure.so3_rates(R, R * sp.diag(*w), "right") is None   # not skew


def test_quaternion_rates():
    q = sp.Matrix(sp.symbols("q0:4"))
    w = sp.Matrix(sp.symbols("w1:4"))
    Om = sp.Rational(1, 2) * sp.Matrix([[0, -w[0], -w[1], -w[2]], [w[0], 0, w[2], -w[1]],
                                        [w[1], -w[2], 0, w[0]], [w[2], w[1], -w[0], 0]])
    got, side = structure.quaternion_rates(q, Om * q)
    assert list(got) == list(w) and side == "body"


def test_quadrotor_constant_gravity_is_group_affine():
    s = structure.discover(tracking(const_g))
    blocks = {f.data["R"]: f.data for f in s.of("se23")}
    assert set(blocks) == {"veh.R", "ref.R"}
    assert all(b["gravity"] == "constant" and b["group_affine"] for b in blocks.values())
    (le,) = s.of("log-error")
    assert le.data["vehicle"]["R"] == "veh.R" and le.data["reference"]["R"] == "ref.R"
    assert "Lie.gravity_residual_const" in le.lean
    # closed-loop rates read R, but the kinematics as written are still R·skew(ω)
    assert {f.data["R"] for f in s.of("so3")} == {"veh.R", "ref.R"}


def test_spacecraft_inverse_square_gravity():
    s = structure.discover(tracking(central_g))
    kinds = {f.data["R"]: f.data["gravity"] for f in s.of("se23")}
    assert kinds == {"veh.R": "inverse-square", "ref.R": "inverse-square"}
    assert not any(f.data["group_affine"] for f in s.of("se23"))
    (le,) = s.of("log-error")
    assert "Lie.gravity_residual_inverse_square" in le.lean


def test_isotropic_linear_gravity_is_group_affine():
    s = structure.discover(tracking(lambda p: -2 * p))
    assert {f.data["gravity"] for f in s.of("se23")} == {"isotropic-linear"}
    assert all(f.data["group_affine"] for f in s.of("se23"))


def test_layers_and_coupled_components():
    b = Builder("TwoMass")
    d = b.add("d", "input")
    ax, av, bx, bv = (b.add(n, "state") for n in ("a.x", "a.v", "b.x", "b.v"))
    b.eq(b.der["a.x"], av)
    b.eq(b.der["a.v"], -ax - av + sp.Rational(1, 5) * (bx - ax) + d)
    b.eq(b.der["b.x"], bv)
    b.eq(b.der["b.v"], -2 * bx - bv + sp.Rational(1, 5) * (ax - bx))
    s = structure.discover(b.model())
    assert s.of("linear")
    (coupled,) = [f for f in s.of("layers") if "components" in f.data]
    assert coupled.data["coupling"] == {"a": ["b.x"], "b": ["a.x"]}


def test_cascade_and_integrator():
    b = Builder("Cascade")
    u = b.add("u", "input")
    x1, x2, x3 = (b.add(n, "state") for n in ("x1", "x2", "x3"))
    b.eq(b.der["x1"], -x1 + u)
    b.eq(b.der["x2"], -x2 + x1)
    b.eq(b.der["x3"], x2)
    s = structure.discover(b.model())
    (casc,) = [f for f in s.of("layers") if "order" in f.data]
    assert casc.data["order"] == [["x1"], ["x2"], ["x3"]]
    assert [f.data["state"] for f in s.of("integrator")] == ["x3"]


QUAD_EQS = """def Equations (t : ℝ) (p : Params) (u : Inputs) (x dx : States) (y : Algebraics) : Prop :=
  dx.«quad.p» = x.«quad.v»
  ∧ dx.«quad.v» = x.«quad.R» *ᵥ y.«quad.a» + ![0, 0, -p.«quad.g»]
  ∧ dx.«quad.R» = x.«quad.R» * Rumoca.skew y.«quad.w»
  ∧ dx.«sc.v» = x.«sc.R» *ᵥ y.«sc.a» - ((x.«sc.p» ⬝ᵥ x.«sc.p») ^ (1.5 : ℝ))⁻¹ • p.mu • x.«sc.p»

"""


def test_lie_link_reads_rumoca_equations():
    eqs = lie_link.equations_text(QUAD_EQS)
    assert len(eqs) == 4
    L = lie_link.block_link(eqs[:3], [], {"p": "quad.p", "v": "quad.v", "R": "quad.R"})
    assert (L.a, L.w, L.g) == ("(y t).«quad.a»", "(y t).«quad.w»", "![0, 0, -p.«quad.g»]")
    a, sign, g = lie_link._top_split(eqs[3].split(" = ", 1)[1][len("x.«sc.R» *ᵥ "):])
    assert a == "y.«sc.a»" and sign == "-" and g.endswith("• p.mu • x.«sc.p»")


class _PB:
    dist_bounds = [F(1), F(1, 2)]
    x0 = [F(0)] * 4


def test_layered_search_finds_strict_coupling_bounds():
    kc = F(1, 5)
    A = [[0, 1, 0, 0], [-1 - kc, F(-6, 5), kc, 0], [0, 0, 0, 1], [0, 0, -2 - kc, F(-3, 2)]]
    la = emit_layered.Layer("a", [0, 1], [2], [0], [[A[0][0], A[0][1]], [A[1][0], A[1][1]]],
                            [[F(0), F(0)], [F(1), kc]], [0])
    lb = emit_layered.Layer("b", [2, 3], [0], [1], [[A[2][2], A[2][3]], [A[3][2], A[3][3]]],
                            [[F(0), F(0)], [F(1), kc]], [2])
    b, c = emit_layered.search(_PB, [la, lb], [0, 2])
    assert all(c[j] < b[j] for j in (0, 2))
