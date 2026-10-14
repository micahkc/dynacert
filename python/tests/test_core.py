"""Tests for the untrusted Python side (the Lean kernel is the real check)."""

from fractions import Fraction as F

import sympy as sp

from dynacert import analysis as an
from dynacert import emit_lti, exact
from dynacert.lean import ident, q, sanitize, sympy_to_lean
from dynacert.methods import lti

A = [[F(0), F(1)], [F(-11), F(-11, 5)]]
B = [[F(0)], [F(1)]]


def test_ldlt_roundtrip():
    M = [[F(4), F(2)], [F(2), F(3)]]
    L, d = exact.psd_witness(M)
    assert exact.check_witness(M, L, d)


def test_ldlt_rejects_indefinite():
    assert exact.psd_witness([[F(1), F(2)], [F(2), F(1)]]) is None


def test_channel_certificate_checks_exactly():
    c = lti.certify_channels(A, B, [1])
    M = lti.channel_lmi(A, B, c.P, c.alpha, c.gammas)
    assert exact.check_witness(M, c.lmi_L, c.lmi_d)
    for b in c.boxes:
        n = len(c.P)
        v = [F(int(j == b.index)) for j in range(n)]
        Mb = [[b.bound ** 2 * c.P[r][s] - c.level * v[r] * v[s] for s in range(n)]
              for r in range(n)]
        assert exact.check_witness(Mb, b.L, b.d)


def test_polytopic_certificate_covers_vertices():
    As = [[[F(0), F(1)], [F(-11), -(F(2) + c)]] for c in (F(1, 10), F(3, 10))]
    c = lti.certify_polytopic(As, B, [1])
    for Av, (L, d) in zip(As, c.witnesses):
        assert exact.check_witness(lti.channel_lmi(Av, B, c.P, c.alpha, c.gammas), L, d)


def test_analysis_lti_and_multipliers():
    m, c, d, e, ev, de, dev = sp.symbols("m c d e ev der_e der_ev")
    eqs = [sp.Eq(de, ev), sp.Eq(dev, (d - c * ev - 11 * e - 2 * ev) / m)]
    res = an.substitute_params(eqs, {m: sp.Rational("1.0"), c: sp.Rational("0.2")})
    ex = an.eliminate(res, [de, dev], [])
    Am, Bm = an.linear_rows([ex.der[de], ex.der[dev]], [e, ev], [d])
    assert Am == A and Bm == B
    tgt = dev - (-11 * e - sp.Rational(11, 5) * ev + d)
    assert an.multipliers(res, tgt) == [(1, F(1))]


def test_decimal_literals_and_names():
    src = "namespace X\n def f := 0.2 + 10.0 * p.k + 3 + 1e-3\n"
    assert emit_lti.decimal_literals(src) == ["0.2", "10.0", "1e-3"]
    assert ident("a.b") == "«a.b»" and ident("e") == "e" and ident("end") == "«end»"
    assert sanitize("Pkg.Model[1]") == "Pkg_Model_1"
    assert q(F(-11, 5)) == "-11/5"


def test_sympy_to_lean():
    c = sp.Symbol("c")
    s = sympy_to_lean(3 - 2 * c, {c: "p.c"})
    assert "p.c" in s and "(-2 : ℝ)" in s
