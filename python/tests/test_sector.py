"""Sector-multiplier certificates and cut selection (paper: "Where to Tear"): channel
extraction from rumoca's equations, the rational sector/peak constants against sampling, the
dominance witness, Proposition 2 screening and the automatic cut, and the committed
PlanarQuadrotor certificate."""

import json
import math
import random
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import pytest

from dynacert import sector as S

ROOT = Path(__file__).resolve().parents[2]
MO = ROOT / "examples" / "aerospace" / "PlanarQuadrotor.mo"


def _have_export():
    try:
        from dynacert import pipeline

        pipeline.rumoca_bin()
        return pipeline.DEFAULT_TARGETS.exists()
    except Exception:  # noqa: BLE001
        return False


needs_rumoca = pytest.mark.skipif(not _have_export(), reason="needs the rumoca export toolchain")
_CACHE = {}


def _quad():
    if "quad" not in _CACHE:
        from dynacert import problem

        prob = problem.load(MO, root=ROOT)
        _CACHE["quad"] = (prob, S.extract(prob))
    return _CACHE["quad"]


@needs_rumoca
def test_channels_are_table_ii():
    _, sp_ = _quad()
    kinds = [(c.kind, c.rule[0]) for c in sp_.channels]
    assert sorted(kinds) == sorted([("sector", "sinrem"), ("sector", "prod_gain"),
                                    ("bounded", "prod"), ("bounded", "prod"),
                                    ("bounded", "prod"), ("sector", "atan2rem")])
    assert [c.name for c in sp_.coords] == ["s_x", "s_z", "theta"]
    g = F(981, 100)
    # linearization at hover: v̇_x = gθ, v̇_z = -s_z, q̇ = -kθ(θ + s_x/g) - kq q
    assert sp_.A[2][4] == g
    assert sp_.A[3] == [0, -4, 0, -4, 0, 0]
    assert sp_.A[5] == [-400 / g, 0, -400 / g, 0, -100, -20]


@needs_rumoca
def test_constants_hold_on_samples():
    """The rational sector intervals and peak bounds contain every sampled residual."""
    _, sp_ = _quad()
    R = [F(3, 2), F(3, 4), F(3, 20)]          # |s_x|, |s_z|, |θ|
    gains, betas = S.constants(sp_, R)
    g, rng = 9.81, random.Random(0)
    for _ in range(2000):
        sx = rng.uniform(-1.5, 1.5)
        sz = rng.uniform(-0.75, 0.75)
        th = rng.uniform(-0.15, 0.15)
        fn = math.hypot(sx, g - sz)
        thd = math.atan2(-sx, g - sz)
        vals = {"sin(theta) - theta": (math.sin(th) - th, th),
                "-s_z*sin(theta)": (-sz * math.sin(th), -sz),
                "100*s_x/981 + theta_d": (thd + sx / g, -sx)}
        for j, ch in enumerate(sp_.channels):
            e = str(ch.expr)
            if ch.kind == "sector":
                key = [k for k in vals if k.replace(" ", "") == e.replace(" ", "")
                       or e.replace(" ", "") == "-theta+sin(theta)" and k.startswith("sin")]
                p, q = vals[key[0]]
                lo, hi = gains[j]
                if abs(q) > 1e-9:
                    d = p / q
                    assert float(lo) - 1e-12 <= d <= float(hi) + 1e-12, (e, d, lo, hi)
            else:
                p = {"(f_norm + s_z - 981/100)*sin(theta)": (fn - (g - sz)) * math.sin(th),
                     "f_norm + s_z - 981/100": fn - (g - sz),
                     "f_norm*(cos(theta) - 1)": fn * (math.cos(th) - 1)}[e]
                assert abs(p) <= float(betas[j]) + 1e-12, (e, p, betas[j])


def test_dom_witness():
    rng = np.random.default_rng(1)
    X = rng.standard_normal((8, 8))
    M = X @ X.T + 0.3 * np.eye(8)
    Mq = S.round_mat(M, 10**4)
    W = S.dom_witness(Mq)
    assert W is not None
    L, d = W
    assert all(v >= 0 for v in d)
    R = [[Mq[i][j] - sum(L[p][i] * d[p] * L[p][j] for p in range(8)) for j in range(8)]
         for i in range(8)]
    assert S.dom_ok(R)
    bad = [[F(1), F(2)], [F(2), F(1)]]
    assert S.dom_witness(bad) is None


@needs_rumoca
def test_cut_selection_recovers_cut_b():
    from dynacert import cuts as C

    _, sp_ = _quad()
    g, cands = C.candidates(sp_)
    names = sp_.states
    chosen = C.choose(sp_, cands)
    assert chosen.source == "scc"
    assert chosen.label(names) == "e_x,v_x,theta,q | e_z,v_z"      # cut B
    assert chosen.strong_cut == 0 and chosen.feasible
    cut_a = [c for c in cands if c.label(names) == "e_x,e_z,v_x,v_z | theta,q"]
    assert cut_a and cut_a[0].feasible is False                      # Proposition 2 rejects A


@needs_rumoca
def test_build_blocks_cut_b():
    _, sp_ = _quad()
    blocks, ifaces = S.build_blocks(sp_, [[0, 2, 4, 5], [1, 3]])
    lat, ver = blocks
    # the only interface is s_z, from the vertical block into the lateral sector channel 1
    assert len(ifaces) == 1 and ifaces[0].sender == 1 and ifaces[0].receivers == [0]
    assert ("iface", 0) in lat.signals and lat.supply_in and ver.supply_out
    assert not any(k == "iface" for k, _ in ver.signals)


def test_committed_certificate_sidecar():
    d = ROOT / "certs" / "Certs" / "PlanarQuadrotor"
    for side, thm in (("sector.json", "SectorCert"), ("compose.json", "ComposeCert")):
        f = d / side
        if not f.exists():
            pytest.skip(f"{side} not generated")
        s = json.loads(f.read_text())
        assert s["theorem"] == f"PlanarQuadrotor.{thm}.certified"
        assert set(s["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
        assert (d / f"{thm}.lean").exists()
        assert F(s["bounds"]["e_x"]) < F(1, 5)       # paper: 0.178 at 25 % disturbance


MO3 = ROOT / "examples" / "aerospace" / "Quadrotor3D.mo"


def _quad3():
    if "quad3" not in _CACHE:
        from dynacert import problem

        prob = problem.load(MO3, root=ROOT)
        _CACHE["quad3"] = (prob, S.extract(prob))
    return _CACHE["quad3"]


@needs_rumoca
def test_quad3d_decomposition_is_exact_and_bounded():
    """The 3D vehicle (quaternion chart, polynomial thrust and kinematics): `ẋ = Az + Bp + Bw`
    holds exactly at sampled points, and every polynomial channel is inside its sector or peak
    bound on the region box."""
    prob, sp_ = _quad3()
    m = prob.model
    assert all(ch.rule[0] == "poly" for ch in sp_.channels)
    assert [a.kind for a in sp_.atoms] == ["unit"]
    eig = np.linalg.eigvals(np.array([[float(v) for v in r] for r in sp_.A]))
    assert max(eig.real) < 0
    vals = S._param_values(m)
    syms = sp_.syms
    algs = {v.name: S._subs(e.rhs, vals) for v in m.algebraics for e in m.equations
            if e.lhs == v.symbol}
    box = {"qx": .1, "qy": .1, "qz": .1, "s_x": 1.5, "s_y": 1.5, "s_z": .8, "p": 1., "q": 1.,
           "r": 1.}
    gains, betas = S.constants(sp_, [F(box[c.name]).limit_denominator(100) for c in sp_.coords])
    rng = random.Random(0)
    for _ in range(100):
        st = {k: rng.uniform(-box[k], box[k]) for k in ("qx", "qy", "qz", "p", "q", "r")}
        for ax in "xyz":
            e, s_ = rng.uniform(-.1, .1), rng.uniform(-box["s_" + ax], box["s_" + ax])
            st["e_" + ax], st["v_" + ax] = e, (s_ - 4 * e) / 4
        sub = {syms[k]: v for k, v in st.items()}
        sub.update({syms[w]: rng.uniform(-1, 1) for w in sp_.dists})
        a = {}
        for _ in range(len(algs)):
            for k, e in algs.items():
                try:
                    a[syms[k]] = float(e.xreplace({**sub, **a}))
                except TypeError:
                    pass
        full = {**sub, **a}
        z = [st[nm] for nm in sp_.states]
        chv = [float(ch.expr.xreplace(full)) for ch in sp_.channels]
        for i, nm in enumerate(sp_.states):
            eq = [e for e in m.equations if e.lhs == m.der[nm]][0]
            f = float(S._subs(eq.rhs, vals).xreplace(full))
            lin = sum(float(sp_.A[i][j]) * z[j] for j in range(sp_.n))
            lin += sum(float(ch.col.get(i, 0)) * v for ch, v in zip(sp_.channels, chv))
            lin += sum(float(sp_.Bw[i][d]) * float(sub[syms[w]]) for d, w in enumerate(sp_.dists))
            assert abs(f - lin) < 1e-9
        for j, ch in enumerate(sp_.channels):
            if ch.kind == "bounded":
                assert abs(chv[j]) <= float(betas[j]) + 1e-12
                continue
            qv = sum(float(c) * v for c, v in zip(sp_.qforms[ch.q], z))
            if abs(qv) > 1e-9:
                lo, hi = gains[j]
                assert float(lo) - 1e-12 <= chv[j] / qv <= float(hi) + 1e-12



@needs_rumoca
def test_quad3d_cut_is_the_papers_conjecture():
    """'Where to Tear' §VIII: on the full vehicle each tilt axis is strongly coupled to its lateral
    axis, thrust magnitude and yaw only through residuals, so the proposed blocks are two
    tilt–lateral blocks, a vertical block and a yaw block (and Proposition 2 accepts the cut)."""
    from dynacert import cuts as C

    _, sp_ = _quad3()
    g, cands = C.candidates(sp_, max_strong=0)
    chosen = C.choose(sp_, cands)
    assert chosen.source == "scc" and chosen.feasible and chosen.strong_cut == 0
    assert chosen.label(sp_.states) == "e_x,v_x,qy,q | e_y,v_y,qx,p | e_z,v_z | qz,r"
