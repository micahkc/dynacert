"""Concept diagrams (no data). Run from anywhere: python3 make_concepts.py"""

from pathlib import Path

from style import *

OUT = Path(__file__).resolve().parents[1] / "images"


def pipeline():
    fig, ax = canvas()
    box(ax, 1.5, 20, 17, 16, "Write", "Modelica equations\n+ annotations:\nwhat to certify", tsize=17, bsize=12)
    box(ax, 23, 20, 15, 16, "Compile", "rumoca: one\nmodel, two views", tsize=17, bsize=12)
    arrow(ax, (18.5, 28), (23, 28))
    box(ax, 43, 35, 21, 16, "Lean view", "the equations and the\nclaim, fixed before\nany search runs", fc=BLUE_T, ec=BLUE, tsize=17, bsize=12)
    box(ax, 43, 5, 21, 16, "Python view + search", "solvers find numbers,\nround to exact fractions", fc=ORANGE_T, ec=ORANGE, tsize=15, bsize=12)
    arrow(ax, (38, 31), (43, 41))
    arrow(ax, (38, 25), (43, 15))
    box(ax, 69, 20, 13, 16, "Check", "Lean kernel,\nexact arithmetic", fc=BLUE_T, ec=BLUE, tsize=17, bsize=11)
    arrow(ax, (64, 41), (69, 31))
    arrow(ax, (64, 15), (69, 25))
    ax.text(68.5, 40, "claim", fontsize=12.5, color=INK2, ha="left", va="center")
    ax.text(68.5, 16, "certificate data", fontsize=12.5, color=INK2, ha="left", va="center")
    box(ax, 86, 20, 12.5, 16, "Theorem", "or nothing:\nno weak result", fc=AQUA_T, ec=AQUA, tsize=16, bsize=11)
    arrow(ax, (82, 28), (86, 28))
    save(fig, OUT / "01-pipeline.png")


def trust():
    fig, ax = canvas()
    ax.add_patch(FancyBboxPatch((2, 4), 46, 49, boxstyle="round,pad=0,rounding_size=1", fc=BLUE_T, ec=BLUE, lw=1.6))
    ax.add_patch(FancyBboxPatch((52, 4), 46, 49, boxstyle="round,pad=0,rounding_size=1", fc=ORANGE_T, ec=ORANGE, lw=1.6))
    ax.text(25, 49.5, "Must be trusted", ha="center", fontsize=22, weight="bold")
    ax.text(75, 49.5, "Does not need to be trusted", ha="center", fontsize=22, weight="bold")
    ax.text(25, 46.6, "A mistake here could produce a wrong result", ha="center", fontsize=13.5, color=INK2)
    ax.text(75, 46.6, "A mistake here makes the build fail, or wastes time", ha="center", fontsize=13.5, color=INK2)
    left = ["Lean kernel", "Mathlib and gnc_lean libraries", "dynacert's Lean theorems (proved once)",
            "rumoca's Modelica-to-Lean translation", "A person reading the short Spec.lean claim"]
    right = ["Python search code", "Numerical solvers (SDP, LP, ADMM)", "Floating-point arithmetic",
             "Structure discovery and method choice", "Simulation, Monte Carlo, falsification, plots"]
    for i, t in enumerate(left):
        ax.text(6, 40.5 - i * 7.2, "•  " + t, fontsize=16.5, va="center")
    for i, t in enumerate(right):
        ax.text(56, 40.5 - i * 7.2, "•  " + t, fontsize=16.5, va="center")
    save(fig, OUT / "02-trust-boundary.png")


def annotations():
    fig, ax = canvas()
    code = [
        ("model ClosedLoop", None),
        ('  input Real x_ref annotation(__Dynacert(', None),
        ('      reference(derivative = "v_ref", start = 0)));', "ref"),
        ("  input Real d annotation(__Dynacert(", None),
        ("      disturbance(bound = 1.0)));", "dist"),
        ("  parameter Real c = 0.2 annotation(__Dynacert(", None),
        ("      uncertain(min = 0.1, max = 0.3)));", "unc"),
        ("  Real x(start = 0, fixed = true) annotation(__Dynacert(", None),
        ("      initialSet(min = -1, max = 1)));", "init"),
        ("  Real e annotation(__Dynacert(certify));", "cert"),
        ("equation  ...", None),
    ]
    ax.add_patch(FancyBboxPatch((1.5, 3), 53, 50, boxstyle="round,pad=0,rounding_size=1", fc=GRAY_T, ec=GRID, lw=1.2))
    ys = {}
    for i, (t, k) in enumerate(code):
        y = 49.5 - i * 4.25
        ax.text(3, y, t, family="DejaVu Sans Mono", fontsize=12.2, va="center", weight="bold" if k else "normal")
        if k:
            ys[k] = y
    means = {"ref": "for every path with x_ref' = v_ref, starting at 0",
             "dist": "for every disturbance with |d(t)| ≤ 1",
             "unc": "for every c between 0.1 and 0.3",
             "init": "for every start x(0) in [-1, 1]",
             "cert": "conclusion: |e(t)| ≤ b, for all time"}
    for k, m in means.items():
        arrow(ax, (55, ys[k]), (60, ys[k]))
        fc = AQUA_T if k == "cert" else BLUE_T
        ec = AQUA if k == "cert" else BLUE
        ax.add_patch(FancyBboxPatch((60, ys[k] - 1.9), 38.5, 3.8, boxstyle="round,pad=0,rounding_size=0.7", fc=fc, ec=ec, lw=1.2))
        ax.text(79.25, ys[k], m, ha="center", va="center", fontsize=12.2)
    save(fig, OUT / "03-annotations-to-claim.png")


def layers():
    fig, ax = canvas()
    rows = [("L0  Model", "What are the equations?", "rumoca: one model, Lean and Python views", BLUE_T, BLUE),
            ("L1  Claim", "What is asserted?", "Spec.lean, from the annotations only", BLUE_T, BLUE),
            ("L2  Structure", "What form do the dynamics have?", "dynacert MODEL.mo structure", ORANGE_T, ORANGE),
            ("L3  Certificate", "How is the claim proved?", "dynacert MODEL.mo certify", BLUE_T, BLUE),
            ("L4  Evidence", "How tight is it? Is the pipeline right?", "dynacert MODEL.mo validate", ORANGE_T, ORANGE),
            ("L5  Products", "What is it used for?", "dynacert MODEL.mo view tube | plots | report", ORANGE_T, ORANGE)]
    for i, (a, b, c, fc, ec) in enumerate(rows):
        y = 46.3 - i * 8.6
        ax.add_patch(FancyBboxPatch((2, y), 96, 7.3, boxstyle="round,pad=0,rounding_size=0.8", fc=fc, ec=ec, lw=1.3))
        ax.text(4, y + 3.65, a, fontsize=17, weight="bold", va="center")
        ax.text(27, y + 3.65, b, fontsize=14.5, va="center")
        ax.text(62, y + 3.65, c, fontsize=12, va="center", color=INK2,
                family="DejaVu Sans Mono" if "dynacert" in c else "DejaVu Sans")
    ax.text(50, 1.4, "Blue layers carry the guarantee (Lean side of L3). Orange layers can only change whether a proof is attempted or how it is shown.",
            ha="center", fontsize=12.2, color=INK2)
    save(fig, OUT / "04-six-layers.png")




def support_matrix():
    cols = ["Dynamics it handles", "Disturb-\nance", "Reference\npath", "Uncertain\nparameter", "Initial\nbox", "Arrays"]
    Y, N, S = "yes", "no", "limited"
    rows = [("lmi", "Linear; linear in uncertain params", Y, Y, Y, Y, Y),
            ("polyhedral", "Linear, fixed parameters", Y, Y, N, N, Y),
            ("switched", "Linear modes chosen by if-expressions", Y, Y, N, Y, N),
            ("layered", "Linear, separate weakly coupled parts", Y, N, N, "untested", "bug"),
            ("sector", "Nonlinear near an equilibrium (listed functions)", Y, N, N, N, N),
            ("compose", "Same as sector, split across a cut", Y, N, N, N, N),
            ("funnel", "Nonlinear along a finite-time path (sin)", Y, S, "untested", N, N),
            ("lie", "SE₂(3) vehicle, PD control, circular orbit only", Y, S, N, N, Y)]
    fig, ax = canvas()
    xs = [17, 53.5, 63, 72.5, 82, 91.5]
    ax.text(1.5, 52.5, "Method", fontsize=15, weight="bold", va="center")
    for x, c in zip(xs, cols):
        ax.text(x, 52.5, c, fontsize=12.5, weight="bold", va="center", ha="left" if x == 17 else "center")
    fill = {Y: AQUA_T, N: GRAY_T, S: "#fdf3d9", "bug": ORANGE_T, "untested": "#ffffff"}
    for i, r in enumerate(rows):
        y = 45 - i * 5.9
        ax.text(1.5, y, r[0], fontsize=15, weight="bold", family="DejaVu Sans Mono", va="center")
        ax.text(17, y, r[1], fontsize=11.6, va="center", color=INK2)
        for x, v in zip(xs[1:], r[2:]):
            ax.add_patch(FancyBboxPatch((x - 4.1, y - 2.3), 8.2, 4.6, boxstyle="round,pad=0,rounding_size=0.6", fc=fill[v], ec=GRID, lw=1))
            ax.text(x, y, v, ha="center", va="center", fontsize=11.5 if v == "untested" else 13)
    save(fig, OUT / "05-method-support-matrix.png")


def refusals():
    rows = [("Unstable plant", "lmi: the LMI search found no certificate (infeasible, or rounding failed)"),
            ("No lemma for this function", "sector: psi_d = -atan(s/2): unsupported nonlinearity"),
            ("Disturbance reaches the output", "lmi: output u depends on {n}, which are neither states nor declared references"),
            ("Uncertain input scaling", "lmi: input matrix depends on uncertain parameters (im)"),
            ("Euclidean-ball disturbance", 'lmi: disturbance d: norm = "2" (a Euclidean ball ‖d‖ ≤ bound) is not supported yet'),
            ("Events (when / reinit)", "rumoca: unsupported-feature: events: when/reinit/pre/sample, time events, ...")]
    fig, ax = canvas()
    for i, (a, b) in enumerate(rows):
        y = 47 - i * 8.6
        ax.add_patch(FancyBboxPatch((2, y - 3.6), 96, 7.2, boxstyle="round,pad=0,rounding_size=0.8", fc=GRAY_T, ec=GRID, lw=1))
        ax.text(4, y + 1.4, a, fontsize=16, weight="bold", va="center")
        ax.text(4, y - 1.6, b, fontsize=11.6, family="DejaVu Sans Mono", color=INK2, va="center")
    save(fig, OUT / "09-honest-refusals.png")


if __name__ == "__main__":
    pipeline(); trust(); annotations(); layers(); support_matrix(); refusals()
