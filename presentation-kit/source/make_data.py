"""Data figures, computed from the certificate index and the validation logs of this repo."""

import glob, json, re, sys
from fractions import Fraction
from pathlib import Path

import numpy as np

from style import *

KIT = Path(__file__).resolve().parents[1]
OUT = KIT / "images"
ROOT = KIT.parent
RUNS = Path(sys.argv[1]) if len(sys.argv) > 1 else KIT / "source" / "falsify-logs"


# Falsification starts from the nominal point, so a bound that also covers an initial box looks loose.
INITIAL_BOX = {"OvenWarmStartFunnel", "DockingAllAnnotations", "SwitchedTrackingFunnel"}


def by_method():
    counts = {}
    for f in glob.glob(str(ROOT / "certs/Certs/*/certificates.json")):
        for c in json.load(open(f))["certificates"]:
            counts[c["method"]] = counts.get(c["method"], 0) + 1
    # Certificates that predate the index
    counts["funnel"] = counts.get("funnel", 0) + 1     # PendulumPID
    counts["lmi"] = counts.get("lmi", 0) + 1           # ClosedLoopUncertain
    items = sorted(counts.items(), key=lambda kv: kv[1])
    fig, ax = plt.subplots(figsize=(13.333, 7.5))
    ax.barh([k for k, _ in items], [v for _, v in items], color=BLUE, height=0.6)
    for i, (_, v) in enumerate(items):
        ax.text(v + 0.5, i, str(v), va="center", fontsize=16)
    ax.set_xlabel("Lean-checked certificates in the repository")
    ax.tick_params(axis="y", labelsize=17, length=0)
    ax.spines["left"].set_visible(False)
    fig.tight_layout(pad=2)
    save(fig, OUT / "06-certificates-by-method.png")
    return counts


def poly_vs_lmi():
    # ReservoirCascadePoly: bounds from certificates.json. Exact peaks by hand: h1 = 1·1 = 1; h2 = 2·1 + 2·0.5 = 3
    d = json.load(open(ROOT / "certs/Certs/ReservoirCascadePoly/certificates.json"))
    b = {c["method"]: {k: float(Fraction(v)) for k, v in c["bounds"].items()} for c in d["certificates"]}
    exact = {"h1": 1.0, "h2": 3.0}
    fig, axes = plt.subplots(1, 2, figsize=(13.333, 7.5))
    for ax, o in zip(axes, ["h1", "h2"]):
        names = ["exact worst case", "polyhedral (128 facets)", "lmi (ellipsoid)"]
        vals = [exact[o], b["polyhedral"][o], b["lmi"][o]]
        cols = [INK2, AQUA, BLUE]
        ax.barh(names[::-1], vals[::-1], color=cols[::-1], height=0.55)
        for i, v in enumerate(vals[::-1]):
            ax.text(v * 0.98, i, f"{v:.4f}", va="center", ha="right", color="white", fontsize=17, weight="bold")
        ax.set_title(f"peak of |{o}|", fontsize=18, color=INK, loc="left")
        ax.tick_params(axis="y", labelsize=14, length=0)
        ax.set_xlim(0, max(vals) * 1.05)
        ax.spines["left"].set_visible(False)
    axes[1].set_yticklabels([])
    fig.tight_layout(pad=2)
    save(fig, OUT / "07-polyhedral-vs-lmi.png")


def funnel():
    """RobotArmSwingFunnel: the proved bound per time segment against the Monte Carlo peak."""
    d = json.load(open(ROOT / "certs/Certs/RobotArmSwingFunnel/funnel.json"))
    seg = [float(Fraction(x)) for x in d["segment_bounds"]["e"]]
    T = float(d["horizon"])
    edges = np.linspace(0, T, len(seg) + 1)
    fig, ax = plt.subplots(figsize=(13.333, 7.5))
    ax.stairs(seg, edges, baseline=0, fill=True, color=BLUE_T)
    ax.stairs(seg, edges, baseline=None, color=BLUE, lw=2.2)
    ax.stairs([-v for v in seg], edges, baseline=0, fill=True, color=BLUE_T)
    ax.stairs([-v for v in seg], edges, baseline=None, color=BLUE, lw=2.2)
    ax.axhline(0, color=GRID, lw=1)
    mc = json.load(open(KIT / "source" / "robotarm_mc_T2.json"))   # 200 rumoca runs on [0, 2]
    for tr in mc["sample"]:
        ax.plot(mc["t"], tr, color=INK2, lw=0.8, alpha=0.45)
    ax.text(0.55, 0.0135, "proved bound in each time segment", fontsize=14, color=INK2)
    ax.text(1.28, 0.0072, "simulated runs", fontsize=14, color=INK2)
    ax.set_xlim(0, T)
    ax.set_xlabel("time [s]")
    ax.set_ylabel("angle tracking error [rad]")
    ax.tick_params(labelsize=14)
    fig.tight_layout(pad=2)
    save(fig, OUT / "16-funnel-RobotArm.png")


def kept_bound(name, output):
    return float(Fraction(json.load(open(ROOT / f"certs/Certs/{name}/certificates.json"))["kept"][output]["bound"]))


def tightness():
    rows = []
    for f in sorted(RUNS.glob("*.fal.log")):
        n = f.name.split(".")[0]
        if n in INITIAL_BOX:
            continue
        for m in re.finditer(r"^\|(.+?)\|: achieved ([\d.e-]+) vs certified", f.read_text(), re.M):
            rows.append((n, m.group(1), float(m.group(2)) / kept_bound(n, m.group(1))))
    per = {}
    for n, o, r in rows:
        per.setdefault(n, []).append(r)
    names = sorted(per, key=lambda k: np.mean(per[k]))
    fig, ax = plt.subplots(figsize=(13.333, 7.5))
    for i, n in enumerate(names):
        ax.plot([min(per[n]), max(per[n])], [i, i], color=GRID, lw=3, zorder=1)
        ax.scatter(per[n], [i] * len(per[n]), s=90, color=BLUE, edgecolor=SURFACE, lw=1.5, zorder=2)
    ax.axvline(1, color=INK2, lw=1.5)
    ax.text(0.995, len(names) - 0.4, "proved bound", ha="right", fontsize=13, color=INK2)
    ax.set_yticks(range(len(names)), names, fontsize=12.5)
    ax.tick_params(axis="y", length=0)
    ax.spines["left"].set_visible(False)
    ax.set_xlim(0, 1.03)
    ax.xaxis.grid(True)
    ax.set_axisbelow(True)
    ax.set_xlabel("worst case found by search ÷ proved bound (one dot per certified output; 1 = no slack)")
    fig.tight_layout(pad=2)
    save(fig, OUT / "08-tightness.png")
    print("tightness rows", rows)
    return rows


if __name__ == "__main__":
    print(by_method())
    poly_vs_lmi()
    funnel()
    if RUNS:
        tightness()
