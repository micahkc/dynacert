"""Figures for certificates, Monte Carlo runs and worst-case searches.

    from dynacert import figures
    with figures.theme("dark"):                 # light (default), dark, paper
        fig = figures.envelope(mc)
    figures.save({"envelope": fig}, "plots", formats=("png", "svg"))
    figures.report(figs, "report.pdf")          # every figure as a page of one PDF

| figure | shows |
|---|---|
| `exceedance(mc)` | empirical tail P(peak/bound > x), DKW band, the scenario-bound ε at the achieved peak |
| `peak_histogram(mc)` | distribution of sampled peaks against the certified bound |
| `envelope(mc)` | quantile bands of each output over time (fan chart), extremes, ±bound |
| `traces(mc)` | sampled trajectories with the worst one highlighted |
| `phase(mc, a, b)` | trajectories in the (a, b) plane with the certified ellipse |
| `worstcase(found, ...)` | each search method's worst trajectory, the disturbance, the switching function |
| `tightness(rows)` | achieved lower bounds against the certified upper bound, per output |
| `tube(tb, runs)`, `tube_phase`, `tube_margin` | the proved tube along a reference; with an `initialSet` funnel (`Cert.funnel`), the shrinking funnel and runs from the initial-box corners |

Certified quantities are drawn in ink (dashed); sampled and searched quantities in series
colors. Every figure function returns a matplotlib Figure and takes `figsize`.
"""

from __future__ import annotations

import contextlib
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np
from matplotlib.ticker import MaxNLocator


@dataclass(frozen=True)
class Palette:
    surface: str
    ink: str
    muted: str
    grid: str
    series: tuple
    font: str = "DejaVu Sans"
    size: float = 9.0
    lw: float = 1.6


THEMES = {
    "light": Palette("#fcfcfb", "#1f1f1e", "#6b6a64", "#e4e3dd",
                     ("#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300")),
    "dark": Palette("#1a1a19", "#f0efec", "#c3c2b7", "#33332f",
                    ("#3987e5", "#d95926", "#199e70", "#c98500", "#d55181", "#008300")),
    "paper": Palette("#ffffff", "#000000", "#555555", "#e6e6e6",
                     ("#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300"),
                     font="DejaVu Serif", size=8.0, lw=1.2),
}
_current = THEMES["light"]


def palette() -> Palette:
    return _current


@contextlib.contextmanager
def theme(name: str = "light"):
    """Use a theme for the figures created inside the block."""
    import matplotlib as mpl

    global _current
    if name not in THEMES:
        raise ValueError(f"unknown theme {name!r}; choose from {', '.join(THEMES)}")
    p = THEMES[name]
    rc = {"figure.facecolor": p.surface, "axes.facecolor": p.surface,
          "savefig.facecolor": p.surface, "axes.edgecolor": p.muted, "axes.labelcolor": p.muted,
          "text.color": p.ink, "xtick.color": p.muted, "ytick.color": p.muted,
          "axes.titlecolor": p.ink, "font.family": p.font, "font.size": p.size,
          "axes.titlesize": p.size + 1, "legend.fontsize": p.size - 1, "legend.frameon": False,
          "axes.grid": True, "grid.color": p.grid, "grid.linewidth": 0.6,
          "axes.spines.top": False, "axes.spines.right": False, "axes.axisbelow": True}
    prev = _current
    _current = p
    try:
        with mpl.rc_context(rc):
            yield p
    finally:
        _current = prev


def _plt():
    import matplotlib.pyplot as plt

    return plt


def _subplots(n: int, ncols: int | None = None, figsize=None, w: float = 4.4, h: float = 3.3,
              **kw):
    ncols = ncols or min(n, 3)
    nrows = -(-n // ncols)
    fig, axes = _plt().subplots(nrows, ncols, figsize=figsize or (w * ncols, h * nrows),
                                squeeze=False, **kw)
    flat = axes.ravel()
    for ax in flat[n:]:
        ax.set_visible(False)
    return fig, flat[:n]


def _bound(ax, b, horizontal=True, label="certified bound", both=True):
    p = palette()
    f = ax.axhline if horizontal else ax.axvline
    f(b, color=p.ink, ls="--", lw=1.1, label=label)
    if both:
        f(-b, color=p.ink, ls="--", lw=1.1)


def _finish(fig, title: str | None):
    if title:
        fig.suptitle(title, fontsize=palette().size + 1.5)
    fig.tight_layout()
    return fig


def _scale(mc, o):
    return float(mc.bounds[o]) if o in mc.bounds else 1.0


def _need_traces(mc):
    if mc.trace_t is None or not mc.traces:
        raise ValueError("this Monte Carlo run kept no traces (trace_points=0)")


# --- Monte Carlo ------------------------------------------------------------------------------

def exceedance(mc, beta: float = 1e-3, normalize: bool = True, logy: bool = True, figsize=None,
               title: str | None = "default"):
    """Empirical tail `P(peak > x)` per output (normalized by the certified bound if any), with
    the DKW band at confidence `1 - beta` and the `scenario_bound` ε at the achieved peak."""
    from . import stats

    p = palette()
    s = mc.summary()
    n, eps = s["n"], float(s["eps"])
    band = stats.dkw(n, beta)
    fig, ax = _plt().subplots(figsize=figsize or (6.4, 4.0))
    floor = 0.5 / n
    xmax = 0.0
    norm = normalize and bool(mc.bounds)
    for k, o in enumerate(mc.peaks):
        c = p.series[k % len(p.series)]
        x = np.sort(mc.peaks[o] / (_scale(mc, o) if norm else 1.0))
        surv = 1.0 - np.arange(1, n + 1) / n
        ax.fill_between(x, np.maximum(surv - band, floor), np.minimum(surv + band, 1.0),
                        step="post", color=c, alpha=0.10, lw=0)
        ax.step(x, np.maximum(surv, floor) if logy else surv, where="post", color=c, lw=p.lw,
                label=o)
        ax.plot([x[-1]], [eps], "o", ms=8, mfc=p.surface, mec=c, mew=2, zorder=3)
        xmax = max(xmax, x[-1])
    if norm:
        ax.axvline(1.0, color=p.ink, lw=1.1, ls="--")
        ax.text(1.0, 0.98, " certified bound", transform=ax.get_xaxis_transform(), va="top",
                fontsize=p.size - 1)
    if logy:
        ax.set_yscale("log")
        ax.set_ylim(floor, 1.05)
    ax.set_xlim(left=0, right=1.05 * max(xmax, 1.0 if norm else xmax))
    ax.set_xlabel("peak / certified bound" if norm else "peak")
    ax.set_ylabel("P(peak / bound > x)" if norm else "P(peak > x)")
    ax.legend(loc="lower left")
    ax.text(0.02, 0.18, f"rings: P(peak > achieved) ≤ ε = {eps:.3g}\n"
            f"with confidence 1 − {float(s['beta']):.0e} (scenario_bound)\n"
            f"bands: DKW, confidence {1 - beta:g}", transform=ax.transAxes, ha="left",
            va="bottom", fontsize=p.size - 1, color=p.muted)
    return _finish(fig, f"{mc.model}: {n} Monte Carlo scenarios ({mc.backend})"
                   if title == "default" else title)


def peak_histogram(mc, bins: int = 40, normalize: bool = False, figsize=None,
                   title: str | None = "default"):
    """Distribution of sampled peaks per output, with the achieved maximum and certified bound."""
    p = palette()
    outs = list(mc.peaks)
    fig, axes = _subplots(len(outs), figsize=figsize)
    for k, (ax, o) in enumerate(zip(axes, outs)):
        c = p.series[k % len(p.series)]
        sc = _scale(mc, o) if normalize else 1.0
        x = mc.peaks[o] / sc
        ax.hist(x, bins=bins, color=c, alpha=0.85, edgecolor=p.surface, linewidth=0.6)
        ax.axvline(x.max(), color=c, lw=p.lw, label=f"achieved {x.max():.4g}")
        if o in mc.bounds:
            _bound(ax, float(mc.bounds[o]) / sc, horizontal=False,
                   label=f"certified {float(mc.bounds[o]) / sc:.4g}", both=False)
        ax.set_xlabel(f"peak |{o}|" + (" / bound" if normalize else ""))
        ax.set_ylabel("scenarios")
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))
        ax.legend(loc="upper left")
        ax.grid(axis="x", visible=False)
    return _finish(fig, f"{mc.model}: peaks of {mc.n} scenarios" if title == "default" else title)


def envelope(mc, quantiles=((0.01, 0.99), (0.1, 0.9), (0.25, 0.75)), extremes: bool = True,
             figsize=None, title: str | None = "default"):
    """Fan chart: quantile bands of each output over time across scenarios, the median, the
    pointwise extremes, and the certified bound."""
    _need_traces(mc)
    p = palette()
    outs = list(mc.traces)
    fig, axes = _subplots(len(outs), ncols=1 if len(outs) < 3 else 2, figsize=figsize, w=8.4,
                          h=2.8)
    t = mc.trace_t
    for k, (ax, o) in enumerate(zip(axes, outs)):
        c = p.series[k % len(p.series)]
        Y = mc.traces[o]
        for j, (lo, hi) in enumerate(quantiles):
            ax.fill_between(t, np.quantile(Y, lo, axis=0), np.quantile(Y, hi, axis=0),
                            color=c, alpha=0.12 + 0.12 * j, lw=0,
                            label=f"{int(lo * 100)}–{int(hi * 100)}%")
        ax.plot(t, np.median(Y, axis=0), color=c, lw=p.lw, label="median")
        if extremes:
            ax.plot(t, Y.max(axis=0), color=c, lw=0.8, ls=":", label="max / min")
            ax.plot(t, Y.min(axis=0), color=c, lw=0.8, ls=":")
        if o in mc.bounds:
            _bound(ax, float(mc.bounds[o]))
        ax.set_ylabel(o)
        ax.set_xlabel("t")
        ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0))
    return _finish(fig, f"{mc.model}: {mc.n} scenarios over time ({mc.backend})"
                   if title == "default" else title)


def traces(mc, n: int = 40, highlight_worst: bool = True, figsize=None,
           title: str | None = "default"):
    """Up to `n` sampled trajectories per output (muted), the worst one highlighted."""
    _need_traces(mc)
    p = palette()
    outs = list(mc.traces)
    fig, axes = _subplots(len(outs), ncols=1 if len(outs) < 3 else 2, figsize=figsize, w=8.4,
                          h=2.8)
    t = mc.trace_t
    for k, (ax, o) in enumerate(zip(axes, outs)):
        c = p.series[k % len(p.series)]
        Y = mc.traces[o]
        for y in Y[:n]:
            ax.plot(t, y, color=p.muted, lw=0.5, alpha=0.45)
        if highlight_worst:
            w = int(np.argmax(np.max(np.abs(Y), axis=1)))
            ax.plot(t, Y[w], color=c, lw=p.lw, label=f"worst of {len(Y)} (peak "
                                                      f"{np.max(np.abs(Y[w])):.4g})")
        if o in mc.bounds:
            _bound(ax, float(mc.bounds[o]))
        ax.set_ylabel(o)
        ax.set_xlabel("t")
        ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0))
    return _finish(fig, f"{mc.model}: sampled trajectories" if title == "default" else title)


def phase(mc, a: str | None = None, b: str | None = None, cert=None, n: int = 60, figsize=None,
          title: str | None = "default"):
    """Trajectories in the plane of two certified outputs, with the certified invariant ellipse
    (if `cert` is given and both are certified coordinates) and the bound box."""
    _need_traces(mc)
    p = palette()
    outs = list(mc.traces)
    if len(outs) < 2 and (a is None or b is None):
        raise ValueError("phase needs two outputs")
    a, b = a or outs[0], b or outs[1]
    fig, ax = _plt().subplots(figsize=figsize or (7.2, 4.6))
    if cert is not None:
        try:
            e = cert.ellipse(a, b)
            ax.fill(e[0], e[1], color=p.series[0], alpha=0.10, lw=0)
            ax.plot(e[0], e[1], color=p.series[0], lw=p.lw, label="certified invariant set")
        except (KeyError, np.linalg.LinAlgError):
            pass
    for ya, yb in list(zip(mc.traces[a], mc.traces[b]))[:n]:
        ax.plot(ya, yb, color=p.muted, lw=0.5, alpha=0.5)
    w = int(np.argmax(np.max(np.abs(mc.traces[a] / _scale(mc, a)), axis=1)))
    ax.plot(mc.traces[a][w], mc.traces[b][w], color=p.series[1], lw=p.lw,
            label=f"worst |{a}| scenario")
    if a in mc.bounds:
        _bound(ax, float(mc.bounds[a]), horizontal=False, label="certified bounds")
    if b in mc.bounds:
        _bound(ax, float(mc.bounds[b]), label=None)
    ax.set_xlabel(a)
    ax.set_ylabel(b)
    ax.set_aspect("auto")
    ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0))
    return _finish(fig, f"{mc.model}: phase plane" if title == "default" else title)


# --- worst case -------------------------------------------------------------------------------

def worstcase(found, output: str, simulate, *, bound: float | None = None, space=None,
              adjoint=None, model: str = "", figsize=None, title: str | None = "default"):
    """The worst trajectory of `output` found by each method, the best scenario's disturbance
    signals, and (with `adjoint`) its switching function `σ`, which the bang-bang optimum
    follows in sign.

    `found` is a list of `(value, method, scenario)`; `simulate` maps a scenario to a run."""
    p = palette()
    found = sorted(found, key=lambda f: f[0])
    best_v, best_how, best = found[-1]
    rows = 2 + (adjoint is not None)
    plt = _plt()
    fig, axes = plt.subplots(rows, 1, sharex=True, figsize=figsize or (9.4, 2.3 * rows + 0.6),
                             gridspec_kw={"height_ratios": [2.2] + [1.0] * (rows - 1)})
    ax = axes[0]
    seen = {}
    for v, how, scn in found:
        seen.setdefault(how.split(" ")[0], (v, how, scn))
    for k, (v, how, scn) in enumerate(sorted(seen.values(), key=lambda f: f[0])):
        run = simulate(scn)
        is_best = scn is best
        c = p.series[k % len(p.series)]
        ax.plot(run.t, run.outputs[output], color=c, lw=p.lw if is_best else 0.9,
                alpha=1.0 if is_best else 0.7, label=f"{how}: {v:.6g}", zorder=3 if is_best else 2)
        if is_best:
            i = int(np.argmax(np.abs(run.outputs[output])))
            ax.plot([run.t[i]], [run.outputs[output][i]], "o", ms=8, mfc=p.surface, mec=c,
                    mew=2, zorder=4)
            best_run = run
    if bound is not None:
        _bound(ax, bound, label=f"certified ±{bound:.6g}")
    ax.set_ylabel(output)
    ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0), fontsize=p.size - 1.5)
    ax = axes[1]
    for k, (n, _) in enumerate(space.dists if space is not None else []):
        y = best_run.inputs.get(n)
        tt = best_run.t
        if y is None:
            f = space.disturbance(best, n)
            tt = np.linspace(0, space.T, 2000)
            y = np.array([f(t) for t in tt])
        ax.plot(tt, y, color=p.series[k % len(p.series)], lw=1.0, drawstyle="steps-post",
                label=n)
        sw = space.edges(best, n) if n in best.edges else []
        for e in sw:
            if e < space.T:
                ax.axvline(e, color=p.grid, lw=0.6, zorder=0)
    ax.set_ylabel("disturbance")
    ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0), fontsize=p.size - 1.5)
    if adjoint is not None:
        ax = axes[2]
        ts, sigma, tstar = adjoint.switching_function(best, output)
        for k, (n, _) in enumerate(space.dists):
            ax.plot(ts, sigma[:, k], color=p.series[k % len(p.series)], lw=1.0, label=f"σ_{n}")
        ax.axhline(0, color=p.muted, lw=0.6)
        ax.axvline(tstar, color=p.ink, lw=0.8, ls=":", label=f"t* = {tstar:.4g}")
        ax.set_ylabel("switching fn.")
        ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0), fontsize=p.size - 1.5)
    axes[-1].set_xlabel("t")
    return _finish(fig, f"{model}: worst case of |{output}| ({best_how}, {best_v:.6g})"
                   if title == "default" else title)


def tightness(rows: dict, model: str = "", figsize=None, title: str | None = "default"):
    """Lower bounds against the certified upper bound, normalized per output.

    `rows[output]` holds `certified` and any of `montecarlo`, `falsify`, `exact` (absolute
    values). Each output is a row on the axis `value / certified`; the shaded span from the best
    lower bound to 1 is what neither side has resolved."""
    p = palette()
    names = list(rows)
    fig, ax = _plt().subplots(figsize=figsize or (6.8, 0.75 * len(names) + 1.4))
    marks = [("montecarlo", "Monte Carlo max", "o", p.series[0]),
             ("falsify", "worst case found", "D", p.series[1]),
             ("exact", "exact", "x", p.ink)]
    used = set()
    lo_all = 1.0
    for y, o in enumerate(names):
        r = rows[o]
        c = float(r["certified"])
        lows = [float(r[k]) / c for k, *_ in marks if r.get(k) is not None and k != "exact"]
        best = max(lows) if lows else None
        if best is not None:
            ax.barh(y, 1.0 - best, left=best, height=0.36, color=p.grid, zorder=1)
            ax.text(1.0 + 0.004, y, f"  gap {100 * (1 - best):.1f}%", va="center",
                    fontsize=p.size - 1, color=p.muted)
            lo_all = min(lo_all, best)
        for k, label, m, col in marks:
            if r.get(k) is None:
                continue
            v = float(r[k]) / c
            lo_all = min(lo_all, v)
            ax.plot(v, y, m, ms=7, color=col, mfc=col if m != "o" else p.surface, mew=1.8,
                    label=label if k not in used else None, zorder=3)
            used.add(k)
        ax.plot([1.0, 1.0], [y - 0.28, y + 0.28], color=p.ink, lw=2.2,
                label="certified" if "cert" not in used else None, zorder=3)
        used.add("cert")
    ax.set_yticks(range(len(names)), [f"|{o}|" for o in names])
    ax.set_ylim(-0.7, len(names) - 0.3)
    ax.invert_yaxis()
    ax.set_xlim(max(0.0, lo_all - 0.05), 1.08)
    ax.set_xlabel("value / certified bound")
    ax.grid(axis="y", visible=False)
    ax.legend(loc="lower left", ncol=4, bbox_to_anchor=(0, 1.0), fontsize=p.size - 1)
    return _finish(fig, f"{model}: how tight is the certificate?" if title == "default" else title)


# --- error-frame tubes -------------------------------------------------------------------------

def _funnel_runs(tb, funnel_runs):
    """Runs from the initial-box corners: given, or simulated on the certified frame dynamics."""
    if getattr(tb, "funnel", None) is None:
        return []
    if funnel_runs is None:
        try:
            return tb.funnel_runs()
        except Exception:  # illustration only
            return []
    return list(funnel_runs)


def tube(tb, runs, worst=(), figsize=None, model: str = "", title: str | None = "default",
         funnel_runs=None):
    """Each physical state over time: the reference centre, the proved tube around it, simulated
    runs on that reference, and the adjoint worst cases. Frames that do not determine every state
    are drawn in error coordinates. With a funnel (`initialSet`), the shrinking funnel
    `zᵀPz ≤ ρ(t)` is drawn inside the tube, with runs from the initial-box corners
    (`funnel_runs`, default `tb.funnel_runs()`)."""
    p = palette()
    fr = tb.frame
    fun = getattr(tb, "funnel", None)
    if fr.reconstructs:
        names, centre = fr.states, tb.center()
        hw = tb.halfwidths()
        val = lambda r, s: r.states[s]  # noqa: E731
    else:
        names = fr.names
        centre = {n: np.zeros_like(tb.t) for n in names}
        Pi = np.linalg.inv(fr.P)
        hw = {n: float(np.sqrt(fr.level * Pi[i, i])) for i, n in enumerate(names)}
        val = lambda r, s: fr.error(r.states, r.inputs)[:, names.index(s)]  # noqa: E731
    fruns = _funnel_runs(tb, funnel_runs)
    sc = np.sqrt(tb.level_at() / fr.level) if fun is not None else None
    fig, axes = _subplots(len(names), ncols=1, figsize=figsize, w=8.6, h=2.6)
    for k, (ax, s) in enumerate(zip(axes, names)):
        c = p.series[0]
        if fun is None:
            ax.fill_between(tb.t, centre[s] - hw[s], centre[s] + hw[s], color=c, alpha=0.16,
                            lw=0, label=f"proved tube (±{hw[s]:.3g})")
            ax.plot(tb.t, centre[s] + hw[s], color=c, lw=0.8)
            ax.plot(tb.t, centre[s] - hw[s], color=c, lw=0.8)
        else:
            fw = hw[s] * sc
            ax.plot(tb.t, centre[s] + hw[s], color=c, lw=0.8, ls=":",
                    label=f"proved tube (±{hw[s]:.3g})")
            ax.plot(tb.t, centre[s] - hw[s], color=c, lw=0.8, ls=":")
            ax.fill_between(tb.t, centre[s] - fw, centre[s] + fw, color=c, alpha=0.18, lw=0,
                            label=f"proved funnel (±{fw[0]:.3g} → ±{hw[s] * np.sqrt(min(fun.rate, fr.level) / fr.level):.3g})")
            ax.plot(tb.t, centre[s] + fw, color=c, lw=0.9)
            ax.plot(tb.t, centre[s] - fw, color=c, lw=0.9)
        for r in runs:
            ax.plot(r.t, val(r, s), color=p.muted, lw=0.5, alpha=0.5)
        for j, r in enumerate(fruns):
            ax.plot(r.t, val(r, s), color=p.series[2], lw=0.9, alpha=0.85,
                    label="from initial-box corners (worst-push w)" if j == 0 else None)
        for j, (o, w) in enumerate(worst):
            ax.plot(w.t, val(w, s), color=p.series[(j + 1) % len(p.series)], lw=p.lw,
                    label=f"worst |{o}|")
        ax.plot(tb.t, centre[s], color=p.ink, lw=1.0, ls="--", label="reference")
        ax.set_ylabel(s)
        ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0))
    axes[-1].set_xlabel("t")
    what = "proved funnel" if fun is not None else "proved tube"
    return _finish(fig, f"{model}: {what} along the reference ({len(runs)} runs)"
                   if title == "default" else title)


def tube_phase(tb, runs, worst=(), a: str | None = None, b: str | None = None,
               sections: int = 12, figsize=None, model: str = "", title: str | None = "default",
               funnel_runs=None):
    """The tube in a physical state plane: the reference path, the proved set at `sections`
    times along it, simulated runs, and the worst cases. With a funnel, the sections shrink
    with `ρ(t)`, the initial box is drawn, and runs start from its corners."""
    p = palette()
    fr = tb.frame
    fun = getattr(tb, "funnel", None)
    a, b = a or fr.states[0], b or fr.states[1]
    fig, ax = _plt().subplots(figsize=figsize or (7.4, 5.0))
    idx = np.linspace(0, len(tb.t) - 1, sections).round().astype(int)
    for n, i in enumerate(idx):
        xa, xb = tb.section(int(i), a, b)
        ax.plot(xa, xb, color=p.series[0], lw=0.9, alpha=0.35 + 0.65 * n / max(1, len(idx) - 1),
                label=("proved funnel set at sampled times" if fun is not None else
                       "proved set at sampled times") if n == len(idx) - 1 else None)
    if fun is not None:
        xa, xb = tb.section(0, a, b, funnel=False)
        ax.plot(xa, xb, color=p.series[0], lw=0.8, ls=":", label="proved tube (every t; drawn at t = 0)")
        box = {d["name"]: (float(Fraction(d["min"])), float(Fraction(d["max"])))
               for d in fun.initial}
        cen = tb.center()
        if a in box or b in box:
            lo_a, hi_a = box.get(a, (cen[a][0], cen[a][0]))
            lo_b, hi_b = box.get(b, (cen[b][0], cen[b][0]))
            ax.plot([lo_a, hi_a, hi_a, lo_a, lo_a], [lo_b, lo_b, hi_b, hi_b, lo_b],
                    color=p.series[3], lw=1.2, label="initial set")
        for j, r in enumerate(_funnel_runs(tb, funnel_runs)):
            ax.plot(r.states[a], r.states[b], color=p.series[2], lw=0.9, alpha=0.85,
                    label="from initial-box corners" if j == 0 else None)
    for r in runs:
        ax.plot(r.states[a], r.states[b], color=p.muted, lw=0.5, alpha=0.5)
    for j, (o, w) in enumerate(worst):
        ax.plot(w.states[a], w.states[b], color=p.series[(j + 1) % len(p.series)], lw=p.lw,
                label=f"worst |{o}|")
    cen = tb.center()
    ax.plot(cen[a], cen[b], color=p.ink, lw=1.2, ls="--", label="reference")
    ax.plot(cen[a][-1:], cen[b][-1:], "o", color=p.ink, ms=4)
    ax.set_xlabel(a)
    ax.set_ylabel(b)
    ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0))
    what = "proved funnel" if fun is not None else "proved tube"
    return _finish(fig, f"{model}: {what} in ({a}, {b})" if title == "default" else title)


def tube_margin(tb, runs, worst=(), figsize=None, model: str = "", title: str | None = "default",
                funnel_runs=None):
    """How full each run keeps the proved set: `zᵀPz / level` over time (the tube is ≤ 1).
    With a funnel, the proved bound `ρ(t)/level` is drawn too, with runs from the initial-box
    corners."""
    p = palette()
    fun = getattr(tb, "funnel", None)
    fig, ax = _plt().subplots(figsize=figsize or (8.0, 3.4))
    if fun is not None:
        ax.plot(tb.t, tb.level_at() / tb.frame.level, color=p.series[0], lw=1.4,
                label=f"proved funnel ρ(t)/level ({fun.theorem or 'Cert.funnel'})")
        for j, r in enumerate(_funnel_runs(tb, funnel_runs)):
            ax.plot(r.t, tb.margin(r), color=p.series[2], lw=0.9, alpha=0.85,
                    label="from initial-box corners" if j == 0 else None)
    for r in runs:
        ax.plot(r.t, tb.margin(r), color=p.muted, lw=0.5, alpha=0.6)
    for j, (o, w) in enumerate(worst):
        ax.plot(w.t, tb.margin(w), color=p.series[(j + 1) % len(p.series)], lw=p.lw,
                label=f"worst |{o}|")
    ax.axhline(1.0, color=p.ink, ls="--", lw=1.1, label="proved tube boundary")
    ax.set_ylim(bottom=0)
    ax.set_xlabel("t")
    ax.set_ylabel("zᵀPz / level")
    ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1.0))
    return _finish(fig, f"{model}: distance to the tube wall" if title == "default" else title)


# --- output -----------------------------------------------------------------------------------

def save(figs: dict, directory: str | Path, formats=("png",), dpi: int = 150,
         prefix: str = "") -> list[Path]:
    """Write each figure as `<directory>/<prefix><name>.<format>`; returns the paths."""
    d = Path(directory)
    d.mkdir(parents=True, exist_ok=True)
    out = []
    for name, fig in figs.items():
        for fmt in formats:
            path = d / f"{prefix}{name}.{fmt}"
            fig.savefig(path, dpi=dpi, bbox_inches="tight")
            out.append(path)
    return out


def report(figs: dict, path: str | Path) -> Path:
    """All figures as the pages of one PDF."""
    from matplotlib.backends.backend_pdf import PdfPages

    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with PdfPages(path) as pdf:
        for fig in figs.values():
            pdf.savefig(fig, bbox_inches="tight")
    return path


def close(figs: dict):
    plt = _plt()
    for fig in figs.values():
        plt.close(fig)


__all__ = ["Palette", "THEMES", "close", "envelope", "exceedance", "palette", "peak_histogram",
           "phase", "report", "save", "theme", "tightness", "traces", "tube", "tube_margin",
           "tube_phase", "worstcase"]
