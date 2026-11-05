"""Shared look for the slide figures: 16:9, white surface, large type, no titles in the image."""

import matplotlib as mpl

mpl.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch

SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK2 = "#52514e"
GRID = "#e4e3df"
BLUE, ORANGE, AQUA, YELLOW = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"
BLUE_T, ORANGE_T, AQUA_T, GRAY_T = "#e6f0fb", "#fdeee7", "#e4f6ef", "#f1f0ec"

mpl.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
    "font.family": "DejaVu Sans", "font.size": 15, "text.color": INK,
    "axes.edgecolor": GRID, "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2,
    "axes.spines.top": False, "axes.spines.right": False, "axes.grid": False,
    "grid.color": GRID, "legend.frameon": False,
})


def canvas(w=13.333, h=7.5, xlim=(0, 100), ylim=(0, 56)):
    fig, ax = plt.subplots(figsize=(w, h))
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.axis("off")
    fig.subplots_adjust(0, 0, 1, 1)
    return fig, ax


def box(ax, x, y, w, h, title, body=None, fc=GRAY_T, ec=INK2, tsize=16, bsize=12.5, mono=False):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0,rounding_size=0.9",
                                fc=fc, ec=ec, lw=1.4))
    if body:
        ax.text(x + w / 2, y + h * 0.72, title, ha="center", va="center", fontsize=tsize, weight="bold")
        ax.text(x + w / 2, y + h * 0.34, body, ha="center", va="center", fontsize=bsize,
                color=INK2, family="DejaVu Sans Mono" if mono else "DejaVu Sans", linespacing=1.35)
    else:
        ax.text(x + w / 2, y + h / 2, title, ha="center", va="center", fontsize=tsize, weight="bold")


def arrow(ax, a, b, label=None, color=INK2, lw=1.8, lx=0, ly=0.8, size=12):
    ax.add_patch(FancyArrowPatch(a, b, arrowstyle="-|>", mutation_scale=18, color=color, lw=lw,
                                 shrinkA=0, shrinkB=0))
    if label:
        ax.text((a[0] + b[0]) / 2 + lx, (a[1] + b[1]) / 2 + ly, label, ha="center", va="bottom",
                fontsize=size, color=INK2)


def save(fig, path, dpi=200):
    fig.savefig(path, dpi=dpi)
    plt.close(fig)
    print("wrote", path)
