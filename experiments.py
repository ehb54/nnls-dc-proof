#!/usr/bin/env python3
"""Paper driver: runs the four randomized suites (the first three with the
same seed and draw order as verify.py, the lattice suite with its own seed),
prints a LaTeX-ready summary table, and renders the manuscript figure.

Conventions: values are unhalved squared residual norms ||Ax-b||^2 = 2F,
matching verify.py; all relative quantities are convention-independent.

Outputs:
  paper/figs/convergence.pdf  (vector, for LaTeX)
  paper/figs/convergence.png  (raster, for quick visual inspection)
  stdout: summary statistics and LaTeX table rows
"""

import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from verify import (nnls_on, ssr, kkt_residuals, dc_nnls,
                    make_smooth_instance, make_gaussian_instance,
                    make_duplicate_instance, make_lattice_instance,
                    interlaced_blocks)

HERE = os.path.dirname(os.path.abspath(__file__))
FIGDIR = os.path.join(HERE, "paper", "figs")

# --- single-hue palette (journal figure: one series role per panel + neutrals)
BLUE = "#3B6FB6"        # data hue
BLUE_DARK = "#1F4E8C"   # emphasis (median curve)
INK = "#1A1A1A"         # primary text
MUTED = "#666666"       # secondary text
GRID = "#D9D9D9"        # recessive grid


def run_suite(name, maker, n_trials, rng, nblocks_choices=(4, 8, 16),
              fan_in_choices=(2, 4), blocks_fn=None):
    """Mirrors verify.run_trials draw order exactly; returns per-trial records."""
    recs = []
    reasons = {}
    for _ in range(n_trials):
        A, b = maker(rng)
        scale = max(1.0, float(np.max(np.abs(A.T @ b))))
        x_full = nnls_on(A, b, range(A.shape[1]))
        v_full = ssr(A, b, x_full)
        blocks = blocks_fn() if blocks_fn else None
        nb = None if blocks else int(rng.choice(nblocks_choices))
        fi = int(rng.choice(fan_in_choices))
        _, _, vals_sp, _ = dc_nnls(A, b, nblocks=nb, blocks=blocks,
                                   iterative=False, fan_in=fi)
        x, _, vals, reason = dc_nnls(A, b, nblocks=nb, blocks=blocks,
                                     iterative=True, fan_in=fi)
        reasons[reason] = reasons.get(reason, 0) + 1
        delta, eps = kkt_residuals(A, b, x)
        recs.append({
            "v_full": v_full,
            "v_sp": vals_sp[-1],
            "vals": vals,
            "rounds": len(vals),
            "val_err": abs(vals[-1] - v_full) / max(1.0, v_full),
            "delta": delta / scale,
            "eps": eps / max(1.0, v_full),
            "sp_subopt": vals_sp[-1] - v_full > 1e-9 * (1.0 + v_full),
        })
    print(f"[{name}] {n_trials} trials done; stopping reasons: {reasons}")
    return recs


def fmt_sci(x):
    if x <= 0:
        return "$0$"
    e = int(np.floor(np.log10(x)))
    m = x / 10 ** e
    return f"${m:.1f}\\times 10^{{{e}}}$"


def latex_row(name, recs):
    rounds = [r["rounds"] for r in recs]
    worst_err = max(r["val_err"] for r in recs)
    worst_delta = max(r["delta"] for r in recs)
    worst_eps = max(r["eps"] for r in recs)
    n_sub = sum(r["sp_subopt"] for r in recs)
    return (f"{name} & {len(recs)} & {min(rounds)}/{int(np.median(rounds))}/"
            f"{max(rounds)} & {fmt_sci(worst_err)} & {fmt_sci(worst_delta)} & "
            f"{fmt_sci(worst_eps)} & {n_sub}/{len(recs)} \\\\")


def make_figure(smooth, all_recs):
    os.makedirs(FIGDIR, exist_ok=True)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.6, 2.7))

    # Panel (a): relative excess SSR per round, smooth-kernel suite.
    # After a trial terminates, its terminal value is carried forward so the
    # per-round median is over all trials at every round.
    floor = 1e-16
    max_r = max(r["rounds"] for r in smooth)
    curves = []
    for r in smooth:
        v_star = r["v_full"]
        y = [max((v - v_star) / v_star, floor) for v in r["vals"]]
        y = y + [y[-1]] * (max_r - len(y))  # carry terminal value forward
        curves.append(y)
        ax1.plot(range(1, len(y) + 1), y, color=BLUE, alpha=0.30, lw=1.0,
                 solid_capstyle="round", zorder=2)
    med = np.median(np.array(curves), axis=0)
    ax1.plot(range(1, max_r + 1), med, color=BLUE_DARK, lw=2.0, marker="o",
             ms=3.5, zorder=3, label="median")
    ax1.set_yscale("log")
    ax1.set_xlabel("round $k$", fontsize=9, color=INK)
    ax1.set_ylabel(r"$(v_k - v^*)\,/\,v^*$", fontsize=9, color=INK)
    ax1.set_title("(a) descent to the exact optimum", fontsize=9, color=INK)
    ax1.annotate("round 1 = non-iterated scheme", xy=(1, med[0]),
                 xytext=(1.55, med[0] * 2.4), fontsize=7.5, color=MUTED,
                 arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.7))
    ax1.annotate("roundoff floor", xy=(int(np.median([r['rounds'] for r in smooth])), 2 * floor),
                 xytext=(2.1, 8 * floor), fontsize=7.5, color=MUTED)
    ax1.set_xticks(range(1, max_r + 1))

    # Panel (b): rounds to termination, all suites pooled
    rounds_all = [r["rounds"] for r in all_recs]
    bins = np.arange(min(rounds_all) - 0.5, max(rounds_all) + 1.5)
    ax2.hist(rounds_all, bins=bins, color=BLUE, edgecolor="white", lw=1.5)
    ax2.set_xlabel("rounds to termination", fontsize=9, color=INK)
    ax2.set_ylabel("trials", fontsize=9, color=INK)
    ax2.set_title(f"(b) rounds to termination (all {len(all_recs)} trials)",
                  fontsize=9, color=INK)
    ax2.set_xticks(range(min(rounds_all), max(rounds_all) + 1))

    for ax in (ax1, ax2):
        ax.spines[["top", "right"]].set_visible(False)
        ax.spines[["left", "bottom"]].set_color(MUTED)
        ax.tick_params(colors=MUTED, labelsize=8)
        ax.grid(axis="y", color=GRID, lw=0.6, zorder=0)
        ax.set_axisbelow(True)

    fig.tight_layout(pad=0.8)
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(FIGDIR, f"convergence.{ext}"), dpi=200)
    print(f"figure written to {FIGDIR}/convergence.{{pdf,png}}")


def main():
    rng = np.random.default_rng(20260807)
    smooth = run_suite("smooth", make_smooth_instance, 60, rng)
    gauss = run_suite("gaussian", make_gaussian_instance, 60, rng)
    dup = run_suite("duplicate", make_duplicate_instance, 40, rng)
    rng2 = np.random.default_rng(20260808)
    lattice = run_suite("lattice-interlaced", make_lattice_instance, 40, rng2,
                        blocks_fn=interlaced_blocks)

    print("\n--- LaTeX table rows ---")
    print(latex_row("smooth correlated kernels", smooth))
    print(latex_row("2-D lattice, interlaced subgrids", lattice))
    print(latex_row("i.i.d.\\ Gaussian", gauss))
    print(latex_row("duplicated columns", dup))

    sp = np.array([(r["v_sp"] - r["v_full"]) / r["v_full"] for r in smooth])
    print(f"\nsmooth suite: single-pass relative excess median "
          f"{np.median(sp):.3f}, max {np.max(sp):.3f}; "
          f"suboptimal in {sum(r['sp_subopt'] for r in smooth)}/60")
    spl = np.array([(r["v_sp"] - r["v_full"]) / r["v_full"] for r in lattice])
    print(f"lattice suite: single-pass relative excess median "
          f"{np.median(spl):.3f}, max {np.max(spl):.3f}; "
          f"suboptimal in {sum(r['sp_subopt'] for r in lattice)}/40")
    make_figure(smooth, smooth + gauss + dup + lattice)


if __name__ == "__main__":
    main()
