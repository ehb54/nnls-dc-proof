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
# Embed TrueType (Type 42) fonts, not Type 3, per journal requirements.
matplotlib.rcParams["pdf.fonttype"] = 42
matplotlib.rcParams["ps.fonttype"] = 42
import matplotlib.pyplot as plt

import time

from verify import (nnls_on, ssr, kkt_residuals, dc_nnls, dc_round,
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
        full_support = set(np.flatnonzero(x_full > 0.0).tolist())
        recs.append({
            "v_full": v_full,
            "v_sp": vals_sp[-1],
            "vals": vals,
            "rounds": len(vals),
            "reason": reason,
            "val_err": abs(vals[-1] - v_full) / max(1.0, v_full),
            "delta": delta / scale,
            "eps": eps / max(1.0, v_full),
            "delta_abs": delta,
            "eps_abs": eps,
            "x1": float(np.sum(x_full)),
            "sp_subopt": vals_sp[-1] - v_full > 1e-9 * (1.0 + v_full),
            "supp_match": set(map(int, np.flatnonzero(x > 0.0))) == full_support,
        })
    n_match = sum(r["supp_match"] for r in recs)
    print(f"[{name}] {n_trials} trials done; stopping reasons: {reasons}; "
          f"support matches full-grid solve: {n_match}/{n_trials}")
    return recs


def run_scaling(sizes, n_trials, rng):
    """Scaling probe on the smooth-kernel generator: fixed m = 80, growing
    n, block counts scaled to keep ~60 columns per block, fan-in 4.  Every
    trial retains a full-grid reference solve.  Returns LaTeX rows."""
    rows = []
    for n in sizes:
        t0 = time.time()
        recs = []
        for _ in range(n_trials):
            A, b = make_smooth_instance(rng, m=80, n=n, k_true=8)
            scale = max(1.0, float(np.max(np.abs(A.T @ b))))
            x_full = nnls_on(A, b, range(n))
            v_full = ssr(A, b, x_full)
            x, R, vals, reason = dc_nnls(A, b, nblocks=max(4, n // 60),
                                         fan_in=4)
            delta, eps = kkt_residuals(A, b, x)
            recs.append({
                "rounds": len(vals),
                "reason": reason,
                "v_full": v_full,
                "val_err": abs(vals[-1] - v_full) / max(1.0, v_full),
                "delta": delta / scale,
                "eps": eps / max(1.0, v_full),
            })
        dt = time.time() - t0
        rr = {}
        for r in recs:
            rr[r["reason"]] = rr.get(r["reason"], 0) + 1
        print(f"  [scaling n={n}] reasons: {rr}; "
              f"max v*: {max(r['v_full'] for r in recs):.4g}")
        rounds = [r["rounds"] for r in recs]
        rows.append(
            f"$n={n}$ & {n_trials} & {min(rounds)}/{np.median(rounds):g}/"
            f"{max(rounds)} & {fmt_sci(max(r['val_err'] for r in recs))} & "
            f"{fmt_sci(max(r['delta'] for r in recs))} & "
            f"{fmt_sci(max(r['eps'] for r in recs))} \\\\")
        print(f"[scaling n={n}] {n_trials} trials in {dt:.1f}s; rounds "
              f"{min(rounds)}-{max(rounds)}")
    return rows


def cycling_probe(rng, n_trials=40, cap=400, long_cap=2000):
    """Support-rule-only termination probe on the duplicated-column
    generator (non-unique optima): with the value rule disabled, does the
    support-stability test ever fire?"""
    instances = []
    n_nonterm = 0
    first_nonterm = None
    for trial in range(n_trials):
        A, b = make_duplicate_instance(rng)
        nb = int(rng.choice((4, 8, 16)))
        fi = int(rng.choice((2, 4)))
        _, _, vals, reason = dc_nnls(A, b, nblocks=nb, fan_in=fi,
                                     max_rounds=cap, value_rule=False)
        if reason == "max_rounds":
            n_nonterm += 1
            if first_nonterm is None:
                first_nonterm = (A, b, nb, fi)
    print(f"[cycling probe] support rule alone: {n_nonterm}/{n_trials} "
          f"failed to stabilize within {cap} rounds")
    if first_nonterm is None:
        return n_nonterm, None
    # Extend the first non-terminating run and look for a support cycle.
    A, b, nb, fi = first_nonterm
    n = A.shape[1]
    blocks = [list(B) for B in np.array_split(np.arange(n), nb)]
    x_full = nnls_on(A, b, range(n))
    v_full = ssr(A, b, x_full)
    R = set()
    supports, values = [], []
    for _ in range(long_cap):
        R, x, diag = dc_round(A, b, blocks, R, fan_in=fi, check=False)
        supports.append(frozenset(R))
        values.append(diag["v"])
    period = None
    tail = supports[-60:]
    for p in range(1, 9):
        if all(tail[i] == tail[i - p] for i in range(p, len(tail))):
            period = p
            break
    n_distinct = len(set(tail))
    v_ok = all(abs(v - v_full) <= 1e-9 * (1.0 + v_full)
               for v in values[3:])
    print(f"[cycling probe] extended run ({long_cap} rounds): period "
          f"{period}, {n_distinct} distinct supports in tail, "
          f"v_k = v* from round 4 on: {v_ok}")
    return n_nonterm, (period, n_distinct, v_ok)


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
    return (f"{name} & {len(recs)} & {min(rounds)}/{np.median(rounds):g}/"
            f"{max(rounds)} & {fmt_sci(worst_err)} & {fmt_sci(worst_delta)} & "
            f"{fmt_sci(worst_eps)} & {n_sub}/{len(recs)} \\\\")


def make_figure(smooth, all_recs):
    os.makedirs(FIGDIR, exist_ok=True)
    # 31pc text width of the Springer sn-jnl class ~ 5.15 in
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(5.15, 2.35))

    # Panel (a): relative excess SSR per round, smooth-kernel suite.
    # After a trial terminates, its terminal value is carried forward so the
    # per-round median is over all trials at every round.  Terminal values
    # sit at the roundoff scale (some are nonpositive); they are clipped at
    # the display floor, which the caption discloses.
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
    ax1.set_xticks(range(1, max_r + 1))

    # Panel (b): rounds to termination, stacked by suite (the regimes are
    # nearly disjoint and pooling would hide that).  Colors: first four
    # slots of the validated categorical palette (adjacent-pair safe).
    suite_order = ["smooth", "lattice", "Gaussian", "duplicated"]
    suite_cols = {"smooth": "#2a78d6", "lattice": "#eb6834",
                  "Gaussian": "#1baf7a", "duplicated": "#eda100"}
    rounds_all = [r["rounds"] for recs in all_recs.values() for r in recs]
    lo, hi = min(rounds_all), max(rounds_all)
    xs = np.arange(lo, hi + 1)
    bottom = np.zeros(len(xs))
    for name in suite_order:
        counts = np.array([sum(1 for r in all_recs[name]
                               if r["rounds"] == k) for k in xs])
        ax2.bar(xs, counts, bottom=bottom, color=suite_cols[name],
                edgecolor="white", lw=0.8, label=name)
        bottom += counts
    ax2.legend(fontsize=6.5, frameon=False, loc="upper right",
               handlelength=1.0, labelspacing=0.3)
    ax2.set_xlabel("rounds to termination", fontsize=9, color=INK)
    ax2.set_ylabel("trials", fontsize=9, color=INK)
    ax2.set_title("(b) rounds to termination", fontsize=9, color=INK)
    ax2.set_xticks(range(lo, hi + 1))

    for ax in (ax1, ax2):
        ax.spines[["top", "right"]].set_visible(False)
        ax.spines[["left", "bottom"]].set_color(MUTED)
        ax.tick_params(colors=MUTED, labelsize=7)
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

    print("\n--- LaTeX table rows (Table 1) ---")
    print(latex_row("smooth correlated kernels", smooth))
    print(latex_row("2-D lattice, interlaced subgrids", lattice))
    print(latex_row("i.i.d.\\ Gaussian", gauss))
    print(latex_row("duplicated columns", dup))

    all_v = [r["v_full"] for recs in (smooth, gauss, dup, lattice)
             for r in recs]
    print(f"\nmax v* across all 200 trials: {max(all_v):.4g}")
    term = [(r["vals"][-1] - r["v_full"]) / r["v_full"] for r in smooth]
    print(f"smooth terminal relative excess: min {min(term):.3g}, "
          f"max {max(term):.3g}")

    # Rounds of the three random-block suites relative to the 3-7 range
    # reported in the SC'06 paper (reference [9] of the manuscript).
    rb = smooth + gauss + dup
    in37 = sum(1 for r in rb if 3 <= r["rounds"] <= 7)
    print(f"random-block suites: {in37}/{len(rb)} trials inside 3-7 rounds; "
          f"span {min(r['rounds'] for r in rb)}-"
          f"{max(r['rounds'] for r in rb)}")

    # Exact-feasibility cross-tabs (v* at roundoff zero).
    feas_thresh = 1e-12
    for name, recs in (("gaussian", gauss), ("duplicated", dup)):
        feas = [r for r in recs if r["v_full"] < feas_thresh]
        nfeas = [r for r in recs if r["v_full"] >= feas_thresh]
        def _tab(rs):
            t = {}
            for r in rs:
                t[r["reason"]] = t.get(r["reason"], 0) + 1
            m = sum(r["supp_match"] for r in rs)
            return t, m
        tf, mf = _tab(feas)
        tn, mn = _tab(nfeas)
        print(f"{name}: exactly feasible {len(feas)}/{len(recs)} "
              f"(reasons {tf}, supp match {mf}); "
              f"v*>0: {len(nfeas)} (reasons {tn}, supp match {mn})")
    n_exact_feas = sum(1 for recs in (smooth, gauss, dup, lattice)
                       for r in recs if r["v_full"] < feas_thresh)
    print(f"exactly feasible trials overall: {n_exact_feas}/200")

    # A posteriori certified gap (Prop 2 with M = ||x*||_1 from the
    # reference solve) for the runs that terminated on the stall rule.
    # Prop 2 bounds F; report in v = 2F units.
    worst = 0.0
    n_stall = 0
    m_lo, m_hi, d_hi = np.inf, 0.0, 0.0
    for recs in (smooth, gauss, dup, lattice):
        for r in recs:
            if r["reason"] == "value_stall":
                n_stall += 1
                worst = max(worst,
                            2.0 * (r["delta_abs"] * r["x1"] + r["eps_abs"]))
                m_lo, m_hi = min(m_lo, r["x1"]), max(m_hi, r["x1"])
                d_hi = max(d_hi, r["delta_abs"])
    print(f"certified gap bound 2(delta*||x*||_1 + eps) over the "
          f"{n_stall} stall-rule runs: max {worst:.3g}; "
          f"M = ||x*||_1 in [{m_lo:.8g}, {m_hi:.8g}]; "
          f"max absolute delta {d_hi:.3g}")

    sp = np.array([(r["v_sp"] - r["v_full"]) / r["v_full"] for r in smooth])
    print(f"smooth suite: single-pass relative excess median "
          f"{np.median(sp):.4f}, max {np.max(sp):.4f}; "
          f"suboptimal in {sum(r['sp_subopt'] for r in smooth)}/60")
    spl = np.array([(r["v_sp"] - r["v_full"]) / r["v_full"] for r in lattice])
    print(f"lattice suite: single-pass relative excess median "
          f"{np.median(spl):.4f}, max {np.max(spl):.4f}; "
          f"suboptimal in {sum(r['sp_subopt'] for r in lattice)}/40")

    print("\n--- LaTeX table rows (Table 2, scaling) ---")
    rng3 = np.random.default_rng(20260809)
    for row in run_scaling([960, 3840, 15360], 6, rng3):
        print(row)

    print()
    rng4 = np.random.default_rng(20260810)
    cycling_probe(rng4)

    make_figure(smooth, {"smooth": smooth, "lattice": lattice,
                         "Gaussian": gauss, "duplicated": dup})


if __name__ == "__main__":
    main()
