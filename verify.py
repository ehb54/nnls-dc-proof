#!/usr/bin/env python3
"""Numerical companion to the equivalence proof for divide-and-conquer NNLS.

Implements the algorithm of Brookes, Boppana & Demeler,
"Computing Large Sparse Multivariate Optimization Problems with an
Application in Biophysics" (SC'06), Text 1 + Section 3.2 iterative variant:

    round(R):  for each block S_i of a partition of S, solve NNLS on S_i U R
               (f returns the support = "parameters that contribute");
               merge the returned supports (union, in stages of the given
               fan-in) and solve NNLS on the union; the final support is
               the new R.
    iterate rounds until the result no longer varies.

Conventions.  All values reported by this code are UNHALVED squared residual
norms  ssr(x) = ||Ax - b||^2  (the manuscript's objective is F = ssr/2;
relative quantities are unaffected).

Floating-point stopping rule (dc_nnls).  A run terminates when
  (a) the returned support is unchanged from the previous round
      ("support_fixed"), or
  (b) the objective fails to improve by more than a relative tolerance of
      1e-12 ("value_stall"), or
  (c) max_rounds is reached ("max_rounds"; never observed).
The stopping reason is returned with the result.

Checks performed here:
  1. The explicit 4-column counterexample showing a SINGLE pass (R0 = empty,
     no refinement) is NOT equivalent to the full problem.
  2. That one refinement round repairs the counterexample, and the fixed
     point satisfies the full-problem KKT conditions.
  3. Randomized trials verifying, at termination:
        value(dc) == value(full NNLS)   (to numerical tolerance)
        BOTH KKT residuals of the manuscript's Proposition 2:
          delta = max(0, max_j a_j^T r)   (pricing)
          eps   = max(0, -(A^T r)^T x)    (complementarity)
        Note pricing alone is NOT sufficient for optimality (A=I, b=1,
        x=2 has a_j^T r <= 0 but is not optimal); both are asserted.
  4. Genuine per-edge monotonicity: at EVERY merge node the parent value is
     asserted <= the minimum of its children's values (Lemma "tree descent"),
     and each round's value is asserted <= the previous round's value
     (Lemma "monotone rounds"), all with relative slack 1e-9.
"""

import numpy as np
from scipy.optimize import nnls as scipy_nnls


# ----------------------------------------------------------------- primitives

def nnls_on(A, b, C):
    """Exact NNLS restricted to column subset C; returns full-length x."""
    n = A.shape[1]
    x = np.zeros(n)
    C = sorted(C)
    if C:
        sol, _ = scipy_nnls(A[:, C], b)
        x[np.asarray(C, dtype=int)] = sol
    return x


def f_support(A, b, C):
    """The paper's f: solve on C, return (support of solution, solution)."""
    x = nnls_on(A, b, C)
    return set(np.flatnonzero(x > 0.0).tolist()), x


def ssr(A, b, x):
    r = A @ x - b
    return float(r @ r)


def kkt_residuals(A, b, x):
    """Both KKT residuals of the full problem at x:
        delta = max(0, max_j a_j^T r)   (pricing residual)
        eps   = max(0, -(A^T r)^T x)    (complementarity residual)
    x >= 0 is a global solution iff delta = eps = 0 (up to roundoff).
    Pricing alone is not sufficient: A=I, b=1, x=2 has delta = 0 but
    eps = 1 and is not optimal."""
    g = A.T @ (b - A @ x)
    delta = max(0.0, float(np.max(g)))
    eps = max(0.0, float(-(g @ x)))
    return delta, eps


# ------------------------------------------------------------------ algorithm

def dc_round(A, b, blocks, R, fan_in=2, check=True):
    """One round: leaves S_i U R, then ATOMIC merge tree (unions of whole
    returned supports, given fan-in), final solve on the root support.
    With check=True, asserts the parent<=min(children) inequality at every
    internal node.  Returns (support, solution, diagnostics)."""
    supports, vals = [], []
    for S in blocks:
        U, y = f_support(A, b, set(S) | set(R))
        supports.append(U)
        vals.append(ssr(A, b, y))
    leaf_vals = list(vals)
    node_vals = []
    while len(supports) > 1:
        nxt_s, nxt_v = [], []
        for i in range(0, len(supports), fan_in):
            kid_vals = vals[i:i + fan_in]
            C = set().union(*supports[i:i + fan_in])
            U, y = f_support(A, b, C)
            v = ssr(A, b, y)
            if check:
                assert v <= min(kid_vals) + 1e-9 * (1.0 + abs(v)), \
                    "tree-descent violated at merge node"
            nxt_s.append(U)
            nxt_v.append(v)
            node_vals.append(v)
        supports, vals = nxt_s, nxt_v
    U, x = f_support(A, b, supports[0] if supports else set())
    v = ssr(A, b, x)
    if check and vals:
        assert v <= min(vals) + 1e-9 * (1.0 + abs(v)), \
            "tree-descent violated at root"
    return U, x, {"leaf_vals": leaf_vals, "node_vals": node_vals, "v": v}


def dc_nnls(A, b, nblocks=None, blocks=None, iterative=True, fan_in=2,
            max_rounds=500, check_monotone=True):
    """Full D&C-NNLS.  Pass either nblocks (contiguous index blocks) or an
    explicit `blocks` partition (list of index lists, e.g. interlaced
    subgrids).  iterative=False reproduces the basic Text 1 scheme.
    Returns (x, support, per-round values, stopping reason)."""
    n = A.shape[1]
    if blocks is None:
        blocks = [list(B) for B in np.array_split(np.arange(n), nblocks)]
    R, x = set(), np.zeros(n)
    vals = []
    reason = "max_rounds"
    for _ in range(max_rounds):
        R_new, x_new, diag = dc_round(A, b, blocks, R, fan_in=fan_in,
                                      check=check_monotone)
        v_new = diag["v"]
        if check_monotone and vals:
            assert v_new <= vals[-1] + 1e-9 * (1.0 + abs(vals[-1])), \
                "round-to-round monotonicity violated"
        vals.append(v_new)
        stalled = len(vals) >= 2 and \
            vals[-1] >= vals[-2] - 1e-12 * max(1.0, abs(vals[-2]))
        fixed = (R_new == R)
        R, x = R_new, x_new
        if not iterative:
            reason = "single_pass"
            break
        if fixed:
            reason = "support_fixed"
            break
        if stalled:
            reason = "value_stall"
            break
    return x, R, vals, reason


# --------------------------------------------------------------- experiments

def counterexample():
    """4 columns in R^3, blocks {a1,a2} and {a3,a4}: the single pass discards
    a2 and a4, which the exact solution needs.  Values printed are unhalved
    SSR; the manuscript's objective F is SSR/2 (so F = 1/24 here)."""
    s = 1.0 / np.sqrt(2.0)
    # rows are (x, y, z) components: a1=(1,0,1)/sqrt2, a2=e1, a3=(0,1,1)/sqrt2, a4=e2
    A = np.array([
        [s, 1.0, 0.0, 0.0],
        [0.0, 0.0, s, 1.0],
        [s, 0.0, s, 0.0],
    ])
    b = np.array([1.0, 1.0, 1.5])

    x_full = nnls_on(A, b, range(4))
    v_full = ssr(A, b, x_full)

    x1, R1, vals1, _ = dc_nnls(A, b, nblocks=2, iterative=False)
    v1 = vals1[-1]
    viol1, _ = kkt_residuals(A, b, x1)

    xi, Ri, valsi, reason = dc_nnls(A, b, nblocks=2, iterative=True)
    vi = valsi[-1]

    print("== Counterexample (single pass vs full) ==")
    print(f"  full NNLS        : SSR = {v_full:.12f}")
    print(f"  single-pass D&C  : SSR = {v1:.12f}   support = {sorted(R1)}"
          f"   (exact SSR 1/12 = {1/12:.12f}; objective F = SSR/2 = 1/24)")
    print(f"  KKT violation at single-pass solution: max_j a_j'r = "
          f"{viol1:.12f}  (exact value 1/6 = {1/6:.12f}; >0 => not optimal)")
    print(f"  iterative D&C    : SSR = {vi:.12f}   rounds = {len(valsi)}  "
          f"stop = {reason}  per-round SSR = {[f'{v:.6g}' for v in valsi]}")
    assert v_full < 1e-24
    assert abs(v1 - 1.0 / 12.0) < 1e-12
    assert abs(viol1 - 1.0 / 6.0) < 1e-12
    assert vi < 1e-20
    print("  PASS: single pass strictly suboptimal; one refinement round"
          " restores the exact solution.\n")


def make_smooth_instance(rng, m=80, n=240, k_true=8, noise=0.02):
    """AUC-flavored design: overlapping Gaussian bump columns (smooth,
    nonnegative, highly correlated), sparse nonnegative truth, noisy data."""
    t = np.linspace(0.0, 1.0, m)
    centers = rng.uniform(0.0, 1.0, n)
    widths = rng.uniform(0.02, 0.15, n)
    A = np.exp(-0.5 * ((t[:, None] - centers[None, :]) / widths[None, :]) ** 2)
    x_true = np.zeros(n)
    idx = rng.choice(n, size=k_true, replace=False)
    x_true[idx] = rng.uniform(0.5, 2.0, k_true)
    b = A @ x_true + noise * rng.standard_normal(m)
    return A, b


def make_gaussian_instance(rng, m=40, n=160):
    A = rng.standard_normal((m, n))
    b = rng.standard_normal(m) * 2.0
    return A, b


def make_duplicate_instance(rng, m=30, n=120):
    """Exact duplicate columns => non-unique minimizers; value equivalence
    must still hold even though supports may differ."""
    half = n // 2
    A0 = rng.standard_normal((m, half))
    A = np.hstack([A0, A0])  # every column duplicated
    x_true = np.zeros(n)
    idx = rng.choice(half, size=5, replace=False)
    x_true[idx] = rng.uniform(0.5, 2.0, 5)
    b = A @ x_true + 0.05 * rng.standard_normal(m)
    return A, b


# 2-D lattice surrogate of a 2DSA grid, with interlaced subgrid partition
# (every stride_c-th center index crossed with every stride_w-th width index),
# mirroring the moving-grid partitioning of the SC'06 paper.
LAT_NC, LAT_NW = 20, 12          # lattice: 20 centers x 12 widths = 240 cols
LAT_SC, LAT_SW = 4, 2            # strides -> 8 interlaced subgrids


def make_lattice_instance(rng, m=80, k_true=8, noise=0.02):
    t = np.linspace(0.0, 1.0, m)
    centers = np.linspace(0.05, 0.95, LAT_NC)
    widths = np.geomspace(0.02, 0.15, LAT_NW)
    cc, ww = np.meshgrid(centers, widths, indexing="ij")  # lexicographic
    cc, ww = cc.ravel(), ww.ravel()
    A = np.exp(-0.5 * ((t[:, None] - cc[None, :]) / ww[None, :]) ** 2)
    n = A.shape[1]
    x_true = np.zeros(n)
    idx = rng.choice(n, size=k_true, replace=False)
    x_true[idx] = rng.uniform(0.5, 2.0, k_true)
    b = A @ x_true + noise * rng.standard_normal(m)
    return A, b


def interlaced_blocks():
    """Partition of the lattice into LAT_SC*LAT_SW interlaced subgrids."""
    blocks = []
    for a in range(LAT_SC):
        for c in range(LAT_SW):
            blocks.append([i * LAT_NW + j
                           for i in range(a, LAT_NC, LAT_SC)
                           for j in range(c, LAT_NW, LAT_SW)])
    return blocks


def run_trials(name, maker, n_trials, rng, nblocks_choices=(4, 8, 16),
               fan_in_choices=(2, 4), blocks_fn=None):
    rounds_hist = []
    sp_gaps = []
    reasons = {}
    worst_val_err = 0.0
    worst_delta = -np.inf
    worst_eps = -np.inf
    for trial in range(n_trials):
        A, b = maker(rng)
        scale = max(1.0, float(np.max(np.abs(A.T @ b))))
        x_full = nnls_on(A, b, range(A.shape[1]))
        v_full = ssr(A, b, x_full)

        blocks = blocks_fn() if blocks_fn else None
        nb = None if blocks else int(rng.choice(nblocks_choices))
        fi = int(rng.choice(fan_in_choices))

        _, _, vals1, _ = dc_nnls(A, b, nblocks=nb, blocks=blocks,
                                 iterative=False, fan_in=fi)
        sp_gaps.append((vals1[-1] - v_full) / max(v_full, 1e-30))

        x, R, vals, reason = dc_nnls(A, b, nblocks=nb, blocks=blocks,
                                     iterative=True, fan_in=fi)
        v = vals[-1]
        val_err = abs(v - v_full) / max(1.0, v_full)
        delta, eps = kkt_residuals(A, b, x)
        delta_s = delta / scale
        eps_s = eps / max(1.0, v_full)
        worst_val_err = max(worst_val_err, val_err)
        worst_delta = max(worst_delta, delta_s)
        worst_eps = max(worst_eps, eps_s)
        rounds_hist.append(len(vals))
        reasons[reason] = reasons.get(reason, 0) + 1
        assert val_err < 1e-7, (name, trial, v, v_full)
        assert delta_s < 1e-7, (name, trial, delta_s)
        assert eps_s < 1e-7, (name, trial, eps_s)
    sp_gaps = np.array(sp_gaps)
    print(f"== {name}: {n_trials} trials ==")
    print(f"  rounds to termination: min {min(rounds_hist)}, "
          f"median {int(np.median(rounds_hist))}, max {max(rounds_hist)}")
    print(f"  stopping reasons: {reasons}")
    print(f"  worst |value(dc) - value(full)| (rel): {worst_val_err:.3e}")
    print(f"  worst scaled pricing residual delta: {worst_delta:.3e}")
    print(f"  worst scaled complementarity residual eps: {worst_eps:.3e}")
    print(f"  single-pass suboptimal (excess > 1e-8 rel): "
          f"{int(np.sum(sp_gaps > 1e-8))}/{n_trials}")
    print("  PASS: iterative D&C matched full NNLS in every trial.\n")


def main():
    counterexample()
    rng = np.random.default_rng(20260807)
    run_trials("AUC-like smooth correlated kernels", make_smooth_instance,
               60, rng)
    run_trials("iid Gaussian designs", make_gaussian_instance, 60, rng)
    run_trials("exact duplicate columns (non-unique optima)",
               make_duplicate_instance, 40, rng)
    rng2 = np.random.default_rng(20260808)
    run_trials("2-D lattice, interlaced subgrid partition",
               make_lattice_instance, 40, rng2, blocks_fn=interlaced_blocks)
    print("All checks passed.")


if __name__ == "__main__":
    main()
