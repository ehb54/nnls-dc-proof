#!/usr/bin/env python3
"""Numerical companion to the equivalence proof for divide-and-conquer NNLS.

Implements the algorithm of Brookes, Boppana & Demeler,
"Computing Large Sparse Multivariate Optimization Problems with an
Application in Biophysics" (SC'06), Text 1 + Section 3.2 iterative variant:

    round(R):  for each block S_i of a partition of S, solve NNLS on S_i U R
               (f returns the support = "parameters that contribute");
               merge the returned supports (union, optionally in stages) and
               solve NNLS on the union; the final support is the new R.
    iterate rounds until the result no longer varies (R fixed).

Checks performed here:
  1. The explicit 4-column counterexample showing a SINGLE pass (R0 = empty,
     no refinement) is NOT equivalent to the full problem.
  2. That one refinement round repairs the counterexample, and the
     "results no longer vary" fixed point satisfies the full-problem KKT
     conditions (global optimality certificate).
  3. Randomized trials (AUC-like smooth correlated kernels, iid Gaussian,
     exact duplicate columns) verifying, at the fixed point:
        value(dc) == value(full NNLS)   (to numerical tolerance)
        max_j a_j^T (b - A x_dc) <= tol (direct global KKT certificate)
     plus statistics: rounds to convergence, single-pass suboptimality gap.
  4. Per-round monotonicity of the objective (Lemma: tree descent), and the
     strict-descent property while KKT violations remain.
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


def kkt_violation(A, b, x):
    """max_j a_j^T (b - A x).  <= 0 (up to roundoff) iff x is a global
    solution of the FULL problem (KKT / pricing test)."""
    return float(np.max(A.T @ (b - A @ x)))


# ------------------------------------------------------------------ algorithm

def dc_round(A, b, blocks, R, fan_in=2):
    """One round: leaves S_i U R, then ATOMIC merge tree (unions of whole
    returned supports, fan-in given), final solve on the last union.
    Returns (support, solution, diagnostics)."""
    leaf_vals = []
    supports = []
    for S in blocks:
        U, y = f_support(A, b, set(S) | set(R))
        supports.append(U)
        leaf_vals.append(ssr(A, b, y))
    node_vals = []
    while len(supports) > 1:
        nxt = []
        for i in range(0, len(supports), fan_in):
            C = set().union(*supports[i:i + fan_in])
            U, y = f_support(A, b, C)
            nxt.append(U)
            node_vals.append(ssr(A, b, y))
        supports = nxt
    U, x = f_support(A, b, supports[0] if supports else set())
    v = ssr(A, b, x)
    return U, x, {"leaf_vals": leaf_vals, "node_vals": node_vals, "v": v}


def dc_nnls(A, b, nblocks, iterative=True, fan_in=2, max_rounds=500,
            check_monotone=True):
    """Full D&C-NNLS.  iterative=False reproduces the basic Text 1 scheme
    (single pass, R0 = empty).  Returns (x, support, per-round values)."""
    n = A.shape[1]
    blocks = [list(B) for B in np.array_split(np.arange(n), nblocks)]
    R, x = set(), np.zeros(n)
    vals = []
    for k in range(max_rounds):
        R_new, x_new, diag = dc_round(A, b, blocks, R, fan_in=fan_in)
        v_new = diag["v"]
        if check_monotone:
            # Lemma (tree descent): root value <= every leaf/internal value.
            slack = 1e-9 * (1.0 + abs(v_new))
            assert all(v_new <= lv + slack
                       for lv in diag["leaf_vals"] + diag["node_vals"]), \
                "tree-descent monotonicity violated"
            # Incumbent feasibility: round value cannot exceed previous value.
            if vals:
                assert v_new <= vals[-1] + 1e-9 * (1.0 + abs(vals[-1])), \
                    "round-to-round monotonicity violated"
        vals.append(v_new)
        stalled = len(vals) >= 2 and \
            vals[-1] >= vals[-2] - 1e-12 * max(1.0, abs(vals[-2]))
        fixed = (R_new == R)
        R, x = R_new, x_new
        if not iterative or fixed or stalled:
            break
    return x, R, vals


# --------------------------------------------------------------- experiments

def counterexample():
    """4 columns in R^3, blocks {a1,a2} and {a3,a4}: the single pass discards
    a2 and a4, which the exact solution needs."""
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

    x1, R1, vals1 = dc_nnls(A, b, nblocks=2, iterative=False)
    v1 = vals1[-1]
    viol1 = kkt_violation(A, b, x1)

    xi, Ri, valsi = dc_nnls(A, b, nblocks=2, iterative=True)
    vi = valsi[-1]

    print("== Counterexample (single pass vs full) ==")
    print(f"  full NNLS        : SSR = {v_full:.12f}")
    print(f"  single-pass D&C  : SSR = {v1:.12f}   support = {sorted(R1)}"
          f"   (exact value 1/12 = {1/12:.12f})")
    print(f"  KKT violation at single-pass solution: max_j a_j'r = "
          f"{viol1:.12f}  (exact value 1/6 = {1/6:.12f}; >0 => not optimal)")
    print(f"  iterative D&C    : SSR = {vi:.12f}   rounds = {len(valsi)}  "
          f"per-round SSR = {[f'{v:.6g}' for v in valsi]}")
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


def run_trials(name, maker, n_trials, rng, nblocks_choices=(4, 8, 16),
               fan_in_choices=(2, 4)):
    rounds_hist = []
    sp_gaps = []
    worst_val_err = 0.0
    worst_kkt = -np.inf
    for trial in range(n_trials):
        A, b = maker(rng)
        scale = max(1.0, float(np.max(np.abs(A.T @ b))))
        x_full = nnls_on(A, b, range(A.shape[1]))
        v_full = ssr(A, b, x_full)

        nb = int(rng.choice(nblocks_choices))
        fi = int(rng.choice(fan_in_choices))

        x1, _, vals1 = dc_nnls(A, b, nblocks=nb, iterative=False, fan_in=fi)
        sp_gaps.append((vals1[-1] - v_full) / max(v_full, 1e-30))

        x, R, vals = dc_nnls(A, b, nblocks=nb, iterative=True, fan_in=fi)
        v = vals[-1]
        val_err = abs(v - v_full) / max(1.0, v_full)
        kkt = kkt_violation(A, b, x) / scale
        worst_val_err = max(worst_val_err, val_err)
        worst_kkt = max(worst_kkt, kkt)
        rounds_hist.append(len(vals))
        assert val_err < 1e-7, (name, trial, v, v_full)
        assert kkt < 1e-7, (name, trial, kkt)
    sp_gaps = np.array(sp_gaps)
    print(f"== {name}: {n_trials} trials ==")
    print(f"  rounds to fixed point: min {min(rounds_hist)}, "
          f"median {int(np.median(rounds_hist))}, max {max(rounds_hist)}")
    print(f"  worst |value(dc) - value(full)| (rel): {worst_val_err:.3e}")
    print(f"  worst scaled KKT violation at fixed point: {worst_kkt:.3e}")
    print(f"  single-pass relative SSR excess: median {np.median(sp_gaps):.3e},"
          f" max {np.max(sp_gaps):.3e}, fraction >1e-8: "
          f"{np.mean(sp_gaps > 1e-8):.2f}")
    print("  PASS: iterative D&C matched full NNLS in every trial.\n")


def main():
    counterexample()
    rng = np.random.default_rng(20260807)
    run_trials("AUC-like smooth correlated kernels", make_smooth_instance,
               60, rng)
    run_trials("iid Gaussian designs", make_gaussian_instance, 60, rng)
    run_trials("exact duplicate columns (non-unique optima)",
               make_duplicate_instance, 40, rng)
    print("All checks passed.")


if __name__ == "__main__":
    main()
