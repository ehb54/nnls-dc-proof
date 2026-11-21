#!/usr/bin/env python3
"""Uniqueness check for the two kernel suites (manuscript, Section 7).

Theorem 2: with r* the optimal residual and Z = {j : a_j^T r* = 0}, the
minimizer is unique when the columns {a_j : j in Z} are linearly
independent.  This script regenerates the 100 kernel-suite instances of
experiments.py (smooth kernels, seed 20260807, and the interlaced lattice,
seed 20260808, in its draw order), takes the support S of each full-grid
floating-point solve, and checks the criterion in exact arithmetic on the
instances' double-precision data:

  * each column of A, and b, is scaled by a power of 2 to integers, which
    changes no support, no sign of a price and no rank;
  * the least-squares problem on S is solved exactly by fraction-free
    (Bareiss) elimination of its Gram matrix, whose leading minors are all
    positive exactly when the columns of S are independent;
  * the solution must be positive on S and every other column must price
    strictly negative.  It then satisfies the optimality conditions (2)
    exactly, so it is a global minimizer, Z = S, and Theorem 2 applies.

It also prints the condition numbers of A_Z and, as an identity check, the
data-only M of Section 6, whose range experiments.py prints for the same
instances.  The exact part takes about 7 CPU-minutes and runs in parallel.
"""

from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

import numpy as np

from verify import nnls_on, make_smooth_instance, make_lattice_instance


def kernel_instances():
    """The smooth and lattice instances of experiments.py.  Its run_suite
    draws the instance, then the block count (unless the blocks are fixed),
    then the fan-in; the same draws are made here."""
    rng = np.random.default_rng(20260807)
    for _ in range(60):
        A, b = make_smooth_instance(rng)
        rng.choice((4, 8, 16))
        rng.choice((2, 4))
        yield "smooth", A, b
    rng2 = np.random.default_rng(20260808)
    for _ in range(40):
        A, b = make_lattice_instance(rng2)
        rng2.choice((2, 4))
        yield "lattice", A, b


def int_vector(v):
    """The integer vector 2^e v for the least e >= 0, and e."""
    fr = [Fraction(float(t)) for t in v]
    den = max(f.denominator for f in fr)
    return [f.numerator * (den // f.denominator) for f in fr], den.bit_length() - 1


def exact_check(A, b, S):
    """Exact check at the support S.  Returns None if the columns of S are
    dependent; otherwise whether the restricted solution is positive and
    stationary, whether every other column prices strictly negative, the
    number of exact zero prices off S, and the smallest exact |a_j^T r*|
    off S (unscaled)."""
    n = A.shape[1]
    cols, ecol = zip(*(int_vector(A[:, j]) for j in range(n)))
    bi, eb = int_vector(b)
    k = len(S)
    M = [[sum(p * q for p, q in zip(cols[a], cols[c])) for c in S]
         + [sum(p * q for p, q in zip(cols[a], bi))] for a in S]
    prev = 1
    for c in range(k):
        if M[c][c] == 0:
            return None
        for r in range(c + 1, k):
            Mr, Mc, f = M[r], M[c], M[r][c]
            for j in range(c + 1, k + 1):
                Mr[j] = (Mr[j] * Mc[c] - f * Mc[j]) // prev
            Mr[c] = 0
        prev = M[c][c]
    D = M[k - 1][k - 1]
    X = [0] * k
    for i in reversed(range(k)):
        q, rem = divmod(M[i][k] * D
                        - sum(M[i][j] * X[j] for j in range(i + 1, k)), M[i][i])
        assert rem == 0
        X[i] = q
    rD = [v * D for v in bi]
    for a, xa in zip(S, X):
        rD = [ri - xa * ai for ri, ai in zip(rD, cols[a])]
    pD = [sum(ai * ri for ai, ri in zip(cols[j], rD)) for j in range(n)]
    in_S = set(S)
    off = [j for j in range(n) if j not in in_S]
    return {
        "positive": D > 0 and min(X) > 0,
        "stationary": all(pD[j] == 0 for j in S),
        "priced_out": all(pD[j] < 0 for j in off),
        "n_zero_off": sum(pD[j] == 0 for j in off),
        "min_gap": float(min(-Fraction(pD[j], D) / 2 ** (ecol[j] + eb)
                             for j in off)),
    }


def main():
    rows, jobs = [], []
    for suite, A, b in kernel_instances():
        n = A.shape[1]
        x = nnls_on(A, b, range(n))
        S = [int(j) for j in np.flatnonzero(x > 0.0)]
        sv = np.linalg.svd(A[:, S], compute_uv=False)
        m_data = (np.sqrt(A.shape[0]) * np.linalg.norm(b)
                  / float(np.min(A.sum(axis=0))))
        rows.append({
            "suite": suite,
            "k": len(S),
            "cond": float(sv[0] / sv[-1]),
            "m_data": float(m_data),
            "ratio": float(m_data / np.sum(x)),
            "scale": max(1.0, float(np.max(np.abs(A.T @ b)))),
        })
        jobs.append((A, b, S))
    with ProcessPoolExecutor() as pool:
        exact = list(pool.map(exact_check, *zip(*jobs)))

    for suite in ("smooth", "lattice"):
        rs = [r for r in rows if r["suite"] == suite]
        conds = [r["cond"] for r in rs]
        print(f"[{suite}] {len(rs)} instances: support sizes "
              f"{min(r['k'] for r in rs)}-{max(r['k'] for r in rs)}; "
              f"cond(A_Z) {min(conds):.3g} to {max(conds):.3g}")
    print(f"identity check (experiments.py prints the same): data-only M in "
          f"[{min(r['m_data'] for r in rows):.4g}, "
          f"{max(r['m_data'] for r in rows):.4g}]; M/||x*||_1 in "
          f"[{min(r['ratio'] for r in rows):.4f}, "
          f"{max(r['ratio'] for r in rows):.4f}]")
    N = len(rows)
    ok = [e is not None for e in exact]
    count = lambda key: sum(bool(e and e[key]) for e in exact)
    gap = min(e["min_gap"] / r["scale"] for e, r in zip(exact, rows) if e)
    print(f"exact arithmetic on the data: the columns of the support are "
          f"independent in {sum(ok)}/{N}; the restricted solution is positive "
          f"in {count('positive')}/{N} and stationary in "
          f"{count('stationary')}/{N}; every other column prices strictly "
          f"negative in {count('priced_out')}/{N} (exact zero prices off the "
          f"support: {sum(e['n_zero_off'] for e in exact if e)})")
    print(f"smallest exact |a_j^T r*| off the support, relative to "
          f"max(1, ||A^T b||_inf): {gap:.2g}")
    assert all(ok) and count("positive") == N and count("stationary") == N
    assert count("priced_out") == N
    print(f"so in all {N} instances the support is Z, its columns are "
          f"independent, and the minimizer is unique (Theorem 2)")


if __name__ == "__main__":
    main()
