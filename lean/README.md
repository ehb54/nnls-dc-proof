# Lean 4 formalization

A machine-checked formalization, in Lean 4 with Mathlib, of the results of
*Exactness of an iterated divide-and-conquer method for large-scale
nonnegative least squares*. About 1,500 lines, with no `sorry`. Every result
in the table below depends only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); `AxiomCheck.lean` prints them for each.

Pinned versions: Lean `v4.36.0` (`lean-toolchain`), Mathlib `v4.36.0`
(commit `fc4f59e`, `lake-manifest.json`).

## Building

    lake exe cache get        # Mathlib's prebuilt cache (~0.5 GB download, ~7 GB unpacked)
    lake build                # this library: about 30 s on a 64-core Linux host
    lake env lean AxiomCheck.lean

`lake exe cache get` compiles a small Mathlib tool with the toolchain's
bundled clang, which needs glibc 2.29 or newer. On an older system (for
example Rocky/RHEL 8, glibc 2.28) build just that tool in a newer container,
or on another machine; the library itself then builds natively, since `lean`
needs no C compiler.

## The article's results in Lean

Names are in the `NnlsDc` namespace.

| Article | Lean | File |
|---|---|---|
| objective `F`, residual, prices, `P(C)`, `Val(C)` | `Problem.F`, `Problem.res`, `Problem.price`, `Problem.IsMin`, `Problem.Val` | `Basic` |
| expansion `F(y) = F(x) - Σ (y_j - x_j) a_jᵀr + ‖A(y-x)‖²/2` | `Problem.F_expand` | `Basic` |
| Lemma 1, existence | `Problem.exists_isMin` | `Existence` |
| Lemma 1, uniqueness of the fit | `Problem.IsMin.fit_eq` | `Basic` |
| Lemma 2 (optimality conditions) | `Problem.isMin_iff_KKT` | `Basic` |
| Lemma 3 (pricing) | `Problem.isGlobalMin_of_price_nonpos` | `Basic` |
| Lemma 4 (restriction) | `Problem.val_anti`, `Problem.IsMin.restrict`, `Problem.IsMin.val_restrict` | `Basic` |
| Algorithms 1–2, conditions (H1)–(H3) | `Tree`, `Tree.WF`, `Run` | `Algorithm` |
| Lemma 5 (tree descent) | `Tree.WF.F_le_child`, `Tree.WF.F_sol_le` | `Algorithm` |
| Lemma 6 (monotone rounds) | `Run.v_succ_le` | `Algorithm` |
| Lemma 7 (strict descent off the optimum) | `Run.v_succ_lt` | `Algorithm` |
| Theorem 1(a) | `Run.theorem1_a` | `Algorithm` |
| Theorem 1(b), soundness of the stopping rule | `Run.theorem1_b`, `Run.stop_sound` | `Algorithm` |
| Theorem 1(c), halting at round `K + 1` | `Run.theorem1_c` | `Algorithm` |
| Theorem 2 | `Run.theorem2`, `Run.theorem2_unique`, `Problem.isGlobalMin_iff`, `Problem.eq_of_isGlobalMin` | `Outputs` |
| Proposition 1 | `Counterexample.single_pass`, `Counterexample.single_pass_tree`, `Counterexample.single_pass_supp`, `Counterexample.merged_residual`, `Counterexample.optimum`, `Counterexample.refinement_round`, `Counterexample.two_rounds` | `Counterexample` |
| Proposition 2 | `Problem.prop2` | `Inexact` |
| Section 6, data-only bound on `‖x*‖₁` | `Problem.l1_bound`, `Problem.l1_le_M`, `Problem.l1_le_M_coord` | `Inexact` |
| Section 8, re-chunking instance | `Rechunk.stops_suboptimal` | `Rechunk` |

## How the setting is modeled

- The columns live in any real inner product space (`ℝ^m` in the article),
  indexed by any finite type; `fit x = Σ_j x_j a_j` is `Ax`.
- One round of Algorithm 1 is a *solved merge tree*. Each node records the
  candidate set it solved and the solution it returned, and a merge node may
  have any number of children. A run of Algorithm 2 is a sequence of such
  trees, rounds `k ≥ 1`, with round 1 the non-iterated pass.
- A `Run` is an infinite sequence of rounds, while Algorithm 2 halts. A run
  that halts extends to a `Run`, since Lemma 1 (`Problem.exists_isMin`)
  supplies the minimizers of any further rounds, and the results concern
  only rounds up to the halting round `K + 1`.
- (H1)–(H3) are hypotheses on a run, and nothing else is assumed. Partitions
  and merge trees may change from round to round. Which minimizer a node
  returns is arbitrary, and may differ between nodes that solve the same
  candidate set.
- `Counterexample` takes Proposition 1's single pass in its canonical
  instantiation, leaves `S₁` and `S₂` and an atomic merge, as the article
  does: (H2)–(H3) also admit the candidate set `{1, 2, 3}`, which fits `b`
  exactly. `two_rounds` states both rounds for a `Run`.
- `Rechunk` keeps (H1) and (H2) but drops (H3). It exhibits the article's
  two-column instance, where both stopping tests fire at `F = 1/4` while
  `v* = 0`.

Where the formal statements differ from the article, they are more general:

- A run needs at least one leaf per round; the article has `p ≥ 2`.
- Proposition 2 needs no sign conditions on `δ` and `ε`.
- The `‖x*‖₁` bound holds for any vector `u` with `⟪u, a_j⟫ ≥ c > 0`.
  `l1_le_M_coord` takes `u = 1` in `ℝ^m`, which gives the article's
  `M = √m ‖b‖₂ / min_j 1ᵀa_j`.

The existence half of Lemma 1 is proved differently from the article.
Instead of citing closedness of finitely generated cones, it inducts on the
candidate set, using an unconstrained least-squares minimizer (an orthogonal
projection) and convexity of `F` along segments. Theorems 1 and 2 do not use
it, because (H1) supplies the minimizers; it shows that (H1) can always be
met.

Not formalized:
- the numerical experiments of Section 7;
- Remark 1's observation that the support test alone can cycle;
- the bound of Section 3 on the support size of basic solutions.

## License

MIT, like the repository's scripts (see `../LICENSE`).
