import NnlsDc.Basic

/-!
# Proposition 2 (inexact solves and pricing) and the data-only bound on `‖x*‖₁`
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Problem

variable {P : Problem ι E}

/-- **Proposition 2.**  Let `x ≥ 0`, with pricing residual `max_j a_jᵀ r ≤ δ`
and complementarity residual `(Aᵀ r)ᵀ x ≥ -ε`.  Then for every global
minimizer `x*`, `F(x) - v* ≤ δ ‖x*‖₁ + ε` and
`‖Ax - Ax*‖² ≤ 2 (δ ‖x*‖₁ + ε)`. -/
theorem prop2 {x xs : ι → ℝ} (hx : ∀ j, 0 ≤ x j) {δ ε : ℝ}
    (hδ : ∀ j, P.price x j ≤ δ) (hε : -ε ≤ ∑ j, x j * P.price x j)
    (hxs : P.IsGlobalMin xs) :
    P.F x - P.F xs ≤ δ * ∑ j, |xs j| + ε ∧
      ‖P.fit x - P.fit xs‖ ^ 2 ≤ 2 * (δ * ∑ j, |xs j| + ε) := by
  have habs : ∑ j, |xs j| = ∑ j, xs j :=
    Finset.sum_congr rfl fun j _ => abs_of_nonneg (hxs.1.1 j)
  have hsplit : ∑ j, (xs j - x j) * P.price x j =
      ∑ j, xs j * P.price x j - ∑ j, x j * P.price x j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hprice : ∑ j, xs j * P.price x j ≤ δ * ∑ j, xs j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by nlinarith [hxs.1.1 j, hδ j]
  have hfirst : P.F x - P.F xs ≤ δ * ∑ j, |xs j| + ε := by
    have := F_ge (P := P) x xs
    rw [habs]
    linarith
  refine ⟨hfirst, ?_⟩
  have := F_ge_of_KKT (KKT_of_isMin hxs) (feasible_univ_iff.mpr hx)
  linarith

/-- At a global minimizer, `Ax* ⟂ r*`, so `‖b‖² = ‖Ax*‖² + ‖r*‖²` and
`‖Ax*‖ ≤ ‖b‖`. -/
theorem norm_fit_le {xs : ι → ℝ} (hxs : P.IsGlobalMin xs) : ‖P.fit xs‖ ≤ ‖P.b‖ := by
  have hk := KKT_of_isMin hxs
  have h0 : ⟪P.fit xs, P.res xs⟫_ℝ = 0 := by
    have : ⟪P.fit xs, P.res xs⟫_ℝ = ∑ j, xs j * P.price xs j := by
      simp only [fit, sum_inner, real_inner_smul_left, price]
    rw [this]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : xs j = 0
    · rw [h, zero_mul]
    · rw [hk.2 j h, mul_zero]
  have hb : P.b = P.fit xs + P.res xs := by simp [res]
  have hsq : ‖P.b‖ ^ 2 = ‖P.fit xs‖ ^ 2 + ‖P.res xs‖ ^ 2 := by
    rw [hb, norm_add_sq_real, h0]
    ring
  have : ‖P.fit xs‖ ^ 2 ≤ ‖P.b‖ ^ 2 := by nlinarith [sq_nonneg ‖P.res xs‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

/-- Data-only bound on `‖x*‖₁`: if `⟪u, a_j⟫ ≥ c` for every column, then
`c ‖x*‖₁ ≤ ‖u‖ ‖b‖` for every global minimizer. -/
theorem l1_bound {xs : ι → ℝ} (hxs : P.IsGlobalMin xs) (u : E) {c : ℝ}
    (hu : ∀ j, c ≤ ⟪u, P.a j⟫_ℝ) : c * ∑ j, |xs j| ≤ ‖u‖ * ‖P.b‖ := by
  have habs : ∑ j, |xs j| = ∑ j, xs j :=
    Finset.sum_congr rfl fun j _ => abs_of_nonneg (hxs.1.1 j)
  rw [habs]
  calc c * ∑ j, xs j = ∑ j, xs j * c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j, xs j * ⟪u, P.a j⟫_ℝ :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hu j) (hxs.1.1 j)
    _ = ⟪u, P.fit xs⟫_ℝ := by simp only [fit, inner_sum, real_inner_smul_right]
    _ ≤ ‖u‖ * ‖P.fit xs‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * ‖P.b‖ := mul_le_mul_of_nonneg_left (norm_fit_le hxs) (norm_nonneg _)

/-- The resulting certificate bound `M = ‖u‖ ‖b‖ / c ≥ ‖x*‖₁` (for `c > 0`). -/
theorem l1_le_M {xs : ι → ℝ} (hxs : P.IsGlobalMin xs) (u : E) {c : ℝ} (hc : 0 < c)
    (hu : ∀ j, c ≤ ⟪u, P.a j⟫_ℝ) : ∑ j, |xs j| ≤ ‖u‖ * ‖P.b‖ / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact l1_bound hxs u hu

/-- The all-ones vector of `ℝ^m`. -/
noncomputable def ones (m : ℕ) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun _ => 1

lemma norm_ones (m : ℕ) : ‖ones m‖ = Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  simp [ones]

lemma inner_ones {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) : ⟪ones m, v⟫_ℝ = ∑ i, v i := by
  simp [ones, PiLp.inner_apply]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The article's data-only bound in coordinates (Section 6): for columns in
`ℝ^m` whose sums are at least `c > 0` (take `c = min_j 1ᵀa_j`),
`‖x*‖₁ ≤ M = √m ‖b‖₂ / c` for every global minimizer. -/
theorem l1_le_M_coord {m : ℕ} {P : Problem ι (EuclideanSpace ℝ (Fin m))} {xs : ι → ℝ}
    (hxs : P.IsGlobalMin xs) {c : ℝ} (hc : 0 < c) (hcol : ∀ j, c ≤ ∑ i, P.a j i) :
    ∑ j, |xs j| ≤ Real.sqrt m * ‖P.b‖ / c := by
  have := l1_le_M hxs (ones m) hc fun j => by rw [inner_ones]; exact hcol j
  rwa [norm_ones] at this

end Problem

end NnlsDc
