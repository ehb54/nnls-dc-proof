import NnlsDc.Algorithm

/-!
# Theorem 2: equivalence of outputs

The terminal iterate of a run has the full computation's value, fit and
residual, with no uniqueness assumption; the global minimizers form the set
`{x ≥ 0 : supp x ⊆ Z, Ax = Ax*}`, `Z` the zero-priced columns; and when the
columns indexed by `Z` are linearly independent the minimizer is unique, so
the run returns exactly the full computation's amplitudes.
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Problem

variable {P : Problem ι E}

/-- `Z = {j : a_jᵀ r* = 0}`, the columns with zero price at `x*`. -/
noncomputable def zeroPrice (P : Problem ι E) (xs : ι → ℝ) : Finset ι :=
  univ.filter fun j => P.price xs j = 0

/-- Theorem 2, solution set: with `x*` a global minimizer, the global
minimizers are exactly the `x ≥ 0` with `supp x ⊆ Z` and `Ax = Ax*`. -/
theorem isGlobalMin_iff {xs : ι → ℝ} (hxs : P.IsGlobalMin xs) (x : ι → ℝ) :
    P.IsGlobalMin x ↔
      (∀ j, 0 ≤ x j) ∧ supp x ⊆ P.zeroPrice xs ∧ P.fit x = P.fit xs := by
  constructor
  · intro hx
    refine ⟨hx.1.1, fun j hj => ?_, hx.fit_eq hxs⟩
    simp only [zeroPrice, mem_filter, mem_univ, true_and]
    rw [← hx.price_eq hxs j]
    exact (KKT_of_isMin hx).2 j (mem_supp.mp hj)
  · rintro ⟨h0, -, hfit⟩
    have hF : P.F x = P.F xs := by simp only [F, hfit]
    refine ⟨feasible_univ_iff.mpr h0, fun y hy => ?_⟩
    rw [hF]
    exact hxs.2 y hy

/-- Theorem 2, uniqueness: if the zero-priced columns are linearly
independent, the global minimizer is unique. -/
theorem eq_of_isGlobalMin {xs : ι → ℝ} (hxs : P.IsGlobalMin xs)
    (hli : LinearIndependent ℝ fun j : P.zeroPrice xs => P.a j)
    {x : ι → ℝ} (hx : P.IsGlobalMin x) : x = xs := by
  have hxZ := ((isGlobalMin_iff hxs x).mp hx).2.1
  have hxsZ := ((isGlobalMin_iff hxs xs).mp hxs).2.1
  have off : ∀ j, j ∉ P.zeroPrice xs → x j = 0 ∧ xs j = 0 := fun j hj =>
    ⟨not_mem_supp.mp fun h => hj (hxZ h), not_mem_supp.mp fun h => hj (hxsZ h)⟩
  have hsum : ∑ j : P.zeroPrice xs, (x j - xs j) • P.a j = 0 := by
    have h1 : P.fit x - P.fit xs = 0 := sub_eq_zero.mpr (hx.fit_eq hxs)
    rw [fit_sub_fit xs x] at h1
    rw [← h1, Finset.sum_coe_sort (P.zeroPrice xs) fun j => (x j - xs j) • P.a j]
    refine Finset.sum_subset (subset_univ _) fun j _ hj => ?_
    rw [(off j hj).1, (off j hj).2, sub_self, zero_smul]
  have hzero := (Fintype.linearIndependent_iff.mp hli) (fun j => x j - xs j) hsum
  funext j
  by_cases hj : j ∈ P.zeroPrice xs
  · exact sub_eq_zero.mp (hzero ⟨j, hj⟩)
  · rw [(off j hj).1, (off j hj).2]

end Problem

namespace Run

variable {P : Problem ι E} (ρ : Run P)

/-- **Theorem 2.**  The terminal iterate `x_{K+1}` (Algorithm 2 halts at round
`K + 1`, Theorem 1(c)) is a global minimizer, and for every global minimizer
`x*` it has the same value, fit and residual — with no uniqueness
assumption. -/
theorem theorem2 {xs : ι → ℝ} (hxs : P.IsGlobalMin xs) :
    P.IsGlobalMin (ρ.x (ρ.K + 1)) ∧ P.F (ρ.x (ρ.K + 1)) = P.F xs ∧
      P.fit (ρ.x (ρ.K + 1)) = P.fit xs ∧ P.res (ρ.x (ρ.K + 1)) = P.res xs := by
  have hg := (ρ.isGlobalMin_of_K_le (Nat.le_succ ρ.K)).1
  exact ⟨hg, hg.F_eq hxs, hg.fit_eq hxs, hg.res_eq hxs⟩

/-- **Theorem 2**, amplitudes: if the zero-priced columns are linearly
independent, the run returns exactly the full computation's minimizer. -/
theorem theorem2_unique {xs : ι → ℝ} (hxs : P.IsGlobalMin xs)
    (hli : LinearIndependent ℝ fun j : P.zeroPrice xs => P.a j) :
    ρ.x (ρ.K + 1) = xs :=
  Problem.eq_of_isGlobalMin hxs hli (ρ.isGlobalMin_of_K_le (Nat.le_succ ρ.K)).1

end Run

end NnlsDc
