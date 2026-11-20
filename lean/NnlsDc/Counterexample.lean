import NnlsDc.Algorithm

/-!
# Proposition 1: the non-iterated scheme is not exact

The article's instance, with unit columns `a₁ = (1,0,1)/√2`, `a₂ = e₁`,
`a₃ = (0,1,1)/√2`, `a₄ = e₂`, data `b = (1, 1, 3/2)` and blocks
`S₁ = {1, 2}`, `S₂ = {3, 4}`.  Columns are indexed `0, …, 3` here.

* In the canonical instantiation (leaves `S₁`, `S₂`, atomic merge), every
  exact solve of `P(S₁)` returns support `{1}` and every exact solve of
  `P(S₂)` returns `{3}`, so the single pass merges `{1, 3}` and returns
  `F = 1/24` (`‖r‖² = 1/12 = ‖b‖²/51`), whichever minimizers are chosen;
  the merge keeps both columns, so `R₁ = {1, 3}`.
* `b` is exactly representable, so `v* = 0`; the pricing test sees the gap
  (`a₂ᵀr = a₄ᵀr = 1/6 > 0` at the merged solution).
* Any first refinement round satisfying (H1)–(H3) reaches `v* = 0`;
  `two_rounds` states both rounds for a run of Algorithm 2.

(H2)–(H3) also allow larger first-round candidate sets: `{1, 2, 3}`, as a
leaf or as the merge, fits `b` exactly (`zfit`), which is why the single pass
is taken in its canonical instantiation.
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

namespace Counterexample

/-- `s = 1/√2`. -/
noncomputable def s : ℝ := 1 / Real.sqrt 2

lemma s_sq : s ^ 2 = 1 / 2 := by
  rw [s, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma s_pos : 0 < s := by
  rw [s]
  positivity

/-- Proposition 1's problem. -/
noncomputable def P : Problem (Fin 4) (EuclideanSpace ℝ (Fin 3)) where
  a := ![!₂[s, 0, s], !₂[1, 0, 0], !₂[0, s, s], !₂[0, 1, 0]]
  b := !₂[1, 1, 3 / 2]

/-- The blocks `S₁ = {1, 2}` and `S₂ = {3, 4}`. -/
def S₁ : Finset (Fin 4) := {0, 1}
def S₂ : Finset (Fin 4) := {2, 3}

lemma fit_eq (x : Fin 4 → ℝ) :
    P.fit x = !₂[x 0 * s + x 1, x 2 * s + x 3, x 0 * s + x 2 * s] := by
  ext i
  fin_cases i <;> simp [P, Problem.fit, Fin.sum_univ_four]

lemma fit_apply (x : Fin 4 → ℝ) :
    (P.fit x) 0 = x 0 * s + x 1 ∧ (P.fit x) 1 = x 2 * s + x 3 ∧
      (P.fit x) 2 = x 0 * s + x 2 * s := by
  rw [fit_eq]
  simp

lemma F_eq (x : Fin 4 → ℝ) :
    P.F x = ((x 0 * s + x 1 - 1) ^ 2 + (x 2 * s + x 3 - 1) ^ 2 +
      (x 0 * s + x 2 * s - 3 / 2) ^ 2) / 2 := by
  rw [Problem.F, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, fit_eq]
  simp [P]

lemma price_eq (x : Fin 4 → ℝ) :
    P.price x 0 = s * (1 - (x 0 * s + x 1)) + s * (3 / 2 - (x 0 * s + x 2 * s)) ∧
      P.price x 1 = 1 - (x 0 * s + x 1) ∧
      P.price x 2 = s * (1 - (x 2 * s + x 3)) + s * (3 / 2 - (x 0 * s + x 2 * s)) ∧
      P.price x 3 = 1 - (x 2 * s + x 3) := by
  simp only [Problem.price, Problem.res, fit_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [P, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

/-! ### The single pass -/

/-- The leaf solution of `P(S₁)`: `x₁ = 5/(2√2)`. -/
noncomputable def y₁ : Fin 4 → ℝ := ![5 / 2 * s, 0, 0, 0]

/-- The leaf solution of `P(S₂)`: `x₃ = 5/(2√2)`. -/
noncomputable def y₂ : Fin 4 → ℝ := ![0, 0, 5 / 2 * s, 0]

/-- The merged solution of `P({1, 3})`: `x₁ = x₃ = 5√2/6`. -/
noncomputable def xm : Fin 4 → ℝ := ![5 / 3 * s, 0, 5 / 3 * s, 0]

lemma isMin_y₁ : P.IsMin S₁ y₁ := by
  have hs := s_sq
  have hp := s_pos
  obtain ⟨h0, h1, -, -⟩ := price_eq y₁
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> simp [y₁]
    positivity
  · fin_cases j <;> simp_all [S₁, y₁]
  · fin_cases j <;> simp_all [S₁, y₁] <;> nlinarith
  · fin_cases j <;> simp_all [y₁]
    nlinarith

lemma isMin_y₂ : P.IsMin S₂ y₂ := by
  have hs := s_sq
  have hp := s_pos
  obtain ⟨-, -, h2, h3⟩ := price_eq y₂
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> simp [y₂]
    positivity
  · fin_cases j <;> simp_all [S₂, y₂]
  · fin_cases j <;> simp_all [S₂, y₂] <;> nlinarith
  · fin_cases j <;> simp_all [y₂]
    nlinarith

lemma isMin_xm : P.IsMin {0, 2} xm := by
  have hs := s_sq
  have hp := s_pos
  obtain ⟨h0, -, h2, -⟩ := price_eq xm
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> simp [xm] <;> positivity
  · fin_cases j <;> simp_all [xm]
  · fin_cases j <;> simp_all [xm] <;> nlinarith
  · fin_cases j <;> simp_all [xm] <;> nlinarith

/-- Every exact solve of `P(S₁)` returns support `{1}` (index `0`). -/
lemma supp_of_isMin_S₁ {y : Fin 4 → ℝ} (hy : P.IsMin S₁ y) : supp y = {0} := by
  have hs := s_sq
  have hp := s_pos
  have hfit := hy.fit_eq isMin_y₁
  have hy2 : y 2 = 0 := hy.1.2 2 (by simp [S₁])
  have hy3 : y 3 = 0 := hy.1.2 3 (by simp [S₁])
  have c0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hfit
  have c2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hfit
  simp only [fit_eq] at c0 c2
  simp [y₁, hy2] at c0 c2
  have c2' : y 0 = 5 / 2 * s := c2.resolve_right hp.ne'
  have hy0 : y 0 * s = 5 / 4 := by rw [c2']; nlinarith
  have hy1 : y 1 = 0 := by nlinarith
  ext j
  fin_cases j <;> simp [hy1, hy2, hy3]
  intro h
  norm_num [h] at hy0

/-- Every exact solve of `P(S₂)` returns support `{3}` (index `2`). -/
lemma supp_of_isMin_S₂ {y : Fin 4 → ℝ} (hy : P.IsMin S₂ y) : supp y = {2} := by
  have hs := s_sq
  have hp := s_pos
  have hfit := hy.fit_eq isMin_y₂
  have hy0 : y 0 = 0 := hy.1.2 0 (by simp [S₂])
  have hy1 : y 1 = 0 := hy.1.2 1 (by simp [S₂])
  have c1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hfit
  have c2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hfit
  simp only [fit_eq] at c1 c2
  simp [y₂, hy0] at c1 c2
  have c2' : y 2 = 5 / 2 * s := c2.resolve_right hp.ne'
  have hy2 : y 2 * s = 5 / 4 := by rw [c2']; nlinarith
  have hy3 : y 3 = 0 := by nlinarith
  ext j
  fin_cases j <;> simp [hy0, hy1, hy3]
  intro h
  norm_num [h] at hy2

lemma F_xm : P.F xm = 1 / 24 := by
  have hs := s_sq
  rw [F_eq]
  simp [xm]
  nlinarith

/-- Every exact solve of the merge `P({1, 3})` keeps both columns: its support
is `{1, 3}` (indices `0, 2`). -/
lemma supp_of_isMin_merge {x : Fin 4 → ℝ} (hx : P.IsMin {0, 2} x) : supp x = {0, 2} := by
  have hs := s_sq
  have hp := s_pos
  have hfit := hx.fit_eq isMin_xm
  have hx1 : x 1 = 0 := hx.1.2 1 (by simp)
  have hx3 : x 3 = 0 := hx.1.2 3 (by simp)
  have c0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hfit
  have c1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hfit
  simp only [fit_eq] at c0 c1
  simp [xm, hx1, hx3] at c0 c1
  have h0 : x 0 ≠ 0 := by
    rw [c0.resolve_right hp.ne']
    exact mul_ne_zero (by norm_num) hp.ne'
  have h2 : x 2 ≠ 0 := by
    rw [c1.resolve_right hp.ne']
    exact mul_ne_zero (by norm_num) hp.ne'
  ext j
  fin_cases j <;> simp [h0, h2, hx1, hx3]

/-- **Proposition 1, single pass.**  In the canonical instantiation (leaves
`S₁`, `S₂`, atomic merge), whatever minimizers the two leaf solves and the
merge return, the non-iterated scheme ends at `F = 1/24`. -/
theorem single_pass {y y' x : Fin 4 → ℝ} (hy : P.IsMin S₁ y) (hy' : P.IsMin S₂ y')
    (hx : P.IsMin (supp y ∪ supp y') x) : P.F x = 1 / 24 := by
  rw [supp_of_isMin_S₁ hy, supp_of_isMin_S₂ hy'] at hx
  have : ({0} ∪ {2} : Finset (Fin 4)) = {0, 2} := by decide
  rw [this] at hx
  rw [hx.F_eq isMin_xm, F_xm]

/-- The same, stated for the round's solved merge tree (Algorithm 1 with
`R = ∅` in its canonical instantiation: leaves `S₁, S₂`, merge of the union of
the returned supports). -/
theorem single_pass_tree {y y' x : Fin 4 → ℝ}
    (ht : (Tree.node (supp y ∪ supp y') x 2 ![Tree.leaf S₁ y, Tree.leaf S₂ y']).WF P) :
    P.F x = 1 / 24 :=
  single_pass (ht.2.2 0) (ht.2.2 1) ht.1

/-- The single pass returns `R₁ = {1, 3}` (indices `0, 2`), whichever
minimizers are chosen. -/
theorem single_pass_supp {y y' x : Fin 4 → ℝ} (hy : P.IsMin S₁ y) (hy' : P.IsMin S₂ y')
    (hx : P.IsMin (supp y ∪ supp y') x) : supp x = {0, 2} := by
  rw [supp_of_isMin_S₁ hy, supp_of_isMin_S₂ hy'] at hx
  have : ({0} ∪ {2} : Finset (Fin 4)) = {0, 2} := by decide
  rw [this] at hx
  exact supp_of_isMin_merge hx

/-- At the merged solution the residual is `(1/6, 1/6, -1/6)`, so
`‖r‖² = 1/12 = ‖b‖²/51`, and the pricing test detects the gap:
`a₂ᵀr = a₄ᵀr = 1/6 > 0`. -/
theorem merged_residual :
    ‖P.res xm‖ ^ 2 = 1 / 12 ∧ ‖P.res xm‖ ^ 2 = ‖P.b‖ ^ 2 / 51 ∧
      P.price xm 1 = 1 / 6 ∧ P.price xm 3 = 1 / 6 := by
  have hs := s_sq
  have hF : ‖P.res xm‖ ^ 2 = 2 * P.F xm := by
    rw [Problem.F, Problem.res, ← norm_neg, neg_sub]
    ring
  have hb : ‖P.b‖ ^ 2 = 17 / 4 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [P]
    norm_num
  obtain ⟨-, h1, -, h3⟩ := price_eq xm
  refine ⟨by rw [hF, F_xm]; norm_num, by rw [hF, F_xm, hb]; norm_num, ?_, ?_⟩
  · rw [h1]; simp [xm]; nlinarith
  · rw [h3]; simp [xm]; nlinarith

/-! ### The optimum and one refinement round -/

/-- An exact representation: `x* = (3/(2√2), 1/4, 3/(2√2), 1/4)`. -/
noncomputable def xstar : Fin 4 → ℝ := ![3 / 2 * s, 1 / 4, 3 / 2 * s, 1 / 4]

lemma F_xstar : P.F xstar = 0 := by
  have hs := s_sq
  rw [F_eq]
  simp [xstar]
  nlinarith

/-- `b` is exactly representable: `v* = 0`. -/
theorem optimum : P.IsGlobalMin xstar ∧ P.Val univ = 0 := by
  have hp := s_pos
  have hg : P.IsGlobalMin xstar := by
    refine ⟨feasible_univ_iff.mpr fun j => ?_, fun y _ => ?_⟩
    · fin_cases j <;> simp [xstar] <;> positivity
    · rw [F_xstar]; exact Problem.F_nonneg y
  exact ⟨hg, by rw [hg.val_eq, F_xstar]⟩

/-- An exact fit inside any leaf containing columns `1, 2, 3` (indices `0, 1, 2`):
`x = (1/√2, 1/2, √2, 0)`. -/
noncomputable def zfit : Fin 4 → ℝ := ![s, 1 / 2, 2 * s, 0]

lemma F_zfit : P.F zfit = 0 := by
  have hs := s_sq
  rw [F_eq]
  simp [zfit]
  nlinarith

/-- **Proposition 1, one refinement round reaches `v*`.**  Every round-2 tree
satisfying (H1)–(H3) — any partition and merge tree, leaves covering all
columns and containing the incumbent support `R₁ = {1, 3}` — returns
`F = 0 = v*`. -/
theorem refinement_round (t : Tree (Fin 4)) (ht : t.WF P)
    (hcover : ∀ j, ∃ D y, t.HasLeaf D y ∧ j ∈ D)
    (hfeed : ∀ D y, t.HasLeaf D y → ({0, 2} : Finset (Fin 4)) ⊆ D) :
    P.F t.sol = 0 := by
  have hp := s_pos
  obtain ⟨D, y, hl, h1⟩ := hcover 1
  have hD : ({0, 1, 2} : Finset (Fin 4)) ⊆ D := by
    intro j hj
    have h02 := hfeed D y hl
    fin_cases j <;> simp_all [Finset.subset_iff]
  have hz : Feasible D zfit := by
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j <;> simp [zfit] <;> positivity
    · fin_cases j <;> simp_all [zfit, Finset.subset_iff]
  have hy : P.F y ≤ 0 := (F_zfit ▸ (ht.isMin_of_hasLeaf hl).2 zfit hz)
  exact le_antisymm (le_trans (ht.F_sol_le hl) hy) (Problem.F_nonneg _)

/-- **Proposition 1 as a run of Algorithm 2.**  If round 1 is the canonical
single pass, it ends at `F = 1/24` with `R₁ = {1, 3}`, and round 2, whatever
its partition and merge tree, reaches `v* = 0`. -/
theorem two_rounds (ρ : Run P) {y y' x : Fin 4 → ℝ}
    (h1 : ρ.tree 1 = Tree.node (supp y ∪ supp y') x 2 ![Tree.leaf S₁ y, Tree.leaf S₂ y']) :
    ρ.v 1 = 1 / 24 ∧ ρ.R 1 = {0, 2} ∧ ρ.v 2 = 0 := by
  have ht := ρ.wf 1 le_rfl
  rw [h1] at ht
  have hx : ρ.x 1 = x := by
    show (ρ.tree 1).sol = x
    rw [h1]
    rfl
  have hR : ρ.R 1 = {0, 2} := by
    show supp (ρ.x 1) = {0, 2}
    rw [hx]
    exact single_pass_supp (ht.2.2 0) (ht.2.2 1) ht.1
  refine ⟨?_, hR, ?_⟩
  · show P.F (ρ.x 1) = 1 / 24
    rw [hx]
    exact single_pass (ht.2.2 0) (ht.2.2 1) ht.1
  · show P.F (ρ.tree 2).sol = 0
    refine refinement_round (ρ.tree 2) (ρ.wf 2 (by norm_num)) (ρ.cover 2 (by norm_num)) ?_
    intro D z hl
    have h : ρ.R 1 ⊆ D := ρ.feedback 1 le_rfl D z hl
    rwa [hR] at h

end Counterexample

end NnlsDc
