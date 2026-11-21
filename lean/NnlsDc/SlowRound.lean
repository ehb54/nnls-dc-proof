import NnlsDc.Algorithm

/-!
# A slow round: no contraction factor and no sound tolerance

The article's Section 8 family, for `0 < t ≤ 1/2`: columns `a₁ = (3, 1, 0)`,
`a₂ = (2, 0, t)`, `a₃ = (1, 1, 0)`, `a₄ = (0, 2, 0)`, data `b = (2, 2, t)` and
blocks `S₁ = {1, 2}`, `S₂ = {3, 4}`, in the canonical instantiation: leaves
`Sᵢ ∪ R` for the incumbent `R`, and one atomic merge.  Columns are indexed
`0, …, 3` here.

* Whatever minimizers the nodes return, round 1 ends at `F = t²/2` with
  `R₁ = {3}`, round 2 at `F = t²/(2 + t²)` with `R₂ = {2, 3}`, and round 3 at
  `F = 0 = v*` (`rounds`, `three_rounds`, `optimum`).
* Round 2 keeps the fraction `2/(2 + t²)` of the gap (`gap_fraction`), so for
  every tolerance `τ > 0` some `t` makes round 2's improvement smaller than
  `τ`, absolutely and relative to `v₁`, although round 2 is not optimal
  (`tolerance_fires`).
* `canonical_rounds` exhibits the three rounds with explicit minimizers.
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

namespace SlowRound

/-- The problem, with parameter `t`. -/
noncomputable def P (t : ℝ) : Problem (Fin 4) (EuclideanSpace ℝ (Fin 3)) where
  a := ![!₂[3, 1, 0], !₂[2, 0, t], !₂[1, 1, 0], !₂[0, 2, 0]]
  b := !₂[2, 2, t]

/-- The blocks `S₁ = {1, 2}` and `S₂ = {3, 4}`. -/
def S₁ : Finset (Fin 4) := {0, 1}
def S₂ : Finset (Fin 4) := {2, 3}

/-- A canonical round with incumbent `R`: leaves `S₁ ∪ R` and `S₂ ∪ R`, and one
atomic merge of their returned supports. -/
noncomputable def canon (R : Finset (Fin 4)) (y y' x : Fin 4 → ℝ) : Tree (Fin 4) :=
  Tree.node (supp y ∪ supp y') x 2 ![Tree.leaf (S₁ ∪ R) y, Tree.leaf (S₂ ∪ R) y']

variable {t : ℝ}

lemma fit_eq (x : Fin 4 → ℝ) :
    (P t).fit x = !₂[3 * x 0 + 2 * x 1 + x 2, x 0 + x 2 + 2 * x 3, t * x 1] := by
  ext i
  fin_cases i <;> simp [P, Problem.fit, Fin.sum_univ_four] <;> ring

lemma fit_apply (x : Fin 4 → ℝ) :
    (P t).fit x 0 = 3 * x 0 + 2 * x 1 + x 2 ∧ (P t).fit x 1 = x 0 + x 2 + 2 * x 3 ∧
      (P t).fit x 2 = t * x 1 := by
  rw [fit_eq]
  simp

lemma F_eq (x : Fin 4 → ℝ) :
    (P t).F x = ((3 * x 0 + 2 * x 1 + x 2 - 2) ^ 2 + (x 0 + x 2 + 2 * x 3 - 2) ^ 2 +
      (t * x 1 - t) ^ 2) / 2 := by
  rw [Problem.F, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, fit_eq]
  simp [P]

lemma price_eq (x : Fin 4 → ℝ) :
    (P t).price x 0 = 3 * (2 - (3 * x 0 + 2 * x 1 + x 2)) + (2 - (x 0 + x 2 + 2 * x 3)) ∧
      (P t).price x 1 = 2 * (2 - (3 * x 0 + 2 * x 1 + x 2)) + t * (t - t * x 1) ∧
      (P t).price x 2 = (2 - (3 * x 0 + 2 * x 1 + x 2)) + (2 - (x 0 + x 2 + 2 * x 3)) ∧
      (P t).price x 3 = 2 * (2 - (x 0 + x 2 + 2 * x 3)) := by
  simp only [Problem.price, Problem.res, fit_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [P, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

/-- Equal fits have equal coordinates. -/
lemma coords {y m : Fin 4 → ℝ} (h : (P t).fit y = (P t).fit m) :
    3 * y 0 + 2 * y 1 + y 2 = 3 * m 0 + 2 * m 1 + m 2 ∧
      y 0 + y 2 + 2 * y 3 = m 0 + m 2 + 2 * m 3 ∧ t * y 1 = t * m 1 := by
  obtain ⟨a0, a1, a2⟩ := fit_apply (t := t) y
  obtain ⟨b0, b1, b2⟩ := fit_apply (t := t) m
  rw [← a0, ← a1, ← a2, ← b0, ← b1, ← b2, h]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The minimizers of the restricted problems -/

/-- The solution of `P(S₁)`: `x₁ = 4/5`. -/
noncomputable def m₁ : Fin 4 → ℝ := ![4 / 5, 0, 0, 0]

/-- The solution of `P(S₂)` and of `P({1, 3})`: `x₃ = 2`. -/
noncomputable def m₃ : Fin 4 → ℝ := ![0, 0, 2, 0]

/-- The solution of `P({1, 2, 3})` and of `P({2, 3})`. -/
noncomputable def mz (t : ℝ) : Fin 4 → ℝ :=
  ![0, t ^ 2 / (2 + t ^ 2), (4 + t ^ 2) / (2 + t ^ 2), 0]

/-- An exact fit: `b = a₂ + a₄`. -/
noncomputable def w : Fin 4 → ℝ := ![0, 1, 0, 1]

lemma F_m₃ : (P t).F m₃ = t ^ 2 / 2 := by
  rw [F_eq]
  norm_num [m₃]

lemma F_mz (ht : 0 < t) : (P t).F (mz t) = t ^ 2 / (2 + t ^ 2) := by
  have hd : (2 + t ^ 2) ≠ 0 := by positivity
  rw [F_eq]
  simp [mz]
  field_simp
  ring

lemma F_w : (P t).F w = 0 := by
  rw [F_eq]
  norm_num [w]

lemma supp_m₁ : supp m₁ = {0} := by
  ext j
  fin_cases j <;> norm_num [m₁]

lemma supp_m₃ : supp m₃ = {2} := by
  ext j
  fin_cases j <;> norm_num [m₃]

lemma supp_w : supp w = {1, 3} := by
  ext j
  fin_cases j <;> norm_num [w]

lemma supp_mz (ht : 0 < t) : supp (mz t) = {1, 2} := by
  have h1 : t ^ 2 / (2 + t ^ 2) ≠ 0 := by positivity
  have h2 : (4 + t ^ 2) / (2 + t ^ 2) ≠ 0 := by positivity
  ext j
  fin_cases j <;> simp [mz, h1, h2]

lemma isMin_m₁ (ht : t ^ 2 ≤ 4 / 5) : (P t).IsMin S₁ m₁ := by
  obtain ⟨h0, h1, -, -⟩ := price_eq (t := t) m₁
  have p0 : (P t).price m₁ 0 = 0 := by rw [h0]; norm_num [m₁]
  have p1 : (P t).price m₁ 1 ≤ 0 := by rw [h1]; norm_num [m₁]; nlinarith
  clear h0 h1
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> norm_num [m₁]
  · fin_cases j <;> simp_all [S₁, m₁]
  · fin_cases j <;> simp_all [S₁]
  · fin_cases j <;> simp_all [m₁]

lemma isMin_m₃ : (P t).IsMin S₂ m₃ := by
  obtain ⟨-, -, h2, h3⟩ := price_eq (t := t) m₃
  have p2 : (P t).price m₃ 2 = 0 := by rw [h2]; norm_num [m₃]
  have p3 : (P t).price m₃ 3 = 0 := by rw [h3]; norm_num [m₃]
  clear h2 h3
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> norm_num [m₃]
  · fin_cases j <;> simp_all [S₂, m₃]
  · fin_cases j <;> simp_all [S₂]
  · fin_cases j <;> simp_all [m₃]

lemma isMin_m₃' : (P t).IsMin {0, 2} m₃ := by
  obtain ⟨h0, -, h2, -⟩ := price_eq (t := t) m₃
  have p0 : (P t).price m₃ 0 = 0 := by rw [h0]; norm_num [m₃]
  have p2 : (P t).price m₃ 2 = 0 := by rw [h2]; norm_num [m₃]
  clear h0 h2
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> norm_num [m₃]
  · fin_cases j <;> simp_all [m₃]
  · fin_cases j <;> simp_all
  · fin_cases j <;> simp_all [m₃]

lemma isMin_mz (ht : 0 < t) : (P t).IsMin {0, 1, 2} (mz t) := by
  have hd : (2 + t ^ 2) ≠ 0 := by positivity
  obtain ⟨h0, h1, h2, -⟩ := price_eq (t := t) (mz t)
  have p0 : (P t).price (mz t) 0 = -(2 * t ^ 2 / (2 + t ^ 2)) := by
    rw [h0]; simp [mz]; field_simp; ring
  have p1 : (P t).price (mz t) 1 = 0 := by rw [h1]; simp [mz]; field_simp; ring
  have p2 : (P t).price (mz t) 2 = 0 := by rw [h2]; simp [mz]; field_simp; ring
  have p0' : (P t).price (mz t) 0 ≤ 0 := by
    rw [p0]
    have : 0 ≤ 2 * t ^ 2 / (2 + t ^ 2) := by positivity
    linarith
  clear h0 h1 h2 p0
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> simp [mz] <;> positivity
  · fin_cases j <;> simp_all [mz]
  · fin_cases j <;> simp_all
  · fin_cases j <;> simp_all [mz]

lemma isMin_w : (P t).IsMin {1, 2, 3} w := by
  refine ⟨⟨fun j => ?_, fun j hj => ?_⟩, fun y _ => ?_⟩
  · fin_cases j <;> norm_num [w]
  · fin_cases j <;> simp_all [w]
  · rw [F_w]
    exact Problem.F_nonneg y

lemma isMin_mz' (ht : 0 < t) : (P t).IsMin {1, 2} (mz t) :=
  (isMin_mz ht).restrict (by simp [supp_mz ht]) (by decide)

/-! ### Every exact solve returns the same point -/

lemma eq_m₁ (ht : 0 < t) (ht' : t ^ 2 ≤ 4 / 5) {y : Fin 4 → ℝ} (hy : (P t).IsMin S₁ y) :
    y = m₁ := by
  obtain ⟨-, c1, c2⟩ := coords (hy.fit_eq (isMin_m₁ ht'))
  have hy2 : y 2 = 0 := hy.1.2 2 (by simp [S₁])
  have hy3 : y 3 = 0 := hy.1.2 3 (by simp [S₁])
  have e1 : y 1 = m₁ 1 := mul_left_cancel₀ ht.ne' c2
  have m2 : m₁ 2 = 0 := rfl
  have m3 : m₁ 3 = 0 := rfl
  have e0 : y 0 = m₁ 0 := by linarith
  funext j
  fin_cases j
  · exact e0
  · exact e1
  · exact hy2.trans m2.symm
  · exact hy3.trans m3.symm

lemma eq_m₃ {y : Fin 4 → ℝ} (hy : (P t).IsMin S₂ y) : y = m₃ := by
  obtain ⟨c0, c1, -⟩ := coords (hy.fit_eq isMin_m₃)
  have hy0 : y 0 = 0 := hy.1.2 0 (by simp [S₂])
  have hy1 : y 1 = 0 := hy.1.2 1 (by simp [S₂])
  have m0 : m₃ 0 = 0 := rfl
  have m1 : m₃ 1 = 0 := rfl
  funext j
  fin_cases j
  · exact hy0.trans m0.symm
  · exact hy1.trans m1.symm
  · show y 2 = m₃ 2
    linarith
  · show y 3 = m₃ 3
    linarith

lemma eq_m₃' {x : Fin 4 → ℝ} (hx : (P t).IsMin {0, 2} x) : x = m₃ := by
  obtain ⟨c0, c1, -⟩ := coords (hx.fit_eq isMin_m₃')
  have hx1 : x 1 = 0 := hx.1.2 1 (by simp)
  have hx3 : x 3 = 0 := hx.1.2 3 (by simp)
  have m1 : m₃ 1 = 0 := rfl
  have m3 : m₃ 3 = 0 := rfl
  funext j
  fin_cases j
  · show x 0 = m₃ 0
    linarith
  · exact hx1.trans m1.symm
  · show x 2 = m₃ 2
    linarith
  · exact hx3.trans m3.symm

lemma eq_mz (ht : 0 < t) {y : Fin 4 → ℝ} (hy : (P t).IsMin {0, 1, 2} y) : y = mz t := by
  obtain ⟨c0, c1, c2⟩ := coords (hy.fit_eq (isMin_mz ht))
  have hy3 : y 3 = 0 := hy.1.2 3 (by simp)
  have e1 : y 1 = mz t 1 := mul_left_cancel₀ ht.ne' c2
  have m3 : mz t 3 = 0 := rfl
  funext j
  fin_cases j
  · show y 0 = mz t 0
    linarith
  · exact e1
  · show y 2 = mz t 2
    linarith
  · exact hy3.trans m3.symm

lemma eq_mz' (ht : 0 < t) {x : Fin 4 → ℝ} (hx : (P t).IsMin {1, 2} x) : x = mz t := by
  obtain ⟨-, c1, c2⟩ := coords (hx.fit_eq (isMin_mz' ht))
  have hx0 : x 0 = 0 := hx.1.2 0 (by simp)
  have hx3 : x 3 = 0 := hx.1.2 3 (by simp)
  have e1 : x 1 = mz t 1 := mul_left_cancel₀ ht.ne' c2
  have m0 : mz t 0 = 0 := rfl
  have m3 : mz t 3 = 0 := rfl
  funext j
  fin_cases j
  · exact hx0.trans m0.symm
  · exact e1
  · show x 2 = mz t 2
    linarith
  · exact hx3.trans m3.symm

/-! ### The three rounds -/

/-- Round 1 (`R₀ = ∅`): `F = t²/2` and `R₁ = {3}`. -/
theorem round1 (ht : 0 < t) (ht' : t ≤ 1 / 2) {y y' x : Fin 4 → ℝ}
    (h : (canon ∅ y y' x).WF (P t)) : (P t).F x = t ^ 2 / 2 ∧ supp x = {2} := by
  have ht2 : t ^ 2 ≤ 4 / 5 := by nlinarith
  unfold canon at h
  have l1 : (P t).IsMin (S₁ ∪ ∅) y := h.2.2 0
  have l2 : (P t).IsMin (S₂ ∪ ∅) y' := h.2.2 1
  have r : (P t).IsMin (supp y ∪ supp y') x := h.1
  rw [Finset.union_empty] at l1 l2
  rw [eq_m₁ ht ht2 l1, eq_m₃ l2, supp_m₁, supp_m₃] at r
  have e : ({0} ∪ {2} : Finset (Fin 4)) = {0, 2} := by decide
  rw [e] at r
  rw [eq_m₃' r]
  exact ⟨F_m₃, supp_m₃⟩

/-- Round 2 (`R₁ = {3}`): `F = t²/(2 + t²)` and `R₂ = {2, 3}`. -/
theorem round2 (ht : 0 < t) {x₁ y y' x : Fin 4 → ℝ} (hR : supp x₁ = {2})
    (h : (canon (supp x₁) y y' x).WF (P t)) :
    (P t).F x = t ^ 2 / (2 + t ^ 2) ∧ supp x = {1, 2} := by
  unfold canon at h
  rw [hR] at h
  have l1 : (P t).IsMin (S₁ ∪ {2}) y := h.2.2 0
  have l2 : (P t).IsMin (S₂ ∪ {2}) y' := h.2.2 1
  have r : (P t).IsMin (supp y ∪ supp y') x := h.1
  have e1 : (S₁ ∪ {2} : Finset (Fin 4)) = {0, 1, 2} := by decide
  have e2 : (S₂ ∪ {2} : Finset (Fin 4)) = S₂ := by decide
  rw [e1] at l1
  rw [e2] at l2
  rw [eq_mz ht l1, eq_m₃ l2, supp_mz ht, supp_m₃] at r
  have e : ({1, 2} ∪ {2} : Finset (Fin 4)) = {1, 2} := by decide
  rw [e] at r
  rw [eq_mz' ht r]
  exact ⟨F_mz ht, supp_mz ht⟩

/-- Round 3 (`R₂ = {2, 3}`): `F = 0`. -/
theorem round3 {x₂ y y' x : Fin 4 → ℝ} (hR : supp x₂ = {1, 2})
    (h : (canon (supp x₂) y y' x).WF (P t)) : (P t).F x = 0 := by
  unfold canon at h
  rw [hR] at h
  have l2 : (P t).IsMin (S₂ ∪ {1, 2}) y' := h.2.2 1
  have e : (S₂ ∪ {1, 2} : Finset (Fin 4)) = {1, 2, 3} := by decide
  rw [e] at l2
  have hy : (P t).F y' ≤ 0 := by
    have := l2.2 w (isMin_w (t := t)).1
    rwa [F_w] at this
  have hx : (P t).F x ≤ (P t).F y' := Tree.WF.F_le_child h 1
  exact le_antisymm (le_trans hx hy) (Problem.F_nonneg _)

/-- **The slow round.**  In the canonical instantiation, whatever minimizers
the nodes return, rounds 1–3 end at `F = t²/2`, `t²/(2 + t²)` and `0`, with
`R₁ = {3}` and `R₂ = {2, 3}`. -/
theorem rounds (ht : 0 < t) (ht' : t ≤ 1 / 2)
    {y₁ y₁' x₁ y₂ y₂' x₂ y₃ y₃' x₃ : Fin 4 → ℝ}
    (h1 : (canon ∅ y₁ y₁' x₁).WF (P t)) (h2 : (canon (supp x₁) y₂ y₂' x₂).WF (P t))
    (h3 : (canon (supp x₂) y₃ y₃' x₃).WF (P t)) :
    (P t).F x₁ = t ^ 2 / 2 ∧ supp x₁ = {2} ∧ (P t).F x₂ = t ^ 2 / (2 + t ^ 2) ∧
      supp x₂ = {1, 2} ∧ (P t).F x₃ = 0 := by
  obtain ⟨hF1, hR1⟩ := round1 ht ht' h1
  obtain ⟨hF2, hR2⟩ := round2 ht hR1 h2
  exact ⟨hF1, hR1, hF2, hR2, round3 hR2 h3⟩

/-- `b` is exactly representable: `v* = 0`. -/
theorem optimum : (P t).IsGlobalMin w ∧ (P t).Val univ = 0 := by
  have hg : (P t).IsGlobalMin w := by
    refine ⟨feasible_univ_iff.mpr fun j => ?_, fun y _ => ?_⟩
    · fin_cases j <;> norm_num [w]
    · rw [F_w]
      exact Problem.F_nonneg y
  exact ⟨hg, by rw [hg.val_eq, F_w]⟩

/-- **The slow round as a run of Algorithm 2.**  If rounds 1–3 of a run are
canonical, they end at `F = t²/2`, `t²/(2 + t²)` and `0 = v*`. -/
theorem three_rounds (ht : 0 < t) (ht' : t ≤ 1 / 2) (ρ : Run (P t))
    (h1 : ∃ y y' x, ρ.tree 1 = canon ∅ y y' x)
    (h2 : ∃ y y' x, ρ.tree 2 = canon (ρ.R 1) y y' x)
    (h3 : ∃ y y' x, ρ.tree 3 = canon (ρ.R 2) y y' x) :
    ρ.v 1 = t ^ 2 / 2 ∧ ρ.v 2 = t ^ 2 / (2 + t ^ 2) ∧ ρ.v 3 = 0 := by
  obtain ⟨y₁, y₁', x₁, e1⟩ := h1
  obtain ⟨y₂, y₂', x₂, e2⟩ := h2
  obtain ⟨y₃, y₃', x₃, e3⟩ := h3
  have hx1 : ρ.x 1 = x₁ := by
    show (ρ.tree 1).sol = x₁
    rw [e1]
    rfl
  have hx2 : ρ.x 2 = x₂ := by
    show (ρ.tree 2).sol = x₂
    rw [e2]
    rfl
  have hx3 : ρ.x 3 = x₃ := by
    show (ρ.tree 3).sol = x₃
    rw [e3]
    rfl
  have w1 := ρ.wf 1 le_rfl
  have w2 := ρ.wf 2 (by norm_num)
  have w3 := ρ.wf 3 (by norm_num)
  rw [e1] at w1
  rw [e2, show ρ.R 1 = supp x₁ by rw [Run.R, hx1]] at w2
  rw [e3, show ρ.R 2 = supp x₂ by rw [Run.R, hx2]] at w3
  obtain ⟨hF1, -, hF2, -, hF3⟩ := rounds ht ht' w1 w2 w3
  refine ⟨?_, ?_, ?_⟩
  · rw [Run.v, hx1, hF1]
  · rw [Run.v, hx2, hF2]
  · rw [Run.v, hx3, hF3]

/-- Round 2 keeps the fraction `2/(2 + t²)` of the gap to `v*`. -/
theorem gap_fraction (ht : 0 < t) (ht' : t ≤ 1 / 2) {y₁ y₁' x₁ y₂ y₂' x₂ : Fin 4 → ℝ}
    (h1 : (canon ∅ y₁ y₁' x₁).WF (P t)) (h2 : (canon (supp x₁) y₂ y₂' x₂).WF (P t)) :
    (P t).F x₂ - (P t).Val univ = 2 / (2 + t ^ 2) * ((P t).F x₁ - (P t).Val univ) := by
  obtain ⟨hF1, hR1⟩ := round1 ht ht' h1
  obtain ⟨hF2, -⟩ := round2 ht hR1 h2
  rw [hF1, hF2, optimum.2]
  ring

/-- **No positive tolerance is sound.**  For every `τ > 0` there is an instance
whose second round improves on the first by less than `τ`, both absolutely and
relative to `v₁`, although its result is not a global minimizer. -/
theorem tolerance_fires {τ : ℝ} (hτ : 0 < τ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ ∀ y₁ y₁' x₁ y₂ y₂' x₂ : Fin 4 → ℝ,
      (canon ∅ y₁ y₁' x₁).WF (P t) → (canon (supp x₁) y₂ y₂' x₂).WF (P t) →
      (P t).F x₁ - (P t).F x₂ < τ * (P t).F x₁ ∧ (P t).F x₁ - (P t).F x₂ < τ ∧
        ¬ (P t).IsGlobalMin x₂ := by
  obtain ⟨t, ht, ht', htτ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧ t ≤ τ :=
    ⟨min (1 / 2) τ, lt_min (by norm_num) hτ, min_le_left _ _, min_le_right _ _⟩
  refine ⟨t, ht, ht', fun y₁ y₁' x₁ y₂ y₂' x₂ h1 h2 => ?_⟩
  obtain ⟨hF1, hR1⟩ := round1 ht ht' h1
  obtain ⟨hF2, -⟩ := round2 ht hR1 h2
  have hu : 0 < t ^ 2 := by positivity
  have hu' : t ^ 2 ≤ τ / 2 := by nlinarith
  have hd : 0 < 2 + t ^ 2 := by positivity
  have key : t ^ 2 / 2 - t ^ 2 / (2 + t ^ 2) = t ^ 4 / (2 * (2 + t ^ 2)) := by
    field_simp
    ring
  rw [hF1, hF2, key]
  refine ⟨?_, ?_, fun hg => ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hu hτ]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hu hτ]
  · have h := hg.2 w (optimum (t := t)).1.1
    rw [F_w, hF2] at h
    have : 0 < t ^ 2 / (2 + t ^ 2) := by positivity
    linarith

/-- The hypotheses of `rounds` are met: the three canonical rounds with explicit
minimizers satisfy (H1) and (H3). -/
theorem canonical_rounds (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    (canon ∅ m₁ m₃ m₃).WF (P t) ∧ (canon (supp m₃) (mz t) m₃ (mz t)).WF (P t) ∧
      (canon (supp (mz t)) (mz t) w w).WF (P t) := by
  have ht2 : t ^ 2 ≤ 4 / 5 := by nlinarith
  unfold canon
  rw [supp_m₁, supp_m₃, supp_mz ht, supp_w]
  have e1 : ({0} ∪ {2} : Finset (Fin 4)) = {0, 2} := by decide
  have e2 : ({1, 2} ∪ {2} : Finset (Fin 4)) = {1, 2} := by decide
  have e3 : ({1, 2} ∪ {1, 3} : Finset (Fin 4)) = {1, 2, 3} := by decide
  have f1 : (S₁ ∪ {2} : Finset (Fin 4)) = {0, 1, 2} := by decide
  have f2 : (S₂ ∪ {2} : Finset (Fin 4)) = S₂ := by decide
  have f3 : (S₁ ∪ {1, 2} : Finset (Fin 4)) = {0, 1, 2} := by decide
  have f4 : (S₂ ∪ {1, 2} : Finset (Fin 4)) = {1, 2, 3} := by decide
  rw [e1, e2, e3, f1, f2, f3, f4, Finset.union_empty, Finset.union_empty]
  simp only [Tree.WF]
  refine ⟨⟨isMin_m₃', fun i => ?_, fun i => ?_⟩, ⟨isMin_mz' ht, fun i => ?_, fun i => ?_⟩,
    ⟨isMin_w, fun i => ?_, fun i => ?_⟩⟩
  · fin_cases i <;> simp [Tree.sol, supp_m₁, supp_m₃]
  · fin_cases i
    · exact isMin_m₁ ht2
    · exact isMin_m₃
  · fin_cases i <;> simp [Tree.sol, supp_mz ht, supp_m₃]
  · fin_cases i
    · exact isMin_mz ht
    · exact isMin_m₃
  · fin_cases i <;> simp [Tree.sol, supp_mz ht, supp_w]
  · fin_cases i
    · exact isMin_mz ht
    · exact isMin_w

end SlowRound

end NnlsDc
