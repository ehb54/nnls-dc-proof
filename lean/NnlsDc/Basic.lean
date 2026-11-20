import Mathlib

/-!
# Restricted NNLS problems

Formalization of the basic facts behind E. H. Brookes, *Exactness of an
iterated divide-and-conquer method for large-scale nonnegative least squares*.

The columns `a j` (`j : ι`, a finite index type) live in a real inner product
space `E` (`E = ℝ^m` in the article) and `b : E` is the data.  For an
amplitude vector `x : ι → ℝ`:

* `fit x = ∑ j, x j • a j` is the article's `Ax`;
* `res x = b - fit x` is the residual `r(x)`;
* `F x = ‖Ax - b‖² / 2` is the objective;
* `price x j = ⟪a j, r(x)⟫` is the article's `a_jᵀ r(x)`.

The restricted problem `P(C)` minimizes `F` over `x ≥ 0` with `supp x ⊆ C`;
`P(S)`, the full problem, is `P(univ)`.

Everything rests on one exact identity (`Problem.F_expand`):

  `F y = F x - ∑ j, (y j - x j) * price x j + ‖Ay - Ax‖² / 2`.
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An NNLS problem: columns `a` and data `b`. -/
structure Problem (ι E : Type*) where
  /-- The columns `a j`. -/
  a : ι → E
  /-- The data `b`. -/
  b : E

/-- The support of an amplitude vector. -/
noncomputable def supp (x : ι → ℝ) : Finset ι := univ.filter fun j => x j ≠ 0

@[simp] lemma mem_supp {x : ι → ℝ} {j : ι} : j ∈ supp x ↔ x j ≠ 0 := by
  simp [supp]

lemma not_mem_supp {x : ι → ℝ} {j : ι} : j ∉ supp x ↔ x j = 0 := by
  simp

/-- `x` is feasible for the restricted problem `P(C)`: nonnegative, and zero
off `C`. -/
def Feasible (C : Finset ι) (x : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ j, j ∉ C → x j = 0

lemma feasible_iff {C : Finset ι} {x : ι → ℝ} :
    Feasible C x ↔ (∀ j, 0 ≤ x j) ∧ supp x ⊆ C := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun j hj => ?_⟩
    by_contra hC
    exact (mem_supp.mp hj) (h1 j hC)
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun j hC => ?_⟩
    by_contra hx
    exact hC (h1 (mem_supp.mpr hx))

omit [Fintype ι] in
lemma Feasible.mono {C D : Finset ι} {x : ι → ℝ} (hx : Feasible C x) (h : C ⊆ D) :
    Feasible D x :=
  ⟨hx.1, fun j hj => hx.2 j fun hC => hj (h hC)⟩

lemma Feasible.supp_subset {C : Finset ι} {x : ι → ℝ} (hx : Feasible C x) :
    supp x ⊆ C :=
  (feasible_iff.mp hx).2

lemma feasible_of_supp_subset {C : Finset ι} {x : ι → ℝ} (h0 : ∀ j, 0 ≤ x j)
    (h : supp x ⊆ C) : Feasible C x :=
  feasible_iff.mpr ⟨h0, h⟩

lemma feasible_univ_iff {x : ι → ℝ} : Feasible univ x ↔ ∀ j, 0 ≤ x j := by
  simp [Feasible]

namespace Problem

variable (P : Problem ι E)

/-- The fitted vector `Ax`. -/
noncomputable def fit (x : ι → ℝ) : E := ∑ j, x j • P.a j

/-- The residual `r(x) = b - Ax`. -/
noncomputable def res (x : ι → ℝ) : E := P.b - P.fit x

/-- The objective `F(x) = ‖Ax - b‖² / 2`. -/
noncomputable def F (x : ι → ℝ) : ℝ := ‖P.fit x - P.b‖ ^ 2 / 2

/-- The price `a_jᵀ r(x)` of column `j` at `x`. -/
noncomputable def price (x : ι → ℝ) (j : ι) : ℝ := ⟪P.a j, P.res x⟫_ℝ

/-- `x` solves the restricted problem `P(C)`. -/
def IsMin (C : Finset ι) (x : ι → ℝ) : Prop :=
  Feasible C x ∧ ∀ y, Feasible C y → P.F x ≤ P.F y

/-- `x` is a global minimizer: it solves the full problem `P(S)`. -/
def IsGlobalMin (x : ι → ℝ) : Prop := P.IsMin univ x

/-- The optimal value `Val(C)` of `P(C)` (an infimum; attained, by the
existence half of Lemma 1, but nothing below needs that). -/
noncomputable def Val (C : Finset ι) : ℝ := sInf (P.F '' {x | Feasible C x})

/-- The optimality conditions (2) of the article on `C` at `x`:
`a_jᵀ r ≤ 0` for `j ∈ C`, and `a_jᵀ r = 0` on `supp x`. -/
def KKT (C : Finset ι) (x : ι → ℝ) : Prop :=
  (∀ j ∈ C, P.price x j ≤ 0) ∧ ∀ j, x j ≠ 0 → P.price x j = 0

variable {P}

lemma F_nonneg (x : ι → ℝ) : 0 ≤ P.F x := by
  unfold F; positivity

/-! ### The expansion identity -/

lemma fit_sub_fit (x y : ι → ℝ) : P.fit y - P.fit x = ∑ j, (y j - x j) • P.a j := by
  simp only [fit, sub_smul, Finset.sum_sub_distrib]

lemma inner_fit_sub_res (x y : ι → ℝ) :
    ⟪P.fit y - P.fit x, P.res x⟫_ℝ = ∑ j, (y j - x j) * P.price x j := by
  rw [fit_sub_fit, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left]
  rfl

/-- The exact expansion of the objective around `x`. -/
theorem F_expand (x y : ι → ℝ) :
    P.F y = P.F x - ∑ j, (y j - x j) * P.price x j + ‖P.fit y - P.fit x‖ ^ 2 / 2 := by
  have h1 : P.fit y - P.b = (P.fit x - P.b) + (P.fit y - P.fit x) := by abel
  have h2 : ⟪P.fit x - P.b, P.fit y - P.fit x⟫_ℝ = -∑ j, (y j - x j) * P.price x j := by
    rw [← inner_fit_sub_res, real_inner_comm, show P.fit x - P.b = -P.res x by
      simp [res]]
    rw [inner_neg_right]
  unfold F
  rw [h1, norm_add_sq_real, h2]
  ring

/-- First-order lower bound: drop the nonnegative quadratic term. -/
lemma F_ge (x y : ι → ℝ) : P.F x - ∑ j, (y j - x j) * P.price x j ≤ P.F y := by
  have := F_expand (P := P) x y
  have : 0 ≤ ‖P.fit y - P.fit x‖ ^ 2 / 2 := by positivity
  linarith

/-- Moving one coordinate: `F(x + s e_j) = F x - s a_jᵀ r + s² ‖a_j‖² / 2`. -/
lemma F_update [DecidableEq ι] (x : ι → ℝ) (j : ι) (s : ℝ) :
    P.F (Function.update x j (x j + s)) =
      P.F x - s * P.price x j + s ^ 2 * ‖P.a j‖ ^ 2 / 2 := by
  have hd : ∀ k, Function.update x j (x j + s) k - x k = if k = j then s else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [F_expand x]
  have hsum : ∑ k, (Function.update x j (x j + s) k - x k) * P.price x k =
      s * P.price x j := by
    simp only [hd, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hfit : P.fit (Function.update x j (x j + s)) - P.fit x = s • P.a j := by
    rw [fit_sub_fit]
    simp only [hd, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum, hfit, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-! ### Lemma 2: optimality conditions -/

lemma sum_nonpos_of_KKT {C : Finset ι} {x y : ι → ℝ} (hk : P.KKT C x)
    (hy : Feasible C y) : ∑ j, (y j - x j) * P.price x j ≤ 0 := by
  apply Finset.sum_nonpos
  intro j _
  by_cases hxj : x j = 0
  · rw [hxj, sub_zero]
    by_cases hjC : j ∈ C
    · exact mul_nonpos_of_nonneg_of_nonpos (hy.1 j) (hk.1 j hjC)
    · rw [hy.2 j hjC, zero_mul]
  · rw [hk.2 j hxj, mul_zero]

/-- Lemma 2 (sufficiency): a feasible point satisfying (2) solves `P(C)`.
In fact `F y ≥ F x + ‖Ay - Ax‖² / 2` for every feasible `y`. -/
lemma F_ge_of_KKT {C : Finset ι} {x y : ι → ℝ} (hk : P.KKT C x) (hy : Feasible C y) :
    P.F x + ‖P.fit y - P.fit x‖ ^ 2 / 2 ≤ P.F y := by
  have := F_expand (P := P) x y
  have := sum_nonpos_of_KKT hk hy
  linarith

theorem isMin_of_KKT {C : Finset ι} {x : ι → ℝ} (hx : Feasible C x) (hk : P.KKT C x) :
    P.IsMin C x :=
  ⟨hx, fun y hy => by
    have := F_ge_of_KKT hk hy
    have : 0 ≤ ‖P.fit y - P.fit x‖ ^ 2 / 2 := by positivity
    linarith⟩

/-- Descent step: a feasible point at which a column of `C` prices positively
can be improved inside `P(C)` (move that coordinate up). -/
theorem exists_lt_of_price_pos {C : Finset ι} {x : ι → ℝ} (hx : Feasible C x) {j : ι}
    (hj : j ∈ C) (hp : 0 < P.price x j) : ∃ y, Feasible C y ∧ P.F y < P.F x := by
  classical
  set N := ‖P.a j‖ ^ 2 with hN
  have hN0 : 0 ≤ N := by positivity
  set t := P.price x j / (N + 1) with ht_def
  have ht : 0 < t := div_pos hp (by linarith)
  have htN : t * N < P.price x j := by
    rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨Function.update x j (x j + t), ⟨fun k => ?_, fun k hk => ?_⟩, ?_⟩
  · by_cases hkj : k = j
    · subst hkj; simp only [Function.update_self]; linarith [hx.1 k]
    · rw [Function.update_of_ne hkj]; exact hx.1 k
  · have hkj : k ≠ j := fun h => hk (h ▸ hj)
    rw [Function.update_of_ne hkj]; exact hx.2 k hk
  · rw [F_update]
    have : t * (t * N / 2 - P.price x j) < 0 :=
      mul_neg_of_pos_of_neg ht (by linarith)
    nlinarith

/-- Descent step downward: if `x j > 0` and column `j` prices negatively,
lowering `x j` improves `F` inside `P(C)`. -/
theorem exists_lt_of_price_neg {C : Finset ι} {x : ι → ℝ} (hx : Feasible C x) {j : ι}
    (hxj : 0 < x j) (hp : P.price x j < 0) : ∃ y, Feasible C y ∧ P.F y < P.F x := by
  classical
  set N := ‖P.a j‖ ^ 2 with hN
  have hN0 : 0 ≤ N := by positivity
  set t := min (x j) (-P.price x j / (N + 1)) with ht_def
  have hq : 0 < -P.price x j / (N + 1) := div_pos (by linarith) (by linarith)
  have ht : 0 < t := lt_min hxj hq
  have htx : t ≤ x j := min_le_left _ _
  have htq : t ≤ -P.price x j / (N + 1) := min_le_right _ _
  have htN : t * N < -P.price x j := by
    have h1 : t * N ≤ -P.price x j / (N + 1) * N :=
      mul_le_mul_of_nonneg_right htq hN0
    have h2 : -P.price x j / (N + 1) * N < -P.price x j := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hjC : j ∈ C := by
    by_contra hC
    have := hx.2 j hC
    linarith
  refine ⟨Function.update x j (x j + -t), ⟨fun k => ?_, fun k hk => ?_⟩, ?_⟩
  · by_cases hkj : k = j
    · subst hkj; simp only [Function.update_self]; linarith
    · rw [Function.update_of_ne hkj]; exact hx.1 k
  · have hkj : k ≠ j := fun h => hk (h ▸ hjC)
    rw [Function.update_of_ne hkj]; exact hx.2 k hk
  · rw [F_update]
    have : t * (t * N / 2 + P.price x j) < 0 :=
      mul_neg_of_pos_of_neg ht (by linarith)
    nlinarith

/-- Lemma 2 (necessity): a solution of `P(C)` satisfies (2). -/
theorem KKT_of_isMin {C : Finset ι} {x : ι → ℝ} (hx : P.IsMin C x) : P.KKT C x := by
  have hneg : ∀ j ∈ C, P.price x j ≤ 0 := by
    intro j hj
    by_contra hp
    obtain ⟨y, hy, hlt⟩ := exists_lt_of_price_pos hx.1 hj (not_le.mp hp)
    exact absurd (hx.2 y hy) (not_le.mpr hlt)
  refine ⟨hneg, fun j hxj => ?_⟩
  have hjC : j ∈ C := hx.1.supp_subset (mem_supp.mpr hxj)
  have hpos : 0 < x j := lt_of_le_of_ne (hx.1.1 j) (Ne.symm hxj)
  refine le_antisymm (hneg j hjC) ?_
  by_contra hp
  obtain ⟨y, hy, hlt⟩ := exists_lt_of_price_neg hx.1 hpos (not_le.mp hp)
  exact absurd (hx.2 y hy) (not_le.mpr hlt)

/-- Lemma 2: a feasible `x` solves `P(C)` if and only if (2) holds. -/
theorem isMin_iff_KKT {C : Finset ι} {x : ι → ℝ} :
    P.IsMin C x ↔ Feasible C x ∧ P.KKT C x :=
  ⟨fun h => ⟨h.1, KKT_of_isMin h⟩, fun h => isMin_of_KKT h.1 h.2⟩

/-- A feasible point of `P(C)` that violates (2) at a column of `C` is beaten by
every solution of `P(C)`. -/
theorem F_lt_of_price_pos {C : Finset ι} {x z : ι → ℝ} (hx : Feasible C x) {j : ι}
    (hj : j ∈ C) (hp : 0 < P.price x j) (hz : P.IsMin C z) : P.F z < P.F x := by
  obtain ⟨y, hy, hlt⟩ := exists_lt_of_price_pos hx hj hp
  exact lt_of_le_of_lt (hz.2 y hy) hlt

/-! ### Lemma 3: pricing -/

/-- Lemma 3 (pricing): a solution of `P(C)` at which no column outside `C`
prices positively solves the full problem. -/
theorem isGlobalMin_of_price_nonpos {C : Finset ι} {x : ι → ℝ} (hx : P.IsMin C x)
    (hout : ∀ j, j ∉ C → P.price x j ≤ 0) : P.IsGlobalMin x := by
  have hk := KKT_of_isMin hx
  refine isMin_of_KKT (hx.1.mono (subset_univ C)) ⟨fun j _ => ?_, hk.2⟩
  by_cases hj : j ∈ C
  · exact hk.1 j hj
  · exact hout j hj

/-- A solution of some `P(C)` that is not a global minimizer has a column
pricing positively. -/
theorem exists_price_pos_of_not_isGlobalMin {C : Finset ι} {x : ι → ℝ}
    (hx : P.IsMin C x) (hg : ¬ P.IsGlobalMin x) : ∃ j, 0 < P.price x j := by
  by_contra h
  push Not at h
  exact hg (isGlobalMin_of_price_nonpos hx fun j _ => h j)

/-! ### Lemma 4: restriction -/

/-- Lemma 4(ii), first part: a solution of `P(C)` solves `P(D)` whenever
`supp x ⊆ D ⊆ C`. -/
theorem IsMin.restrict {C D : Finset ι} {x : ι → ℝ} (hx : P.IsMin C x)
    (hD : supp x ⊆ D) (hDC : D ⊆ C) : P.IsMin D x :=
  ⟨feasible_of_supp_subset hx.1.1 hD, fun y hy => hx.2 y (hy.mono hDC)⟩

/-- In particular a solution of `P(C)` solves `P(supp x)`. -/
theorem IsMin.restrict_supp {C : Finset ι} {x : ι → ℝ} (hx : P.IsMin C x) :
    P.IsMin (supp x) x :=
  hx.restrict (subset_refl _) hx.1.supp_subset

/-- Two solutions of the same restricted problem have the same value. -/
theorem IsMin.F_eq {C : Finset ι} {x y : ι → ℝ} (hx : P.IsMin C x) (hy : P.IsMin C y) :
    P.F x = P.F y :=
  le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/-- A solution of `P(C)` attains `Val(C)`. -/
theorem IsMin.val_eq {C : Finset ι} {x : ι → ℝ} (hx : P.IsMin C x) : P.Val C = P.F x := by
  have : IsLeast (P.F '' {x | Feasible C x}) (P.F x) :=
    ⟨⟨x, hx.1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hx.2 y hy⟩
  exact this.csInf_eq

/-- Lemma 4(i): enlarging the candidate set cannot raise the infimum. -/
theorem val_anti {C C' : Finset ι} (h : C ⊆ C') : P.Val C' ≤ P.Val C := by
  have hne : (P.F '' {x | Feasible C x}).Nonempty :=
    ⟨P.F 0, 0, ⟨fun _ => le_rfl, fun _ _ => rfl⟩, rfl⟩
  have hbdd : BddBelow (P.F '' {x | Feasible C' x}) :=
    ⟨0, by rintro _ ⟨y, _, rfl⟩; exact F_nonneg y⟩
  refine le_csInf hne ?_
  rintro _ ⟨y, hy, rfl⟩
  exact csInf_le hbdd ⟨y, hy.mono h, rfl⟩

/-- Lemma 4(ii), second part: `Val(D) = Val(C)`. -/
theorem IsMin.val_restrict {C D : Finset ι} {x : ι → ℝ} (hx : P.IsMin C x)
    (hD : supp x ⊆ D) (hDC : D ⊆ C) : P.Val D = P.Val C := by
  rw [(hx.restrict hD hDC).val_eq, hx.val_eq]

/-! ### Lemma 1, second half: uniqueness of the fit -/

/-- Lemma 1 (uniqueness of the fit): all solutions of `P(C)` have the same
fitted vector `Ax`, hence the same residual. -/
theorem IsMin.fit_eq {C : Finset ι} {x y : ι → ℝ} (hx : P.IsMin C x) (hy : P.IsMin C y) :
    P.fit x = P.fit y := by
  have h1 := F_ge_of_KKT (KKT_of_isMin hx) hy.1
  have h2 := hx.F_eq hy
  have h3 : ‖P.fit y - P.fit x‖ ^ 2 = 0 := by
    have : 0 ≤ ‖P.fit y - P.fit x‖ ^ 2 := by positivity
    linarith
  have : P.fit y - P.fit x = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero] at h3
    exact h3
  exact (sub_eq_zero.mp this).symm

theorem IsMin.res_eq {C : Finset ι} {x y : ι → ℝ} (hx : P.IsMin C x) (hy : P.IsMin C y) :
    P.res x = P.res y := by
  simp only [res, hx.fit_eq hy]

theorem IsMin.price_eq {C : Finset ι} {x y : ι → ℝ} (hx : P.IsMin C x) (hy : P.IsMin C y)
    (j : ι) : P.price x j = P.price y j := by
  simp only [price, hx.res_eq hy]

end Problem

end NnlsDc
