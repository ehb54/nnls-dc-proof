import NnlsDc.Basic

/-!
# Lemma 1, first half: every restricted problem attains its minimum

The article's proof cites closedness of finitely generated cones.  This file
argues directly instead, by strong induction on the candidate set `C`:

* least squares on `C` *without* the sign constraint has a minimizer `z`
  (orthogonal projection of `b` onto a finite-dimensional subspace);
* if `z ≥ 0` it solves `P(C)`;
* otherwise every feasible `y` is matched, along the segment from `y` towards
  `z`, by a point that is no worse and is feasible for `C` minus one column,
  so the best of the smaller problems' minimizers solves `P(C)`.

Nothing in Theorems 1–2 depends on this file: condition (H1) supplies the
minimizers there.  It shows that (H1) can always be met.
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

namespace Problem

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Problem ι E}

/-- `F` is convex along segments. -/
lemma F_segment (x z : ι → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.F (fun j => x j + t * (z j - x j)) ≤ (1 - t) * P.F x + t * P.F z := by
  have h1 := F_expand (P := P) x (fun j => x j + t * (z j - x j))
  have h2 := F_expand (P := P) x z
  have hs : ∑ j, ((x j + t * (z j - x j)) - x j) * P.price x j =
      t * ∑ j, (z j - x j) * P.price x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hf : P.fit (fun j => x j + t * (z j - x j)) - P.fit x = t • (P.fit z - P.fit x) := by
    rw [fit_sub_fit, fit_sub_fit, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]; congr 1; ring
  rw [hs, hf, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
  have hq : 0 ≤ ‖P.fit z - P.fit x‖ ^ 2 := by positivity
  have htt : t ^ 2 ≤ t := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr htt) hq]

/-- Amplitude vectors vanishing off `C`, as a submodule. -/
def supported (C : Finset ι) : Submodule ℝ (ι → ℝ) where
  carrier := {x | ∀ j, j ∉ C → x j = 0}
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c x hx j hj
    simp [hx j hj]

omit [Fintype ι] in
lemma mem_supported {C : Finset ι} {x : ι → ℝ} : x ∈ supported C ↔ ∀ j, j ∉ C → x j = 0 :=
  Iff.rfl

/-- The fit `x ↦ Ax` as a linear map. -/
noncomputable def fitL (P : Problem ι E) : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ P.a

lemma fitL_apply (x : ι → ℝ) : P.fitL x = P.fit x := by
  simp [fitL, fit, Fintype.linearCombination_apply]

/-- Least squares on `C` without the sign constraint has a minimizer. -/
lemma exists_unconstrained (C : Finset ι) :
    ∃ z ∈ supported C, ∀ x ∈ supported C, P.F z ≤ P.F x := by
  set K : Submodule ℝ E := (supported C).map P.fitL
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex
    ⟨0, K.zero_mem⟩ (Submodule.isComplete_of_finiteDimensional K) K.convex P.b
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hvK
  refine ⟨z, hz, fun x hx => ?_⟩
  have hbdd : BddBelow (Set.range fun w : (K : Set E) => ‖P.b - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have hle : ‖P.b - P.fitL z‖ ≤ ‖P.b - P.fitL x‖ := by
    rw [hv]
    exact ciInf_le hbdd ⟨P.fitL x, Submodule.mem_map_of_mem hx⟩
  rw [fitL_apply, fitL_apply] at hle
  unfold F
  rw [norm_sub_rev (P.fit z), norm_sub_rev (P.fit x)]
  gcongr

/-- Segment step: if `z`, supported in `C`, is no worse than a feasible `y`
and has a negative coordinate, then some point of the segment from `y`
towards `z` is no worse than `y` and is feasible for `C` minus one column. -/
lemma exists_face [DecidableEq ι] {C : Finset ι} {y z : ι → ℝ} (hy : Feasible C y) (hz : z ∈ supported C)
    (hzy : P.F z ≤ P.F y) {j₀ : ι} (hj₀ : z j₀ < 0) :
    ∃ j ∈ C, ∃ w, Feasible (C.erase j) w ∧ P.F w ≤ P.F y := by
  classical
  have hj₀C : j₀ ∈ C := by
    by_contra h
    have := hz j₀ h
    linarith
  set J := C.filter fun j => z j < 0 with hJdef
  have hJ : J.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨hj₀C, hj₀⟩⟩
  obtain ⟨j, hjJ, hmin⟩ := J.exists_min_image (fun j => y j / (y j - z j)) hJ
  have hjC : j ∈ C := (Finset.mem_filter.mp hjJ).1
  have hzj : z j < 0 := (Finset.mem_filter.mp hjJ).2
  have hden : 0 < y j - z j := by linarith [hy.1 j]
  set t := y j / (y j - z j) with ht_def
  have ht0 : 0 ≤ t := div_nonneg (hy.1 j) hden.le
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hden]
    linarith
  refine ⟨j, hjC, fun k => y k + t * (z k - y k), ⟨fun k => ?_, fun k hk => ?_⟩, ?_⟩
  · show 0 ≤ y k + t * (z k - y k)
    by_cases hkJ : k ∈ J
    · have hzk : z k < 0 := (Finset.mem_filter.mp hkJ).2
      have hdk : 0 < y k - z k := by linarith [hy.1 k]
      have htk : t ≤ y k / (y k - z k) := hmin k hkJ
      rw [le_div_iff₀ hdk] at htk
      nlinarith
    · have hzk : 0 ≤ z k := by
        by_cases hkC : k ∈ C
        · exact not_lt.mp fun h => hkJ (Finset.mem_filter.mpr ⟨hkC, h⟩)
        · rw [hz k hkC]
      have := hy.1 k
      nlinarith
  · show y k + t * (z k - y k) = 0
    by_cases hkj : k = j
    · subst hkj
      have hne : y k - z k ≠ 0 := hden.ne'
      rw [ht_def]
      field_simp
      ring
    · have hkC : k ∉ C := fun h => hk (Finset.mem_erase.mpr ⟨hkj, h⟩)
      rw [hy.2 k hkC, hz k hkC]
      ring
  · calc P.F (fun k => y k + t * (z k - y k)) ≤ (1 - t) * P.F y + t * P.F z :=
          F_segment y z ht0 ht1
      _ ≤ P.F y := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hzy)]

/-- **Lemma 1 (existence).**  Every restricted problem `P(C)` attains its
minimum. -/
theorem exists_isMin (C : Finset ι) : ∃ x, P.IsMin C x := by
  classical
  refine Finset.strongInduction (p := fun C => ∃ x, P.IsMin C x) (fun C ih => ?_) C
  obtain ⟨z, hz, hzmin⟩ := exists_unconstrained (P := P) C
  by_cases hnn : ∀ j, 0 ≤ z j
  · exact ⟨z, ⟨hnn, hz⟩, fun y hy => hzmin y hy.2⟩
  · push Not at hnn
    obtain ⟨j₀, hj₀⟩ := hnn
    have hj₀C : j₀ ∈ C := by
      by_contra h
      have := hz j₀ h
      linarith
    have hface : ∀ j ∈ C, ∃ x, P.IsMin (C.erase j) x := fun j hj =>
      ih _ (Finset.erase_ssubset hj)
    choose! xf hxf using hface
    obtain ⟨j, hjC, hjmin⟩ := C.exists_min_image (fun j => P.F (xf j)) ⟨j₀, hj₀C⟩
    refine ⟨xf j, (hxf j hjC).1.mono (Finset.erase_subset j C), fun y hy => ?_⟩
    obtain ⟨k, hkC, w, hw, hwy⟩ := exists_face hy hz (hzmin y hy.2) hj₀
    calc P.F (xf j) ≤ P.F (xf k) := hjmin k hkC
      _ ≤ P.F w := (hxf k hkC).2 w hw
      _ ≤ P.F y := hwy

/-- In particular `Val(C)` is attained. -/
theorem exists_val_eq (C : Finset ι) : ∃ x, P.IsMin C x ∧ P.F x = P.Val C := by
  obtain ⟨x, hx⟩ := exists_isMin (P := P) C
  exact ⟨x, hx, hx.val_eq.symm⟩

/-- The full problem has a global minimizer. -/
theorem exists_isGlobalMin : ∃ x, P.IsGlobalMin x :=
  exists_isMin univ

end Problem

end NnlsDc
