import NnlsDc.Algorithm

/-!
# Section 8: without (H3) the stopping test can fire at a suboptimal point

The article's two-column instance: `a₁ = (1, 1)`, `a₂ = (0, -1)`,
`b = (1, 0)`, blocks `{1}` and `{2}`, and a merge stage that re-chunks the
union of the returned supports into single columns.  Columns are indexed
`0, 1` here.

Every node solves its own problem exactly (H1) and the leaves satisfy (H2),
but round 2's re-chunked merge drops column `1` from the support `{1, 2}`
that its leaf returned, so (H3) fails.  Round 2 loses ground (a leaf reaches
`F = 0`, the root returns `F = 1/4`), and both stopping tests fire, at
`F = 1/4` while `v* = 0`.
-/

open scoped InnerProductSpace
open Finset

namespace NnlsDc

namespace Tree

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Condition (H1) alone: every node solves its own restricted problem
exactly, with no constraint linking a merge node to its children. -/
def Exact (P : Problem ι E) : Tree ι → Prop
  | leaf C x => P.IsMin C x
  | node C x _ child => P.IsMin C x ∧ ∀ i, Exact P (child i)

end Tree

namespace Rechunk

/-- The two-column problem. -/
noncomputable def Q : Problem (Fin 2) (EuclideanSpace ℝ (Fin 2)) where
  a := ![!₂[1, 1], !₂[0, -1]]
  b := !₂[1, 0]

lemma F_eq (x : Fin 2 → ℝ) : Q.F x = ((x 0 - 1) ^ 2 + (x 0 - x 1) ^ 2) / 2 := by
  rw [Problem.F, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [Q, Problem.fit, Fin.sum_univ_two]
  ring

lemma price_eq (x : Fin 2 → ℝ) :
    Q.price x 0 = 1 - 2 * x 0 + x 1 ∧ Q.price x 1 = x 0 - x 1 := by
  simp only [Problem.price, Problem.res, Problem.fit]
  constructor <;> simp [Q, PiLp.inner_apply, Fin.sum_univ_two] <;> ring

/-- Solutions: `P({1})` gives `(1/2, 0)`, `P({2})` gives `0`, and
`P({1, 2})` fits `b` exactly with `(1, 1)`. -/
noncomputable def xh : Fin 2 → ℝ := ![1 / 2, 0]
noncomputable def x0 : Fin 2 → ℝ := ![0, 0]
noncomputable def x1 : Fin 2 → ℝ := ![1, 1]

lemma isMin_xh : Q.IsMin {0} xh := by
  obtain ⟨h0, -⟩ := price_eq xh
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> norm_num [xh]
  · fin_cases j <;> simp_all [xh]
  · fin_cases j <;> simp_all [xh]
  · fin_cases j <;> simp_all [xh]

lemma isMin_x0 : Q.IsMin {1} x0 := by
  obtain ⟨-, h1⟩ := price_eq x0
  refine Problem.isMin_of_KKT ⟨fun j => ?_, fun j hj => ?_⟩ ⟨fun j hj => ?_, fun j hj => ?_⟩
  · fin_cases j <;> simp [x0]
  · fin_cases j <;> simp_all [x0]
  · fin_cases j <;> simp_all [x0]
  · fin_cases j <;> simp_all [x0]

lemma isMin_x1 : Q.IsGlobalMin x1 := by
  refine ⟨feasible_univ_iff.mpr fun j => ?_, fun y _ => ?_⟩
  · fin_cases j <;> simp [x1]
  · have : Q.F x1 = 0 := by rw [F_eq]; simp [x1]
    rw [this]
    exact Problem.F_nonneg y

lemma isMin_x1' : Q.IsMin {0, 1} x1 := by
  have h := isMin_x1
  have huniv : ({0, 1} : Finset (Fin 2)) = univ := by decide
  rw [huniv]
  exact h

lemma supp_xh : supp xh = {0} := by
  ext j
  fin_cases j <;> simp [xh]

lemma supp_x1 : supp x1 = {0, 1} := by
  ext j
  fin_cases j <;> simp [x1]

/-- Round 1 (the non-iterated pass, blocks `{1}`, `{2}`): the merge solves
the union `{1}` of the returned supports. -/
noncomputable def t1 : Tree (Fin 2) :=
  .node {0} xh 2 ![.leaf {0} xh, .leaf {1} x0]

/-- Round 2: the leaves contain `R₁ = {1}`; the merge stage re-chunks the
union `{1, 2}` of their supports into the single columns `{1}` and `{2}`,
and the root solves the union of what those chunks return. -/
noncomputable def t2 : Tree (Fin 2) :=
  .node {0} xh 2 ![.node {0} xh 1 ![.leaf {0} xh], .node {1} x0 1 ![.leaf {0, 1} x1]]

/-- **Section 8's instance.**  Both rounds satisfy (H1) and (H2), round 1
also (H3), but round 2 violates (H3); round 2 loses ground, and both stopping
tests fire (`R₂ = R₁`, `v₂ = v₁`) at `F = 1/4`, while `v* = 0`. -/
theorem stops_suboptimal :
    -- (H1) in both rounds
    t1.Exact Q ∧ t2.Exact Q ∧
    -- (H2): coverage in both rounds, feedback of `R₁` into round 2
    (∀ j, ∃ D y, t1.HasLeaf D y ∧ j ∈ D) ∧ (∀ j, ∃ D y, t2.HasLeaf D y ∧ j ∈ D) ∧
    (∀ D y, t2.HasLeaf D y → supp t1.sol ⊆ D) ∧
    -- (H3) holds in round 1 and fails in round 2
    t1.WF Q ∧ ¬ t2.WF Q ∧
    -- round 2 loses ground: a leaf fits exactly, the root does not
    t2.HasLeaf {0, 1} x1 ∧ Q.F x1 = 0 ∧ Q.F t2.sol = 1 / 4 ∧
    -- both stopping tests fire, at a suboptimal point
    supp t2.sol = supp t1.sol ∧ Q.F t2.sol = Q.F t1.sol ∧ Q.Val univ = 0 := by
  have hF1 : Q.F x1 = 0 := by rw [F_eq]; simp [x1]
  have hFh : Q.F xh = 1 / 4 := by rw [F_eq]; norm_num [xh]
  have hval : Q.Val univ = 0 := by rw [isMin_x1.val_eq, hF1]
  have hleaves2 : ∀ D y, t2.HasLeaf D y ↔ (D = {0} ∧ y = xh) ∨ (D = {0, 1} ∧ y = x1) := by
    intro D y
    simp [t2, Tree.hasLeaf_node_iff, Tree.hasLeaf_leaf_iff, Fin.exists_fin_two]
  have hleaves1 : ∀ D y, t1.HasLeaf D y ↔ (D = {0} ∧ y = xh) ∨ (D = {1} ∧ y = x0) := by
    intro D y
    simp [t1, Tree.hasLeaf_node_iff, Tree.hasLeaf_leaf_iff, Fin.exists_fin_two]
  have hsupp0 : supp x0 = ∅ := by
    ext j
    fin_cases j <;> simp [x0]
  refine ⟨?_, ?_, fun j => ?_, fun j => ?_, fun D y h => ?_, ?_, fun h => ?_,
    (hleaves2 _ _).mpr (Or.inr ⟨rfl, rfl⟩), hF1, hFh, rfl, rfl, hval⟩
  · refine ⟨isMin_xh, fun i => ?_⟩
    fin_cases i
    · exact isMin_xh
    · exact isMin_x0
  · refine ⟨isMin_xh, fun i => ?_⟩
    fin_cases i
    · exact ⟨isMin_xh, fun i => by fin_cases i; exact isMin_xh⟩
    · exact ⟨isMin_x0, fun i => by fin_cases i; exact isMin_x1'⟩
  · fin_cases j
    · exact ⟨{0}, xh, (hleaves1 _ _).mpr (Or.inl ⟨rfl, rfl⟩), by simp⟩
    · exact ⟨{1}, x0, (hleaves1 _ _).mpr (Or.inr ⟨rfl, rfl⟩), by simp⟩
  · fin_cases j
    · exact ⟨{0}, xh, (hleaves2 _ _).mpr (Or.inl ⟨rfl, rfl⟩), by simp⟩
    · exact ⟨{0, 1}, x1, (hleaves2 _ _).mpr (Or.inr ⟨rfl, rfl⟩), by simp⟩
  · show supp xh ⊆ D
    rw [supp_xh]
    rcases (hleaves2 D y).mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact subset_refl _
    · simp
  · refine ⟨isMin_xh, fun i => ?_, fun i => ?_⟩
    · fin_cases i
      · show supp xh ⊆ {0}
        rw [supp_xh]
      · show supp x0 ⊆ {0}
        rw [hsupp0]
        exact empty_subset _
    · fin_cases i
      · exact isMin_xh
      · exact isMin_x0
  · -- the second chunk solves `{2}`, but its child returned support `{1, 2}`
    have hB : supp x1 ⊆ {1} := (h.2.2 1).2.1 0
    have h0 : (0 : Fin 2) ∈ supp x1 := by rw [supp_x1]; simp
    exact absurd (hB h0) (by simp)

end Rechunk

end NnlsDc
