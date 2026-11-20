import NnlsDc.Basic

/-!
# Algorithms 1–2, Lemmas 5–7 and Theorem 1

One round of the method (Algorithm 1) is recorded as a *solved merge tree*:
every node carries the candidate set it solved and the solution it returned.
Leaves are the blocks `B_i` (each containing the incumbent support); internal
nodes are merges, with any fan-in.  A run of Algorithm 2 is a sequence of such
trees, round `k ≥ 1`, round 1 being the non-iterated pass (`R₀ = ∅`).

The article's conditions become hypotheses on a run:

* (H1) every node solves its restricted problem exactly (`Tree.WF`);
* (H2) the leaves of each round cover all columns, and from round 2 on every
  leaf contains the previous round's support (`Run.cover`, `Run.feedback`);
* (H3) every merge node's candidate set contains the complete returned support
  of each child (`Tree.WF`).

Nothing else is assumed: partitions and merge trees may change from round to
round, and *which* minimizer a node returns is arbitrary (it may differ
between nodes solving the same candidate set).
-/

open Finset

namespace NnlsDc

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A solved merge tree for one round.  Every node records the candidate set
it solved and the solution it returned; an internal node has `k` children
indexed by `Fin k`. -/
inductive Tree (ι : Type*) where
  | leaf (C : Finset ι) (x : ι → ℝ)
  | node (C : Finset ι) (x : ι → ℝ) (k : ℕ) (child : Fin k → Tree ι)

namespace Tree

/-- The candidate set solved at the root. -/
def cand : Tree ι → Finset ι
  | leaf C _ => C
  | node C _ _ _ => C

/-- The solution returned at the root. -/
def sol : Tree ι → ι → ℝ
  | leaf _ x => x
  | node _ x _ _ => x

/-- `t.HasLeaf D y`: the tree has a leaf that solved `D` and returned `y`. -/
inductive HasLeaf : Tree ι → Finset ι → (ι → ℝ) → Prop
  | leaf (C : Finset ι) (x : ι → ℝ) : HasLeaf (Tree.leaf C x) C x
  | node {C : Finset ι} {x : ι → ℝ} {k : ℕ} {child : Fin k → Tree ι} (i : Fin k)
      {D : Finset ι} {y : ι → ℝ} :
      HasLeaf (child i) D y → HasLeaf (Tree.node C x k child) D y

omit [Fintype ι] in
theorem hasLeaf_leaf_iff {C D : Finset ι} {x y : ι → ℝ} :
    (Tree.leaf C x).HasLeaf D y ↔ D = C ∧ y = x := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .leaf _ _

omit [Fintype ι] in
theorem hasLeaf_node_iff {C D : Finset ι} {x y : ι → ℝ} {k : ℕ} {child : Fin k → Tree ι} :
    (Tree.node C x k child).HasLeaf D y ↔ ∃ i, (child i).HasLeaf D y := by
  constructor
  · intro h
    cases h with
    | node i h => exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact .node i h

/-- Conditions (H1) and (H3) on a round's tree: every node solves its
restricted problem exactly, and every merge node's candidate set contains the
complete returned support of each child. -/
def WF (P : Problem ι E) : Tree ι → Prop
  | leaf C x => P.IsMin C x
  | node C x _ child => P.IsMin C x ∧ (∀ i, supp (child i).sol ⊆ C) ∧ ∀ i, WF P (child i)

variable {P : Problem ι E}

theorem WF.isMin {t : Tree ι} (ht : t.WF P) : P.IsMin t.cand t.sol := by
  cases t with
  | leaf C x => exact ht
  | node C x k child => exact ht.1

theorem WF.isMin_of_hasLeaf {t : Tree ι} (ht : t.WF P) {D : Finset ι} {y : ι → ℝ}
    (h : t.HasLeaf D y) : P.IsMin D y := by
  induction h with
  | leaf C x => exact ht
  | node i _ ih => exact ih (ht.2.2 i)

/-- Lemma 5, first part: a merge node is at least as good as each child,
because the child's complete support is in the node's candidate set. -/
theorem WF.F_le_child {C : Finset ι} {x : ι → ℝ} {k : ℕ} {child : Fin k → Tree ι}
    (ht : (Tree.node C x k child).WF P) (i : Fin k) : P.F x ≤ P.F (child i).sol :=
  ht.1.2 _ (feasible_of_supp_subset (ht.2.2 i).isMin.1.1 (ht.2.1 i))

/-- Lemma 5 (tree descent): the root's value is at most every leaf's value. -/
theorem WF.F_sol_le {t : Tree ι} (ht : t.WF P) {D : Finset ι} {y : ι → ℝ}
    (h : t.HasLeaf D y) : P.F t.sol ≤ P.F y := by
  induction h with
  | leaf C x => exact le_rfl
  | node i _ ih => exact le_trans (WF.F_le_child ht i) (ih (ht.2.2 i))

end Tree

/-- A run of Algorithm 2 satisfying (H1)–(H3).  `tree k` is the solved merge
tree of round `k ≥ 1`; round 1 is the non-iterated pass (`R₀ = ∅`, so it has
no feedback condition).  Index `0` is unused. -/
structure Run (P : Problem ι E) where
  /-- The solved merge tree of round `k`. -/
  tree : ℕ → Tree ι
  /-- (H1) and (H3) in every round. -/
  wf : ∀ k, 1 ≤ k → (tree k).WF P
  /-- Every round has a leaf (Algorithm 1 has `p ≥ 2` of them). -/
  hasLeaf : ∀ k, 1 ≤ k → ∃ D y, (tree k).HasLeaf D y
  /-- (H2), coverage: the leaves of every round cover all columns. -/
  cover : ∀ k, 1 ≤ k → ∀ j, ∃ D y, (tree k).HasLeaf D y ∧ j ∈ D
  /-- (H2), feedback: from round 2 on, every leaf contains the previous
  round's support. -/
  feedback : ∀ k, 1 ≤ k → ∀ D y, (tree (k + 1)).HasLeaf D y → supp (tree k).sol ⊆ D

/-- The set `V = {Val(C) : C ⊆ S}` of restricted optimal values. -/
noncomputable def values (P : Problem ι E) : Finset ℝ := univ.image P.Val

namespace Run

variable {P : Problem ι E} (ρ : Run P)

/-- The result `x_k` of round `k`. -/
def x (k : ℕ) : ι → ℝ := (ρ.tree k).sol

/-- `R_k = supp x_k`. -/
noncomputable def R (k : ℕ) : Finset ι := supp (ρ.x k)

/-- `v_k = F(x_k)`. -/
noncomputable def v (k : ℕ) : ℝ := P.F (ρ.x k)

/-- Algorithm 2's stopping test at round `k ≥ 2`: the support or the value is
unchanged from round `k - 1`. -/
def StopsAt (k : ℕ) : Prop := 2 ≤ k ∧ (ρ.R k = ρ.R (k - 1) ∨ ρ.v k = ρ.v (k - 1))

theorem isMin (k : ℕ) (hk : 1 ≤ k) : P.IsMin (ρ.tree k).cand (ρ.x k) :=
  (ρ.wf k hk).isMin

theorem nonneg (k : ℕ) (hk : 1 ≤ k) (j : ι) : 0 ≤ ρ.x k j :=
  (ρ.isMin k hk).1.1 j

/-- The incumbent `x_k` is feasible for every leaf problem of round `k + 1`
(this is where feedback, (H2), enters). -/
theorem feasible_leaf (k : ℕ) (hk : 1 ≤ k) {D : Finset ι} {y : ι → ℝ}
    (hl : (ρ.tree (k + 1)).HasLeaf D y) : Feasible D (ρ.x k) :=
  feasible_of_supp_subset (ρ.nonneg k hk) (ρ.feedback k hk D y hl)

/-- Lemma 4(ii) applied to a round: `v_k = Val(R_k)`. -/
theorem v_eq_val (k : ℕ) (hk : 1 ≤ k) : ρ.v k = P.Val (ρ.R k) :=
  ((ρ.isMin k hk).restrict_supp.val_eq).symm

theorem v_mem_values (k : ℕ) (hk : 1 ≤ k) : ρ.v k ∈ values P := by
  rw [ρ.v_eq_val k hk]
  exact mem_image_of_mem _ (mem_univ _)

/-- An unchanged support forces an unchanged value. -/
theorem v_eq_of_R_eq {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (h : ρ.R k = ρ.R l) :
    ρ.v k = ρ.v l := by
  rw [ρ.v_eq_val k hk, ρ.v_eq_val l hl, h]

/-- Lemma 6 (monotone rounds): `v_{k+1} ≤ v_k`. -/
theorem v_succ_le (k : ℕ) (hk : 1 ≤ k) : ρ.v (k + 1) ≤ ρ.v k := by
  obtain ⟨D, y, hl⟩ := ρ.hasLeaf (k + 1) (by omega)
  have hwf := ρ.wf (k + 1) (by omega)
  calc ρ.v (k + 1) = P.F (ρ.tree (k + 1)).sol := rfl
    _ ≤ P.F y := hwf.F_sol_le hl
    _ ≤ P.F (ρ.x k) := (hwf.isMin_of_hasLeaf hl).2 _ (ρ.feasible_leaf k hk hl)

/-- Lemma 7 (strict descent off the optimum): if `x_k` is not a global
minimizer then `v_{k+1} < v_k`.  Some column prices positively at `x_k`; by
coverage it lies in a leaf of round `k + 1`, which by feedback also contains
`R_k`, so that leaf beats `x_k`, and by Lemma 5 so does the root. -/
theorem v_succ_lt (k : ℕ) (hk : 1 ≤ k) (hg : ¬ P.IsGlobalMin (ρ.x k)) :
    ρ.v (k + 1) < ρ.v k := by
  obtain ⟨j, hj⟩ := Problem.exists_price_pos_of_not_isGlobalMin (ρ.isMin k hk) hg
  obtain ⟨D, y, hl, hjD⟩ := ρ.cover (k + 1) (by omega) j
  have hwf := ρ.wf (k + 1) (by omega)
  calc ρ.v (k + 1) = P.F (ρ.tree (k + 1)).sol := rfl
    _ ≤ P.F y := hwf.F_sol_le hl
    _ < P.F (ρ.x k) :=
        Problem.F_lt_of_price_pos (ρ.feasible_leaf k hk hl) hjD hj (hwf.isMin_of_hasLeaf hl)

/-- A round whose value does not improve was preceded by a global minimizer,
and is itself one. -/
theorem isGlobalMin_of_v_eq (k : ℕ) (hk : 1 ≤ k) (h : ρ.v (k + 1) = ρ.v k) :
    P.IsGlobalMin (ρ.x k) ∧ P.IsGlobalMin (ρ.x (k + 1)) := by
  have hg : P.IsGlobalMin (ρ.x k) := by
    by_contra hg
    have := ρ.v_succ_lt k hk hg
    linarith
  refine ⟨hg, feasible_univ_iff.mpr (ρ.nonneg (k + 1) (by omega)), fun y hy => ?_⟩
  calc P.F (ρ.x (k + 1)) = ρ.v (k + 1) := rfl
    _ = ρ.v k := h
    _ ≤ P.F y := hg.2 y hy

/-- Once a round returns a global minimizer, every later round returns one,
with the same value. -/
theorem stays_optimal (k : ℕ) (hk : 1 ≤ k) (hg : P.IsGlobalMin (ρ.x k)) :
    ρ.v (k + 1) = ρ.v k ∧ P.IsGlobalMin (ρ.x (k + 1)) := by
  have heq : ρ.v (k + 1) = ρ.v k :=
    le_antisymm (ρ.v_succ_le k hk)
      (hg.2 _ (feasible_univ_iff.mpr (ρ.nonneg (k + 1) (by omega))))
  exact ⟨heq, (ρ.isGlobalMin_of_v_eq k hk heq).2⟩

/-- A strictly decreasing stretch of a real sequence. -/
lemma lt_of_chain {v : ℕ → ℝ} {a b : ℕ} (h : ∀ k, a ≤ k → k < b → v (k + 1) < v k)
    {i j : ℕ} (hai : a ≤ i) (hij : i < j) (hjb : j ≤ b) : v j < v i := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h' | h'
    · exact lt_trans (h j (by omega) (by omega)) (ih h' (by omega))
    · subst h'; exact h i hai (by omega)

/-- Rounds `1, …, b` of a strictly decreasing stretch are at most `|V|` many. -/
theorem le_card_values {b : ℕ} (h : ∀ k, 1 ≤ k → k < b → ρ.v (k + 1) < ρ.v k) :
    b ≤ (values P).card := by
  have hinj : Set.InjOn ρ.v (Icc 1 b : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (lt_of_chain h hi.1 hlt hj.2).ne' hij
    · exact (lt_of_chain h hj.1 hlt hi.2).ne hij
  have hmaps : ∀ k ∈ Icc 1 b, ρ.v k ∈ values P := fun k hk =>
    ρ.v_mem_values k (mem_Icc.mp hk).1
  have := card_le_card_of_injOn ρ.v hmaps hinj
  simpa using this

/-- Some round returns a global minimizer. -/
theorem exists_isGlobalMin : ∃ k, 1 ≤ k ∧ P.IsGlobalMin (ρ.x k) := by
  by_contra hcon
  push Not at hcon
  have h := ρ.le_card_values (b := (values P).card + 1) fun k hk _ =>
    ρ.v_succ_lt k hk (hcon k hk)
  omega

open Classical in
/-- `K`: the first round that returns a global minimizer. -/
noncomputable def K : ℕ := Nat.find ρ.exists_isGlobalMin

theorem one_le_K : 1 ≤ ρ.K := by
  classical
  exact (Nat.find_spec ρ.exists_isGlobalMin).1

theorem isGlobalMin_K : P.IsGlobalMin (ρ.x ρ.K) := by
  classical
  exact (Nat.find_spec ρ.exists_isGlobalMin).2

theorem not_isGlobalMin_of_lt_K {k : ℕ} (hk : 1 ≤ k) (hK : k < ρ.K) :
    ¬ P.IsGlobalMin (ρ.x k) := by
  classical
  exact fun hg => Nat.find_min ρ.exists_isGlobalMin hK ⟨hk, hg⟩

theorem isGlobalMin_of_K_le {k : ℕ} (hk : ρ.K ≤ k) :
    P.IsGlobalMin (ρ.x k) ∧ ρ.v k = ρ.v ρ.K := by
  induction k with
  | zero => exact absurd hk (by have := ρ.one_le_K; omega)
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · have hk' : ρ.K ≤ k := Nat.lt_succ_iff.mp h
      obtain ⟨hg, hv⟩ := ih hk'
      obtain ⟨hv', hg'⟩ := ρ.stays_optimal k (le_trans ρ.one_le_K hk') hg
      exact ⟨hg', hv'.trans hv⟩
    · rw [← h]; exact ⟨ρ.isGlobalMin_K, rfl⟩

/-- **Theorem 1(a).**  The first round `K` returning a global minimizer exists
and satisfies `K ≤ |V|`, `V = {Val(C) : C ⊆ S}`; every later round returns a
global minimizer, with value `v* = Val(S)`. -/
theorem theorem1_a :
    1 ≤ ρ.K ∧ P.IsGlobalMin (ρ.x ρ.K) ∧
    (∀ k, 1 ≤ k → k < ρ.K → ¬ P.IsGlobalMin (ρ.x k)) ∧
    ρ.K ≤ (values P).card ∧
    ∀ k, ρ.K ≤ k → P.IsGlobalMin (ρ.x k) ∧ ρ.v k = P.Val univ := by
  refine ⟨ρ.one_le_K, ρ.isGlobalMin_K, fun k hk hK => ρ.not_isGlobalMin_of_lt_K hk hK,
    ρ.le_card_values fun k hk hK => ρ.v_succ_lt k hk (ρ.not_isGlobalMin_of_lt_K hk hK),
    fun k hk => ?_⟩
  obtain ⟨hg, _⟩ := ρ.isGlobalMin_of_K_le hk
  exact ⟨hg, (Problem.IsMin.val_eq hg).symm⟩

/-- **Theorem 1(b).**  If a round leaves the value unchanged, `v_k = v_{k-1}`
for some `k ≥ 2`, then `x_{k-1}` and `x_k` are global minimizers. -/
theorem theorem1_b (k : ℕ) (hk : 2 ≤ k) (h : ρ.v k = ρ.v (k - 1)) :
    P.IsGlobalMin (ρ.x (k - 1)) ∧ P.IsGlobalMin (ρ.x k) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  simpa using ρ.isGlobalMin_of_v_eq l (by omega) (by simpa using h)

/-- The implemented stopping rule is a sound certificate: whenever either
test fires (unchanged support or unchanged value), the last two results are
global minimizers. -/
theorem stop_sound {k : ℕ} (h : ρ.StopsAt k) :
    P.IsGlobalMin (ρ.x (k - 1)) ∧ P.IsGlobalMin (ρ.x k) := by
  obtain ⟨hk, hR | hv⟩ := h
  · exact ρ.theorem1_b k hk (ρ.v_eq_of_R_eq (by omega) (by omega) hR)
  · exact ρ.theorem1_b k hk hv

/-- **Theorem 1(c).**  Algorithm 2 halts at round `K + 1 ≤ |V| + 1` exactly:
no stopping test fires at any round `k ≤ K`, and the value test fires at
round `K + 1`. -/
theorem theorem1_c :
    (∀ k, k ≤ ρ.K → ¬ ρ.StopsAt k) ∧ ρ.v (ρ.K + 1) = ρ.v ρ.K ∧ ρ.StopsAt (ρ.K + 1) ∧
    ρ.K + 1 ≤ (values P).card + 1 := by
  have hv : ρ.v (ρ.K + 1) = ρ.v ρ.K := (ρ.stays_optimal ρ.K ρ.one_le_K ρ.isGlobalMin_K).1
  refine ⟨fun k hkK hs => ?_, hv, ⟨by have := ρ.one_le_K; omega, Or.inr (by simpa using hv)⟩,
    by have := ρ.theorem1_a.2.2.2.1; omega⟩
  have h2 := hs.1
  exact ρ.not_isGlobalMin_of_lt_K (k := k - 1) (by omega) (by omega) (ρ.stop_sound hs).1

end Run

end NnlsDc
