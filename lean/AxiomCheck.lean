import NnlsDc

/-! Run `lake env lean AxiomCheck.lean` after `lake build`: every result below
should depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular not on `sorryAx`.  The list covers every result
in the README's table, in the article's order. -/

-- the objective's expansion
#print axioms NnlsDc.Problem.F_expand
-- Lemma 1
#print axioms NnlsDc.Problem.exists_isMin
#print axioms NnlsDc.Problem.exists_isGlobalMin
#print axioms NnlsDc.Problem.IsMin.fit_eq
-- Lemma 2
#print axioms NnlsDc.Problem.isMin_iff_KKT
-- Lemma 3
#print axioms NnlsDc.Problem.isGlobalMin_of_price_nonpos
-- Lemma 4
#print axioms NnlsDc.Problem.val_anti
#print axioms NnlsDc.Problem.IsMin.restrict
#print axioms NnlsDc.Problem.IsMin.val_restrict
-- Lemma 5
#print axioms NnlsDc.Tree.WF.F_le_child
#print axioms NnlsDc.Tree.WF.F_sol_le
-- Lemmas 6 and 7
#print axioms NnlsDc.Run.v_succ_le
#print axioms NnlsDc.Run.v_succ_lt
-- Theorem 1
#print axioms NnlsDc.Run.theorem1_a
#print axioms NnlsDc.Run.theorem1_b
#print axioms NnlsDc.Run.stop_sound
#print axioms NnlsDc.Run.theorem1_c
-- Theorem 2
#print axioms NnlsDc.Run.theorem2
#print axioms NnlsDc.Run.theorem2_unique
#print axioms NnlsDc.Problem.isGlobalMin_iff
#print axioms NnlsDc.Problem.eq_of_isGlobalMin
-- Proposition 1
#print axioms NnlsDc.Counterexample.single_pass
#print axioms NnlsDc.Counterexample.single_pass_tree
#print axioms NnlsDc.Counterexample.single_pass_supp
#print axioms NnlsDc.Counterexample.merged_residual
#print axioms NnlsDc.Counterexample.optimum
#print axioms NnlsDc.Counterexample.refinement_round
#print axioms NnlsDc.Counterexample.two_rounds
-- Proposition 2
#print axioms NnlsDc.Problem.prop2
-- Section 6, the bound on ‖x*‖₁
#print axioms NnlsDc.Problem.l1_bound
#print axioms NnlsDc.Problem.l1_le_M
#print axioms NnlsDc.Problem.l1_le_M_coord
-- Section 8, the re-chunking instance
#print axioms NnlsDc.Rechunk.stops_suboptimal
-- Section 8, the parametrized instance (a slow round)
#print axioms NnlsDc.SlowRound.rounds
#print axioms NnlsDc.SlowRound.three_rounds
#print axioms NnlsDc.SlowRound.optimum
#print axioms NnlsDc.SlowRound.gap_fraction
#print axioms NnlsDc.SlowRound.tolerance_fires
#print axioms NnlsDc.SlowRound.canonical_rounds
