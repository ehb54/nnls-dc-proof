import NnlsDc

/-! Run `lake env lean AxiomCheck.lean` after `lake build`: every result below
should depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular not on `sorryAx`. -/

#print axioms NnlsDc.Run.theorem1_a
#print axioms NnlsDc.Run.theorem1_b
#print axioms NnlsDc.Run.theorem1_c
#print axioms NnlsDc.Run.stop_sound
#print axioms NnlsDc.Run.theorem2
#print axioms NnlsDc.Run.theorem2_unique
#print axioms NnlsDc.Problem.isGlobalMin_iff
#print axioms NnlsDc.Problem.prop2
#print axioms NnlsDc.Problem.l1_le_M
#print axioms NnlsDc.Counterexample.single_pass
#print axioms NnlsDc.Counterexample.merged_residual
#print axioms NnlsDc.Counterexample.optimum
#print axioms NnlsDc.Counterexample.refinement_round
#print axioms NnlsDc.Problem.l1_le_M_coord
#print axioms NnlsDc.Problem.exists_isMin
#print axioms NnlsDc.Problem.exists_isGlobalMin
#print axioms NnlsDc.Rechunk.stops_suboptimal
