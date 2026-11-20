# Exactness of iterated divide-and-conquer NNLS

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21839524.svg)](https://doi.org/10.5281/zenodo.21839524)

Proof that the iterative divide-and-conquer NNLS method of Brookes,
Boppana & Demeler (SC'06, doi 10.1145/1188455.1188541), the method
behind UltraScan's 2DSA, terminates finitely at a global minimizer of
the full-grid problem when its subproblems are solved exactly and its
merges union whole supports, plus a counterexample showing the
non-iterated scheme is not exact. How the shipped UltraScan code
relates to these conditions is set out in Online Resource 2.

## Contents

- `paper/` — Optimization Letters manuscript in the Springer Nature
  template (`main.tex`, `refs.bib`, `sn-jnl.cls` + `sn-mathphys-num.bst`
  from the December 2024 sn-article package, `Makefile`), with two
  supplements: `online-resource-1.tex` (an intuitive guide to the
  proof) and `online-resource-2.tex` (notes on the UltraScan
  implementation). `make` builds all three PDFs (pdflatex + bibtex; on
  BasicTeX, install `algorithms algorithmicx float sttools
  threeparttable appendix breakurl wrapfig` via `tlmgr --usermode`).
- `verify.py` — assertion-based verification: counterexample, 200
  randomized trials, per-edge monotonicity checks at every merge node,
  both KKT residuals (pricing and complementarity) asserted at
  termination.
- `experiments.py` — paper driver: reruns the suites (same seed/draw
  order as verify.py), the scaling probe and the cycling probe, prints
  the LaTeX table rows and the statistics quoted in the text, and renders
  `paper/figs/convergence.{pdf,png}`.
- `nnls_dc_equivalence.md` — the working proof note that preceded the
  manuscript, kept for its extended remarks. Its numbering differs, and
  where the two differ the manuscript is authoritative.
- `lean/` — a Lean 4 + Mathlib formalization of the article's lemmas,
  Theorems 1–2, Propositions 1–2, the Section 6 bound on `‖x*‖₁` and the
  Section 8 re-chunking instance; machine-checked, no `sorry` (see
  `lean/README.md`).

## Environment

Python needs numpy/scipy/matplotlib (tested versions pinned in
`requirements.txt`):

    python3 -m venv venv && venv/bin/pip install -r requirements.txt
    venv/bin/python verify.py
    venv/bin/python experiments.py

Seeds 20260807 (suites i, iii, iv) and 20260808 (interlaced-lattice
suite) reproduce Table 1, 20260809 the scaling probe of Table 2, and
20260810 the cycling probe. Values printed by the code are unhalved
squared residual norms ||Ax-b||^2 = 2F. The BLAS results are not
bitwise reproducible from run to run, so regenerating the figure can
shift the roundoff-level tails of panel (a) slightly; every number in
the tables and text reproduces exactly.

## License

The scripts (`verify.py`, `experiments.py`, `paper/Makefile`) are
released under the MIT License (see `LICENSE`). The manuscript and
supplement texts (`paper/*.tex`, `paper/refs.bib`, the figures, the
PDFs, and `nnls_dc_equivalence.md`) are (c) 2026 Emre H. Brookes, all
rights reserved pending journal publication.

## Archive

Releases are archived on Zenodo under concept DOI
[10.5281/zenodo.21839524](https://doi.org/10.5281/zenodo.21839524),
which always resolves to the latest release; each release also has
its own version DOI. Release v1.2.0 accompanies the submitted
manuscript.

## Possible future work

- Replace the Gaussian-kernel surrogates with real Lamm-equation
  (ASTFEM) design matrices exported from UltraScan.
