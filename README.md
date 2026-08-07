# Exactness of iterated divide-and-conquer NNLS

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21839524.svg)](https://doi.org/10.5281/zenodo.21839524)

Proof that the iterative divide-and-conquer NNLS method of Brookes,
Boppana & Demeler (SC'06, doi 10.1145/1188455.1188541) — as deployed in
UltraScan's 2DSA — terminates finitely at a global minimizer of the
full-grid problem, plus a counterexample showing the non-iterated scheme
is not exact.

## Contents

- `nnls_dc_equivalence.md` — self-contained proof note (superset of the
  paper's math, with extended remarks).
- `verify.py` — assertion-based verification: counterexample, 200
  randomized trials, per-edge monotonicity checks at every merge node,
  both KKT residuals (pricing and complementarity) asserted at
  termination.
- `experiments.py` — paper driver: reruns the suites (same seed/draw
  order as verify.py), prints the LaTeX table rows, renders
  `paper/figs/convergence.{pdf,png}`.
- `paper/` — Optimization Letters manuscript in the Springer Nature
  template (`main.tex`, `sn-jnl.cls` + `sn-mathphys-num.bst` from the
  December 2024 sn-article package, `refs.bib`, `Makefile`). `make`
  builds `main.pdf` (pdflatex + bibtex; on BasicTeX install
  `algorithms algorithmicx float sttools threeparttable appendix
  breakurl wrapfig` via `tlmgr --usermode`, already done on this
  machine).

## Environment

Python needs numpy/scipy/matplotlib (tested versions pinned in
`requirements.txt`):

    python3 -m venv venv && venv/bin/pip install -r requirements.txt
    venv/bin/python verify.py
    venv/bin/python experiments.py

Seeds 20260807 (suites i, iii, iv) and 20260808 (interlaced-lattice
suite) reproduce all numbers in the paper's Table 1. Values printed by
the code are unhalved squared residual norms ||Ax-b||^2 = 2F.

## License

The scripts (`verify.py`, `experiments.py`, `paper/Makefile`) are
released under the MIT License (see `LICENSE`). The manuscript text
(`paper/main.tex`, `paper/refs.bib`, the figures, and
`nnls_dc_equivalence.md`) is (c) 2026 Emre H. Brookes, all rights
reserved pending journal publication.

## Archive

Releases are archived on Zenodo under concept DOI
[10.5281/zenodo.21839524](https://doi.org/10.5281/zenodo.21839524)
(v1.0.0 = submission version, doi 10.5281/zenodo.21839525).

## Possible future work

- Replace the Gaussian-kernel surrogates with real Lamm-equation
  (ASTFEM) design matrices exported from UltraScan.
