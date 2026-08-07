# Exactness of iterated divide-and-conquer NNLS

Proof that the iterative divide-and-conquer NNLS method of Brookes,
Boppana & Demeler (SC'06, doi 10.1145/1188455.1188541) — as deployed in
UltraScan's 2DSA — terminates finitely at a global minimizer of the
full-grid problem, plus a counterexample showing the non-iterated scheme
is not exact.

## Contents

- `nnls_dc_equivalence.md` — self-contained proof note (superset of the
  paper's math, with extended remarks).
- `verify.py` — assertion-based verification: counterexample, 160
  randomized trials, per-node monotonicity checks, KKT certificates.
- `experiments.py` — paper driver: reruns the suites (same seed/draw
  order as verify.py), prints the LaTeX table rows, renders
  `paper/figs/convergence.{pdf,png}`.
- `paper/` — Optimization Letters draft (`main.tex`, `refs.bib`,
  `Makefile`). `make` builds `main.pdf` (pdflatex + bibtex; BasicTeX
  needs `algorithms`/`algorithmicx`/`float` installed via
  `tlmgr --usermode`, already done on this machine).

## Environment

Python needs numpy/scipy/matplotlib:

    python3 -m venv venv && venv/bin/pip install numpy scipy matplotlib
    venv/bin/python verify.py
    venv/bin/python experiments.py

Seed 20260807 reproduces all numbers in the paper's Table 1.

## Submission TODOs (flagged in main.tex/refs.bib)

- Verify page range of the Demeler 2005 RSC chapter citation.
- Retarget to Springer Nature `sn-jnl.cls` at submission.
- Optional: add a LICENSE (scripts) and archive a release via Zenodo for
  a citable DOI.
