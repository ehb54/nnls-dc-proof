PDFLATEX = /Library/TeX/texbin/pdflatex
BIBTEX   = /Library/TeX/texbin/bibtex
# run from the repository root; see README for the venv
PYTHON  ?= venv/bin/python

all: main.pdf online-resource-1.pdf online-resource-2.pdf

main.pdf: main.tex refs.bib figs/convergence.pdf
	$(PDFLATEX) -interaction=nonstopmode main
	$(BIBTEX) main
	$(PDFLATEX) -interaction=nonstopmode main
	$(PDFLATEX) -interaction=nonstopmode main

online-resource-1.pdf: online-resource-1.tex
	$(PDFLATEX) -interaction=nonstopmode online-resource-1
	$(PDFLATEX) -interaction=nonstopmode online-resource-1

online-resource-2.pdf: online-resource-2.tex
	$(PDFLATEX) -interaction=nonstopmode online-resource-2
	$(PDFLATEX) -interaction=nonstopmode online-resource-2

figs/convergence.pdf:
	cd .. && $(PYTHON) experiments.py

clean:
	rm -f *.aux *.bbl *.blg *.log *.out main.pdf

.PHONY: all clean
