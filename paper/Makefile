PDFLATEX = /Library/TeX/texbin/pdflatex
BIBTEX   = /Library/TeX/texbin/bibtex

all: main.pdf

main.pdf: main.tex refs.bib figs/convergence.pdf
	$(PDFLATEX) -interaction=nonstopmode main
	$(BIBTEX) main
	$(PDFLATEX) -interaction=nonstopmode main
	$(PDFLATEX) -interaction=nonstopmode main

figs/convergence.pdf:
	cd .. && python experiments.py

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf

.PHONY: all clean
