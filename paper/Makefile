PDFLATEX = /Library/TeX/texbin/pdflatex
BIBTEX   = /Library/TeX/texbin/bibtex

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
	cd .. && python experiments.py

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf

.PHONY: all clean
