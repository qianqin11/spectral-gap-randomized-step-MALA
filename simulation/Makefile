.PHONY: all paper figures simulations clean

all: paper

paper: figures
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

figures:
	python3 scripts/hard_target_mala_simulation.py --plots-only

simulations:
	python3 scripts/hard_target_mala_simulation.py

clean:
	latexmk -C main.tex
