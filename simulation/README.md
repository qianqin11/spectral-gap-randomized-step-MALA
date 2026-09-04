# A Global Spectral Gap for MALA with a Uniformly Randomized Step Size

This repository contains the LaTeX source for the manuscript and the
reproducible code, data, and figures for the numerical experiments in
Section 6.

## Repository layout

- `main.tex`: manuscript source.
- `simulation_section_updated.tex`: drop-in LaTeX source for Section 6.
- `uniform_random_mala.bib`: BibTeX database.
- `scripts/hard_target_mala_simulation.py`: simulation and plotting code.
- `data/`: committed Monte Carlo result tables, including i.i.d. standard
  errors computed from the individual Rao--Blackwellized observations.
- `figures/`: publication-ready PDF figures and PNG previews.
- `main.pdf`: compiled manuscript.

## Simulation design

The simulations use

\[
U_{d,h_0}(x)
=\frac{m}{2}x_1^2+
\sum_{i=2}^d\left[
\frac{L+m}{4}x_i^2-\frac{(L-m)h_0}{2}
\cos\left(\frac{x_i}{\sqrt{h_0}}\right)
\right],
\]

with `m = 0.1`, `L = 1`, and `h0 = 4 / (L * sqrt(d))`. Fixed-step
MALA uses `h = H`; randomized-step MALA draws
`h ~ Uniform(0, H)` independently at each iteration. The code uses seed
`20260825` and Rao--Blackwellizes over the final accept/reject uniform.

- Origin experiment: dimensions 25, 50, 100, 200, and 400; 80,000
  independent proposals per method and dimension. As a continuation, at
  dimension 200 it includes one 40,000-iteration chain per method from the
  origin with `H = h0`, recording the first coordinate at every iteration.
- Stationary experiment: dimension 200; 48,000 independent one-step
  experiments per method and endpoint; `H/h0` ranges from 0.05 to 100.

The figure error bars extend two ordinary i.i.d. standard errors on either
side of each estimate.  The code processes observations in memory-sized
chunks, but chunks play no role in the statistical analysis.

## Reproduce the figures

Create a Python environment and install the dependencies:

~~~bash
python -m pip install -r requirements.txt
~~~

Regenerate the figures from the committed result tables:

~~~bash
python scripts/hard_target_mala_simulation.py --plots-only
~~~

Rerun only the trace experiment:

~~~bash
python scripts/hard_target_mala_simulation.py --trace-only
~~~

Rerun both experiments and overwrite the committed tables and figures:

~~~bash
python scripts/hard_target_mala_simulation.py
~~~

## Build the manuscript

With a LaTeX distribution containing `latexmk`, `pdflatex`, and `bibtex`:

~~~bash
make paper
~~~

The default `make` target regenerates the figures from the committed data
before compiling `main.pdf`.
