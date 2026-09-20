# Uniform-random MALA

This repository accompanies the paper *A global spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.

- The [simulation package](simulation/README.md) contains the code and data
  for reproducing the numerical results in Section 6.
- The [Lean package](formalization/README.md) contains formal proofs of the
  randomized-step spectral-gap and mixing-time bounds, the fixed-step
  minimax obstruction, and the general aggregation lemma and theorem.

Start with the [paper reader guide](formalization/PAPER_READER_GUIDE.md)
for an introduction to the formalization, a map from the paper to the source
files, and instructions for checking definitions and complete proof
dependencies. The [theorem map](formalization/THEOREM_MAP.md) indexes individual
results, and [verification evidence](formalization/BUILD_STATUS.md) records
the build and dependency checks.
