# Uniform-random MALA

This repository accompanies the paper *A spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.

- The [simulation package](simulation/README.md) contains the code and data
  for reproducing the numerical results in Section 6.
- The [Lean package](formalization/README.md) formalizes all results in the
  paper except Lemmas B.2–B.5. Coverage includes spectral gaps, mixing,
  Gaussian CLTs from arbitrary initial distributions, variance comparisons,
  nonstationary mean-square error, the nonconvex rejection bound, and the
  general aggregation lemma and theorem.

Start with the [paper reader guide](formalization/PAPER_READER_GUIDE.md)
for an introduction to the formalization, a map from the paper to the source
files, and instructions for checking definitions and complete proof
dependencies. The [theorem map](formalization/THEOREM_MAP.md) indexes individual
results, and [verification evidence](formalization/BUILD_STATUS.md) records
the build and dependency checks.
