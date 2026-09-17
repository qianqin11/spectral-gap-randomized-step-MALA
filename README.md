This repository contains simulation code and a Lean verification package for the paper *A global spectral gap for Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.

The [simulation package](simulation/README.md) contains the code for reproducing the results in Section 6 of the paper.

The [Lean package](formalization/README.md) provides instructions for checking the proofs. Its [reader guide](formalization/PAPER_READER_GUIDE.md) identifies the source files to compare with the paper's assumptions, algorithms, quantities, and theorem statements, and explains how to trace the complete proof dependencies.

Alongside the MALA spectral-gap results, the package formalizes the general fractional aggregation lemma (Lemma 3.5) and component-aggregation theorem (Theorem 3.6). These results combine one-step flow estimates into spectral-gap bounds and can be used independently of the MALA application; see the [aggregation guide](formalization/PAPER_READER_GUIDE.md#aggregation-lemma-35-and-theorem-36).
