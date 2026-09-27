# Development history

This page records changes relevant to reading and reproducing the formalization.
For the current mathematical scope and verification evidence, see
`FORMALIZATION_STATUS.md`, `THEOREM_MAP.md`, and `BUILD_STATUS.md`.

## Updated manuscript coverage (2026-09-26)

The package now proves every result in the supplied manuscript except the
explicitly excluded Lemmas B.2–B.5. The public statements use the current
normalization and include the spectral-gap and mixing corollaries, actual
asymptotic variance and Gaussian CLTs, variance comparison, nonstationary
mean-square error, and the small-step fixed-MALA bound. Proposition B.1 is
proved under its nonconvex assumptions by a finite-chain and weak-limit route.

The CLT uses the actual infinite Markov trajectory, identified with every
finite path law. Martingale estimates, the Poisson equation, density
truncation, and first-acceptance approximation establish convergence from
every initial probability distribution. The aggregation lemma and theorem
remain independently reusable results.

Documentation introduces the whole package and separates statement lookup,
definition comparison, proof dependencies, and reproducible verification.
See `BUILD_STATUS.md` for the final verification evidence for this update.

## Manuscript source and reference concordance

The manuscript source, bibliography, compiled paper, and three included figure
PDFs are distributed together under `paper/`. The Lean comments and theorem
map use the source's stable TeX labels alongside printed theorem numbers.
The manuscript audit checks active source references and citations, required
assets, the recorded PDF checksum, and references from Lean comments.

The reader documentation presents the mathematical assumptions, public
results, proof dependencies, and reproduction commands. Detailed earlier
implementation notes remain in the historical records below.

## First-order interface and universal constants

The public input `C1Potential` uses continuous differentiability, first-order
strong convexity, and a Lipschitz actual gradient. A proved descent inequality
connects this input to the internal analytic development. The public
existential main-theorem statements use `A₀ ≥ 1`; their concrete universal
witness satisfies `A₀ ≥ 2`. At that earlier stage the nonconvex extension in
Appendix B was outside the formalized scope; Proposition B.1 is now included.

## Historical records

- `validation/historical/pre-first-order/`: the earlier Hessian-facing package.
- `validation/historical/2026-09-12/`: the first-order verification snapshot.
- `validation/historical/2026-09-15/`: the later universal-constant revision
  and the manuscript distribution at that checkpoint.
- `validation/historical/2026-09-15/WORKLOG.md`: detailed implementation
  chronology. Its inventories and pending tasks describe their recorded dates.

The archival derivations in `BAKRY_LEDOUX_DISCRETE_LANGEVIN_PROOF.md` and
`LEAN_FRIENDLY_PROOF_LEDGER.md` provide mathematical background; their staged
status descriptions are historical rather than current verification claims.
