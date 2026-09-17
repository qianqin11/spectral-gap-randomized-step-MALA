# Coverage and verification report

The Lean development formalizes Theorem 2.1 (`thm:main`) from the paper's
first-order assumptions (`eq:first-order-assumptions`), with both non-lazy
and half-lazy conclusions and a common choice of universal constants
satisfying `A₀ ≥ 1`. It also includes Corollary 2.2
(`cor:sqrt-d-endpoint`) and the smooth fixed-step minimax obstruction in
Proposition 2.3 (`prop:minimax-fixed-step-ceiling`).

The current kernel-build and audit results are maintained in
[BUILD_STATUS.md](BUILD_STATUS.md). This report explains the coverage and
how to interpret that evidence.

## Reading the endpoints

The principal declaration is
`UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds`.
Its input `C1Potential` records continuous differentiability, the
first-order strong-convexity inequality, and Lipschitz continuity of the
actual Riesz gradient. The upper Taylor bound is proved, and the internal
MALA drift is definitionally that gradient. No separate analytic certificate
is an argument to the main theorem.

[THEOREM_MAP.md](THEOREM_MAP.md) pairs each covered result with its paper
number, TeX label, and exact Lean declarations.
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) gives the coverage table;
[PAPER_READER_GUIDE.md](PAPER_READER_GUIDE.md) provides a reading order.

## Supporting mathematics

The randomized-step proof combines the disjoint mixture-energy comparison
(Lemma 3.1, `lem:Kt`), overlap (Proposition 3.2, `prop:overlap`), separation
(Proposition 3.3, `prop:separated`), both flow bounds (Proposition 3.4,
`prop:flow`), and fractional/hard-assignment aggregation (Lemma 3.5,
`lem:fractional`; Theorem 3.6, `thm:aggregation`). The aggregation theorems
retain the stated `L²` energy-domination hypothesis.

The development also contains the following reusable results:

- equivalence of the `L²` Poincaré and Rayleigh-infimum spectral gaps,
  including zero-variance and infinite-energy cases;
- Markov, reversibility, Dirichlet-energy, and Rayleigh-gap identities for
  the half-lazy kernel;
- real-exponent moment interpolation for the public `p ≥ 1` rejection range;
- fractional aggregation with extended-valued energies and truncation limits;
- Gaussian OU/Bobkov interpolation, finite-Euler transport, and weak-limit
  stability for target enlargement;
- Rayleigh test-function and indicator-cut upper bounds;
- the smooth hard potential, Gaussian trigonometric identities, and product
  concentration used in Proposition A.1 (`prop:generic-fixed-step-obstruction`).

[PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) explains how these
arguments fit together. [REUSABLE_RESULTS.md](REUSABLE_RESULTS.md) gives
names and imports for reuse.

## Scope boundary

The manuscript's continuous-time rejection derivation is not transcribed.
Lean obtains the standing strongly convex case of Proposition B.1
(`prop:stationary-rejection`) from finite Gaussian likelihoods, finite-Euler
energy bounds, Euler/RWM comparison, and weak-limit closure. Appendix B's
additional nonconvex `C¹` generalization is not formalized. This limitation
does not leave an unproved rejection premise in the main theorem.

The optional Hessian adapter supplies smooth special cases and the
fixed-step hard witness. It is not an assumption of the first-order
lower-bound endpoint. [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) details the
logical assumptions and dependencies.

## Reproducing and interpreting validation

Run `scripts/check.ps1` on Windows or `bash scripts/check.sh` on Linux or
macOS after retrieving the pinned dependencies with `lake exe cache get`.
Complete prerequisites and commands are in [README.md](README.md).

The gate builds the Lean source, checks the public `AllResults` import,
and executes the `#print axioms` requests in `DependencyAudit.lean`.
The dependency checker permits only `propext`, `Classical.choice`, and
`Quot.sound`, and fails on missing requests, Lean errors, or additional
axioms. The source checks and numerical trials are separate parts of the
gate; a successful source or numerical audit alone is not a kernel check.

The manuscript source, bibliography, three figure PDFs, and typeset paper
are included in `paper/`. The manuscript audit checks the supplied PDF
against [its recorded digest](validation/manuscript-pdf.sha256), inspects
source labels, references, citations, and figure dependencies, and checks
paper references in Lean. Mathematical correspondence still requires the
statement-level map and scope qualifications above. A source audit does not
replace typesetting; `BUILD_STATUS.md` records LaTeX validation separately.

Historical records in `validation/historical/` document earlier versions.
The historical first-order transition is described in
[FIRST_ORDER_REVISION.md](FIRST_ORDER_REVISION.md). Neither historical build
logs nor their counts should be read as current validation results.
