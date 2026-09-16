# Package manifest — kernel-checked first-order revision

Release validation date: **2026-09-15**.

- `UniformRandomMALA/`: 154 library modules.
- `UniformRandomMALA.lean`: aggregate root, for 155 Lean files in total.
- First-order revision modules:
  - `Concrete/C1ToFirstOrder.lean`;
  - `DiscreteTime/MomentInterpolation.lean`;
  - `Concrete/RejectionMomentsOne.lean`;
  - `Concrete/C1MainTheorem.lean`.
- `Concrete/C1MainTheorem.lean`: reader-facing theorem, corollary,
  isoperimetry, rejection/overlap, and full-parameter flow endpoints.
- `AllResults.lean`: compact public import surface.
- `DependencyAudit.lean`: 266 actual `#print axioms` requests.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: pinned Lean/mathlib
  4.33.0 configuration; mathlib is the only direct dependency.
- `paper/`: the revised 47-page `main.pdf` only. TeX source, bibliography,
  and separate figures are not included. The PDF checksum is recorded in
  `validation/manuscript-pdf.sha256`.
- `scripts/`: Lean source, first-order, PDF identity/inventory, numerical,
  build, public-import, and axiom gates for Bash and PowerShell; tests for
  the PDF audit failure cases.
- `validation/`: curated release evidence and checksums. Historical records for
  the older Hessian-facing package are under
  `validation/historical/pre-first-order/`.
- `../simulation/`: numerical companion material: one Python script, two
  committed CSV result tables, three PDF figures with PNG previews, pinned
  Python requirements, and synchronized reader/Make documentation. The
  simulation code, data, and figure files were not changed by the Lean audit;
  its README and Makefile were corrected to match the distributed files.

The release ZIP excludes `.lake/`, dependency caches, compiled Lean objects,
Git data, Python bytecode, `tmp/`, and `validation/local/`. Running the checker locally
recreates `.lake/`; this is expected and does not change the source package.
`validation/SHA256SUMS.txt` covers the distributed files under `formalization/`
except itself, using repository-relative paths. It does not cover the sibling
`simulation/` directory or the repository-level README/workflow.
