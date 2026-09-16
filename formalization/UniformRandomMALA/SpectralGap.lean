/-
# Internal first-order spectral-gap core

This module exposes the certificate-free concrete uniform-random-MALA
spectral-gap lower bound from `FirstOrderPotential`. The kernel samples its
step uniformly from `(0,H)`; the bound holds for every `H > 0` and uses
explicit universal constants.

The recommended endpoint is
`UniformRandomMALA.Concrete.FirstOrderPotential.universal_masterRHS_spectralGap_lower`.
It assumes a `FirstOrderPotential d` and a positive endpoint `H`; all
universal constants and the Bakry--Ledoux input are discharged internally.

The revised manuscript-facing theorem, with the actual gradient and exactly
the stated `C1Potential` assumptions, is exported from
`Concrete/C1MainTheorem.lean` and `UniformRandomMALA.AllResults`.

The parameterized companion is
`UniformRandomMALA.Concrete.FirstOrderPotential.masterRHS_spectralGap_lower`.
-/

import UniformRandomMALA.MALAOverlap
import UniformRandomMALA.BakryLedoux
import UniformRandomMALA.Concrete.GlobalFromBakryLedoux
import UniformRandomMALA.Concrete.UniversalConstants
import UniformRandomMALA.Concrete.GaussianRampCanonicalInterpolation
