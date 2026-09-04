/-
# Final spectral-gap theorem

Public entry point for the unconditional concrete uniform-random-MALA
spectral-gap lower bound in *A Global Spectral Gap for MALA with a Uniformly
Randomized Step Size*. The kernel samples its step uniformly from `(0,H)`;
the bound holds for every `H > 0` and uses explicit universal constants.

The recommended endpoint is
`UniformRandomMALA.Concrete.FirstOrderPotential.universal_masterRHS_spectralGap_lower`.
It assumes a `FirstOrderPotential d` and a positive endpoint `H`; all
universal constants and the Bakry--Ledoux input are discharged internally.

The parameterized companion is
`UniformRandomMALA.Concrete.FirstOrderPotential.masterRHS_spectralGap_lower`.
-/

import UniformRandomMALA.MALAOverlap
import UniformRandomMALA.BakryLedoux
import UniformRandomMALA.Concrete.GlobalFromBakryLedoux
import UniformRandomMALA.Concrete.UniversalConstants
import UniformRandomMALA.Concrete.GaussianRampCanonicalInterpolation
