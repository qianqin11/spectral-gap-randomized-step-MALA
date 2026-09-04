/-
# Public results of the UniformRandomMALA formalization

This is the compact reviewer-facing import.  It exposes the unconditional
MALA local-overlap theorem, weak-limit stability, Gaussian Bobkov and
Bakry--Ledoux results, and the final concrete spectral-gap theorem for Qian
Qin's *A Global Spectral Gap for MALA with a Uniformly Randomized Step Size*.

For the complete historical/internal import surface use `import
UniformRandomMALA`; for the completed concrete theorem chain, prefer this
module.
-/

import UniformRandomMALA.MALAOverlap
import UniformRandomMALA.WeakLimitStability
import UniformRandomMALA.GaussianBobkov
import UniformRandomMALA.BakryLedoux
import UniformRandomMALA.SpectralGap
import UniformRandomMALA.Concrete.HessianMainTheorem
import UniformRandomMALA.Concrete.LazyKernel
import UniformRandomMALA.Concrete.SqrtDimensionCorollary
import UniformRandomMALA.Concrete.FractionalAggregation
import UniformRandomMALA.Concrete.AllParameterMALAFlow
import UniformRandomMALA.Concrete.FixedStepMinimax
