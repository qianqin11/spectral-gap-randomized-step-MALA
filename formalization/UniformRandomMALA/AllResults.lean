/-
# Public results of the UniformRandomMALA formalization

This is the compact reviewer-facing import.  It exposes the certificate-free
MALA local-overlap theorem under the stated first-order potential assumptions,
weak-limit stability, Gaussian Bobkov and
Bakry--Ledoux results, aggregation, and the concrete spectral-gap and
mixing-time corollaries for Qian
Qin's *A global spectral gap for Metropolis-adjusted Langevin algorithm with
a uniformly randomized step size*.

For the complete historical/internal import surface use
`import UniformRandomMALA`; for the completed concrete theorem chain, prefer
this module.
-/

import UniformRandomMALA.Concrete.C1MainTheorem
import UniformRandomMALA.Concrete.TunedSpectralGap
import UniformRandomMALA.Concrete.MixingTime
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
