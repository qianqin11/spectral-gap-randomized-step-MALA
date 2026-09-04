/-
# Bakry--Ledoux enlargement

Public entry point for the isoperimetric part of *A Global Spectral Gap for
MALA with a Uniformly Randomized Step Size*.  If `Phi` is the standard normal
CDF, the predicate `BakryLedouxEnlargement pi m Phi PhiInv` states

`Phi (PhiInv (pi A) + sqrt m * r) <= pi (Metric.thickening r A)`

for measurable interior-mass sets and `r > 0`.  This module includes a sharp,
unconditional curvature-one theorem for standard Gaussian measure on every
finite Euclidean coordinate space.  It then transfers that theorem through
finite Euler endpoint maps and a weak limit to the normalized strongly
log-concave target, with curvature `m`.

The target transfer is entirely discrete: no SDE existence, diffusion
invariance, or martingale-problem theorem is assumed.

Principal declarations:

* `UniformRandomMALA.Concrete.bakryLedouxEnlargement_stdGaussian_finiteIndex`;
* `UniformRandomMALA.DiscreteTime.target_bakryLedoux`.

See `REUSABLE_RESULTS.md` for exact scope and downstream examples.
-/

import UniformRandomMALA.WeakLimitStability
import UniformRandomMALA.GaussianBobkov
import UniformRandomMALA.Concrete.FiniteEulerEnlargement
import UniformRandomMALA.Concrete.FiniteEulerTargetIdentification
import UniformRandomMALA.Concrete.GaussianRampCanonicalInterpolation
