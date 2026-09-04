/-
# Gaussian Bobkov inequality by canonical OU interpolation

Public entry point for the Gaussian isoperimetric input.  It develops the
normal profile `I(u) = phi(PhiInv(u))`, the Mehler Ornstein--Uhlenbeck
semigroup, the nonnegative residual in Bobkov's interpolation, its long-time
and endpoint closure, and the resulting inequality for smooth mollified
distance ramps.

Older development notes call the residual calculation, functional closure,
and ramp specialization G3, G4, and G5.  Those are construction-stage labels,
not additional assumptions or paper theorem numbers.

Principal declarations include
`UniformRandomMALA.Concrete.gaussianBobkovSmoothInterpolation_of_boundedThirdJet`
and `UniformRandomMALA.Concrete.gaussianRampMollified_bobkov`.

The first is a reusable constructor with explicit bounded derivative,
Riesz-Hessian, and third-derivative data.  The second is the unconditional
specialization used to prove finite-dimensional Gaussian enlargement.  See
`REUSABLE_RESULTS.md` for the distinction.
-/

import UniformRandomMALA.Concrete.GaussianOUCanonicalInterpolation
import UniformRandomMALA.Concrete.GaussianBobkovFunctional
import UniformRandomMALA.Concrete.GaussianRampCanonicalInterpolation
