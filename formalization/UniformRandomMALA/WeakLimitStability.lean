/-
# Weak-limit stability of enlargement inequalities

Public entry point for a general Portmanteau transfer theorem.  If probability
measures `mu_n` converge weakly to `mu`, positive scale coefficients `c_n`
converge to `c > 0`, and each `mu_n` satisfies a metric-enlargement profile at
radius `r / c_n`, then the corresponding inequality holds for `mu` at radius
`r / c`.  The proof uses compact inner approximation and open/closed
Portmanteau bounds.

The Gaussian specialization concludes Bakry--Ledoux curvature `c⁻²` and
handles the normal-profile endpoint issue internally.  It does not require a
caller-supplied continuity theorem for enlargement masses.

Principal declarations include
`UniformRandomMALA.Concrete.enlargement_profile_of_weakLimit` and
`UniformRandomMALA.Concrete.bakryLedouxEnlargement_of_weakLimit`.
-/

import UniformRandomMALA.Concrete.WeakLimitEnlargement
import UniformRandomMALA.Concrete.GaussianWeakLimit
