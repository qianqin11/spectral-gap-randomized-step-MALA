/-
# Sharper `p >= 2` overlap core for MALA kernels

This module exposes the certificate-free `p >= 2` discrete-time local-overlap
core for dyadic MALA kernels. Outside an explicitly controlled exceptional
set, nearby starting points have overlapping transition laws; a more
conservative scale gives the same conclusion globally. The content-named
declaration
`UniformRandomMALA.Concrete.FirstOrderPotential.mala_overlap_bounds` packages
both estimates in this sharper range.

The revised paper's Proposition 3.2 allows every `p >= 1`. Its reader-facing
endpoint is `UniformRandomMALA.Concrete.C1Potential.mala_overlap_bounds` in
`Concrete/C1MainTheorem.lean`; it obtains the extra range by second-moment
interpolation and uses correspondingly rescaled constants.

The proof uses explicit constants `1 / (16 * exp 1)` and
`6144 * (exp 1)^3`.
-/

import UniformRandomMALA.Concrete.MALAOverlapBounds

open MeasureTheory Set

namespace UniformRandomMALA
namespace Concrete.FirstOrderPotential

noncomputable section

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Content-named public alias for the admissible local step-size constant. -/
abbrev malaOverlapSmallStepConstant : ℝ := proposition32CrSmall

/-- Content-named public alias for the exceptional-mass constant. -/
abbrev malaOverlapExceptionalConstant : ℝ := proposition32CrLarge

/-- The two MALA local-overlap bounds used by the paper's conductance
argument. The first gives a measurable good set with a moment-indexed
exceptional-mass estimate; the second is a global small-step estimate. Both
conclude setwise total variation at most `3/4` for points within
`sqrt t / 16`. -/
theorem mala_overlap_bounds :
    (∀ p t : ℝ, 2 ≤ p → ∀ ht : 0 < t,
      t ≤ malaOverlapSmallStepConstant /
        (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ G : Set (State d),
        MeasurableSet G ∧
        (V.target : Measure (State d)) Gᶜ ≤
          ENNReal.ofReal
            ((malaOverlapExceptionalConstant * V.L * t *
              Real.sqrt (p * ((d : ℝ) + p))) ^ p) ∧
        ∀ x ∈ G, ∀ y ∈ G,
          ‖x - y‖ ≤ Real.sqrt t / 16 →
          setwiseTV (V.dyadicMALA t ht x)
            (V.dyadicMALA t ht y) ≤ 3 / 4) ∧
    (∀ t : ℝ, ∀ ht : 0 < t,
      t ≤ 1 / (2 * V.L * (d : ℝ)) →
      ∀ x y : State d,
        ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.dyadicMALA t ht x)
          (V.dyadicMALA t ht y) ≤ 3 / 4) :=
  V.proposition32_discreteTime

end
end Concrete.FirstOrderPotential
end UniformRandomMALA
