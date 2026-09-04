import UniformRandomMALA.Certificates

/-!
# Main theorem

This file contains the formal min/max assembly at the end of the paper.
There are no placeholders: once the safe and ladder certificates are
provided, the global endpoint bound follows by a complete Lean proof.
-/

namespace UniformRandomMALA

noncomputable section

/--
Theorem `thm:main`, in the paper's compact scale notation.

The proof follows the paper's two cases:
* if `pStar < d`, combine the ladder and safe certificates using `max`;
* otherwise, the rejection-controlled scale is at most the safe scale.
-/
theorem global_gap_for_every_endpoint
    (p : Parameters) (c : GapCertificates p) :
    p.masterRHS ≤ c.gap := by
  unfold Parameters.masterRHS
  by_cases hsmall : p.pStar < p.d
  · rw [p.certifiedScale_eq_max_scales]
    have hsq := max_sq_min_eq_min_max_sq
      p.H p.rejectionScale p.safeScale
      p.H_nonneg p.rejectionScale_nonneg p.safeScale_nonneg
    rw [← hsq]
    rw [mul_max_of_nonneg'
      (p.c0 * (p.m / p.H))
      ((min p.H p.rejectionScale) ^ 2)
      ((min p.H p.safeScale) ^ 2)
      p.gapPrefactor_nonneg]
    exact max_le (c.ladder hsmall) c.safe
  · have hlarge : p.d ≤ p.pStar := le_of_not_gt hsmall
    rw [p.certifiedScale_eq_safeScale_of_dim_le_moment hlarge]
    exact c.safe

/-- Fully expanded statement matching equation `master-gap` in the draft. -/
theorem global_gap_for_every_endpoint_expanded
    (p : Parameters) (c : GapCertificates p) :
    p.c0 * (p.m / p.H) *
        (min p.H
          ((p.b0 / p.L) *
            max
              (1 / Real.sqrt (p.pStar * (p.d + p.pStar)))
              (1 / p.d))) ^ 2 ≤
      c.gap := by
  simpa [Parameters.masterRHS, Parameters.certifiedScale,
    Parameters.baseFactor, Parameters.certifiedShape,
    Parameters.rejectionShape, Parameters.safeShape] using
    global_gap_for_every_endpoint p c

/-- The main theorem extracted directly from all named analytic interfaces. -/
theorem global_gap_from_analytic_interfaces
    (p : Parameters) (a : PaperAnalyticInterfaces p) :
    p.masterRHS ≤
      a.kernelObjects.spectralGap (a.kernelObjects.uniformMALA p.H) := by
  exact global_gap_for_every_endpoint p (GapCertificates.ofAnalyticInterfaces p a)

/-- Lazification divides the certified right spectral gap by two. -/
theorem lazy_global_gap
    (p : Parameters) (c : GapCertificates p) :
    p.masterRHS / 2 ≤ c.gap / 2 := by
  exact div_le_div_of_nonneg_right
    (global_gap_for_every_endpoint p c) (by norm_num)

end

end UniformRandomMALA
