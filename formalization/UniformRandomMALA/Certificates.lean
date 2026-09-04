import UniformRandomMALA.AnalyticInterfaces

/-!
# Safe and ladder gap certificates

The lengthy analytic proof reduces to two lower bounds with a common
universal prefactor.  This record is the narrow interface used by the final
min/max argument.
-/

namespace UniformRandomMALA

noncomputable section

/-- The two component estimates immediately before the proof's final case split. -/
structure GapCertificates (p : Parameters) where
  gap : ℝ
  safe :
    p.c0 * (p.m / p.H) * (min p.H p.safeScale) ^ 2 ≤ gap
  ladder :
    p.pStar < p.d →
      p.c0 * (p.m / p.H) * (min p.H p.rejectionScale) ^ 2 ≤ gap

namespace GapCertificates

/-- Extract the two numerical certificates from the full analytic interface. -/
def ofAnalyticInterfaces
    (p : Parameters) (a : PaperAnalyticInterfaces p) : GapCertificates p where
  gap := a.kernelObjects.spectralGap (a.kernelObjects.uniformMALA p.H)
  safe := GapAssembly.safeCertificate p
    (a.kernelObjects.spectralGap (a.kernelObjects.uniformMALA p.H))
    (PaperAnalyticInterfaces.gapAssembly p a)
  ladder := fun hsmall => GapAssembly.ladderCertificate p
    (a.kernelObjects.spectralGap (a.kernelObjects.uniformMALA p.H))
    (PaperAnalyticInterfaces.gapAssembly p a) hsmall

lemma gap_nonneg (p : Parameters) (c : GapCertificates p) : 0 ≤ c.gap := by
  have hsafe := c.safe
  have hrhs :
      0 ≤ p.c0 * (p.m / p.H) * (min p.H p.safeScale) ^ 2 := by
    exact mul_nonneg p.gapPrefactor_nonneg (sq_nonneg _)
  exact le_trans hrhs hsafe

end GapCertificates

end

end UniformRandomMALA
