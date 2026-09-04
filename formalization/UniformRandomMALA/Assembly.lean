import UniformRandomMALA.Arithmetic

/-!
# Assembly data before the final min/max argument

This file sits between the paper's analytic lemmas and the final theorem.
It does not assume the final `c₀`-scaled safe and ladder certificates.
Instead it records exactly the outputs of component aggregation and of the
harmonic-sum estimate, and derives the corresponding raw gap bounds.
-/

namespace UniformRandomMALA

noncomputable section

/-- Output of the harmonic aggregation step for the geometric moment ladder. -/
structure LadderEvidence (p : Parameters) (gap : ℝ) where
  C : ℝ
  harmonic : ℝ
  hC : 0 < C
  hharmonic : 0 < harmonic
  harmonicUpper :
    harmonic ≤
      C * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
        (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2)
  aggregationLower : 1 / (2 * harmonic) ≤ gap

namespace LadderEvidence

/-- Equation `ladder-gap-bound`, retaining the explicit harmonic constant. -/
theorem rawGap
    (p : Parameters) (gap : ℝ) (e : LadderEvidence p gap) :
    (1 / (2 * e.C)) * (p.m / p.H) *
        (min p.H p.rejectionScale) ^ 2 ≤ gap := by
  have hcoarse :
      p.m * p.ladderTheta ^ 2 * p.b0 ^ 2 /
          (2 * e.C * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar)) ≤ gap := by
    exact ladder_gap_from_harmonic_bound
      gap p.H p.L p.m p.ladderTheta p.b0 p.pStar p.d e.C e.harmonic
      p.hH p.hL p.hm p.ladderTheta_pos p.hb0 p.hpStar_pos p.hd
      e.hC e.hharmonic e.harmonicUpper e.aggregationLower
  rw [p.ladder_coefficient_identity e.C e.hC] at hcoarse
  exact hcoarse

end LadderEvidence

/--
Numerical data obtained after the safe component and ladder components have
been passed through `thm:aggregation`.  The two bounds on `c₀` implement
the paper's instruction to decrease the universal constant once more.
-/
structure GapAssembly (p : Parameters) (gap : ℝ) where
  /-- One-component aggregation output for `t_s = min(H,b₀/(Ld))`. -/
  safeAggregation :
    oneComponentAggregation
        (componentWeight p.H p.safeEndpoint)
        (safePhiSq p.m p.safeEndpoint) ≤ gap
  /-- The geometric ladder is needed only in the regime `p⋆ < d`. -/
  ladder : p.pStar < p.d → LadderEvidence p gap
  /-- Common constant is no larger than the exact safe coefficient. -/
  c0_le_safe : p.c0 ≤ Real.log 2 / (2 : ℝ) ^ 28
  /-- Common constant is no larger than every ladder coefficient used. -/
  c0_le_ladder :
    ∀ h : p.pStar < p.d, p.c0 ≤ 1 / (2 * (ladder h).C)

namespace GapAssembly

/-- Exact safe-component output before replacing its constant by `c₀`. -/
theorem safeRaw
    (p : Parameters) (gap : ℝ) (a : GapAssembly p gap) :
    (Real.log 2 / (2 : ℝ) ^ 28) * (p.m / p.H) *
        p.safeEndpoint ^ 2 ≤ gap := by
  have h := a.safeAggregation
  rw [safe_one_component_value p.H p.m p.safeEndpoint
    p.hH p.hm p.safeEndpoint_pos] at h
  have hid :
      p.m * p.safeEndpoint ^ 2 * Real.log 2 /
          ((2 : ℝ) ^ 28 * p.H) =
        (Real.log 2 / (2 : ℝ) ^ 28) * (p.m / p.H) *
          p.safeEndpoint ^ 2 := by
    field_simp [ne_of_gt p.hH]
    <;> ring
  rw [hid] at h
  exact h

/-- Safe bound with the common universal coefficient `c₀`. -/
theorem safeCertificate
    (p : Parameters) (gap : ℝ) (a : GapAssembly p gap) :
    p.c0 * (p.m / p.H) * (min p.H p.safeScale) ^ 2 ≤ gap := by
  have hscale :
      0 ≤ (p.m / p.H) * (min p.H p.safeScale) ^ 2 := by
    exact mul_nonneg (div_nonneg p.m_nonneg p.H_nonneg) (sq_nonneg _)
  have hcoef := mul_le_mul_of_nonneg_right a.c0_le_safe hscale
  have hraw := GapAssembly.safeRaw p gap a
  unfold Parameters.safeEndpoint at hraw
  exact le_trans (by simpa [mul_assoc] using hcoef) hraw

/-- Ladder bound with the common universal coefficient `c₀`. -/
theorem ladderCertificate
    (p : Parameters) (gap : ℝ) (a : GapAssembly p gap)
    (hsmall : p.pStar < p.d) :
    p.c0 * (p.m / p.H) * (min p.H p.rejectionScale) ^ 2 ≤ gap := by
  let e : LadderEvidence p gap := a.ladder hsmall
  have hscale :
      0 ≤ (p.m / p.H) * (min p.H p.rejectionScale) ^ 2 := by
    exact mul_nonneg (div_nonneg p.m_nonneg p.H_nonneg) (sq_nonneg _)
  have hraw := LadderEvidence.rawGap p gap e
  have hcoef' :
      p.c0 * ((p.m / p.H) * (min p.H p.rejectionScale) ^ 2) ≤
        (1 / (2 * e.C)) *
          ((p.m / p.H) * (min p.H p.rejectionScale) ^ 2) := by
    exact mul_le_mul_of_nonneg_right (a.c0_le_ladder hsmall) hscale
  exact le_trans (by simpa [mul_assoc] using hcoef') hraw

end GapAssembly

end

end UniformRandomMALA
