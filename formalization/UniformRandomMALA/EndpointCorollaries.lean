import UniformRandomMALA.MainTheorem

/-!
# Endpoint substitutions

These are the algebraic corollaries obtained by substituting the two
endpoints used in the paper into the master bound.
-/

namespace UniformRandomMALA

noncomputable section

namespace Parameters

/-- The paper's notation `M_{d,kappa}`. -/
def M (p : Parameters) : ℝ := p.certifiedShape

lemma M_pos (p : Parameters) : 0 < p.M := p.certifiedShape_pos

lemma M_nonneg (p : Parameters) : 0 ≤ p.M := le_of_lt p.M_pos

lemma certifiedScale_eq_b0_mul_M_div_L (p : Parameters) :
    p.certifiedScale = p.b0 * (p.M / p.L) := by
  unfold certifiedScale baseFactor M
  ring

/-- Exact substitution `H = c M/L`. -/
theorem adapted_endpoint_identity
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c * p.M / p.L) :
    p.masterRHS =
      (p.c0 / p.kappa) * (min c p.b0) ^ 2 / c * p.M := by
  have hscale : p.certifiedScale = p.b0 * (p.M / p.L) :=
    p.certifiedScale_eq_b0_mul_M_div_L
  have hspos : 0 < p.M / p.L := div_pos p.M_pos p.hL
  have hHscaled : p.H = c * (p.M / p.L) := by
    rw [hendpoint]
    ring
  have hmin :
      min p.H p.certifiedScale = min c p.b0 * (p.M / p.L) := by
    rw [hHscaled, hscale]
    exact min_mul_of_nonneg' c p.b0 (p.M / p.L) (le_of_lt hspos)
  unfold masterRHS
  rw [hmin, hendpoint, p.hkappa]
  field_simp [ne_of_gt p.hm, ne_of_gt p.hL, ne_of_gt p.M_pos,
    ne_of_gt hc]
  <;> ring

/-- An adapted-endpoint consequence retained in Lean but not stated separately
in the current paper. -/
theorem adapted_endpoint
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c * p.M / p.L)
    (cert : GapCertificates p) :
    (p.c0 / p.kappa) * (min c p.b0) ^ 2 / c * p.M ≤ cert.gap := by
  rw [← p.adapted_endpoint_identity c hc hendpoint]
  exact global_gap_for_every_endpoint p cert

/-- Exact substitution `H = c/(L sqrt d)`. -/
theorem sqrt_dimension_endpoint_identity
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d)) :
    p.masterRHS =
      p.c0 * Real.sqrt p.d / (c * p.kappa) *
        (min (c / Real.sqrt p.d) (p.b0 * p.M)) ^ 2 := by
  have hroot : 0 < Real.sqrt p.d := Real.sqrt_pos.2 p.hd
  have hinvL : 0 < 1 / p.L := one_div_pos.mpr p.hL
  have hscale : p.certifiedScale = (1 / p.L) * (p.b0 * p.M) := by
    unfold certifiedScale baseFactor M
    field_simp [ne_of_gt p.hL]
    <;> ring
  have hHscaled : p.H = (1 / p.L) * (c / Real.sqrt p.d) := by
    rw [hendpoint]
    field_simp [ne_of_gt p.hL, ne_of_gt hroot]
    <;> ring
  have hmin :
      min p.H p.certifiedScale =
        (1 / p.L) * min (c / Real.sqrt p.d) (p.b0 * p.M) := by
    rw [hHscaled, hscale]
    exact (mul_min_of_nonneg'
      (1 / p.L) (c / Real.sqrt p.d) (p.b0 * p.M)
      (le_of_lt hinvL)).symm
  unfold masterRHS
  rw [hmin, hendpoint, p.hkappa]
  field_simp [ne_of_gt p.hm, ne_of_gt p.hL, ne_of_gt hroot,
    ne_of_gt hc]
  <;> ring

/-- The general `H = c/(L sqrt d)` form underlying Corollary 2.2. -/
theorem sqrt_dimension_endpoint
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d))
    (cert : GapCertificates p) :
    p.c0 * Real.sqrt p.d / (c * p.kappa) *
        (min (c / Real.sqrt p.d) (p.b0 * p.M)) ^ 2 ≤ cert.gap := by
  rw [← p.sqrt_dimension_endpoint_identity c hc hendpoint]
  exact global_gap_for_every_endpoint p cert

/-- If `pStar ≤ d`, then `M ≥ 1/sqrt(2 pStar d)`. -/
theorem M_lower_of_moment_le_dimension
    (p : Parameters) (hpd : p.pStar ≤ p.d) :
    1 / Real.sqrt (2 * p.pStar * p.d) ≤ p.M := by
  have harg1 : 0 < p.pStar * (p.d + p.pStar) := p.rejectionArgument_pos
  have harg2 : 0 < 2 * p.pStar * p.d :=
    mul_pos (mul_pos (by norm_num) p.hpStar_pos) p.hd
  have hprod :
      p.pStar * (p.d + p.pStar) ≤ 2 * p.pStar * p.d := by
    have hmul := mul_le_mul_of_nonneg_left hpd p.pStar_nonneg
    nlinarith [mul_self_nonneg p.pStar]
  have hsqrt :
      Real.sqrt (p.pStar * (p.d + p.pStar)) ≤
        Real.sqrt (2 * p.pStar * p.d) := by
    exact Real.sqrt_le_sqrt hprod
  have hrecip :
      1 / Real.sqrt (2 * p.pStar * p.d) ≤
        1 / Real.sqrt (p.pStar * (p.d + p.pStar)) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 harg2) (Real.sqrt_pos.2 harg1)).2
    simpa using hsqrt
  exact le_trans hrecip (le_max_left _ _)

/--
A directly formalized `pStar ≤ d` specialization of Corollary 2.2, after factoring
`sqrt (2*pStar*d) = sqrt (2*pStar) * sqrt d`.
-/
theorem sqrt_dimension_endpoint_small_moment
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d))
    (hpd : p.pStar ≤ p.d)
    (cert : GapCertificates p) :
    p.c0 * Real.sqrt p.d / (c * p.kappa) *
        (min (c / Real.sqrt p.d)
          (p.b0 / Real.sqrt (2 * p.pStar * p.d))) ^ 2 ≤ cert.gap := by
  have hM := p.M_lower_of_moment_le_dimension hpd
  have hbM :
      p.b0 / Real.sqrt (2 * p.pStar * p.d) ≤ p.b0 * p.M := by
    have hb := p.baseFactor_nonneg
    have hb0 : 0 ≤ p.b0 := le_of_lt p.hb0
    have := mul_le_mul_of_nonneg_left hM hb0
    simpa [div_eq_mul_inv, mul_assoc] using this
  have hmin :
      min (c / Real.sqrt p.d)
          (p.b0 / Real.sqrt (2 * p.pStar * p.d)) ≤
        min (c / Real.sqrt p.d) (p.b0 * p.M) := by
    exact min_le_min (le_refl _) hbM
  have hleft_nonneg :
      0 ≤ min (c / Real.sqrt p.d)
        (p.b0 / Real.sqrt (2 * p.pStar * p.d)) := by
    apply min_nonneg_of_nonneg
    · exact div_nonneg (le_of_lt hc) (Real.sqrt_nonneg _)
    · exact div_nonneg (le_of_lt p.hb0) (Real.sqrt_nonneg _)
  have hsq := sq_le_sq_of_nonneg hleft_nonneg hmin
  have hpref : 0 ≤ p.c0 * Real.sqrt p.d / (c * p.kappa) := by
    exact div_nonneg
      (mul_nonneg (le_of_lt p.hc0) (Real.sqrt_nonneg _))
      (mul_nonneg (le_of_lt hc) (le_trans zero_le_one p.hkappa_one))
  have hscaled := mul_le_mul_of_nonneg_left hsq hpref
  exact le_trans hscaled (p.sqrt_dimension_endpoint c hc hendpoint cert)

/--
The former restricted endpoint display in its paper-style factorization.
This is the preceding theorem after pulling the common factor
`1 / sqrt d` through the minimum.
-/
theorem sqrt_dimension_endpoint_small_moment_paper
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d))
    (hpd : p.pStar ≤ p.d)
    (cert : GapCertificates p) :
    (p.c0 / (p.kappa * Real.sqrt p.d)) *
        ((min c (p.b0 / Real.sqrt (2 * p.pStar))) ^ 2 / c) ≤
      cert.gap := by
  have hrootD : 0 < Real.sqrt p.d := Real.sqrt_pos.2 p.hd
  have htwoP : 0 < 2 * p.pStar := mul_pos (by norm_num) p.hpStar_pos
  have hrootTwoP : 0 < Real.sqrt (2 * p.pStar) := Real.sqrt_pos.2 htwoP
  have htwoPD : 0 < 2 * p.pStar * p.d := mul_pos htwoP p.hd
  have hsqrtProduct :
      Real.sqrt (2 * p.pStar * p.d) =
        Real.sqrt (2 * p.pStar) * Real.sqrt p.d := by
    have hleftSq :
        (Real.sqrt (2 * p.pStar * p.d)) ^ 2 = 2 * p.pStar * p.d := by
      simpa using Real.sq_sqrt (le_of_lt htwoPD)
    have hfirstSq :
        (Real.sqrt (2 * p.pStar)) ^ 2 = 2 * p.pStar := by
      simpa using Real.sq_sqrt (le_of_lt htwoP)
    have hsecondSq : (Real.sqrt p.d) ^ 2 = p.d := by
      simpa using Real.sq_sqrt p.d_nonneg
    have hrightNonneg :
        0 ≤ Real.sqrt (2 * p.pStar) * Real.sqrt p.d := by positivity
    have hleftNonneg : 0 ≤ Real.sqrt (2 * p.pStar * p.d) :=
      Real.sqrt_nonneg _
    nlinarith
  have hminFactor :
      min (c / Real.sqrt p.d)
          (p.b0 / Real.sqrt (2 * p.pStar * p.d)) =
        (1 / Real.sqrt p.d) *
          min c (p.b0 / Real.sqrt (2 * p.pStar)) := by
    have hcFactor :
        c / Real.sqrt p.d = (1 / Real.sqrt p.d) * c := by ring
    have hbFactor :
        p.b0 / Real.sqrt (2 * p.pStar * p.d) =
          (1 / Real.sqrt p.d) *
            (p.b0 / Real.sqrt (2 * p.pStar)) := by
      rw [hsqrtProduct]
      field_simp [ne_of_gt hrootD, ne_of_gt hrootTwoP]
      <;> ring
    rw [hcFactor, hbFactor]
    exact (mul_min_of_nonneg'
      (1 / Real.sqrt p.d) c
      (p.b0 / Real.sqrt (2 * p.pStar))
      (by positivity)).symm
  have hcurrent :=
    p.sqrt_dimension_endpoint_small_moment c hc hendpoint hpd cert
  rw [hminFactor] at hcurrent
  have hidentity :
      p.c0 * Real.sqrt p.d / (c * p.kappa) *
          ((1 / Real.sqrt p.d) *
            min c (p.b0 / Real.sqrt (2 * p.pStar))) ^ 2 =
        (p.c0 / (p.kappa * Real.sqrt p.d)) *
          ((min c (p.b0 / Real.sqrt (2 * p.pStar))) ^ 2 / c) := by
    have hkappa : 0 < p.kappa := lt_of_lt_of_le zero_lt_one p.hkappa_one
    field_simp [ne_of_gt hrootD, ne_of_gt hc, ne_of_gt hkappa]
    <;> ring
  rw [hidentity] at hcurrent
  exact hcurrent

end Parameters

end

end UniformRandomMALA
