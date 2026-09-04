import UniformRandomMALA.Concrete.HessianMainTheorem
import UniformRandomMALA.EndpointCorollaries

/-!
# The square-root-dimension endpoint corollary

This file formalizes both displays of Corollary 2.2 at
`H = c / (L * sqrt d)`.  In particular, the simplified display is proved for
the full parameter range: no assumption `pStar ≤ d` is used.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Parameters

/-- The first displayed right-hand side in Corollary 2.2. -/
def sqrtDimensionCorollaryRHS (p : Parameters) (c : ℝ) : ℝ :=
  p.c0 / (p.kappa * Real.sqrt p.d) *
    min c (p.b0 ^ 2 / c *
      max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d))

/-- The simplified second displayed right-hand side in Corollary 2.2. -/
def sqrtDimensionCorollarySimplifiedRHS (p : Parameters) (c : ℝ) : ℝ :=
  p.c0 / (p.kappa * Real.sqrt p.d) *
    min c (p.b0 ^ 2 / (2 * c * p.pStar))

/-- The exact scalar simplification quoted in Corollary 2.2.  It holds
without assuming `pStar ≤ d`. -/
theorem min_sqrtDimensionDenominator_le_two_pStar (p : Parameters) :
    min (p.pStar * (p.d + p.pStar) / p.d) p.d ≤ 2 * p.pStar := by
  rcases le_total p.pStar p.d with hpd | hdp
  · refine (min_le_left _ _).trans ?_
    apply (div_le_iff₀ p.hd).2
    have hsum : p.d + p.pStar ≤ 2 * p.d := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum p.pStar_nonneg
    nlinarith
  · exact (min_le_right _ _).trans (by nlinarith [p.pStar_nonneg])

/-- The reciprocal shape used in the first display is bounded below by
`1/(2 pStar)` throughout the full parameter range. -/
theorem one_div_two_pStar_le_sqrtDimensionShape (p : Parameters) :
    1 / (2 * p.pStar) ≤
      max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d) := by
  rcases le_total p.pStar p.d with hpd | hdp
  · refine le_trans ?_ (le_max_left _ _)
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) p.hpStar_pos) p.rejectionArgument_pos).2
    have hsum : p.d + p.pStar ≤ 2 * p.d := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum p.pStar_nonneg
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) p.hpStar_pos) p.hd).2
    nlinarith [p.pStar_nonneg]

/-- The simplified Corollary 2.2 right-hand side is no larger than the first
display, without a comparison hypothesis between `pStar` and `d`. -/
theorem sqrtDimensionCorollarySimplifiedRHS_le
    (p : Parameters) (c : ℝ) (hc : 0 < c) :
    p.sqrtDimensionCorollarySimplifiedRHS c ≤
      p.sqrtDimensionCorollaryRHS c := by
  have hroot : 0 < Real.sqrt p.d := Real.sqrt_pos.2 p.hd
  have hkappa : 0 < p.kappa := lt_of_lt_of_le zero_lt_one p.hkappa_one
  have hpref : 0 ≤ p.c0 / (p.kappa * Real.sqrt p.d) :=
    le_of_lt (div_pos p.hc0 (mul_pos hkappa hroot))
  have hbscale : 0 ≤ p.b0 ^ 2 / c := by positivity
  have hshape := p.one_div_two_pStar_le_sqrtDimensionShape
  have hsecond :
      p.b0 ^ 2 / (2 * c * p.pStar) ≤
        p.b0 ^ 2 / c *
          max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d) := by
    calc
      p.b0 ^ 2 / (2 * c * p.pStar) =
          p.b0 ^ 2 / c * (1 / (2 * p.pStar)) := by
        field_simp [ne_of_gt hc, ne_of_gt p.hpStar_pos]
      _ ≤ p.b0 ^ 2 / c *
          max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d) :=
        mul_le_mul_of_nonneg_left hshape hbscale
  unfold sqrtDimensionCorollarySimplifiedRHS sqrtDimensionCorollaryRHS
  exact mul_le_mul_of_nonneg_left
    (min_le_min le_rfl hsecond) hpref

/-- The rejection/safe max in Corollary 2.2 is bounded by `d * M²`.
This direction is all that is needed for the endpoint lower bound. -/
theorem sqrtDimensionShape_le_d_mul_M_sq (p : Parameters) :
    max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d) ≤
      p.d * p.M ^ 2 := by
  have hrej : p.rejectionShape ≤ p.M := le_max_left _ _
  have hsafe : p.safeShape ≤ p.M := le_max_right _ _
  have hrejSq : p.rejectionShape ^ 2 ≤ p.M ^ 2 :=
    sq_le_sq_of_nonneg p.rejectionShape_nonneg hrej
  have hsafeSq : p.safeShape ^ 2 ≤ p.M ^ 2 :=
    sq_le_sq_of_nonneg p.safeShape_nonneg hsafe
  have hdnonneg := p.d_nonneg
  have hrejScaled := mul_le_mul_of_nonneg_left hrejSq hdnonneg
  have hsafeScaled := mul_le_mul_of_nonneg_left hsafeSq hdnonneg
  apply max_le
  · calc
      p.d / (p.pStar * (p.d + p.pStar)) =
          p.d * p.rejectionShape ^ 2 := by
        unfold rejectionShape
        have hsqrt := Real.sq_sqrt (le_of_lt p.rejectionArgument_pos)
        rw [div_pow, one_pow, hsqrt]
        rw [div_eq_mul_inv]
        simp only [one_div]
      _ ≤ p.d * p.M ^ 2 := hrejScaled
  · calc
      1 / p.d = p.d * p.safeShape ^ 2 := by
        unfold safeShape
        field_simp [ne_of_gt p.hd]
      _ ≤ p.d * p.M ^ 2 := hsafeScaled

/-- At `H = c/(L sqrt d)`, the first displayed Corollary 2.2 right-hand
side is bounded by the master right-hand side. -/
theorem sqrtDimensionCorollaryRHS_le_masterRHS
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d)) :
    p.sqrtDimensionCorollaryRHS c ≤ p.masterRHS := by
  rw [p.sqrt_dimension_endpoint_identity c hc hendpoint]
  have hroot : 0 < Real.sqrt p.d := Real.sqrt_pos.2 p.hd
  have hrootSq : (Real.sqrt p.d) ^ 2 = p.d :=
    Real.sq_sqrt p.d_nonneg
  have hkappa : 0 < p.kappa := lt_of_lt_of_le zero_lt_one p.hkappa_one
  have hpref : 0 ≤ p.c0 / (p.kappa * Real.sqrt p.d) :=
    le_of_lt (div_pos p.hc0 (mul_pos hkappa hroot))
  have hshapeNonneg :
      0 ≤ max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d) := by
    exact le_trans (le_of_lt (one_div_pos.mpr p.hd)) (le_max_right _ _)
  by_cases hbranch : c / Real.sqrt p.d ≤ p.b0 * p.M
  · rw [min_eq_left hbranch]
    calc
      p.sqrtDimensionCorollaryRHS c ≤
          p.c0 / (p.kappa * Real.sqrt p.d) * c := by
        unfold sqrtDimensionCorollaryRHS
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) hpref
      _ = p.c0 * Real.sqrt p.d / (c * p.kappa) *
          (c / Real.sqrt p.d) ^ 2 := by
        field_simp [ne_of_gt hroot, ne_of_gt hc, ne_of_gt hkappa]
  · have hbranch' : p.b0 * p.M ≤ c / Real.sqrt p.d :=
      le_of_not_ge hbranch
    rw [min_eq_right hbranch']
    calc
      p.sqrtDimensionCorollaryRHS c ≤
          p.c0 / (p.kappa * Real.sqrt p.d) *
            (p.b0 ^ 2 / c *
              max (p.d / (p.pStar * (p.d + p.pStar))) (1 / p.d)) := by
        unfold sqrtDimensionCorollaryRHS
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) hpref
      _ ≤ p.c0 / (p.kappa * Real.sqrt p.d) *
            (p.b0 ^ 2 / c * (p.d * p.M ^ 2)) := by
        gcongr
        exact p.sqrtDimensionShape_le_d_mul_M_sq
      _ = p.c0 * Real.sqrt p.d / (c * p.kappa) *
          (p.b0 * p.M) ^ 2 := by
        field_simp [ne_of_gt hroot, ne_of_gt hc, ne_of_gt hkappa]
        rw [hrootSq]
        ring

/-- Transfer of the first Corollary 2.2 display from any proved master-gap
lower bound. -/
theorem sqrtDimensionCorollaryRHS_le_gap
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d))
    {gap : ℝ≥0∞} (hmaster : ENNReal.ofReal p.masterRHS ≤ gap) :
    ENNReal.ofReal (p.sqrtDimensionCorollaryRHS c) ≤ gap :=
  (ENNReal.ofReal_le_ofReal
    (p.sqrtDimensionCorollaryRHS_le_masterRHS c hc hendpoint)).trans hmaster

/-- Transfer of the simplified second Corollary 2.2 display from any proved
master-gap lower bound, in the full parameter range. -/
theorem sqrtDimensionCorollarySimplifiedRHS_le_gap
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt p.d))
    {gap : ℝ≥0∞} (hmaster : ENNReal.ofReal p.masterRHS ≤ gap) :
    ENNReal.ofReal (p.sqrtDimensionCorollarySimplifiedRHS c) ≤ gap :=
  (ENNReal.ofReal_le_ofReal
    (p.sqrtDimensionCorollarySimplifiedRHS_le c hc)).trans
    (p.sqrtDimensionCorollaryRHS_le_gap c hc hendpoint hmaster)

end Parameters

namespace Concrete.HessianBoundedPotential

variable {d : ℕ}

/-- Corollary 2.2, first display, for randomized MALA under the manuscript's
`C²` Hessian assumptions. -/
theorem sqrtDimensionCorollary_rayleighSpectralGap_lower
    (V : HessianBoundedPotential d) (c : ℝ) (hc : 0 < c) :
    let W := V.toFirstOrderPotential
    let H := c / (W.L * Real.sqrt (d : ℝ))
    let hH : 0 < H := div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
    let p := W.universalParameters H hH
    ENNReal.ofReal (p.sqrtDimensionCorollaryRHS c) ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  let W := V.toFirstOrderPotential
  let H := c / (W.L * Real.sqrt (d : ℝ))
  have hH : 0 < H :=
    div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
  let p := W.universalParameters H hH
  have hmaster := V.universal_masterRHS_rayleighSpectralGap_lower H hH
  exact p.sqrtDimensionCorollaryRHS_le_gap c hc rfl hmaster

/-- Corollary 2.2, simplified second display, for randomized MALA under the
manuscript's `C²` Hessian assumptions and without assuming `pStar ≤ d`. -/
theorem sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
    (V : HessianBoundedPotential d) (c : ℝ) (hc : 0 < c) :
    let W := V.toFirstOrderPotential
    let H := c / (W.L * Real.sqrt (d : ℝ))
    let hH : 0 < H := div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
    let p := W.universalParameters H hH
    ENNReal.ofReal (p.sqrtDimensionCorollarySimplifiedRHS c) ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  let W := V.toFirstOrderPotential
  let H := c / (W.L * Real.sqrt (d : ℝ))
  have hH : 0 < H :=
    div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
  let p := W.universalParameters H hH
  have hmaster := V.universal_masterRHS_rayleighSpectralGap_lower H hH
  exact p.sqrtDimensionCorollarySimplifiedRHS_le_gap c hc rfl hmaster

end Concrete.HessianBoundedPotential

end

end UniformRandomMALA
