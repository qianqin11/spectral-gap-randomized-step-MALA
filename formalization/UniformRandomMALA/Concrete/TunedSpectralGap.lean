import UniformRandomMALA.Concrete.C1MainTheorem

/-!
# The tuned square-root-logarithmic spectral-gap bound

The third display of Corollary 2.2 (`cor:sqrt-d-endpoint`) follows from its
already formalized second display by choosing `c = c' / sqrt pStar`.
The concrete endpoint below uses the same universal constants and the same
normalized target and randomized MALA kernel as Theorem 2.1 (`thm:main`).
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Parameters

/-- The third displayed right-hand side of Corollary 2.2 (`cor:sqrt-d-endpoint`). -/
def tunedSqrtDimensionCorollaryRHS (p : Parameters) (c : ℝ) : ℝ :=
  p.c0 / (p.kappa * Real.sqrt (p.d * p.pStar)) *
    min c (p.b0 ^ 2 / (2 * c))

/-- Substituting `c / sqrt pStar` into the second display gives the third
display exactly. -/
theorem tunedSqrtDimensionCorollaryRHS_eq (p : Parameters) (c : ℝ) :
    p.tunedSqrtDimensionCorollaryRHS c =
      p.sqrtDimensionCorollarySimplifiedRHS (c / Real.sqrt p.pStar) := by
  have hs : 0 < Real.sqrt p.pStar := Real.sqrt_pos.2 p.hpStar_pos
  have hs_sq := Real.sq_sqrt p.pStar_nonneg
  have hsecond :
      p.b0 ^ 2 / (2 * (c / Real.sqrt p.pStar) * p.pStar) =
        (p.b0 ^ 2 / (2 * c)) / Real.sqrt p.pStar := by
    rw [div_div]
    congr 1
    calc
      2 * (c / Real.sqrt p.pStar) * p.pStar =
          2 * (c / Real.sqrt p.pStar) * (Real.sqrt p.pStar) ^ 2 := by
        rw [hs_sq]
      _ = 2 * c * Real.sqrt p.pStar := by field_simp [hs.ne']
  unfold tunedSqrtDimensionCorollaryRHS sqrtDimensionCorollarySimplifiedRHS
  rw [hsecond, min_div_div_right hs.le, Real.sqrt_mul p.d_nonneg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The tuned endpoint is precisely the endpoint in the second display with
the rescaled tuning constant. -/
theorem tunedSqrtDimension_endpoint_eq (p : Parameters) (c : ℝ) :
    c / (p.L * Real.sqrt (p.d * p.pStar)) =
      (c / Real.sqrt p.pStar) / (p.L * Real.sqrt p.d) := by
  rw [Real.sqrt_mul p.d_nonneg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The third display of Corollary 2.2 (`cor:sqrt-d-endpoint`) follows from any established master
bound; its endpoint has no relation assumption between `pStar` and `d`. -/
theorem tunedSqrtDimensionCorollaryRHS_le_gap
    (p : Parameters) (c : ℝ) (hc : 0 < c)
    (hendpoint : p.H = c / (p.L * Real.sqrt (p.d * p.pStar)))
    {gap : ℝ≥0∞} (hmaster : ENNReal.ofReal p.masterRHS ≤ gap) :
    ENNReal.ofReal (p.tunedSqrtDimensionCorollaryRHS c) ≤ gap := by
  rw [p.tunedSqrtDimensionCorollaryRHS_eq c]
  apply p.sqrtDimensionCorollarySimplifiedRHS_le_gap
    (c / Real.sqrt p.pStar) (div_pos hc (Real.sqrt_pos.2 p.hpStar_pos))
    _ hmaster
  exact hendpoint.trans (p.tunedSqrtDimension_endpoint_eq c)

end Parameters

namespace Concrete.C1Potential

variable {d : ℕ}

/-- Positivity of the manuscript's moment threshold with the universal
constant used by the end-to-end proof. -/
lemma paperMomentThreshold_concrete_pos (V : C1Potential d) :
    0 < V.paperMomentThreshold FirstOrderPotential.concreteA0 :=
  (V.toFirstOrderPotential.universalParameters 1 (by norm_num)).hpStar_pos

/-- The smaller endpoint in Corollary 2.2 (`cor:sqrt-d-endpoint`) and
Corollary 2.4 (`cor:mixing`):
`H = c / (L * sqrt (d * pStar))`. It does not depend on mixing accuracy. -/
def paperTunedStep (V : C1Potential d) (c : ℝ) : ℝ :=
  c / (V.L * Real.sqrt
    ((d : ℝ) * V.paperMomentThreshold FirstOrderPotential.concreteA0))

lemma paperTunedStep_pos (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    0 < V.paperTunedStep c :=
  div_pos hc (mul_pos V.hL (Real.sqrt_pos.2
    (mul_pos V.toFirstOrderPotential.dimension_real_pos
      V.paperMomentThreshold_concrete_pos)))

/-- The literal third display of Corollary 2.2 (`cor:sqrt-d-endpoint`), with the same fixed universal
constants as the end-to-end master theorem. -/
def paperTunedGapRHS (V : C1Potential d) (c : ℝ) : ℝ :=
  concreteGapConstant /
      ((V.L / V.m) * Real.sqrt
        ((d : ℝ) * V.paperMomentThreshold FirstOrderPotential.concreteA0)) *
    min c (FirstOrderPotential.concreteB0 ^ 2 / (2 * c))

lemma paperTunedGapRHS_pos (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    0 < V.paperTunedGapRHS c := by
  unfold paperTunedGapRHS
  exact mul_pos
    (div_pos concreteGapConstant_pos
      (mul_pos (div_pos V.hL V.hm)
        (Real.sqrt_pos.2 (mul_pos V.toFirstOrderPotential.dimension_real_pos
          V.paperMomentThreshold_concrete_pos))))
    (lt_min hc (div_pos (sq_pos_of_pos FirstOrderPotential.concreteB0_pos)
      (mul_pos (by norm_num) hc)))

/-- Corollary 2.2 (`cor:sqrt-d-endpoint`), newly added third display, for the
actual randomized MALA kernel under the manuscript's first-order assumptions.
The master bound and all its analytic ingredients are discharged internally. -/
theorem tunedSqrtDimensionCorollary_rayleighSpectralGap_lower
    (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (V.paperTunedGapRHS c) ≤
      rayleighSpectralGap
        (V.toFirstOrderPotential.target : Measure (State d))
        (V.toFirstOrderPotential.uniformMALA
          (V.paperTunedStep c) (V.paperTunedStep_pos c hc)) := by
  let p := V.toFirstOrderPotential.universalParameters
    (V.paperTunedStep c) (V.paperTunedStep_pos c hc)
  exact p.tunedSqrtDimensionCorollaryRHS_le_gap c hc rfl
    (V.universal_masterRHS_rayleighSpectralGap_lower
      (V.paperTunedStep c) (V.paperTunedStep_pos c hc))

end Concrete.C1Potential

end

end UniformRandomMALA
