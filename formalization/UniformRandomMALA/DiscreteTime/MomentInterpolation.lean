import UniformRandomMALA.DiscreteTime.Averaging

/-!
# Extending a second-moment bound to exponents between one and two

This is Jensen's inequality, not an extra moment hypothesis. It is used to
extend the existing `p ≥ 2` discrete-time rejection theorem to `p ≥ 1`.
-/

namespace UniformRandomMALA.DiscreteTime

open MeasureTheory

noncomputable section

/-- On a probability space, a nonnegative function with second moment at most
`C²` has `p`-moment at most `C^p` for `1 ≤ p ≤ 2`. -/
theorem integral_rpow_le_of_second_moment
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {p C : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hC : 0 ≤ C)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfp : Integrable (fun x => f x ^ p) μ)
    (hf2 : Integrable (fun x => f x ^ (2 : ℝ)) μ)
    (hsecond : (∫ x, f x ^ (2 : ℝ) ∂μ) ≤ C ^ (2 : ℝ)) :
    (∫ x, f x ^ p ∂μ) ≤ C ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hq : 1 ≤ 2 / p := (le_div_iff₀ hp0).2 (by simpa using hp2)
  have hprod : p * (2 / p) = 2 := by field_simp [hp_ne]
  have hprod' : (2 / p) * (p / 2) = 1 := by field_simp [hp_ne]
  have hpoint (x : α) : (f x ^ p) ^ (2 / p) = f x ^ (2 : ℝ) := by
    rw [← Real.rpow_mul (hf0 x), hprod]
  have hfpq : Integrable (fun x => (f x ^ p) ^ (2 / p)) μ := by
    simpa only [hpoint] using hf2
  have hJ := rpow_integral_le_integral_rpow hq
    (ae_of_all _ (fun x => Real.rpow_nonneg (hf0 x) p)) hfp hfpq
  simp only [hpoint] at hJ
  have hI0 : 0 ≤ ∫ x, f x ^ p ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (hf0 x) p)
  have hraise := Real.rpow_le_rpow
    (Real.rpow_nonneg hI0 (2 / p)) (hJ.trans hsecond)
    (show 0 ≤ p / 2 by positivity)
  rw [← Real.rpow_mul hI0, hprod', Real.rpow_one,
    ← Real.rpow_mul hC, show (2 : ℝ) * (p / 2) = p by ring] at hraise
  exact hraise

end

end UniformRandomMALA.DiscreteTime
