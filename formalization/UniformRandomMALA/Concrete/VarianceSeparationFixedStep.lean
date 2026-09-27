import UniformRandomMALA.Concrete.VarianceSeparationWitness
import UniformRandomMALA.Concrete.FixedStepMinimax
import UniformRandomMALA.Concrete.TargetGapOne

/-!
# The fixed-step variance-separation witness

Corollary 2.7 (`cor:variance-separation`), assertion (ii), follows from the
proved minimax gap ceiling and actual large-variance witnesses. The
asymptotic variance is the genuine extended stationary limit, including
zero-gap kernels and infinite variance.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

private theorem one_div_max_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / max a b = min (1 / a) (1 / b) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, min_eq_right (one_div_le_one_div_of_le ha hab)]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left hba, min_eq_left (one_div_le_one_div_of_le hb hba)]

/-- The complete fixed-step assertion of Corollary 2.7
(`cor:variance-separation`). The exponential constant is universal; the
variance prefactor depends only on the fixed lower condition-number bound.
The selected potential is genuinely smooth and has the requested `m,L`. -/
theorem exists_universal_fixedStep_variance_separation :
    ∃ a : ℝ, 0 < a ∧
      ∀ {κ₀ : ℝ}, 1 < κ₀ →
        ∃ c : ℝ, 0 < c ∧
          ∀ {d : ℕ}, 2 ≤ d →
          ∀ {m L : ℝ}, 0 < m → m < L → κ₀ ≤ L / m →
          ∀ {h : ℝ} (hh : 0 < h),
            ∃ V : HessianBoundedPotential d,
              V.m = m ∧ V.L = L ∧ ContDiff ℝ ⊤ V.U ∧
              ∃ f : State d → ℝ,
                MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d)) ∧
                variance f (V.toFirstOrderPotential.target : Measure (State d)) = 1 ∧
                ENNReal.ofReal (c * min
                  (((L / m) * d) / Real.log ((L / m) * d)) (Real.exp (a * d))) ≤
                  asymptoticVarianceExtended
                    (V.toFirstOrderPotential.target : Measure (State d))
                    (V.toFirstOrderPotential.malaKernel h hh) f := by
  obtain ⟨a, ha, hminimax⟩ := exists_universal_fixedStepMinimaxGap_paper_upper
  refine ⟨a, ha, ?_⟩
  intro κ₀ hκ₀
  obtain ⟨C, hC, hCbound⟩ := hminimax hκ₀
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro d hd m L hm hmL hκ h hh
  let Q := max (Real.log ((L / m) * d) / ((L / m) * d)) (Real.exp (-a * d))
  have hQ : 0 < Q := (Real.exp_pos _).trans_le (le_max_right _ _)
  have hinf : fixedStepWorstPotentialGap d m L h ≤ ENNReal.ofReal (C * Q) := by
    apply le_trans (le_iSup (fun h : {h : ℝ // 0 < h} => fixedStepWorstPotentialGap d m L h) ⟨h, hh⟩)
    exact hCbound hd hm hmL hκ
  have hstrict : fixedStepWorstPotentialGap d m L h < ENNReal.ofReal (2 * C * Q) :=
    hinf.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith [mul_pos hC hQ]))
  obtain ⟨value, hvalue, hsmall⟩ := sInf_lt_iff.mp hstrict
  obtain ⟨hh', V, hVm, hVL, hsmooth, rfl⟩ := hvalue
  let W := V.toFirstOrderPotential
  let K := W.malaKernel h hh
  let : IsMarkovKernel K := W.malaKernel_isMarkovKernel h hh
  have hrev : Kernel.IsReversible K (W.target : Measure (State d)) := W.malaKernel_isReversible h hh
  obtain ⟨f, hf, hv, hσ⟩ := exists_unit_variance_ge_of_gap_le
    (W.target : Measure (State d)) K hrev
    (B := 2 * C * Q) (by positivity) hsmall.le (W.rayleighSpectralGap_le_one K hrev)
  refine ⟨V, hVm, hVL, hsmooth, f, hf, hv, ?_⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hκ1 : 1 < L / m := hκ₀.trans_le hκ
  have hdpos : (0 : ℝ) < d := by linarith
  have hκd : 1 < (L / m) * d := by
    calc
      (1 : ℝ) < d := by linarith
      _ < (L / m) * d := by simpa using mul_lt_mul_of_pos_right hκ1 hdpos
  have hA : 0 < Real.log ((L / m) * d) / ((L / m) * d) :=
    div_pos (Real.log_pos hκd) (zero_lt_one.trans hκd)
  have hinverse : 1 / Q = min
      (((L / m) * d) / Real.log ((L / m) * d)) (Real.exp (a * d)) := by
    rw [show Q = max (Real.log ((L / m) * d) / ((L / m) * d)) (Real.exp (-a * d)) from rfl,
      one_div_max_pos hA (Real.exp_pos _)]
    simp only [one_div, inv_div, ← Real.exp_neg, neg_mul, neg_neg]
  have hid : 1 / (2 * (2 * C * Q)) = (1 / (4 * C)) * min
      (((L / m) * d) / Real.log ((L / m) * d)) (Real.exp (a * d)) := by
    rw [← hinverse]
    field_simp
    norm_num
  rw [hid] at hσ
  exact hσ

end
end UniformRandomMALA.Concrete
