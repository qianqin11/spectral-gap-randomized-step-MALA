import UniformRandomMALA.Concrete.PaperNormalizedGap
import UniformRandomMALA.Concrete.MixingTime

/-!
# Mixing with the normalized logarithmic threshold

Corollary 2.5 (`cor:mixing`) uses the actual initial density and kernel
iterates, `pStar = 1 + log d + log kappa`, and a universal multiple of
`max c (1/c)` as its tuning-dependent prefactor.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The universal multiplier in the mixing corollary. -/
def normalizedMixingUniversalConstant : ℝ :=
  2 / C1Potential.normalizedCorollaryConstant

lemma normalizedMixingUniversalConstant_pos : 0 < normalizedMixingUniversalConstant :=
  div_pos (by norm_num) C1Potential.normalizedCorollaryConstant_pos

/-- The literal tuning dependence in Corollary 2.5 (`cor:mixing`). -/
def normalizedMixingConstant (c : ℝ) : ℝ :=
  normalizedMixingUniversalConstant * max c (1 / c)

lemma normalizedMixingConstant_pos {c : ℝ} (hc : 0 < c) :
    0 < normalizedMixingConstant c :=
  mul_pos normalizedMixingUniversalConstant_pos (hc.trans_le (le_max_left _ _))

lemma one_div_min_self_reciprocal (c : ℝ) :
    1 / min c (1 / c) = max c (1 / c) := by
  rcases le_total c (1 / c) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, one_div_one_div]

namespace C1Potential

variable {d : ℕ}

/-- The normalized dimensional factor in Corollary 2.5 (`cor:mixing`). -/
def normalizedMixingScale (V : C1Potential d) : ℝ :=
  (V.L / V.m) * Real.sqrt ((d : ℝ) * V.normalizedMomentThreshold)

lemma normalizedMixingScale_pos (V : C1Potential d) : 0 < V.normalizedMixingScale :=
  mul_pos (div_pos V.hL V.hm) (Real.sqrt_pos.2
    (mul_pos V.toFirstOrderPotential.dimension_real_pos V.normalizedMomentThreshold_pos))

lemma two_div_normalizedTunedGapRHS (V : C1Potential d) (c : ℝ) :
    2 / V.normalizedTunedGapRHS c = normalizedMixingConstant c * V.normalizedMixingScale := by
  calc
    2 / V.normalizedTunedGapRHS c =
        normalizedMixingUniversalConstant * V.normalizedMixingScale *
          (1 / min c (1 / c)) := by
      unfold normalizedTunedGapRHS normalizedMixingScale normalizedMixingUniversalConstant
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = _ := by rw [one_div_min_self_reciprocal]; unfold normalizedMixingConstant; ring

/-- Corollary 2.5 (`cor:mixing`), both displayed ceilings with the normalized
threshold and a universal multiple of `max c (1/c)`. Only the paper's
potential, initial-law, positive-tuning, and positive-accuracy assumptions
remain; the gap and convergence estimates are proved internally. -/
theorem normalizedMixingTimeCorollary
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (V.toFirstOrderPotential.target : Measure (State d)))
    (hDensity : MemLp
      (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
      2 (V.toFirstOrderPotential.target : Measure (State d)))
    (ε : ℝ) (hε : 0 < ε) :
    let W := V.toFirstOrderPotential
    let H := V.normalizedTunedStep c
    let hH := V.normalizedTunedStep_pos c hc
    let ell := mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε
    let gap := (rayleighSpectralGap (W.target : Measure (State d))
      (W.uniformMALA H hH)).toReal
    (mixingTime (W.lazyUniformMALA H hH) μ (W.target : Measure (State d)) ε ≤
      (⌈2 * ell / gap⌉₊ : ℕ∞)) ∧
    ((⌈2 * ell / gap⌉₊ : ℕ∞) ≤
      (⌈normalizedMixingConstant c * ell * V.normalizedMixingScale⌉₊ : ℕ∞)) := by
  let W := V.toFirstOrderPotential
  let H := V.normalizedTunedStep c
  let hH := V.normalizedTunedStep_pos c hc
  let K := W.uniformMALA H hH
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel H hH
  have hrev : Kernel.IsReversible K (W.target : Measure (State d)) :=
    W.uniformMALA_isReversible H hH
  have htop := W.rayleighSpectralGap_ne_top K hrev
  have hbound : V.normalizedTunedGapRHS c ≤
      (rayleighSpectralGap (W.target : Measure (State d)) K).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).1
      (V.normalizedTunedCorollary_rayleighSpectralGap_lower c hc)
  have hpos := (V.normalizedTunedGapRHS_pos c hc).trans_le hbound
  constructor
  · exact mixingTime_halfLazy_le_actualGap μ (W.target : Measure (State d))
      hμ hDensity K hrev hpos (W.rayleighSpectralGap_le_two K hrev) ε hε
  · apply Nat.cast_le.mpr
    apply Nat.ceil_mono
    calc
      2 * mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε /
          (rayleighSpectralGap (W.target : Measure (State d)) K).toReal ≤
          2 * mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε /
            V.normalizedTunedGapRHS c :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (mixingLog_nonneg _ _))
          (V.normalizedTunedGapRHS_pos c hc) hbound
      _ = normalizedMixingConstant c *
          mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε *
          V.normalizedMixingScale := by
        rw [mul_div_right_comm, V.two_div_normalizedTunedGapRHS c]
        ring

/-- The universal coefficient is chosen before every tuning parameter and
every target in Corollary 2.5 (`cor:mixing`). -/
theorem exists_universal_normalizedMixingTimeCorollary :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d : ℕ} (V : C1Potential d) (c : ℝ) (hc : 0 < c)
        (μ : Measure (State d)) [IsProbabilityMeasure μ],
        μ ≪ (V.toFirstOrderPotential.target : Measure (State d)) →
        MemLp
          (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
          2 (V.toFirstOrderPotential.target : Measure (State d)) →
        ∀ ε : ℝ, 0 < ε →
        mixingTime
          (V.toFirstOrderPotential.lazyUniformMALA (V.normalizedTunedStep c)
            (V.normalizedTunedStep_pos c hc))
          μ (V.toFirstOrderPotential.target : Measure (State d)) ε ≤
          (⌈(C * max c (1 / c)) * mixingLog
            (centeredDensityL2Norm μ (V.toFirstOrderPotential.target : Measure (State d))) ε *
              V.normalizedMixingScale⌉₊ : ℕ∞) := by
  refine ⟨normalizedMixingUniversalConstant, normalizedMixingUniversalConstant_pos, ?_⟩
  intro d V c hc μ hprob hμ hDensity ε hε
  exact (V.normalizedMixingTimeCorollary c hc μ hμ hDensity ε hε).1.trans
    (V.normalizedMixingTimeCorollary c hc μ hμ hDensity ε hε).2

end C1Potential
end
end UniformRandomMALA.Concrete
