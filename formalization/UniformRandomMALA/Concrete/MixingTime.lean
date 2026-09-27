import UniformRandomMALA.Concrete.L2MixingTV
import UniformRandomMALA.Concrete.MixingTimeArithmetic
import UniformRandomMALA.Concrete.TargetGapRange
import UniformRandomMALA.Concrete.TunedSpectralGap

/-!
# Mixing time of half-lazy randomized MALA

The generic ceiling argument and an earlier threshold convention are
derived from actual kernel iterates and proved total-variation contraction.
The current paper-facing Corollary 2.5 (`cor:mixing`), including its
normalized threshold and explicit tuning dependence, is exported by
`PaperNormalizedMixing.lean`.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The paper's total-variation mixing time, including time zero and the
value infinity if the tolerance is never reached. -/
def mixingTime (K : Kernel α α) (μ π : Measure α) (ε : ℝ) : ℕ∞ :=
  mixingTimeOfErrors
    (fun n => setwiseTV (DiscreteTime.finiteKernelIterate K n ∘ₘ μ) π) ε

/-- A positive lower bound for a half-lazy kernel's gap gives the exact
ceiling estimate for its actual transition laws. -/
theorem mixingTime_halfLazy_le
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K))
    (ε : ℝ) (hε : 0 < ε) :
    mixingTime (halfLazyKernel K) μ π ε ≤
      (⌈mixingLog (centeredDensityL2Norm μ π) ε / g⌉₊ : ℕ∞) := by
  apply mixingTimeOfErrors_le_of_geometric
    (centeredDensityL2Norm_nonneg μ π) hε hg0 hg1
  exact setwiseTV_iterate_halfLazy_le μ π hμ hDensity K hrev hg0.le hg1 hgap

/-- A finite positive non-lazy gap gives the first ceiling in the paper's
mixing corollary, with its exact factor two. -/
theorem mixingTime_halfLazy_le_actualGap
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hgapPos : 0 < (rayleighSpectralGap π K).toReal)
    (hgapTwo : rayleighSpectralGap π K ≤ 2)
    (ε : ℝ) (hε : 0 < ε) :
    mixingTime (halfLazyKernel K) μ π ε ≤
      (⌈2 * mixingLog (centeredDensityL2Norm μ π) ε /
        (rayleighSpectralGap π K).toReal⌉₊ : ℕ∞) := by
  have htop : rayleighSpectralGap π K ≠ ∞ :=
    ne_of_lt (hgapTwo.trans_lt (by norm_num))
  have htwo : (rayleighSpectralGap π K).toReal ≤ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hgapTwo)
  have hhalf : ENNReal.ofReal ((rayleighSpectralGap π K).toReal / 2) ≤
      rayleighSpectralGap π (halfLazyKernel K) := by
    rw [rayleighSpectralGap_halfLazyKernel,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_toReal htop]
    simp [div_eq_mul_inv, mul_comm]
  have h := mixingTime_halfLazy_le μ π hμ hDensity K hrev
    (div_pos hgapPos (by norm_num)) (by linarith) hhalf ε hε
  convert h using 2
  congr 1
  ring

/-- Explicit prefactor for arbitrary positive tuning `c`. Its dependence
on `c` cannot be suppressed when quantifying over all positive tunings. -/
def paperMixingConstant (c : ℝ) : ℝ :=
  2 / (concreteGapConstant * min c (FirstOrderPotential.concreteB0 ^ 2 / (2 * c)))

theorem paperMixingConstant_pos {c : ℝ} (hc : 0 < c) :
    0 < paperMixingConstant c := by
  apply div_pos (by norm_num)
  exact mul_pos concreteGapConstant_pos
    (lt_min hc (div_pos (sq_pos_of_pos FirstOrderPotential.concreteB0_pos)
      (mul_pos (by norm_num) hc)))

namespace C1Potential

variable {d : ℕ}

/-- The dimension and condition-number factor in the mixing corollary. -/
def paperMixingScale (V : C1Potential d) : ℝ :=
  (V.L / V.m) * Real.sqrt
    ((d : ℝ) * V.paperMomentThreshold FirstOrderPotential.concreteA0)

theorem paperMixingScale_pos (V : C1Potential d) : 0 < V.paperMixingScale :=
  mul_pos (div_pos V.hL V.hm) (Real.sqrt_pos.2
    (mul_pos V.toFirstOrderPotential.dimension_real_pos V.paperMomentThreshold_concrete_pos))

theorem two_div_paperTunedGapRHS (V : C1Potential d) (c : ℝ) :
    2 / V.paperTunedGapRHS c = paperMixingConstant c * V.paperMixingScale := by
  unfold paperTunedGapRHS paperMixingConstant paperMixingScale
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Both ceiling bounds in the earlier threshold convention, retained as a
compatibility API. The prefactor is `paperMixingConstant c`; all analytic
and spectral-gap inputs are proved from the potential and initial law. -/
theorem mixingTimeCorollary
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (V.toFirstOrderPotential.target : Measure (State d)))
    (hDensity : MemLp
      (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
      2 (V.toFirstOrderPotential.target : Measure (State d)))
    (ε : ℝ) (hε : 0 < ε) :
    let W := V.toFirstOrderPotential
    let H := V.paperTunedStep c
    let hH := V.paperTunedStep_pos c hc
    let ell := mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε
    let gap := (rayleighSpectralGap (W.target : Measure (State d))
      (W.uniformMALA H hH)).toReal
    (mixingTime (W.lazyUniformMALA H hH) μ (W.target : Measure (State d)) ε ≤
      (⌈2 * ell / gap⌉₊ : ℕ∞)) ∧
    ((⌈2 * ell / gap⌉₊ : ℕ∞) ≤
      (⌈paperMixingConstant c * ell * V.paperMixingScale⌉₊ : ℕ∞)) := by
  let W := V.toFirstOrderPotential
  let H := V.paperTunedStep c
  let hH := V.paperTunedStep_pos c hc
  let K := W.uniformMALA H hH
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel H hH
  have hrev : Kernel.IsReversible K (W.target : Measure (State d)) :=
    W.uniformMALA_isReversible H hH
  have htop := W.rayleighSpectralGap_ne_top K hrev
  have hbound : V.paperTunedGapRHS c ≤
      (rayleighSpectralGap (W.target : Measure (State d)) K).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).1
      (V.tunedSqrtDimensionCorollary_rayleighSpectralGap_lower c hc)
  have hpos := (V.paperTunedGapRHS_pos c hc).trans_le hbound
  constructor
  · exact mixingTime_halfLazy_le_actualGap μ (W.target : Measure (State d))
      hμ hDensity K hrev hpos (W.rayleighSpectralGap_le_two K hrev) ε hε
  · apply Nat.cast_le.mpr
    apply Nat.ceil_mono
    calc
      2 * mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε /
          (rayleighSpectralGap (W.target : Measure (State d)) K).toReal ≤
          2 * mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε /
            V.paperTunedGapRHS c :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (mixingLog_nonneg _ _))
          (V.paperTunedGapRHS_pos c hc) hbound
      _ = paperMixingConstant c *
          mixingLog (centeredDensityL2Norm μ (W.target : Measure (State d))) ε *
          V.paperMixingScale := by
        rw [mul_div_right_comm, V.two_div_paperTunedGapRHS c]
        ring

/-- A universal tuning choice gives a universal prefactor in Corollary 2.5
(`cor:mixing`). Neither constant depends on the target, initial law, or
accuracy. -/
theorem exists_universal_mixingTimeCorollary :
    ∃ (c C : ℝ) (hc : 0 < c), 0 < C ∧
      ∀ {d : ℕ} (V : C1Potential d)
        (μ : Measure (State d)) [IsProbabilityMeasure μ],
        μ ≪ (V.toFirstOrderPotential.target : Measure (State d)) →
        MemLp
          (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
          2 (V.toFirstOrderPotential.target : Measure (State d)) →
        ∀ ε : ℝ, 0 < ε →
        mixingTime
          (V.toFirstOrderPotential.lazyUniformMALA (V.paperTunedStep c)
            (V.paperTunedStep_pos c hc))
          μ (V.toFirstOrderPotential.target : Measure (State d)) ε ≤
          (⌈C * mixingLog
            (centeredDensityL2Norm μ (V.toFirstOrderPotential.target : Measure (State d))) ε *
              V.paperMixingScale⌉₊ : ℕ∞) := by
  refine ⟨FirstOrderPotential.concreteB0, paperMixingConstant FirstOrderPotential.concreteB0,
    FirstOrderPotential.concreteB0_pos, paperMixingConstant_pos FirstOrderPotential.concreteB0_pos, ?_⟩
  intro d V μ hprob hμ hDensity ε hε
  exact (V.mixingTimeCorollary FirstOrderPotential.concreteB0
    FirstOrderPotential.concreteB0_pos μ hμ hDensity ε hε).1.trans
      (V.mixingTimeCorollary FirstOrderPotential.concreteB0
        FirstOrderPotential.concreteB0_pos μ hμ hDensity ε hε).2

end C1Potential

end

end UniformRandomMALA.Concrete
