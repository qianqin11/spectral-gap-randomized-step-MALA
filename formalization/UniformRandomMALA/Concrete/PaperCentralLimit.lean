import UniformRandomMALA.Concrete.MarkovGaussianCLT
import UniformRandomMALA.Concrete.MarkovCLTAbsolutelyContinuous
import UniformRandomMALA.Concrete.MarkovCLTArbitraryStart
import UniformRandomMALA.Concrete.MALAFirstAcceptance
import UniformRandomMALA.Concrete.PaperAsymptoticVariance

/-!
# The central limit theorem for randomized MALA

Corollary 2.6 (`cor:asymptotic-variance`) holds on the actual infinite
trajectory law from every initial probability distribution. The centered
sum uses the original measurable observable. Its Gaussian variance is the
limit of the actual stationary sample variances, whose gap and dimensional
bounds are supplied by `PaperAsymptoticVariance`.

The proof combines the Poisson martingale CLT, bounded-density truncation,
and the first-acceptance approximation. No initial density, moment,
stationarity, convergence, or ergodicity certificate is an input.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A positive right spectral gap and an everywhere possible absolutely
continuous acceptance give the CLT from every initial probability law. -/
theorem markovCLT_of_gap_and_acceptance
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K A : Kernel α α) [IsMarkovKernel K]
    (r : α → ℝ≥0∞) (hr : Measurable r) (hr1 : ∀ x, r x < 1)
    (hπ : Kernel.Invariant K π) (hA : ∀ x, A x ≪ π)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    TendstoInDistribution (normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π))
      atTop (id : ℝ → ℝ) (fun _ => infiniteMarkovPathLaw μ K)
      (gaussianReal 0 ⟨stationaryAsymptoticVariance π K f,
        (stationaryAsymptoticVariance_spec π K hπ hf hg hg2 hgap).1⟩) := by
  have hv := (stationaryAsymptoticVariance_spec π K hπ hf hg hg2 hgap).1
  apply markov_CLT_of_acceptance_approximation μ π K A r hr hr1 hπ hA hdecomp
    (hm.sub_const _) hv
  intro ν _ hν
  apply tendstoInDistribution_gaussian_of_characteristic
    (fun _ => infiniteMarkovPathLaw ν K)
    (normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π))
    (fun n => (measurable_normalizedMarkovSum (hm.sub_const _) n).aemeasurable) hv
  apply markov_characteristic_tendsto_of_bounded_initial ν π hν K (hm.sub_const _)
    (fun t => (Real.exp (-(t ^ 2 * stationaryAsymptoticVariance π K f / 2)) : ℂ))
  intro η hη B hB hdom t
  let : IsProbabilityMeasure η := hη
  exact boundedInitial_normalizedMarkovSum_characteristic_tendsto
    π η K hπ hB hdom hm hf hg hg2 hgap t

namespace C1Potential

variable {d : ℕ}

/-- The nonlazy central limit assertion of Corollary 2.6
(`cor:asymptotic-variance`), from every initial probability distribution. -/
theorem central_limit_nonlazy
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    {f : State d → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d))) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let K := W.uniformMALA (V.normalizedTunedStep c) (V.normalizedTunedStep_pos c hc)
    let _ : IsMarkovKernel K := W.uniformMALA_isMarkovKernel _ _
    TendstoInDistribution (normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π))
      atTop (id : ℝ → ℝ) (fun _ => infiniteMarkovPathLaw μ K)
      (gaussianReal 0 ⟨stationaryAsymptoticVariance π K f,
        (V.stationaryAsymptoticVariance_nonlazy_bounds c hc hf).1⟩) := by
  dsimp only
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let H := V.normalizedTunedStep c
  let hH := V.normalizedTunedStep_pos c hc
  let K := W.uniformMALA H hH
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel _ _
  let g := min (V.normalizedTunedGapRHS c) 1
  have hg : 0 < g := lt_min (V.normalizedTunedGapRHS_pos c hc) zero_lt_one
  have hg2 : g ≤ 2 := (min_le_right _ _).trans (by norm_num)
  have hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K :=
    (ENNReal.ofReal_mono (min_le_left _ _)).trans
      (V.normalizedTunedCorollary_rayleighSpectralGap_lower c hc)
  exact markovCLT_of_gap_and_acceptance π μ K (W.uniformMALAAccepted H)
    (W.uniformMALARejectionWeight H) (W.measurable_uniformMALARejectionWeight H hH)
    (W.uniformMALARejectionWeight_lt_one H hH) (W.uniformMALA_isReversible H hH).invariant
    (W.uniformMALAAccepted_absolutelyContinuous_target H hH)
    (W.uniformMALA_eq_accepted_add_rejection H hH) hm hf hg hg2 hgap

/-- The half-lazy central limit assertion of Corollary 2.6
(`cor:asymptotic-variance`), with its own actual stationary asymptotic variance. -/
theorem central_limit_lazy
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    {f : State d → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d))) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let P := W.lazyUniformMALA (V.normalizedTunedStep c) (V.normalizedTunedStep_pos c hc)
    let _ : IsMarkovKernel P := W.lazyUniformMALA_isMarkovKernel _ _
    TendstoInDistribution (normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π))
      atTop (id : ℝ → ℝ) (fun _ => infiniteMarkovPathLaw μ P)
      (gaussianReal 0 ⟨stationaryAsymptoticVariance π P f,
        (V.stationaryAsymptoticVariance_lazy_bounds c hc hf).1⟩) := by
  dsimp only
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let H := V.normalizedTunedStep c
  let hH := V.normalizedTunedStep_pos c hc
  let P := W.lazyUniformMALA H hH
  let : IsMarkovKernel P := W.lazyUniformMALA_isMarkovKernel _ _
  have hhalf : ENNReal.ofReal (V.normalizedTunedGapRHS c / 2) ≤ rayleighSpectralGap π P := by
    rw [W.rayleighSpectralGap_lazyUniformMALA H hH,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa only [ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm] using
      (mul_le_mul_of_nonneg_left (V.normalizedTunedCorollary_rayleighSpectralGap_lower c hc)
        (by positivity : 0 ≤ (2 : ℝ≥0∞)⁻¹))
  let g := min (V.normalizedTunedGapRHS c / 2) 1
  have hg : 0 < g := lt_min (div_pos (V.normalizedTunedGapRHS_pos c hc) (by norm_num)) zero_lt_one
  have hg2 : g ≤ 2 := (min_le_right _ _).trans (by norm_num)
  have hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π P :=
    (ENNReal.ofReal_mono (min_le_left _ _)).trans hhalf
  exact markovCLT_of_gap_and_acceptance π μ P (W.lazyUniformMALAAccepted H)
    (W.lazyUniformMALARejectionWeight H) (W.measurable_lazyUniformMALARejectionWeight H hH)
    (W.lazyUniformMALARejectionWeight_lt_one H hH) (W.lazyUniformMALA_isReversible H hH).invariant
    (W.lazyUniformMALAAccepted_absolutelyContinuous_target H hH)
    (W.lazyUniformMALA_eq_accepted_add_rejection H hH) hm hf hg hg2 hgap

end C1Potential
end
end UniformRandomMALA.Concrete
