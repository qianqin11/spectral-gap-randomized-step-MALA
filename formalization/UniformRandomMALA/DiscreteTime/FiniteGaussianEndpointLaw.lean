import UniformRandomMALA.DiscreteTime.FiniteGaussianLikelihood
import UniformRandomMALA.DiscreteTime.GaussianMaximum
import UniformRandomMALA.DiscreteTime.GaussianLawBridge

/-!
# Concrete endpoint law of the finite Gaussian likelihood

This file finishes the finite, unconditional change-of-measure argument.
The sum of the centered finite innovations is identified by characteristic
functions, the frozen recursion is reduced to its closed affine form, and
the resulting endpoint is the concrete Gaussian MALA proposal.  The final
theorem integrates this conditional identity against the target and gives
equality of the two edge measures.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete Concrete.FirstOrderPotential

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- The sum of `n` coordinates under the finite product standard Gaussian
is a standard Gaussian dilated by `sqrt n`. -/
lemma map_fin_sum_stdGaussian :
    Measure.map (fun z : Fin n → State d => ∑ i, z i)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
      Measure.map (fun z : State d => Real.sqrt n • z)
        (stdGaussian (State d)) := by
  let μ : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let Z : Fin n → (Fin n → State d) → State d := fun i z => z i
  have hZ : ∀ i ∈ (Finset.univ : Finset (Fin n)), Measurable (Z i) := by
    intro i hi
    exact measurable_pi_apply i
  have hIndep : iIndepFun Z μ := by
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hLaw : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Measure.map (Z i) μ = stdGaussian (State d) := by
    intro i hi
    simpa [μ, Z] using
      (Measure.pi_map_eval (fun _ : Fin n => stdGaussian (State d)) i)
  simpa [μ, Z] using
    (map_finsetSum_eq_map_sqrt_card_smul_stdGaussian
      μ Z (Finset.univ : Finset (Fin n)) hZ
        (hIndep.restrict _) hLaw)

/-- If `n * delta = h`, the frozen finite endpoint has exactly the
concrete MALA Gaussian proposal law. -/
lemma map_finiteFrozenEndpointRec_initial_eq_gaussianDensityProposal
    (delta h : ℝ) (hh : 0 < h) (htime : (n : ℝ) * delta = h)
    (x0 : State d) :
    Measure.map (finiteFrozenEndpointRec V delta x0 x0)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
      V.gaussianDensityProposal h x0 := by
  have hscale : Real.sqrt (2 * delta) * Real.sqrt (n : ℝ) =
      Real.sqrt (2 * h) := by
    rw [← htime]
    calc
      Real.sqrt (2 * delta) * Real.sqrt (n : ℝ) =
          (Real.sqrt 2 * Real.sqrt delta) * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * (Real.sqrt (n : ℝ) * Real.sqrt delta) := by
        ring
      _ = Real.sqrt 2 * Real.sqrt ((n : ℝ) * delta) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      _ = Real.sqrt (2 * ((n : ℝ) * delta)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [gaussianDensityProposal_eq_map_stdGaussian V hh x0]
  calc
    Measure.map (finiteFrozenEndpointRec V delta x0 x0)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
        Measure.map (fun z : Fin n → State d =>
          V.proposalMean h x0 + Real.sqrt (2 * delta) • ∑ i, z i)
          (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
      congr 1
      funext z
      rw [finiteFrozenEndpointRec_initial_eq_closedForm]
      simp only [proposalMean, htime]
    _ = Measure.map (fun s : State d =>
          V.proposalMean h x0 + Real.sqrt (2 * delta) • s)
          (Measure.map (fun z : Fin n → State d => ∑ i, z i)
            (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop
    _ = Measure.map (fun s : State d =>
          V.proposalMean h x0 + Real.sqrt (2 * delta) • s)
          (Measure.map (fun z : State d => Real.sqrt n • z)
            (stdGaussian (State d))) := by
      rw [map_fin_sum_stdGaussian]
    _ = Measure.map (fun z : State d =>
          V.proposalMean h x0 + Real.sqrt (2 * h) • z)
          (stdGaussian (State d)) := by
      rw [Measure.map_map]
      · congr 1
        funext z
        simp only [Function.comp_apply, smul_smul, hscale]
      · fun_prop
      · fun_prop

/-- Conditional endpoint-law identity in the exponential `DRec`
presentation. -/
lemma map_finiteEulerEndpointRec_DRec_withDensity_eq_gaussianDensityProposal
    (delta h : ℝ) (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : ℝ) * delta = h) (x0 : State d) :
    Measure.map (finiteEulerEndpointRec V delta x0)
        ((Measure.pi (fun _ : Fin n => stdGaussian (State d))).withDensity
          (fun z => ENNReal.ofReal
            (finiteGaussianDRec V 1 delta x0 x0 z))) =
      V.gaussianDensityProposal h x0 := by
  rw [map_finiteEulerEndpointRec_DRec_withDensity
    V delta hdelta x0 x0 n]
  exact map_finiteFrozenEndpointRec_initial_eq_gaussianDensityProposal
    V delta h hh htime x0

/-- Fully unconditioned endpoint-edge identity.  The finite Euler edge law
weighted by `DRec` is exactly `target(dx) Q_h(x,dy)`. -/
theorem map_finiteEulerTiltedEdge_eq_compProd_gaussianDensityProposal
    (delta h : ℝ) (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : ℝ) * delta = h) :
    Measure.map
        (fun p : State d × (Fin n → State d) =>
          (p.1, finiteEulerEndpointRec V delta p.1 p.2))
        (((V.target : Measure (State d)).prod
            (Measure.pi (fun _ : Fin n => stdGaussian (State d)))).withDensity
          (fun p => ENNReal.ofReal
            (finiteGaussianDRec V 1 delta p.1 p.1 p.2))) =
      (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h := by
  let base : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let pairMap : State d × (Fin n → State d) → State d × State d :=
    fun p => (p.1, finiteEulerEndpointRec V delta p.1 p.2)
  let density : State d × (Fin n → State d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (finiteGaussianDRec V 1 delta p.1 p.1 p.2)
  have hpair : Measurable pairMap :=
    measurable_fst.prodMk (measurable_finiteEulerEndpointRec_joint V delta n)
  have hdensity : Measurable density :=
    ENNReal.measurable_ofReal.comp
      (measurable_finiteGaussianDRec_initial V 1 delta hdelta n)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hpair]
  change (∫⁻ a, f (pairMap a)
      ∂(((V.target : Measure (State d)).prod base).withDensity density)) = _
  have hwd := lintegral_withDensity_eq_lintegral_mul
    ((V.target : Measure (State d)).prod base) hdensity (hf.comp hpair)
  change (∫⁻ a, f (pairMap a)
      ∂(((V.target : Measure (State d)).prod base).withDensity density)) =
    ∫⁻ a, density a * f (pairMap a)
      ∂((V.target : Measure (State d)).prod base) at hwd
  rw [hwd]
  have hprod := lintegral_prod
    (μ := (V.target : Measure (State d))) (ν := base)
    (fun a => density a * f (pairMap a))
    (hdensity.mul (hf.comp hpair)).aemeasurable
  change (∫⁻ a, density a * f (pairMap a)
      ∂((V.target : Measure (State d)).prod base)) =
    ∫⁻ x0, ∫⁻ z, density (x0, z) * f (pairMap (x0, z))
      ∂base ∂(V.target : Measure (State d)) at hprod
  rw [hprod]
  rw [Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro x0
  let densityX : (Fin n → State d) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (finiteGaussianDRec V 1 delta x0 x0 z)
  let fX : State d → ℝ≥0∞ := fun y => f (x0, y)
  have hdensityX : Measurable densityX :=
    ENNReal.measurable_ofReal.comp
      (measurable_finiteGaussianDRec V 1 delta hdelta x0 n x0)
  have hfX : Measurable fX := hf.comp (measurable_const.prodMk measurable_id)
  calc
    (∫⁻ z, density (x0, z) * f (pairMap (x0, z)) ∂base) =
        ∫⁻ z, fX (finiteEulerEndpointRec V delta x0 z)
          ∂(base.withDensity densityX) := by
      have hxwd := lintegral_withDensity_eq_lintegral_mul base hdensityX
        (hfX.comp (measurable_finiteEulerEndpointRec V delta x0 n))
      change (∫⁻ z, fX (finiteEulerEndpointRec V delta x0 z)
          ∂(base.withDensity densityX)) =
        ∫⁻ z, densityX z *
          fX (finiteEulerEndpointRec V delta x0 z) ∂base at hxwd
      simpa [density, densityX, pairMap, fX] using hxwd.symm
    _ = ∫⁻ y, fX y ∂Measure.map
          (finiteEulerEndpointRec V delta x0) (base.withDensity densityX) := by
      symm
      exact lintegral_map hfX
        (measurable_finiteEulerEndpointRec V delta x0 n)
    _ = ∫⁻ y, fX y ∂V.gaussianDensityProposal h x0 := by
      rw [map_finiteEulerEndpointRec_DRec_withDensity_eq_gaussianDensityProposal
        V delta h hdelta hh htime x0]

end DiscreteTime

end

end UniformRandomMALA
