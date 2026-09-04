import UniformRandomMALA.Concrete.GaussianBobkovFunctional
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Gaussian OU generator and Bobkov flow

This file supplies the analytic bridge between the Mehler semigroup and the
pointwise algebra in `GaussianBobkov`.  The first ingredient is Gaussian
integration by parts, proved from the explicit one-dimensional density.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal ProbabilityTheory InnerProductSpace

noncomputable section

namespace Concrete

/-- One-dimensional integration by parts for the standard Gaussian.  The
three integrability hypotheses are exactly the three terms in ordinary
integration by parts after exposing the Gaussian density. -/
theorem integral_deriv_standardGaussian_eq_integral_mul
    {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf'int : Integrable f' standardGaussianMeasure)
    (hxfint : Integrable (fun x => x * f x) standardGaussianMeasure)
    (hfint : Integrable f standardGaussianMeasure) :
    ∫ x, f' x ∂standardGaussianMeasure =
      ∫ x, x * f x ∂standardGaussianMeasure := by
  have hmeasure : standardGaussianMeasure =
      volume.withDensity (gaussianPDF 0 1) := by
    exact gaussianReal_of_var_ne_zero 0 (by norm_num)
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x = normalDensity x := by
    simp [normalDensity, gaussianPDFReal]
  have hf'vol : Integrable (fun x => f' x * normalDensity x) := by
    rw [hmeasure] at hf'int
    have h := (integrable_withDensity_iff
      (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).1 hf'int
    simpa [hpdf, mul_comm] using h
  have hxfvol : Integrable (fun x => (x * f x) * normalDensity x) := by
    rw [hmeasure] at hxfint
    have h := (integrable_withDensity_iff
      (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).1 hxfint
    simpa [hpdf, mul_comm] using h
  have hfvol : Integrable (fun x => f x * normalDensity x) := by
    rw [hmeasure] at hfint
    have h := (integrable_withDensity_iff
      (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).1 hfint
    simpa [hpdf, mul_comm] using h
  have hleft :
      ∫ x, f x * (-x * normalDensity x) =
        -∫ x, f' x * normalDensity x := by
    exact integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hf x) (fun x _ => hasDerivAt_normalDensity x)
      (hxfvol.neg.congr (ae_of_all _ fun x => by
        simp only [Pi.mul_apply, Pi.neg_apply]
        ring))
      (hf'vol.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply]))
      (hfvol.congr (ae_of_all _ fun x => by simp only [Pi.mul_apply]))
  have hweighted :
      ∫ x, f' x * normalDensity x =
        ∫ x, x * f x * normalDensity x := by
    have hneg :
        -(∫ x, x * f x * normalDensity x) =
          -(∫ x, f' x * normalDensity x) := by
      rw [← MeasureTheory.integral_neg (fun x => x * f x * normalDensity x)]
      calc
        ∫ x, -(x * f x * normalDensity x) =
            ∫ x, f x * (-x * normalDensity x) := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
        _ = _ := hleft
    exact neg_injective hneg.symm
  rw [hmeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top),
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, hpdf]
  calc
    ∫ x, normalDensity x * f' x = ∫ x, f' x * normalDensity x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => mul_comm _ _
    _ = ∫ x, x * f x * normalDensity x := hweighted
    _ = ∫ x, normalDensity x * (x * f x) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

/-- Coordinatewise integration by parts for a finite product of independent
standard Gaussians.  The coordinate derivative is stated after inserting the
distinguished coordinate, which makes the Fubini argument independent of any
choice of basis. -/
theorem integral_partial_pi_standardGaussian_eq_integral_mul
    {n : ℕ} (i : Fin (n + 1)) {g gi : (Fin (n + 1) → ℝ) → ℝ}
    (hderiv : ∀ (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt (fun t => g (i.insertNth t w))
        (gi (i.insertNth r w)) r)
    (hgi : Integrable gi
      (Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)))
    (hzg : Integrable (fun z => z i * g z)
      (Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)))
    (hg : Integrable g
      (Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure))) :
    ∫ z, gi z
        ∂(Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)) =
      ∫ z, z i * g z
        ∂(Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let ν : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => standardGaussianMeasure)
  let ins : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) :=
    fun p => i.insertNth p.1 p.2
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure))
      (standardGaussianMeasure.prod ν) := by
    simpa [e, ν] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => standardGaussianMeasure) i)
  have hmpsymm : MeasurePreserving e.symm
      (standardGaussianMeasure.prod ν)
      (Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)) :=
    hmp.symm e
  have heins : (fun p => e.symm p) = ins := by
    funext p
    simp [e, ins, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv]
  have hgiPair : Integrable (fun p => gi (ins p))
      (standardGaussianMeasure.prod ν) := by
    have h := (hmpsymm.integrable_comp_emb e.symm.measurableEmbedding).2 hgi
    simpa only [Function.comp_def, heins] using h
  have hzgPair : Integrable (fun p => p.1 * g (ins p))
      (standardGaussianMeasure.prod ν) := by
    have h := (hmpsymm.integrable_comp_emb e.symm.measurableEmbedding).2 hzg
    simpa only [Function.comp_def, heins, ins, Fin.insertNth_apply_same] using h
  have hgPair : Integrable (fun p => g (ins p))
      (standardGaussianMeasure.prod ν) := by
    have h := (hmpsymm.integrable_comp_emb e.symm.measurableEmbedding).2 hg
    simpa only [Function.comp_def, heins] using h
  have hsections : ∀ᵐ w ∂ν,
      Integrable (fun r => gi (ins (r, w))) standardGaussianMeasure ∧
      Integrable (fun r => r * g (ins (r, w))) standardGaussianMeasure ∧
      Integrable (fun r => g (ins (r, w))) standardGaussianMeasure := by
    filter_upwards [hgiPair.prod_left_ae, hzgPair.prod_left_ae,
      hgPair.prod_left_ae] with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  calc
    ∫ z, gi z
        ∂(Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)) =
        ∫ p, gi (ins p) ∂(standardGaussianMeasure.prod ν) := by
      simpa only [Function.comp_def, heins] using
        (hmpsymm.integral_comp' gi).symm
    _ = ∫ w, ∫ r, gi (ins (r, w)) ∂standardGaussianMeasure ∂ν :=
      integral_prod_symm _ hgiPair
    _ = ∫ w, ∫ r, r * g (ins (r, w)) ∂standardGaussianMeasure ∂ν := by
      apply integral_congr_ae
      filter_upwards [hsections] with w hw
      exact integral_deriv_standardGaussian_eq_integral_mul
        (f := fun r => g (ins (r, w)))
        (f' := fun r => gi (ins (r, w)))
        (by intro r; simpa [ins] using hderiv w r) hw.1 hw.2.1 hw.2.2
    _ = ∫ p, p.1 * g (ins p) ∂(standardGaussianMeasure.prod ν) :=
      (integral_prod_symm _ hzgPair).symm
    _ = ∫ z, z i * g z
        ∂(Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)) := by
      simpa only [Function.comp_def, heins, ins, Fin.insertNth_apply_same] using
        hmpsymm.integral_comp' (fun z => z i * g z)

/-- Coordinate Gaussian integration by parts on Euclidean space. -/
theorem integral_partial_stdGaussian_eq_integral_mul
    {n : ℕ} (i : Fin (n + 1))
    {g gi : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hderiv : ∀ (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun t => g (WithLp.toLp 2 (i.insertNth t w)))
        (gi (WithLp.toLp 2 (i.insertNth r w))) r)
    (hgi : Integrable gi (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hzg : Integrable (fun z => z i * g z)
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hg : Integrable g (stdGaussian (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∫ z, gi z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) =
      ∫ z, z i * g z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => standardGaussianMeasure)
  let e := MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)
  have hmp : MeasurePreserving e μ
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) := by
    refine ⟨e.measurable, ?_⟩
    change Measure.map (WithLp.toLp 2) μ =
      stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))
    simpa [μ, standardGaussianMeasure] using
      (map_pi_eq_stdGaussian (ι := Fin (n + 1)))
  have hgi' : Integrable (gi ∘ e) μ :=
    (hmp.integrable_comp hgi.aestronglyMeasurable).2 hgi
  have hzg' : Integrable (fun z => z i * g (e z)) μ := by
    have h := (hmp.integrable_comp hzg.aestronglyMeasurable).2 hzg
    simpa only [Function.comp_def, e, MeasurableEquiv.toLp_apply] using h
  have hg' : Integrable (g ∘ e) μ :=
    (hmp.integrable_comp hg.aestronglyMeasurable).2 hg
  have hibp := integral_partial_pi_standardGaussian_eq_integral_mul i
    (g := g ∘ e) (gi := gi ∘ e)
    (by intro w r; simpa [e, Function.comp_def] using hderiv w r)
    (by simpa [μ] using hgi') (by simpa [μ] using hzg')
    (by simpa [μ] using hg')
  calc
    ∫ z, gi z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) =
        ∫ z, gi (e z) ∂μ := (hmp.integral_comp' gi).symm
    _ = ∫ z, z i * g (e z) ∂μ := hibp
    _ = ∫ z, z i * g z
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
      simpa only [Function.comp_def, e, MeasurableEquiv.toLp_apply] using
        hmp.integral_comp' (fun z => z i * g z)

/-- Time derivative of the deterministic Mehler coefficient. -/
theorem hasDerivAt_ouDriftCoeff (t : ℝ) :
    HasDerivAt ouDriftCoeff (-ouDriftCoeff t) t := by
  change HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-t)) t
  convert (hasDerivAt_neg t).exp using 1 <;> ring

theorem antitone_ouDriftCoeff : Antitone ouDriftCoeff := by
  intro s t hst
  exact Real.exp_le_exp.mpr (neg_le_neg hst)

theorem monotone_ouNoiseCoeff_on_nonneg :
    MonotoneOn ouNoiseCoeff (Set.Ici (0 : ℝ)) := by
  intro s hs t ht hst
  apply Real.sqrt_le_sqrt
  exact sub_le_sub_left
    (Real.exp_le_exp.mpr (by linarith)) 1

/-- Positivity of the Mehler variance away from time zero. -/
lemma bobkovVarianceCoeff_pos {t : ℝ} (ht : 0 < t) :
    0 < bobkovVarianceCoeff t := by
  unfold bobkovVarianceCoeff
  rw [sub_pos]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- Time derivative of the noise coefficient at positive time. -/
theorem hasDerivAt_ouNoiseCoeff {t : ℝ} (ht : 0 < t) :
    HasDerivAt ouNoiseCoeff
      (ouDriftCoeff t ^ 2 / ouNoiseCoeff t) t := by
  have hc0 : bobkovVarianceCoeff t ≠ 0 :=
    (bobkovVarianceCoeff_pos ht).ne'
  have hraw := (hasDerivAt_bobkovVarianceCoeff t).sqrt hc0
  have hnoise : ouNoiseCoeff t = Real.sqrt (bobkovVarianceCoeff t) := rfl
  have hdrift : ouDriftCoeff t ^ 2 = 1 - bobkovVarianceCoeff t := by
    rw [← ouDriftCoeff_sq_add_ouNoiseCoeff_sq ht.le,
      bobkovVarianceCoeff_eq_ouNoiseCoeff_sq ht.le]
    ring
  change HasDerivAt (fun r => Real.sqrt (bobkovVarianceCoeff r))
    (ouDriftCoeff t ^ 2 / Real.sqrt (bobkovVarianceCoeff t)) t
  convert hraw using 1
  rw [← hdrift]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Velocity of a Mehler trajectory at positive time. -/
def gaussianOUTransitionTimeDeriv (t : ℝ) (x z : E) : E :=
  (-ouDriftCoeff t) • x +
    (ouDriftCoeff t ^ 2 / ouNoiseCoeff t) • z

theorem hasDerivAt_gaussianOUTransition_time
    {t : ℝ} (ht : 0 < t) (x z : E) :
    HasDerivAt (fun r => gaussianOUTransition r x z)
      (gaussianOUTransitionTimeDeriv t x z) t := by
  unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
  exact (hasDerivAt_ouDriftCoeff t).smul_const x |>.add
    ((hasDerivAt_ouNoiseCoeff ht).smul_const z)

section TimeDerivative

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- Direct positive-time derivative of the Mehler integral.  Boundedness of
`Dq` supplies a Gaussian-integrable local dominating function; this is why no
differentiation-under-the-integral premise appears in the statement. -/
theorem hasDerivAt_gaussianOUSemigroup_time_direct
    {t : ℝ} (ht : 0 < t)
    (q : BoundedContinuousFunction E ℝ)
    (Dq : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDq : ∀ y, HasFDerivAt q (Dq y) y) (x : E) :
    HasDerivAt (fun r => gaussianOUSemigroup r q x)
      (∫ z, Dq (gaussianOUTransition t x z)
        (gaussianOUTransitionTimeDeriv t x z) ∂stdGaussian E) t := by
  let U : Set ℝ := Metric.ball t (t / 2)
  let a0 : ℝ := ouDriftCoeff (t / 2)
  let b0 : ℝ := ouNoiseCoeff (t / 2)
  let k : ℝ := a0 ^ 2 / b0
  let bound : E → ℝ := fun z => ‖Dq‖ * (a0 * ‖x‖ + k * ‖z‖)
  have ht2 : 0 < t / 2 := by linarith
  have hb0 : 0 < b0 := by
    dsimp only [b0, ouNoiseCoeff]
    exact Real.sqrt_pos.2 (by
      change 0 < bobkovVarianceCoeff (t / 2)
      exact bobkovVarianceCoeff_pos ht2)
  have ha0 : 0 < a0 := ouDriftCoeff_pos _
  have hk0 : 0 ≤ k := div_nonneg (sq_nonneg _) hb0.le
  have hU : U ∈ nhds t := Metric.ball_mem_nhds t ht2
  have hrpos : ∀ r ∈ U, 0 < r := by
    intro r hr
    have hdist : |r - t| < t / 2 := by
      simpa [U, Real.dist_eq] using hr
    rw [abs_lt] at hdist
    linarith
  have ha_le : ∀ r ∈ U, ouDriftCoeff r ≤ a0 := by
    intro r hr
    exact antitone_ouDriftCoeff (by
      have hdist : |r - t| < t / 2 := by
        simpa [U, Real.dist_eq] using hr
      rw [abs_lt] at hdist
      linarith)
  have hb_le : ∀ r ∈ U, b0 ≤ ouNoiseCoeff r := by
    intro r hr
    apply monotone_ouNoiseCoeff_on_nonneg ht2.le (hrpos r hr).le
    have hdist : |r - t| < t / 2 := by
      simpa [U, Real.dist_eq] using hr
    rw [abs_lt] at hdist
    linarith
  have hk_le : ∀ r ∈ U,
      ouDriftCoeff r ^ 2 / ouNoiseCoeff r ≤ k := by
    intro r hr
    have har0 : 0 ≤ ouDriftCoeff r := (ouDriftCoeff_pos r).le
    have hbr0 : 0 < ouNoiseCoeff r := by
      dsimp only [ouNoiseCoeff]
      exact Real.sqrt_pos.2 (by
        change 0 < bobkovVarianceCoeff r
        exact bobkovVarianceCoeff_pos (hrpos r hr))
    exact div_le_div₀ (sq_nonneg a0)
      ((sq_le_sq₀ har0 ha0.le).2 (ha_le r hr)) hb0 (hb_le r hr)
  have hboundInt : Integrable bound (stdGaussian E) := by
    have hnorm : Integrable (fun z : E => ‖z‖) (stdGaussian E) :=
      IsGaussian.integrable_id.norm
    exact ((integrable_const (a0 * ‖x‖)).add
      (hnorm.const_mul k)).const_mul ‖Dq‖
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E)
    (F := fun r z => q (gaussianOUTransition r x z))
    (F' := fun r z => Dq (gaussianOUTransition r x z)
      (gaussianOUTransitionTimeDeriv r x z))
    (bound := bound) hU
  have hresult : HasDerivAt
      (fun r => ∫ z, q (gaussianOUTransition r x z) ∂stdGaussian E)
      (∫ z, Dq (gaussianOUTransition t x z)
        (gaussianOUTransitionTimeDeriv t x z) ∂stdGaussian E) t := by
    apply (hmain ?_ ?_ ?_ ?_ hboundInt ?_).2
    · exact Filter.Eventually.of_forall fun r =>
        (q.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        (q.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖q‖ ?_
      exact Filter.Eventually.of_forall fun z => q.norm_coe_le_norm _
    · exact (show Continuous (fun z : E =>
          Dq (gaussianOUTransition t x z)
            (gaussianOUTransitionTimeDeriv t x z)) by
        unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
        fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z r hr => by
        have haabs : |ouDriftCoeff r| ≤ a0 := by
          rw [abs_of_pos (ouDriftCoeff_pos r)]
          exact ha_le r hr
        have hkabs :
            |ouDriftCoeff r ^ 2 / ouNoiseCoeff r| ≤ k := by
          rw [abs_of_nonneg (div_nonneg (sq_nonneg _)
            (ouNoiseCoeff_nonneg r))]
          exact hk_le r hr
        have hvel : ‖gaussianOUTransitionTimeDeriv r x z‖ ≤
            a0 * ‖x‖ + k * ‖z‖ := by
          unfold gaussianOUTransitionTimeDeriv
          calc
            ‖(-ouDriftCoeff r) • x +
                (ouDriftCoeff r ^ 2 / ouNoiseCoeff r) • z‖ ≤
                ‖(-ouDriftCoeff r) • x‖ +
                  ‖(ouDriftCoeff r ^ 2 / ouNoiseCoeff r) • z‖ :=
              norm_add_le _ _
            _ = |ouDriftCoeff r| * ‖x‖ +
                |ouDriftCoeff r ^ 2 / ouNoiseCoeff r| * ‖z‖ := by
              simp only [norm_smul, Real.norm_eq_abs, abs_neg]
            _ ≤ a0 * ‖x‖ + k * ‖z‖ :=
              add_le_add
                (mul_le_mul_of_nonneg_right haabs (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hkabs (norm_nonneg _))
        calc
          ‖Dq (gaussianOUTransition r x z)
              (gaussianOUTransitionTimeDeriv r x z)‖ ≤
              ‖Dq (gaussianOUTransition r x z)‖ *
                ‖gaussianOUTransitionTimeDeriv r x z‖ :=
            (Dq (gaussianOUTransition r x z)).le_opNorm _
          _ ≤ ‖Dq‖ * ‖gaussianOUTransitionTimeDeriv r x z‖ :=
            mul_le_mul_of_nonneg_right (Dq.norm_coe_le_norm _) (norm_nonneg _)
          _ ≤ ‖Dq‖ * (a0 * ‖x‖ + k * ‖z‖) :=
            mul_le_mul_of_nonneg_left hvel (norm_nonneg Dq)
          _ = bound z := rfl
    · exact Filter.Eventually.of_forall fun z r hr => by
        have hcomp := (hDq (gaussianOUTransition r x z)).comp r
          (hasDerivAt_gaussianOUTransition_time (hrpos r hr) x z).hasFDerivAt
        simpa [Function.comp_def] using hcomp.hasDerivAt
  simpa [gaussianOUSemigroup] using hresult

/-- Differentiation of a genuinely time-dependent Mehler family.  The local
dominating function is explicit in the hypotheses, while measurability and
integrability of the value at the differentiation time follow from the
bounded-continuous family. -/
theorem hasDerivAt_gaussianOUSemigroup_timeDependent_direct
    {s : ℝ} (hs : 0 < s)
    (Q : ℝ → BoundedContinuousFunction E ℝ)
    (Qt : ℝ → BoundedContinuousFunction E ℝ)
    (DQ : ℝ → BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (x : E) (U : Set ℝ) (hU : U ∈ nhds s)
    (bound : E → ℝ) (hboundInt : Integrable bound (stdGaussian E))
    (hbound : ∀ᵐ z ∂stdGaussian E, ∀ r ∈ U,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound z)
    (hjoint : ∀ᵐ z ∂stdGaussian E, ∀ r ∈ U,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r) :
    HasDerivAt (fun r => gaussianOUSemigroup r (Q r) x)
      (∫ z, Qt s (gaussianOUTransition s x z) +
        DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z) ∂stdGaussian E) s := by
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E)
    (F := fun r z => Q r (gaussianOUTransition r x z))
    (F' := fun r z => Qt r (gaussianOUTransition r x z) +
      DQ r (gaussianOUTransition r x z)
        (gaussianOUTransitionTimeDeriv r x z))
    (bound := bound) hU
  have hresult : HasDerivAt
      (fun r => ∫ z, Q r (gaussianOUTransition r x z) ∂stdGaussian E)
      (∫ z, Qt s (gaussianOUTransition s x z) +
        DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z) ∂stdGaussian E) s := by
    apply (hmain ?_ ?_ ?_ hbound hboundInt hjoint).2
    · exact Filter.Eventually.of_forall fun r =>
        ((Q r).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        ((Q s).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖Q s‖ ?_
      exact Filter.Eventually.of_forall fun z => (Q s).norm_coe_le_norm _
    · exact (show Continuous (fun z : E =>
          Qt s (gaussianOUTransition s x z) +
            DQ s (gaussianOUTransition s x z)
              (gaussianOUTransitionTimeDeriv s x z)) by
        unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
        fun_prop).aestronglyMeasurable
  simpa [gaussianOUSemigroup] using hresult

/-- A bounded covector field evaluated on the positive-time Mehler velocity
is Gaussian-integrable.  The velocity has only affine growth in the
innovation, so the first Gaussian moment is sufficient. -/
theorem integrable_boundedCovector_gaussianOUTransitionTimeDeriv
    {t : ℝ} (ht : 0 < t)
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    Integrable (fun z => D (gaussianOUTransition t x z)
      (gaussianOUTransitionTimeDeriv t x z)) (stdGaussian E) := by
  let a : ℝ := ouDriftCoeff t
  let k : ℝ := ouDriftCoeff t ^ 2 / ouNoiseCoeff t
  let bound : E → ℝ := fun z =>
    ‖D‖ * (|a| * ‖x‖ + |k| * ‖z‖)
  have hboundInt : Integrable bound (stdGaussian E) := by
    have hnorm : Integrable (fun z : E => ‖z‖) (stdGaussian E) :=
      IsGaussian.integrable_id.norm
    exact ((integrable_const (|a| * ‖x‖)).add
      (hnorm.const_mul |k|)).const_mul ‖D‖
  apply hboundInt.mono'
  · exact (show Continuous (fun z : E =>
        D (gaussianOUTransition t x z)
          (gaussianOUTransitionTimeDeriv t x z)) by
      unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      have hvel : ‖gaussianOUTransitionTimeDeriv t x z‖ ≤
          |a| * ‖x‖ + |k| * ‖z‖ := by
        unfold gaussianOUTransitionTimeDeriv
        calc
          ‖(-ouDriftCoeff t) • x +
              (ouDriftCoeff t ^ 2 / ouNoiseCoeff t) • z‖ ≤
              ‖(-ouDriftCoeff t) • x‖ +
                ‖(ouDriftCoeff t ^ 2 / ouNoiseCoeff t) • z‖ :=
            norm_add_le _ _
          _ = |a| * ‖x‖ + |k| * ‖z‖ := by
            simp only [norm_smul, Real.norm_eq_abs, abs_neg, a, k]
      calc
        ‖D (gaussianOUTransition t x z)
            (gaussianOUTransitionTimeDeriv t x z)‖ ≤
            ‖D (gaussianOUTransition t x z)‖ *
              ‖gaussianOUTransitionTimeDeriv t x z‖ :=
          (D (gaussianOUTransition t x z)).le_opNorm _
        _ ≤ ‖D‖ * ‖gaussianOUTransitionTimeDeriv t x z‖ :=
          mul_le_mul_of_nonneg_right (D.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖D‖ * (|a| * ‖x‖ + |k| * ‖z‖) :=
          mul_le_mul_of_nonneg_left hvel (norm_nonneg D)
        _ = bound z := rfl

/-- Time-dependent Mehler differentiation with a possibly unbounded time
derivative field.  Only its value along the Mehler transition at the
differentiation time is required to be integrable.  This is the natural
interface for backward OU fields, whose time derivatives contain a linear
drift term. -/
theorem hasDerivAt_gaussianOUSemigroup_timeDependent_direct_integrable
    {s : ℝ} (hs : 0 < s)
    (Q : ℝ → BoundedContinuousFunction E ℝ)
    (Qt : ℝ → E → ℝ)
    (DQ : ℝ → BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (x : E) (U : Set ℝ) (hU : U ∈ nhds s)
    (bound : E → ℝ) (hboundInt : Integrable bound (stdGaussian E))
    (hQtInt : Integrable
      (fun z => Qt s (gaussianOUTransition s x z)) (stdGaussian E))
    (hbound : ∀ᵐ z ∂stdGaussian E, ∀ r ∈ U,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound z)
    (hjoint : ∀ᵐ z ∂stdGaussian E, ∀ r ∈ U,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r) :
    HasDerivAt (fun r => gaussianOUSemigroup r (Q r) x)
      (∫ z, Qt s (gaussianOUTransition s x z) +
        DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z) ∂stdGaussian E) s := by
  have hspaceInt :=
    integrable_boundedCovector_gaussianOUTransitionTimeDeriv hs (DQ s) x
  have hderivMeas : AEStronglyMeasurable (fun z =>
      Qt s (gaussianOUTransition s x z) +
        DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z)) (stdGaussian E) :=
    hQtInt.aestronglyMeasurable.add hspaceInt.aestronglyMeasurable
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E)
    (F := fun r z => Q r (gaussianOUTransition r x z))
    (F' := fun r z => Qt r (gaussianOUTransition r x z) +
      DQ r (gaussianOUTransition r x z)
        (gaussianOUTransitionTimeDeriv r x z))
    (bound := bound) hU
  have hresult : HasDerivAt
      (fun r => ∫ z, Q r (gaussianOUTransition r x z) ∂stdGaussian E)
      (∫ z, Qt s (gaussianOUTransition s x z) +
        DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z) ∂stdGaussian E) s := by
    apply (hmain ?_ ?_ hderivMeas hbound hboundInt hjoint).2
    · exact Filter.Eventually.of_forall fun r =>
        ((Q r).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        ((Q s).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖Q s‖ ?_
      exact Filter.Eventually.of_forall fun z => (Q s).norm_coe_le_norm _
  simpa [gaussianOUSemigroup] using hresult

end TimeDerivative

/-- The coordinate OU generator written with named first and diagonal second
derivatives.  This is the form directly produced by Gaussian integration by
parts. -/
def gaussianOUGeneratorCoordinates
    {n : ℕ}
    (q1 q2 : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, (q2 i y - y i * q1 i y)

/-- Integrability of a coordinate OU generator along a Mehler transition
when all named derivatives are bounded continuous. -/
theorem integrable_gaussianOUGeneratorCoordinates_transition
    {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (q1 q2 : Fin (n + 1) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ) :
    Integrable (fun z => gaussianOUGeneratorCoordinates
      (fun i y => q1 i y) (fun i y => q2 i y)
      (gaussianOUTransition t x z))
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  have hq1int (i : Fin (n + 1)) : Integrable
      (fun z : G => q1 i (gaussianOUTransition t x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      ((q1 i).continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q1 i‖ ?_
    exact Filter.Eventually.of_forall fun z => (q1 i).norm_coe_le_norm _
  have hq2int (i : Fin (n + 1)) : Integrable
      (fun z : G => q2 i (gaussianOUTransition t x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      ((q2 i).continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q2 i‖ ?_
    exact Filter.Eventually.of_forall fun z => (q2 i).norm_coe_le_norm _
  have hzq1int (i : Fin (n + 1)) : Integrable
      (fun z : G => z i * q1 i (gaussianOUTransition t x z))
      (stdGaussian G) := by
    have hnorm : Integrable (fun z : G => ‖z‖) (stdGaussian G) :=
      IsGaussian.integrable_id.norm
    refine (hnorm.const_mul ‖q1 i‖).mono'
      ((EuclideanSpace.proj i).continuous.mul
        ((q1 i).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop))).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |z i| * |q1 i (gaussianOUTransition t x z)| ≤
            ‖z‖ * ‖q1 i‖ := by
          gcongr
          · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
          · simpa [Real.norm_eq_abs] using (q1 i).norm_coe_le_norm
              (gaussianOUTransition t x z)
        _ = ‖q1 i‖ * ‖z‖ := mul_comm _ _
  unfold gaussianOUGeneratorCoordinates
  apply integrable_finset_sum
  intro i _
  apply (hq2int i).sub
  have hlin := ((hq1int i).const_mul (ouDriftCoeff t * x i)).add
    ((hzq1int i).const_mul (ouNoiseCoeff t))
  apply hlin.congr
  exact Filter.Eventually.of_forall fun z => by
    simp only [Pi.add_apply, gaussianOUTransition, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring

section GeneratorIdentification

/-- At positive time, the derivative of the Mehler semigroup is the Gaussian
OU generator.  First derivatives are represented by the bounded covector
`Dq`; `q1` names its coordinates, and `q2` names the diagonal coordinate
derivatives of `q1`.  The latter hypothesis is an ordinary `HasDerivAt`
statement on coordinate lines, not an assumed generator identity. -/
theorem hasDerivAt_gaussianOUSemigroup_time_generatorCoordinates
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (q : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Dq : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (q1 q2 : Fin (n + 1) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (hDq : ∀ y, HasFDerivAt q (Dq y) y)
    (hDcoord : ∀ y v, Dq y v = ∑ i, q1 i y * v i)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (hq12 : ∀ (i : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 i (gaussianOUTransition t
          x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff t * q2 i (gaussianOUTransition t x
          (WithLp.toLp 2 (i.insertNth r w)))) r) :
    HasDerivAt (fun r => gaussianOUSemigroup r q x)
      (∫ z, gaussianOUGeneratorCoordinates
        (fun i y => q1 i y) (fun i y => q2 i y)
        (gaussianOUTransition t x z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) t := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  let a : ℝ := ouDriftCoeff t
  let b : ℝ := ouNoiseCoeff t
  have hb : 0 < b := by
    dsimp only [b, ouNoiseCoeff]
    exact Real.sqrt_pos.2 (by
      change 0 < bobkovVarianceCoeff t
      exact bobkovVarianceCoeff_pos ht)
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simpa [a, b] using ouDriftCoeff_sq_add_ouNoiseCoeff_sq ht.le
  have htime := hasDerivAt_gaussianOUSemigroup_time_direct ht q Dq hDq x
  have hq1int (i : Fin (n + 1)) : Integrable
      (fun z : G => q1 i (gaussianOUTransition t x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      ((q1 i).continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q1 i‖ ?_
    exact Filter.Eventually.of_forall fun z => (q1 i).norm_coe_le_norm _
  have hq2int (i : Fin (n + 1)) : Integrable
      (fun z : G => q2 i (gaussianOUTransition t x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      ((q2 i).continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q2 i‖ ?_
    exact Filter.Eventually.of_forall fun z => (q2 i).norm_coe_le_norm _
  have hzq1int (i : Fin (n + 1)) : Integrable
      (fun z : G => z i * q1 i (gaussianOUTransition t x z))
      (stdGaussian G) := by
    have hnorm : Integrable (fun z : G => ‖z‖) (stdGaussian G) :=
      IsGaussian.integrable_id.norm
    refine (hnorm.const_mul ‖q1 i‖).mono'
      ((EuclideanSpace.proj i).continuous.mul
        ((q1 i).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop))).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |z i| * |q1 i (gaussianOUTransition t x z)| ≤
            ‖z‖ * ‖q1 i‖ := by
          gcongr
          · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
          · simpa [Real.norm_eq_abs] using (q1 i).norm_coe_le_norm
              (gaussianOUTransition t x z)
        _ = ‖q1 i‖ * ‖z‖ := mul_comm _ _
  have hibp (i : Fin (n + 1)) :
      ∫ z : G, z i * q1 i (gaussianOUTransition t x z) ∂stdGaussian G =
        b * ∫ z : G, q2 i (gaussianOUTransition t x z) ∂stdGaussian G := by
    have hraw := integral_partial_stdGaussian_eq_integral_mul i
      (g := fun z : G => q1 i (gaussianOUTransition t x z))
      (gi := fun z : G => b * q2 i (gaussianOUTransition t x z))
      (by
        intro w r
        have h := hq12 i w r
        simpa [G, b, gaussianOUTransition, add_comm, add_left_comm,
          add_assoc] using h)
      ((hq2int i).const_mul b) (hzq1int i) (hq1int i)
    rw [integral_const_mul] at hraw
    exact hraw.symm
  have hdirectPoint (z : G) :
      Dq (gaussianOUTransition t x z)
          (gaussianOUTransitionTimeDeriv t x z) =
        ∑ i, ((-a * x i) * q1 i (gaussianOUTransition t x z) +
          (a ^ 2 / b) *
            (z i * q1 i (gaussianOUTransition t x z))) := by
    rw [hDcoord]
    apply Finset.sum_congr rfl
    intro i _
    simp only [gaussianOUTransitionTimeDeriv, a, b, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  have hgeneratorPoint (z : G) :
      gaussianOUGeneratorCoordinates
          (fun i y => q1 i y) (fun i y => q2 i y)
          (gaussianOUTransition t x z) =
        ∑ i, (q2 i (gaussianOUTransition t x z) -
          ((a * x i) * q1 i (gaussianOUTransition t x z) +
            b * (z i * q1 i (gaussianOUTransition t x z)))) := by
    unfold gaussianOUGeneratorCoordinates gaussianOUTransition
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, a, b]
    ring
  have hcoord (i : Fin (n + 1)) :
      ∫ z : G, ((-a * x i) * q1 i (gaussianOUTransition t x z) +
          (a ^ 2 / b) * (z i * q1 i (gaussianOUTransition t x z)))
          ∂stdGaussian G =
        ∫ z : G, (q2 i (gaussianOUTransition t x z) -
          ((a * x i) * q1 i (gaussianOUTransition t x z) +
            b * (z i * q1 i (gaussianOUTransition t x z))))
          ∂stdGaussian G := by
    rw [integral_add
        ((hq1int i).const_mul (-a * x i))
        ((hzq1int i).const_mul (a ^ 2 / b)),
      integral_const_mul, integral_const_mul]
    have hright :
        (∫ z : G, (q2 i (gaussianOUTransition t x z) -
          ((a * x i) * q1 i (gaussianOUTransition t x z) +
            b * (z i * q1 i (gaussianOUTransition t x z))))
          ∂stdGaussian G) =
        (∫ z : G, q2 i (gaussianOUTransition t x z) ∂stdGaussian G) -
          ((a * x i) *
              ∫ z : G, q1 i (gaussianOUTransition t x z) ∂stdGaussian G) -
          b * ∫ z : G, z i * q1 i (gaussianOUTransition t x z)
            ∂stdGaussian G := by
      calc
        _ = (∫ z : G, q2 i (gaussianOUTransition t x z)
              ∂stdGaussian G) -
            ∫ z : G, ((a * x i) * q1 i (gaussianOUTransition t x z) +
              b * (z i * q1 i (gaussianOUTransition t x z)))
              ∂stdGaussian G := by
          exact integral_sub (hq2int i)
            (((hq1int i).const_mul (a * x i)).add
              ((hzq1int i).const_mul b))
        _ = _ := by
          rw [integral_add
            ((hq1int i).const_mul (a * x i))
            ((hzq1int i).const_mul b),
            integral_const_mul, integral_const_mul]
          ring
    rw [hright, hibp i]
    have hcancel (R : ℝ) : (a ^ 2 / b) * (b * R) = a ^ 2 * R := by
      field_simp
    rw [hcancel]
    have hsq : a ^ 2 = 1 - b ^ 2 := by linarith [hab]
    rw [hsq]
    ring
  have hintegral :
      (∫ z : G, Dq (gaussianOUTransition t x z)
          (gaussianOUTransitionTimeDeriv t x z) ∂stdGaussian G) =
        ∫ z : G, gaussianOUGeneratorCoordinates
          (fun i y => q1 i y) (fun i y => q2 i y)
          (gaussianOUTransition t x z) ∂stdGaussian G := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hdirectPoint),
      integral_congr_ae (Filter.Eventually.of_forall hgeneratorPoint)]
    rw [integral_finset_sum]
    · rw [integral_finset_sum]
      · exact Finset.sum_congr rfl fun i _ => hcoord i
      · intro i _
        exact (hq2int i).sub (((hq1int i).const_mul (a * x i)).add
          ((hzq1int i).const_mul b))
    · intro i _
      exact ((hq1int i).const_mul (-a * x i)).add
        ((hzq1int i).const_mul (a ^ 2 / b))
  exact htime.congr_deriv hintegral

/-- Time-dependent Mehler evolution in generator form.  This combines the
direct parametric-integral derivative with the fixed-function generator
identity; uniqueness of derivatives identifies the spatial term. -/
theorem hasDerivAt_gaussianOUSemigroup_timeDependent_generatorCoordinates
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Q : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Qt : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (DQ : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (q1 q2 : Fin (n + 1) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (hDQ : ∀ y, HasFDerivAt (Q s) (DQ s y) y)
    (hDcoord : ∀ y v, DQ s y v = ∑ i, q1 i y * v i)
    (hq12 : ∀ (i : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff s * q2 i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w)))) r)
    (U : Set ℝ) (hU : U ∈ nhds s)
    (bound : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hboundInt : Integrable bound
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbound : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound z)
    (hjoint : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r) :
    HasDerivAt (fun r => gaussianOUSemigroup r (Q r) x)
      (∫ z, Qt s (gaussianOUTransition s x z) +
        gaussianOUGeneratorCoordinates
          (fun i y => q1 i y) (fun i y => q2 i y)
          (gaussianOUTransition s x z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) s := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  have htd := hasDerivAt_gaussianOUSemigroup_timeDependent_direct
    hs Q Qt DQ x U hU bound hboundInt hbound hjoint
  have hfixedDirect := hasDerivAt_gaussianOUSemigroup_time_direct
    hs (Q s) (DQ s) hDQ x
  have hfixedGenerator :=
    hasDerivAt_gaussianOUSemigroup_time_generatorCoordinates
      hs (Q s) (DQ s) q1 q2 hDQ hDcoord x hq12
  have hspatial :
      (∫ z : G, DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z) ∂stdGaussian G) =
        ∫ z : G, gaussianOUGeneratorCoordinates
          (fun i y => q1 i y) (fun i y => q2 i y)
          (gaussianOUTransition s x z) ∂stdGaussian G :=
    hfixedDirect.unique hfixedGenerator
  have hsU : s ∈ U := mem_of_mem_nhds hU
  have hsumInt : Integrable (fun z : G =>
      Qt s (gaussianOUTransition s x z) +
        DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z)) (stdGaussian G) := by
    apply hboundInt.mono'
    · exact (show Continuous (fun z : G =>
          Qt s (gaussianOUTransition s x z) +
            DQ s (gaussianOUTransition s x z)
              (gaussianOUTransitionTimeDeriv s x z)) by
        unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
        fun_prop).aestronglyMeasurable
    · exact hbound.mono fun z hz => hz s hsU
  have hqtInt : Integrable (fun z : G =>
      Qt s (gaussianOUTransition s x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      ((Qt s).continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Qt s‖ ?_
    exact Filter.Eventually.of_forall fun z => (Qt s).norm_coe_le_norm _
  have hspaceInt : Integrable (fun z : G =>
      DQ s (gaussianOUTransition s x z)
        (gaussianOUTransitionTimeDeriv s x z)) (stdGaussian G) := by
    have hsub := hsumInt.sub hqtInt
    apply hsub.congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]
      ring
  have hgenInt : Integrable (fun z : G =>
      gaussianOUGeneratorCoordinates
        (fun i y => q1 i y) (fun i y => q2 i y)
        (gaussianOUTransition s x z)) (stdGaussian G) :=
    integrable_gaussianOUGeneratorCoordinates_transition s x q1 q2
  apply htd.congr_deriv
  rw [integral_add hqtInt hspaceInt, integral_add hqtInt hgenInt, hspatial]

/-- Generator-form evolution for a time-dependent Mehler family whose time
derivative need only be integrable, rather than bounded.  This removes the
artificial boundedness obstruction in the canonical Bobkov interpolation. -/
theorem hasDerivAt_gaussianOUSemigroup_timeDependent_generatorCoordinates_integrable
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (Q : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Qt : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (DQ : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (q1 q2 : Fin (n + 1) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (hDQ : ∀ y, HasFDerivAt (Q s) (DQ s y) y)
    (hDcoord : ∀ y v, DQ s y v = ∑ i, q1 i y * v i)
    (hq12 : ∀ (i : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff s * q2 i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w)))) r)
    (U : Set ℝ) (hU : U ∈ nhds s)
    (bound : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hboundInt : Integrable bound
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hQtInt : Integrable
      (fun z => Qt s (gaussianOUTransition s x z))
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbound : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound z)
    (hjoint : ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r) :
    HasDerivAt (fun r => gaussianOUSemigroup r (Q r) x)
      (∫ z, Qt s (gaussianOUTransition s x z) +
        gaussianOUGeneratorCoordinates
          (fun i y => q1 i y) (fun i y => q2 i y)
          (gaussianOUTransition s x z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) s := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  have htd :=
    hasDerivAt_gaussianOUSemigroup_timeDependent_direct_integrable
      hs Q Qt DQ x U hU bound hboundInt hQtInt hbound hjoint
  have hfixedDirect := hasDerivAt_gaussianOUSemigroup_time_direct
    hs (Q s) (DQ s) hDQ x
  have hfixedGenerator :=
    hasDerivAt_gaussianOUSemigroup_time_generatorCoordinates
      hs (Q s) (DQ s) q1 q2 hDQ hDcoord x hq12
  have hspatial :
      (∫ z : G, DQ s (gaussianOUTransition s x z)
          (gaussianOUTransitionTimeDeriv s x z) ∂stdGaussian G) =
        ∫ z : G, gaussianOUGeneratorCoordinates
          (fun i y => q1 i y) (fun i y => q2 i y)
          (gaussianOUTransition s x z) ∂stdGaussian G :=
    hfixedDirect.unique hfixedGenerator
  have hspaceInt :=
    integrable_boundedCovector_gaussianOUTransitionTimeDeriv hs (DQ s) x
  have hgenInt : Integrable (fun z : G =>
      gaussianOUGeneratorCoordinates
        (fun i y => q1 i y) (fun i y => q2 i y)
        (gaussianOUTransition s x z)) (stdGaussian G) :=
    integrable_gaussianOUGeneratorCoordinates_transition s x q1 q2
  apply htd.congr_deriv
  rw [integral_add hQtInt hspaceInt, integral_add hQtInt hgenInt, hspatial]

end GeneratorIdentification

section BobkovInterpolationClosure

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
  [SecondCountableTopology X]

/-- The smooth functional Bobkov inequality in the form produced by G3--G4.
The separate bounded continuous derivative is the datum required by the
Mehler interpolation module; `hDf` identifies it with the Fréchet derivative
appearing in the geometric inequality. -/
def GaussianBobkovSmooth : Prop :=
  ∀ (f : BoundedContinuousFunction X ℝ)
    (Df : BoundedContinuousFunction X (X →L[ℝ] ℝ)),
    (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
    ContDiff ℝ (⊤ : ℕ∞) (⇑f) →
    (∀ x, fderiv ℝ (⇑f) x = Df x) →
    normalProfileClosed (∫ x, f x ∂stdGaussian X) ≤
      ∫ x, Real.sqrt
        (normalProfileClosed (f x) ^ 2 + ‖Df x‖ ^ 2) ∂stdGaussian X

/-- A smooth OU interpolation certificate for the local Bobkov inequality.
Unlike the former `hlocal` premise, its analytic field is the differentiated
Mehler evolution equation; the sign is a pointwise residual statement. -/
structure GaussianBobkovSmoothInterpolation
    (f q : BoundedContinuousFunction X ℝ)
    (Df : BoundedContinuousFunction X (X →L[ℝ] ℝ))
    (t : ℝ) (x : X) where
  Q : ℝ → BoundedContinuousFunction X ℝ
  residual : ℝ → BoundedContinuousFunction X ℝ
  continuous_flow : ContinuousOn
    (fun s => gaussianOUSemigroup s (Q s) x) (Set.Icc 0 t)
  hasDerivAt_flow : ∀ s ∈ Set.Ioo 0 t,
    HasDerivAt (fun r => gaussianOUSemigroup r (Q r) x)
      (gaussianOUSemigroup s (residual s) x) s
  residual_nonneg : ∀ s ∈ Set.Ioo 0 t, ∀ y, 0 ≤ residual s y
  initial : Q 0 x = normalProfile (gaussianOUSemigroup t f x)
  terminal : ∀ y, Q t y = Real.sqrt
    (q y ^ 2 + bobkovVarianceCoeff t * ‖Df y‖ ^ 2)

/-- Build a smooth interpolation certificate from the differentiated Mehler
flow and the explicit G3 coordinate representation of its residual.  The
pointwise sign is discharged by `bobkovSqrtResidual_nonneg`. -/
def GaussianBobkovSmoothInterpolation.ofPointwiseG3
    {n : ℕ}
    {f q : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ}
    {Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {t : ℝ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (Q residual : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (hcontinuous : ContinuousOn
      (fun s => gaussianOUSemigroup s (Q s) x) (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ioo 0 t,
      HasDerivAt (fun r => gaussianOUSemigroup r (Q r) x)
        (gaussianOUSemigroup s (residual s) x) s)
    (hG3 : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      ∃ (I Ip : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1)))
        (H : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))),
        0 < I ∧ residual s y =
          bobkovSqrtResidual (bobkovVarianceCoeff s) I Ip v H)
    (hinitial : Q 0 x = normalProfile (gaussianOUSemigroup t f x))
    (hterminal : ∀ y, Q t y = Real.sqrt
      (q y ^ 2 + bobkovVarianceCoeff t * ‖Df y‖ ^ 2)) :
    GaussianBobkovSmoothInterpolation f q Df t x where
  Q := Q
  residual := residual
  continuous_flow := hcontinuous
  hasDerivAt_flow := hderiv
  residual_nonneg := by
    intro s hs y
    obtain ⟨I, Ip, v, H, hI, hr⟩ := hG3 s hs y
    rw [hr]
    exact bobkovSqrtResidual_nonneg
      (bobkovVarianceCoeff_nonneg hs.1.le) hI Ip v H
  initial := hinitial
  terminal := hterminal

/-- Construct the Bobkov interpolation certificate from ordinary smooth
time/space derivative data.  The differentiated flow is obtained from the
time-dependent Mehler generator theorem above, so it is not a premise of
this constructor. -/
def GaussianBobkovSmoothInterpolation.ofSmoothGeneratorFamily
    {n : ℕ}
    {f q : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ}
    {Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {t : ℝ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (Q Qt residual : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (DQ : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (q1 q2 : ℝ → Fin (n + 1) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (U : ℝ → Set ℝ)
    (bound : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hcontinuous : ContinuousOn
      (fun s => gaussianOUSemigroup s (Q s) x) (Set.Icc 0 t))
    (hDQ : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      HasFDerivAt (Q s) (DQ s y) y)
    (hDcoord : ∀ s ∈ Set.Ioo 0 t, ∀ y v,
      DQ s y v = ∑ i, q1 s i y * v i)
    (hq12 : ∀ s ∈ Set.Ioo 0 t, ∀ (i : Fin (n + 1))
      (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 s i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff s * q2 s i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w)))) r)
    (hU : ∀ s ∈ Set.Ioo 0 t, U s ∈ nhds s)
    (hboundInt : ∀ s ∈ Set.Ioo 0 t,
      Integrable (bound s)
        (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbound : ∀ s ∈ Set.Ioo 0 t,
      ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U s,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound s z)
    (hjoint : ∀ s ∈ Set.Ioo 0 t,
      ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U s,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r)
    (hresidual : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      residual s y = Qt s y + gaussianOUGeneratorCoordinates
        (fun i z => q1 s i z) (fun i z => q2 s i z) y)
    (hG3 : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      ∃ (I Ip : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1)))
        (H : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))),
        0 < I ∧ residual s y =
          bobkovSqrtResidual (bobkovVarianceCoeff s) I Ip v H)
    (hinitial : Q 0 x = normalProfile (gaussianOUSemigroup t f x))
    (hterminal : ∀ y, Q t y = Real.sqrt
      (q y ^ 2 + bobkovVarianceCoeff t * ‖Df y‖ ^ 2)) :
    GaussianBobkovSmoothInterpolation f q Df t x := by
  apply GaussianBobkovSmoothInterpolation.ofPointwiseG3
    Q residual hcontinuous ?_ hG3 hinitial hterminal
  intro s hs
  have hevol :=
    hasDerivAt_gaussianOUSemigroup_timeDependent_generatorCoordinates
      hs.1 Q Qt DQ (q1 s) (q2 s) x
      (hDQ s hs) (hDcoord s hs) (hq12 s hs)
      (U s) (hU s hs) (bound s) (hboundInt s hs)
      (hbound s hs) (hjoint s hs)
  apply hevol.congr_deriv
  unfold gaussianOUSemigroup
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => (hresidual s hs _).symm

/-- The canonical-friendly version of `ofSmoothGeneratorFamily`: the time
derivative `Qt` may grow in space, provided it is integrable along the Mehler
transition and the full path derivative has the stated local dominator. -/
def GaussianBobkovSmoothInterpolation.ofSmoothGeneratorFamilyIntegrable
    {n : ℕ}
    {f q : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ}
    {Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {t : ℝ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (Q residual : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Qt : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (DQ : ℝ → BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (q1 q2 : ℝ → Fin (n + 1) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (U : ℝ → Set ℝ)
    (bound : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hcontinuous : ContinuousOn
      (fun s => gaussianOUSemigroup s (Q s) x) (Set.Icc 0 t))
    (hDQ : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      HasFDerivAt (Q s) (DQ s y) y)
    (hDcoord : ∀ s ∈ Set.Ioo 0 t, ∀ y v,
      DQ s y v = ∑ i, q1 s i y * v i)
    (hq12 : ∀ s ∈ Set.Ioo 0 t, ∀ (i : Fin (n + 1))
      (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 s i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff s * q2 s i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w)))) r)
    (hU : ∀ s ∈ Set.Ioo 0 t, U s ∈ nhds s)
    (hboundInt : ∀ s ∈ Set.Ioo 0 t,
      Integrable (bound s)
        (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hQtInt : ∀ s ∈ Set.Ioo 0 t,
      Integrable (fun z => Qt s (gaussianOUTransition s x z))
        (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbound : ∀ s ∈ Set.Ioo 0 t,
      ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U s,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound s z)
    (hjoint : ∀ s ∈ Set.Ioo 0 t,
      ∀ᵐ z ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))),
      ∀ r ∈ U s,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r)
    (hresidual : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      residual s y = Qt s y + gaussianOUGeneratorCoordinates
        (fun i z => q1 s i z) (fun i z => q2 s i z) y)
    (hG3 : ∀ s ∈ Set.Ioo 0 t, ∀ y,
      ∃ (I Ip : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1)))
        (H : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))),
        0 < I ∧ residual s y =
          bobkovSqrtResidual (bobkovVarianceCoeff s) I Ip v H)
    (hinitial : Q 0 x = normalProfile (gaussianOUSemigroup t f x))
    (hterminal : ∀ y, Q t y = Real.sqrt
      (q y ^ 2 + bobkovVarianceCoeff t * ‖Df y‖ ^ 2)) :
    GaussianBobkovSmoothInterpolation f q Df t x := by
  apply GaussianBobkovSmoothInterpolation.ofPointwiseG3
    Q residual hcontinuous ?_ hG3 hinitial hterminal
  intro s hs
  have hevol :=
    hasDerivAt_gaussianOUSemigroup_timeDependent_generatorCoordinates_integrable
      hs.1 Q Qt DQ (q1 s) (q2 s) x
      (hDQ s hs) (hDcoord s hs) (hq12 s hs)
      (U s) (hU s hs) (bound s) (hboundInt s hs)
      (hQtInt s hs) (hbound s hs) (hjoint s hs)
  apply hevol.congr_deriv
  unfold gaussianOUSemigroup
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => (hresidual s hs _).symm

/-- G3 local Bobkov inequality obtained from a smooth interpolation
certificate.  Monotonicity is proved here from the nonnegative residual. -/
theorem gaussianBobkov_local_of_smoothInterpolation
    {f q : BoundedContinuousFunction X ℝ}
    {Df : BoundedContinuousFunction X (X →L[ℝ] ℝ)}
    {t : ℝ} (ht : 0 ≤ t) {x : X}
    (h : GaussianBobkovSmoothInterpolation f q Df t x) :
    normalProfile (gaussianOUSemigroup t f x) ≤
      gaussianBobkovOUIntegral t q Df x := by
  let F : ℝ → ℝ := fun s => gaussianOUSemigroup s (h.Q s) x
  have hF : F 0 ≤ F t := by
    apply bobkov_interpolation_endpoint_le ht h.continuous_flow
    · intro s hs
      exact h.hasDerivAt_flow s hs
    · intro s hs
      unfold gaussianOUSemigroup
      exact integral_nonneg fun z => h.residual_nonneg s hs _
  have hzero : F 0 = normalProfile (gaussianOUSemigroup t f x) := by
    simp [F, h.initial]
  have htfinal : F t = gaussianBobkovOUIntegral t q Df x := by
    unfold F gaussianOUSemigroup gaussianBobkovOUIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => h.terminal _
  rwa [hzero, htfinal] at hF

/-- G4 with the local-inequality premise replaced by smooth OU
interpolation certificates for the affine endpoint truncations. -/
theorem gaussianBobkov_functionalClosed_of_smoothInterpolations
    (f : BoundedContinuousFunction X ℝ)
    (Df : BoundedContinuousFunction X (X →L[ℝ] ℝ))
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (x : X)
    (hflow : ∀ (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
      (t : ℝ) (ht : 0 ≤ t),
      GaussianBobkovSmoothInterpolation
        (bobkovTruncationBCF e f)
        (normalProfileCompBCF (bobkovTruncationBCF e f) e he0
          (bobkovTruncationBCF_mem_Icc e f hf he1))
        ((1 - 2 * e) • Df) t x) :
    normalProfileClosed (∫ y, f y ∂stdGaussian X) ≤
      ∫ y, Real.sqrt (normalProfileClosed (f y) ^ 2 + ‖Df y‖ ^ 2)
        ∂stdGaussian X := by
  apply gaussianBobkov_functionalClosed_of_localTruncations f Df hf x
  intro e he0 he1 t ht
  exact gaussianBobkov_local_of_smoothInterpolation ht
    (hflow e he0 he1 t ht)

/-- The remaining canonical G3 construction, stated only for smooth bounded
data.  It asks for the explicit OU interpolation certificate at the single
base point `0`; G4 makes the resulting functional inequality independent of
that point. -/
def GaussianBobkovSmoothInterpolationProperty : Prop :=
  ∀ (f : BoundedContinuousFunction X ℝ)
    (Df : BoundedContinuousFunction X (X →L[ℝ] ℝ))
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1),
    ContDiff ℝ (⊤ : ℕ∞) (⇑f) →
    (∀ y, fderiv ℝ (⇑f) y = Df y) →
    ∀ (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
      (t : ℝ) (ht : 0 ≤ t),
      Nonempty (GaussianBobkovSmoothInterpolation
        (bobkovTruncationBCF e f)
        (normalProfileCompBCF (bobkovTruncationBCF e f) e he0
          (bobkovTruncationBCF_mem_Icc e f hf he1))
        ((1 - 2 * e) • Df) t 0)

/-- G3-to-G4 closure for smooth data. -/
theorem gaussianBobkovSmooth_of_smoothInterpolations
    (hflow : GaussianBobkovSmoothInterpolationProperty (X := X)) :
    GaussianBobkovSmooth (X := X) := by
  intro f Df hf hsmooth hDf
  exact gaussianBobkov_functionalClosed_of_smoothInterpolations
    f Df hf 0 (fun e he0 he1 t ht =>
      Classical.choice (hflow f Df hf hsmooth hDf e he0 he1 t ht))

end BobkovInterpolationClosure

end Concrete

end

end UniformRandomMALA
