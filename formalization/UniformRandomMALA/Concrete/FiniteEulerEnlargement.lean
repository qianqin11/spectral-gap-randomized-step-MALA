import UniformRandomMALA.Concrete.FiniteEulerGaussianImage
import UniformRandomMALA.Concrete.GaussianRampMollification
import UniformRandomMALA.Concrete.GaussianWeakLimit

/-!
# Gaussian enlargement for finite Euler endpoints

This module performs the deterministic image step of the discrete Langevin
route.  A positive-Lipschitz image of a measure with an enlargement profile
inherits the same profile with the radius divided by the Lipschitz constant.
Applying this to the finite Euler endpoint gives the exact finite-mesh input
needed by the weak-limit module.
-/

namespace UniformRandomMALA

open MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory NNReal

noncomputable section

namespace Concrete

section LipschitzImage

variable {X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A Lipschitz image inherits an enlargement inequality with source radius
`r/C`.  This coefficient form avoids introducing a square of the Lipschitz
constant before the finite-Euler specialization. -/
theorem enlargement_map_of_lipschitzWith
    (mu : Measure X) [IsFiniteMeasure mu]
    {m : ℝ} {Phi PhiInv : ℝ → ℝ}
    (hBL : BakryLedouxEnlargement mu m Phi PhiInv)
    (F : X → Y) {C : ℝ≥0} (hF : LipschitzWith C F)
    (hC : 0 < (C : ℝ)) :
    ∀ A : Set Y, MeasurableSet A →
      0 < (Measure.map F mu).real A →
      (Measure.map F mu).real A < 1 → ∀ r : ℝ, 0 < r →
      Phi (PhiInv ((Measure.map F mu).real A) +
          Real.sqrt m * (r / (C : ℝ))) ≤
        (Measure.map F mu).real (thickening r A) := by
  intro A hA hApos hAone r hr
  have hFmeas : Measurable F := hF.continuous.measurable
  let B : Set X := F ⁻¹' A
  have hB : MeasurableSet B := hA.preimage hFmeas
  have hmass : mu.real B = (Measure.map F mu).real A := by
    simp [B, measureReal_def, Measure.map_apply hFmeas hA]
  have hrC : 0 < r / (C : ℝ) := div_pos hr hC
  have hsource := hBL B hB (by simpa [hmass] using hApos)
    (by simpa [hmass] using hAone) (r / (C : ℝ)) hrC
  have hsubset : thickening (r / (C : ℝ)) B ⊆
      F ⁻¹' thickening r A := by
    intro x hx
    obtain ⟨y, hyB, hxy⟩ := mem_thickening_iff.mp hx
    apply mem_thickening_iff.mpr
    refine ⟨F y, hyB, ?_⟩
    calc
      dist (F x) (F y) ≤ (C : ℝ) * dist x y := hF.dist_le_mul x y
      _ < (C : ℝ) * (r / (C : ℝ)) :=
        mul_lt_mul_of_pos_left hxy hC
      _ = r := by field_simp [hC.ne']
  calc
    Phi (PhiInv ((Measure.map F mu).real A) +
        Real.sqrt m * (r / (C : ℝ))) =
        Phi (PhiInv (mu.real B) +
          Real.sqrt m * (r / (C : ℝ))) := by rw [hmass]
    _ ≤ mu.real (thickening (r / (C : ℝ)) B) := hsource
    _ ≤ mu.real (F ⁻¹' thickening r A) := measureReal_mono hsubset
    _ = (Measure.map F mu).real (thickening r A) := by
      simp only [measureReal_def]
      rw [Measure.map_apply hFmeas isOpen_thickening.measurableSet]

end LipschitzImage

section EulerEndpoint

open DiscreteTime

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Probability-measure packaging of a finite Euler endpoint driven by one
finite-dimensional standard Gaussian innovation vector. -/
def finiteEulerEuclideanEndpointLaw
    (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d) :
    ProbabilityMeasure (State d) := by
  let F : EuclideanSpace ℝ (Fin n × Fin d) → State d :=
    finiteEulerEuclideanEndpoint V delta x0
  have hF : Measurable F :=
    (finiteEulerEuclideanEndpoint_lipschitzWith V delta hdelta hsmall x0).continuous.measurable
  exact ⟨Measure.map F (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))),
    Measure.isProbabilityMeasure_map hF.aemeasurable⟩

@[simp] theorem finiteEulerEuclideanEndpointLaw_toMeasure
    (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d) :
    (finiteEulerEuclideanEndpointLaw V n delta hdelta hsmall x0 :
        Measure (State d)) =
      Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) := rfl

/-- Every finite Euler endpoint inherits sharp Gaussian enlargement with its
explicit finite-mesh Lipschitz coefficient. -/
theorem finiteEulerEuclideanEndpoint_enlargement
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d)
    (hGaussian : BakryLedouxEnlargement
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ∀ A : Set (State d), MeasurableSet A →
      0 < (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A →
      (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A < 1 →
      ∀ r : ℝ, 0 < r →
      cdf standardGaussianMeasure
          (lowerQuantile standardGaussianMeasure
              ((Measure.map (finiteEulerEuclideanEndpoint V delta x0)
                (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A) +
            r / Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta))) ≤
        (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real
            (thickening r A) := by
  have hdenom : 0 < 2 * V.m - V.L ^ 2 * delta := sub_pos.mpr hsmall
  have hcoef : 0 < 2 / (2 * V.m - V.L ^ 2 * delta) :=
    div_pos (by norm_num) hdenom
  let C : ℝ≥0 := ⟨Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta)),
    Real.sqrt_nonneg _⟩
  have hC : 0 < (C : ℝ) := by
    change 0 < Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta))
    exact Real.sqrt_pos.2 hcoef
  have hLip : LipschitzWith C
      (finiteEulerEuclideanEndpoint V delta x0 :
        EuclideanSpace ℝ (Fin n × Fin d) → State d) := by
    simpa only [C] using
      finiteEulerEuclideanEndpoint_lipschitzWith V delta hdelta hsmall x0
  have hmap := enlargement_map_of_lipschitzWith
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) hGaussian
    (finiteEulerEuclideanEndpoint V delta x0)
    hLip hC
  have hCcoe : (C : ℝ) =
      Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta)) := rfl
  simpa only [Real.sqrt_one, one_mul, hCcoe] using hmap

/-- The same finite endpoint theorem with the sharp Gaussian source theorem
supplied by the canonical smooth OU interpolation property. -/
theorem finiteEulerEuclideanEndpoint_enlargement_of_smoothInterpolations
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d)
    (hflow : GaussianBobkovSmoothInterpolationProperty
      (X := EuclideanSpace ℝ (Fin n × Fin d))) :
    ∀ A : Set (State d), MeasurableSet A →
      0 < (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A →
      (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A < 1 →
      ∀ r : ℝ, 0 < r →
      cdf standardGaussianMeasure
          (lowerQuantile standardGaussianMeasure
              ((Measure.map (finiteEulerEuclideanEndpoint V delta x0)
                (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A) +
            r / Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta))) ≤
        (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real
            (thickening r A) := by
  exact finiteEulerEuclideanEndpoint_enlargement V delta hdelta hsmall x0
    (bakryLedouxEnlargement_of_smoothInterpolations hflow)

/-- End-to-end finite-mesh enlargement from the canonical-Q residual
certificate, with no ramp, perimeter, or continuity premise left exposed. -/
theorem finiteEulerEuclideanEndpoint_enlargement_of_canonicalInterpolations
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d)
    (hcanonical : CanonicalGaussianBobkovInterpolationProperty
      (E := EuclideanSpace ℝ (Fin n × Fin d))) :
    ∀ A : Set (State d), MeasurableSet A →
      0 < (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A →
      (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A < 1 →
      ∀ r : ℝ, 0 < r →
      cdf standardGaussianMeasure
          (lowerQuantile standardGaussianMeasure
              ((Measure.map (finiteEulerEuclideanEndpoint V delta x0)
                (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real A) +
            r / Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta))) ≤
        (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))).real
            (thickening r A) := by
  exact finiteEulerEuclideanEndpoint_enlargement V delta hdelta hsmall x0
    (bakryLedouxEnlargement_of_canonicalInterpolations hcanonical)

/-- A weak limit of finite Euler endpoint laws has the sharp
Bakry--Ledoux curvature `m`, provided the mesh tends to zero and every finite
Gaussian innovation source satisfies sharp enlargement. -/
theorem finiteEulerEndpointLimit_bakryLedoux
    (steps : ℕ → ℕ) (delta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < delta k)
    (hsmall : ∀ k, V.L ^ 2 * delta k < 2 * V.m)
    (hdeltaZero : Filter.Tendsto delta Filter.atTop (nhds 0))
    (x0 : State d)
    (hGaussian : ∀ k, BakryLedouxEnlargement
      (stdGaussian (EuclideanSpace ℝ (Fin (steps k) × Fin d))) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure))
    {muLimit : ProbabilityMeasure (State d)}
    (hmu : Filter.Tendsto
      (fun k => finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
        (hdelta k) (hsmall k) x0)
      Filter.atTop (nhds muLimit)) :
    BakryLedouxEnlargement (muLimit : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  let cSeq : ℕ → ℝ := fun k =>
    Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta k))
  let c : ℝ := Real.sqrt (1 / V.m)
  have hcoef : Filter.Tendsto
      (fun k => 2 / (2 * V.m - V.L ^ 2 * delta k))
      Filter.atTop (nhds (1 / V.m)) :=
    (tendsto_finiteEulerSensitivityCoefficient_zero V).comp hdeltaZero
  have hc : Filter.Tendsto cSeq Filter.atTop (nhds c) := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp hcoef
  have hcPos : 0 < c := by
    dsimp only [c]
    exact Real.sqrt_pos.2 (div_pos (by norm_num) V.hm)
  have hcSeq : ∀ k, 0 < cSeq k := by
    intro k
    dsimp only [cSeq]
    apply Real.sqrt_pos.2
    exact div_pos (by norm_num) (sub_pos.mpr (hsmall k))
  have hfinite : ∀ k (A : Set (State d)), MeasurableSet A →
      0 < (finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
        (hdelta k) (hsmall k) x0 : Measure (State d)).real A →
      (finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
        (hdelta k) (hsmall k) x0 : Measure (State d)).real A < 1 →
      ∀ r : ℝ, 0 < r →
        normalCDFReal
            (lowerQuantile standardGaussianMeasure
                ((finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
                  (hdelta k) (hsmall k) x0 : Measure (State d)).real A) +
              r / cSeq k) ≤
          (finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
            (hdelta k) (hsmall k) x0 : Measure (State d)).real
              (thickening r A) := by
    intro k A hA hA0 hA1 r hr
    rw [← cdf_standardGaussian_eq_normalCDFReal]
    simpa only [finiteEulerEuclideanEndpointLaw_toMeasure, cSeq] using
      finiteEulerEuclideanEndpoint_enlargement
        V (n := steps k) (delta k) (hdelta k) (hsmall k) x0
        (hGaussian k) A hA hA0 hA1 r hr
  have hlimit := bakryLedouxEnlargement_of_weakLimit
    (mu := fun k => finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
      (hdelta k) (hsmall k) x0)
    (muLimit := muLimit) (cSeq := cSeq) (c := c)
    hmu hc hcPos hcSeq hfinite
  have hcurvature : c ^ (-2 : ℤ) = V.m := by
    dsimp only [c]
    rw [zpow_neg, zpow_two]
    rw [show Real.sqrt (1 / V.m) * Real.sqrt (1 / V.m) =
        Real.sqrt (1 / V.m) ^ 2 by ring,
      Real.sq_sqrt (div_nonneg (by norm_num) V.hm.le)]
    field_simp [V.hm.ne']
  simpa only [hcurvature] using hlimit

/-- The weak-limit theorem with the finite Gaussian source supplied through
the earlier canonical-interpolation interface. -/
theorem finiteEulerEndpointLimit_bakryLedoux_of_canonicalInterpolations
    (steps : ℕ → ℕ) (delta : ℕ → ℝ)
    (hdelta : ∀ k, 0 < delta k)
    (hsmall : ∀ k, V.L ^ 2 * delta k < 2 * V.m)
    (hdeltaZero : Filter.Tendsto delta Filter.atTop (nhds 0))
    (x0 : State d)
    (hcanonical : ∀ k,
      CanonicalGaussianBobkovInterpolationProperty
        (E := EuclideanSpace ℝ (Fin (steps k) × Fin d)))
    {muLimit : ProbabilityMeasure (State d)}
    (hmu : Filter.Tendsto
      (fun k => finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
        (hdelta k) (hsmall k) x0)
      Filter.atTop (nhds muLimit)) :
    BakryLedouxEnlargement (muLimit : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact finiteEulerEndpointLimit_bakryLedoux V steps delta hdelta hsmall
    hdeltaZero x0
    (fun k => bakryLedouxEnlargement_of_canonicalInterpolations
      (hcanonical k)) hmu

end EulerEndpoint

end Concrete

end

end UniformRandomMALA
