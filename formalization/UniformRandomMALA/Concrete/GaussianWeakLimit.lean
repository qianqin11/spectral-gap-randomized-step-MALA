import UniformRandomMALA.Concrete.GaussianNormalProfile
import UniformRandomMALA.Concrete.WeakLimitEnlargement

/-!
# Gaussian enlargement under weak limits

This file specializes the abstract Portmanteau sandwich to the actual
Gaussian shift profile.  The finite measures only need the usual
interior-mass Bakry--Ledoux statement.  Endpoint conventions for an abstract
`ENNReal` profile are therefore avoided: compact inner approximation first
fixes a strictly smaller real mass, and continuity of the Gaussian quantile
is used only at the interior mass of the limiting set.
-/

namespace UniformRandomMALA

open Filter MeasureTheory Metric ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Concrete

/-- A fixed subcritical Gaussian mass and a fixed subcritical shift survive
weak convergence.  The output is closed so that the upper Portmanteau bound
applies. -/
theorem gaussianShift_compact_le_closedThickening_of_weakLimit
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {mu : ℕ → ProbabilityMeasure X} {muLimit : ProbabilityMeasure X}
    {cSeq : ℕ → ℝ} {c : ℝ}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hc : Tendsto cSeq atTop (nhds c))
    (hcSeq : ∀ n, 0 < cSeq n)
    (hfinite : ∀ n (A : Set X), MeasurableSet A →
      0 < (mu n : Measure X).real A →
      (mu n : Measure X).real A < 1 →
      ∀ r : ℝ, 0 < r →
        normalCDFReal
            (lowerQuantile standardGaussianMeasure
                ((mu n : Measure X).real A) + r / cSeq n) ≤
          (mu n : Measure X).real (thickening r A))
    {K : Set X} {q u s epsilon : ℝ}
    (hq0 : 0 < q) (hqK : q < (muLimit : Measure X).real K)
    (hs : 0 < s) (hus : u * c < s)
    (hepsilon : 0 < epsilon) :
    normalCDFReal
        (lowerQuantile standardGaussianMeasure q + u) ≤
      (muLimit : Measure X).real (cthickening (s + epsilon) K) := by
  let G : Set X := thickening epsilon K
  let F : Set X := cthickening (s + epsilon) K
  have hqENN : ENNReal.ofReal q < (muLimit : Measure X) G := by
    have hqK' : ENNReal.ofReal q < (muLimit : Measure X) K := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal hq0.le
        (measure_ne_top (muLimit : Measure X) K)]
      simpa only [Measure.real_def] using hqK
    exact hqK'.trans_le (measure_mono (self_subset_thickening hepsilon K))
  have hopen :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hmu
      (show IsOpen G from isOpen_thickening)
  have hqLiminf : ENNReal.ofReal q <
      atTop.liminf (fun n => (mu n : Measure X) G) :=
    hqENN.trans_le hopen
  have hmassEventually : ∀ᶠ n in atTop,
      q < (mu n : Measure X).real G := by
    filter_upwards [eventually_lt_of_lt_liminf hqLiminf] with n hn
    have hreal := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (measure_ne_top (mu n : Measure X) G)).2 hn
    simpa [Measure.real_def, ENNReal.toReal_ofReal hq0.le] using hreal
  have hscaleEventually : ∀ᶠ n in atTop, u * cSeq n < s := by
    have htendsto : Tendsto (fun n => u * cSeq n) atTop (nhds (u * c)) :=
      tendsto_const_nhds.mul hc
    exact (tendsto_order.1 htendsto).2 s hus
  have hbound : ∀ᶠ n in atTop,
      ENNReal.ofReal
          (normalCDFReal
            (lowerQuantile standardGaussianMeasure q + u)) ≤
        (mu n : Measure X) F := by
    filter_upwards [hmassEventually, hscaleEventually] with n hqmass husn
    have hqmass0 : 0 < (mu n : Measure X).real G := hq0.trans hqmass
    by_cases hmass1 : (mu n : Measure X).real G < 1
    · have huc : u ≤ s / cSeq n := by
        rw [le_div_iff₀ (hcSeq n)]
        exact husn.le
      have hreal :
          normalCDFReal
              (lowerQuantile standardGaussianMeasure q + u) ≤
            (mu n : Measure X).real F := by
        calc
          normalCDFReal
              (lowerQuantile standardGaussianMeasure q + u) ≤
              normalCDFReal
                (lowerQuantile standardGaussianMeasure
                    ((mu n : Measure X).real G) + u) := by
            apply strictMono_normalCDFReal.monotone
            gcongr
            exact lowerQuantile_mono standardGaussianMeasure hqmass.le
              hmass1 hq0
          _ ≤ normalCDFReal
                (lowerQuantile standardGaussianMeasure
                    ((mu n : Measure X).real G) + s / cSeq n) := by
            apply strictMono_normalCDFReal.monotone
            gcongr
          _ ≤ (mu n : Measure X).real (thickening s G) :=
            hfinite n G isOpen_thickening.measurableSet hqmass0 hmass1 s hs
          _ ≤ (mu n : Measure X).real F := by
            apply measureReal_mono
            exact (thickening_thickening_subset s epsilon K).trans
              (by simpa only [add_comm] using
                thickening_subset_cthickening (s + epsilon) K)
            exact measure_ne_top (mu n : Measure X) F
      have hofReal := ENNReal.ofReal_le_ofReal hreal
      simpa [F, Measure.real_def,
        ENNReal.ofReal_toReal (measure_ne_top (mu n : Measure X) F)] using
        hofReal
    · have hmassEq : (mu n : Measure X).real G = 1 :=
        le_antisymm measureReal_le_one (le_of_not_gt hmass1)
      have hGF : G ⊆ F := by
        exact (self_subset_thickening hs G).trans
          ((thickening_thickening_subset s epsilon K).trans
            (by simpa only [add_comm] using
              thickening_subset_cthickening (s + epsilon) K))
      have hFone : (mu n : Measure X).real F = 1 := by
        exact le_antisymm measureReal_le_one
          (hmassEq ▸ measureReal_mono hGF
            (measure_ne_top (mu n : Measure X) F))
      have hreal : normalCDFReal
          (lowerQuantile standardGaussianMeasure q + u) ≤
          (mu n : Measure X).real F := by
        rw [hFone]
        exact (normalCDFReal_lt_one _).le
      have hofReal := ENNReal.ofReal_le_ofReal hreal
      simpa [F, Measure.real_def,
        ENNReal.ofReal_toReal (measure_ne_top (mu n : Measure X) F)] using
        hofReal
  have htransfer :
      ENNReal.ofReal
          (normalCDFReal
            (lowerQuantile standardGaussianMeasure q + u)) ≤
        (muLimit : Measure X) F := by
    simpa using profile_measure_open_le_closed_of_tendsto hmu
      (show IsOpen G from isOpen_thickening)
      (show IsClosed F from isClosed_cthickening)
      (fun _ : ℝ≥0∞ => ENNReal.ofReal
        (normalCDFReal
          (lowerQuantile standardGaussianMeasure q + u)))
      monotone_const continuous_const hbound
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (measure_ne_top (muLimit : Measure X) F)).2 htransfer
  simpa [F, Measure.real_def,
    ENNReal.toReal_ofReal (normalCDFReal_pos _).le] using hreal

/-- Gaussian enlargement with positive varying scale constants is stable
under weak convergence.  Unlike the abstract profile theorem, this theorem
assumes only the standard interior-mass Bakry--Ledoux inequality for each
approximating measure and returns that same interior-mass statement for the
limit. -/
theorem bakryLedouxEnlargement_of_weakLimit
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {mu : ℕ → ProbabilityMeasure X} {muLimit : ProbabilityMeasure X}
    [Measure.Regular (muLimit : Measure X)]
    {cSeq : ℕ → ℝ} {c : ℝ}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hc : Tendsto cSeq atTop (nhds c)) (hcPos : 0 < c)
    (hcSeq : ∀ n, 0 < cSeq n)
    (hfinite : ∀ n (A : Set X), MeasurableSet A →
      0 < (mu n : Measure X).real A →
      (mu n : Measure X).real A < 1 →
      ∀ r : ℝ, 0 < r →
        normalCDFReal
            (lowerQuantile standardGaussianMeasure
                ((mu n : Measure X).real A) + r / cSeq n) ≤
          (mu n : Measure X).real (thickening r A)) :
    BakryLedouxEnlargement (muLimit : Measure X) (c ^ (-2 : ℤ))
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  intro A hA hA0 hA1 r hr
  rw [cdf_standardGaussian_eq_normalCDFReal]
  have hcSq : Real.sqrt (c ^ (-2 : ℤ)) = c⁻¹ := by
    rw [zpow_neg, zpow_two, Real.sqrt_inv]
    rw [show c * c = c ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos hcPos]
  rw [hcSq, inv_mul_eq_div]
  let target : ℝ := (muLimit : Measure X).real (thickening r A)
  let mass : ℝ := (muLimit : Measure X).real A
  let shift : ℝ := r / c
  have hshift : 0 < shift := div_pos hr hcPos
  have hmass0 : 0 < mass := by simpa only [mass] using hA0
  have hmass1 : mass < 1 := by simpa only [mass] using hA1
  by_contra hgoal
  have hstrict : target < normalCDFReal
      (lowerQuantile standardGaussianMeasure mass + shift) := by
    simpa only [target, mass, shift] using lt_of_not_ge hgoal
  let Hmass : ℝ → ℝ := fun q => normalCDFReal
    (lowerQuantile standardGaussianMeasure q + shift)
  have hHmass : ContinuousAt Hmass mass := by
    exact (hasDerivAt_normalCDFReal _).continuousAt.comp
      ((continuousAt_lowerQuantile_standardGaussian
        (show mass ∈ Ioo (0 : ℝ) 1 from ⟨hmass0, hmass1⟩)).add
        continuousAt_const)
  have hmassEvent : ∀ᶠ q in 𝓝 mass, target < Hmass q := by
    exact hHmass (Ioi_mem_nhds (by simpa [Hmass] using hstrict))
  obtain ⟨q, hqmass, hqprofile, hq0⟩ :=
    (hmassEvent.and (Ioi_mem_nhds hmass0)).exists_lt
  let Hshift : ℝ → ℝ := fun u => normalCDFReal
    (lowerQuantile standardGaussianMeasure q + u)
  have hHshift : ContinuousAt Hshift shift :=
    (hasDerivAt_normalCDFReal _).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
  have hshiftEvent : ∀ᶠ u in 𝓝 shift, target < Hshift u := by
    exact hHshift (Ioi_mem_nhds (by simpa [Hshift, Hmass] using hqprofile))
  obtain ⟨u, hushift, huprofile, hu0⟩ :=
    (hshiftEvent.and (Ioi_mem_nhds hshift)).exists_lt
  have hqENN : ENNReal.ofReal q < (muLimit : Measure X) A := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hq0.le
      (measure_ne_top (muLimit : Measure X) A)]
    simpa [mass, Measure.real_def] using hqmass
  obtain ⟨K, hKA, hKcompact, hqK⟩ :=
    hA.exists_lt_isCompact_of_ne_top
      (measure_ne_top (muLimit : Measure X) A) hqENN
  have hqKreal : q < (muLimit : Measure X).real K := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (measure_ne_top (muLimit : Measure X) K)).2 hqK
    simpa only [Measure.real_def, ENNReal.toReal_ofReal hq0.le] using h
  let s : ℝ := (u * c + r) / 2
  let epsilon : ℝ := (r - s) / 2
  have huc : u * c < r := by
    rw [lt_div_iff₀ hcPos] at hushift
    simpa only [mul_comm, shift] using hushift
  have hs : 0 < s := by
    dsimp only [s]
    have huc0 : 0 ≤ u * c := mul_nonneg hu0.le hcPos.le
    linarith
  have hucs : u * c < s := by
    dsimp only [s]
    linarith
  have hsr : s < r := by
    dsimp only [s]
    linarith
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hesr : s + epsilon < r := by
    dsimp only [epsilon]
    linarith
  have hcompact := gaussianShift_compact_le_closedThickening_of_weakLimit
    (K := K) (q := q) (u := u) (s := s) (epsilon := epsilon)
    hmu hc hcSeq hfinite hq0 hqKreal hs hucs hepsilon
  have hclosedOpen :
      (muLimit : Measure X).real (cthickening (s + epsilon) K) ≤ target := by
    dsimp only [target]
    apply measureReal_mono
    exact (cthickening_subset_thickening' hr hesr K).trans
      (thickening_subset_of_subset r hKA)
    exact measure_ne_top (muLimit : Measure X) (thickening r A)
  exact (not_lt_of_ge (hcompact.trans hclosedOpen))
    (by simpa [Hshift] using huprofile)

end Concrete

end

end UniformRandomMALA
