import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import UniformRandomMALA.DiscreteTime.MovingReference

/-!
# Elementary Prokhorov bridges for the discrete-time proof

This file isolates the compactness and coupling facts used when finite endpoint
laws are sent to a weak limit.  The statements concern only probability
measures on product spaces, continuous push-forwards, and set inclusions.  No
continuous-time process or path-space convergence is used.
-/

namespace UniformRandomMALA

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section

namespace DiscreteTime

section TightProducts

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y]

/-- A named version of Mathlib's product tightness criterion.  It is the
compactness input for endpoint couplings: tightness of both endpoint
marginals implies tightness of the joint laws. -/
theorem isTightMeasureSet_of_tight_fst_snd
    {S : Set (Measure (X × Y))}
    (hfst : IsTightMeasureSet (Measure.fst '' S))
    (hsnd : IsTightMeasureSet (Measure.snd '' S)) :
    IsTightMeasureSet S :=
  IsTightMeasureSet.prodMk hfst hsnd

/-- Joint measures whose first marginal is fixed and whose second marginal
ranges in a tight family form a tight family. -/
theorem isTightMeasureSet_of_fixed_fst_tight_snd
    (mu : Measure X) (T : Set (Measure Y))
    (hmu : IsTightMeasureSet ({mu} : Set (Measure X)))
    (hT : IsTightMeasureSet T) :
    IsTightMeasureSet
      {kappa : Measure (X × Y) | kappa.fst = mu ∧ kappa.snd ∈ T} := by
  apply isTightMeasureSet_of_tight_fst_snd
  · apply hmu.subset
    rintro eta ⟨kappa, hkappa, rfl⟩
    simpa only [mem_singleton_iff] using hkappa.1
  · apply hT.subset
    rintro eta ⟨kappa, hkappa, rfl⟩
    exact hkappa.2

/-- If both marginals are fixed tight measures, the whole family of their
couplings is tight. -/
theorem isTightMeasureSet_of_fixed_marginals
    (mu : Measure X) (nu : Measure Y)
    (hmu : IsTightMeasureSet ({mu} : Set (Measure X)))
    (hnu : IsTightMeasureSet ({nu} : Set (Measure Y))) :
    IsTightMeasureSet
      {kappa : Measure (X × Y) | kappa.fst = mu ∧ kappa.snd = nu} := by
  have h := isTightMeasureSet_of_fixed_fst_tight_snd mu ({nu} : Set (Measure Y)) hmu hnu
  simpa only [mem_singleton_iff] using h

end TightProducts

section PolishTightProducts

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X]
  [IsCompletelyPseudoMetrizableSpace X] [SecondCountableTopology X]
  [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y]
  [IsCompletelyPseudoMetrizableSpace Y] [SecondCountableTopology Y]
  [BorelSpace Y]

/-- In Polish-type state spaces, fixed probability marginals are
automatically tight, so their whole family of couplings is tight without any
additional analytic hypothesis. -/
theorem isTightMeasureSet_probability_couplings_of_fixed_marginals
    (mu : ProbabilityMeasure X) (nu : ProbabilityMeasure Y) :
    IsTightMeasureSet
      {kappa : Measure (X × Y) |
        kappa.fst = (mu : Measure X) ∧ kappa.snd = (nu : Measure Y)} := by
  apply isTightMeasureSet_of_fixed_marginals
  · exact isTightMeasureSet_singleton
  · exact isTightMeasureSet_singleton

end PolishTightProducts

section CouplingDistance

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The elementary setwise estimate behind the coupling bound for the
Levy--Prokhorov distance.  If the first endpoint is in `B`, then either the
second endpoint is in the `r`-thickening of `B`, or the two endpoints are at
distance at least `r`. -/
theorem fst_measure_le_snd_thickening_add_tail
    (kappa : Measure (X × X)) (r : ℝ)
    {B : Set X} (hB : MeasurableSet B) :
    kappa.fst B ≤
      kappa.snd (Metric.thickening r B) +
        kappa {z : X × X | r ≤ dist z.1 z.2} := by
  rw [Measure.fst_apply hB,
    Measure.snd_apply Metric.isOpen_thickening.measurableSet]
  calc
    kappa (Prod.fst ⁻¹' B) ≤
        kappa ((Prod.snd ⁻¹' Metric.thickening r B) ∪
          {z : X × X | r ≤ dist z.1 z.2}) := by
      apply measure_mono
      intro z hz
      by_cases hdist : r ≤ dist z.1 z.2
      · exact Or.inr hdist
      · exact Or.inl ((Metric.mem_thickening_iff).2
          ⟨z.1, hz, by simpa only [dist_comm] using lt_of_not_ge hdist⟩)
    _ ≤ kappa (Prod.snd ⁻¹' Metric.thickening r B) +
        kappa {z : X × X | r ≤ dist z.1 z.2} :=
      measure_union_le _ _

/-- A coupling whose endpoints disagree by at least `delta` with probability
at most `delta` gives a Levy--Prokhorov bound of `delta`.  The proof uses only
the preceding set inclusion and Mathlib's one-sided characterization for
probability measures. -/
theorem levyProkhorovEDist_le_of_coupling_tail
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (kappa : Measure (X × X))
    (hfst : kappa.fst = mu) (hsnd : kappa.snd = nu)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (htail : kappa {z : X × X | delta ≤ dist z.1 z.2} ≤
      ENNReal.ofReal delta) :
    levyProkhorovEDist mu nu ≤ ENNReal.ofReal delta := by
  apply levyProkhorovEDist_le_of_forall_le
  intro epsilon B hdeltaepsilon hepsilon hB
  have hdeltalt : delta < epsilon.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hdelta hepsilon.ne).mp hdeltaepsilon
  have htail_epsilon :
      kappa {z : X × X | epsilon.toReal ≤ dist z.1 z.2} ≤ epsilon := by
    calc
      kappa {z : X × X | epsilon.toReal ≤ dist z.1 z.2} ≤
          kappa {z : X × X | delta ≤ dist z.1 z.2} := by
        apply measure_mono
        intro z hz
        exact hdeltalt.le.trans hz
      _ ≤ ENNReal.ofReal delta := htail
      _ ≤ epsilon := hdeltaepsilon.le
  calc
    mu B = kappa.fst B := by rw [hfst]
    _ ≤ kappa.snd (Metric.thickening epsilon.toReal B) +
        kappa {z : X × X | epsilon.toReal ≤ dist z.1 z.2} :=
      fst_measure_le_snd_thickening_add_tail kappa epsilon.toReal hB
    _ ≤ kappa.snd (Metric.thickening epsilon.toReal B) + epsilon :=
      add_le_add (le_refl _) htail_epsilon
    _ = nu (Metric.thickening epsilon.toReal B) + epsilon := by rw [hsnd]

omit [BorelSpace X] in
/-- A second-moment coupling estimate implies the tail hypothesis used by
`levyProkhorovEDist_le_of_coupling_tail`.  The cubic scale is chosen so that
Markov's inequality at threshold `delta ^ 2` leaves the probability bound
`delta`. -/
theorem coupling_tail_le_of_lintegral_sq_le_cube
    [OpensMeasurableSpace (X × X)]
    (kappa : Measure (X × X)) {delta : ℝ} (hdelta : 0 < delta)
    (hsecond :
      (∫⁻ z : X × X, ENNReal.ofReal (dist z.1 z.2 ^ 2) ∂kappa) ≤
        ENNReal.ofReal (delta ^ 3)) :
    kappa {z : X × X | delta ≤ dist z.1 z.2} ≤
      ENNReal.ofReal delta := by
  let a : ℝ≥0∞ := ENNReal.ofReal (delta ^ 2)
  let f : X × X → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (dist z.1 z.2 ^ 2)
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      ((continuous_fst.dist continuous_snd).pow 2).measurable
  have hsubset :
      {z : X × X | delta ≤ dist z.1 z.2} ⊆ {z : X × X | a ≤ f z} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal
      ((sq_le_sq₀ hdelta.le dist_nonneg).2 hz)
  have hmul :
      a * kappa {z : X × X | delta ≤ dist z.1 z.2} ≤
        a * ENNReal.ofReal delta := by
    calc
      a * kappa {z : X × X | delta ≤ dist z.1 z.2} ≤
          a * kappa {z : X × X | a ≤ f z} := by
        gcongr
      _ ≤ ∫⁻ z, f z ∂kappa := mul_meas_ge_le_lintegral hf a
      _ ≤ ENNReal.ofReal (delta ^ 3) := hsecond
      _ = a * ENNReal.ofReal delta := by
        rw [show delta ^ 3 = delta ^ 2 * delta by ring,
          ENNReal.ofReal_mul (sq_nonneg delta)]
  exact (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hdelta))
    ENNReal.ofReal_ne_top).mp hmul

/-- Combined second-moment-to-Levy--Prokhorov estimate for an endpoint
coupling. -/
theorem levyProkhorovEDist_le_of_coupling_lintegral_sq_le_cube
    [OpensMeasurableSpace (X × X)]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (kappa : Measure (X × X))
    (hfst : kappa.fst = mu) (hsnd : kappa.snd = nu)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsecond :
      (∫⁻ z : X × X, ENNReal.ofReal (dist z.1 z.2 ^ 2) ∂kappa) ≤
        ENNReal.ofReal (delta ^ 3)) :
    levyProkhorovEDist mu nu ≤ ENNReal.ofReal delta := by
  apply levyProkhorovEDist_le_of_coupling_tail mu nu kappa hfst hsnd hdelta.le
  exact coupling_tail_le_of_lintegral_sq_le_cube kappa hdelta hsecond

end CouplingDistance

section WeakLimits

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [HasOuterApproxClosed Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- A marginal identity passes to a weak limit.  This is just the continuous
mapping theorem for probability measures plus uniqueness of limits. -/
theorem probabilityMeasure_map_eq_of_tendsto
    {kappa : ℕ → ProbabilityMeasure X}
    {kappaLimit : ProbabilityMeasure X}
    {mu : ℕ → ProbabilityMeasure Y}
    {muLimit : ProbabilityMeasure Y}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hmu : Tendsto mu atTop (nhds muLimit))
    {f : X → Y} (hf : Continuous f)
    (hmarginal : ∀ n, (kappa n).map hf.measurable.aemeasurable = mu n) :
    kappaLimit.map hf.measurable.aemeasurable = muLimit := by
  exact tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      kappa kappaLimit hkappa hf)
    (by simpa only [hmarginal] using hmu)

end WeakLimits

section ProductWeakLimits

section FirstMarginal

variable {X Y : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace (X × Y)]

/-- The first marginal of a sequence of joint laws passes to the weak limit. -/
theorem fst_eq_of_probabilityMeasure_tendsto
    {kappa : ℕ → ProbabilityMeasure (X × Y)}
    {kappaLimit : ProbabilityMeasure (X × Y)}
    {mu : ℕ → ProbabilityMeasure X}
    {muLimit : ProbabilityMeasure X}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hfst : ∀ n, (kappa n : Measure (X × Y)).fst = (mu n : Measure X)) :
    (kappaLimit : Measure (X × Y)).fst = (muLimit : Measure X) := by
  have hmarginal (n : ℕ) :
      (kappa n).map continuous_fst.measurable.aemeasurable = mu n := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map, Measure.fst] using hfst n
  have hlimit := probabilityMeasure_map_eq_of_tendsto
    hkappa hmu continuous_fst hmarginal
  exact congrArg ProbabilityMeasure.toMeasure hlimit

end FirstMarginal

section SecondMarginal

variable {X Y : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [OpensMeasurableSpace (X × Y)]

/-- The second marginal of a sequence of joint laws passes to the weak limit. -/
theorem snd_eq_of_probabilityMeasure_tendsto
    {kappa : ℕ → ProbabilityMeasure (X × Y)}
    {kappaLimit : ProbabilityMeasure (X × Y)}
    {nu : ℕ → ProbabilityMeasure Y}
    {nuLimit : ProbabilityMeasure Y}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hnu : Tendsto nu atTop (nhds nuLimit))
    (hsnd : ∀ n, (kappa n : Measure (X × Y)).snd = (nu n : Measure Y)) :
    (kappaLimit : Measure (X × Y)).snd = (nuLimit : Measure Y) := by
  have hmarginal (n : ℕ) :
      (kappa n).map continuous_snd.measurable.aemeasurable = nu n := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map, Measure.snd] using hsnd n
  have hlimit := probabilityMeasure_map_eq_of_tendsto
    hkappa hnu continuous_snd hmarginal
  exact congrArg ProbabilityMeasure.toMeasure hlimit

end SecondMarginal

section Swap


variable {X : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X]
  [BorelSpace (X × X)] [OpensMeasurableSpace (X × X)]

/-- Swap invariance is closed under weak convergence. -/
theorem map_swap_eq_self_of_probabilityMeasure_tendsto
    {kappa : ℕ → ProbabilityMeasure (X × X)}
    {kappaLimit : ProbabilityMeasure (X × X)}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hsymm : ∀ n,
      Measure.map Prod.swap (kappa n : Measure (X × X)) =
        (kappa n : Measure (X × X))) :
    Measure.map Prod.swap (kappaLimit : Measure (X × X)) =
      (kappaLimit : Measure (X × X)) := by
  have hsymm_probability (n : ℕ) :
      (kappa n).map measurable_swap.aemeasurable = kappa n := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map] using hsymm n
  have hlimit := probabilityMeasure_map_eq_of_tendsto
    hkappa hkappa continuous_swap hsymm_probability
  exact congrArg ProbabilityMeasure.toMeasure hlimit

end Swap

end ProductWeakLimits

section CompactSubsequences

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace (X × Y)] [OpensMeasurableSpace (X × Y)]

/-- Tightness of both marginal families makes the closure of a family of
joint probability measures compact. -/
theorem isCompact_closure_probabilityMeasures_of_tight_marginals
    {S : Set (ProbabilityMeasure (X × Y))}
    (hfst : IsTightMeasureSet
      (Measure.fst ''
        {((kappa : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
          kappa ∈ S}))
    (hsnd : IsTightMeasureSet
      (Measure.snd ''
        {((kappa : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
          kappa ∈ S})) :
    IsCompact (closure S) := by
  apply isCompact_closure_of_isTightMeasureSet
  exact isTightMeasureSet_of_tight_fst_snd hfst hsnd

end CompactSubsequences

section SequentialProkhorov

variable {X Y : Type*}
  [PseudoMetricSpace X] [T2Space X]
  [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [T2Space Y]
  [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y]
  [BorelSpace (X × Y)] [OpensMeasurableSpace (X × Y)]

/-- Sequential form of Prokhorov compactness.  Mathlib's weak topology on
probability measures is not globally registered as first-countable.  On a
separable pseudometric space, we transport the compact family through the
Levy--Prokhorov homeomorphism, extract a metric-space subsequence there, and
transport the convergence back. -/
theorem exists_tendsto_subseq_of_tight_marginals
    {S : Set (ProbabilityMeasure (X × Y))}
    (hfst : IsTightMeasureSet
      (Measure.fst ''
        {((kappa : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
          kappa ∈ S}))
    (hsnd : IsTightMeasureSet
      (Measure.snd ''
        {((kappa : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
          kappa ∈ S}))
    (kappa : ℕ → ProbabilityMeasure (X × Y))
    (hkappa : ∀ n, kappa n ∈ S) :
    ∃ kappaLimit ∈ closure S, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧
        Tendsto (kappa ∘ subseq) atTop (nhds kappaLimit) := by
  let e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := X × Y)
  have hcompact : IsCompact (closure S) :=
    isCompact_closure_probabilityMeasures_of_tight_marginals hfst hsnd
  have hcompactImage : IsCompact (e '' closure S) := hcompact.image e.continuous
  have himage (n : ℕ) : e (kappa n) ∈ e '' closure S :=
    ⟨kappa n, subset_closure (hkappa n), rfl⟩
  obtain ⟨limitImage, hlimitImage, subseq, hsubseq, htendsto⟩ :=
    hcompactImage.isSeqCompact himage
  obtain ⟨kappaLimit, hkappaLimit, hkappaLimitImage⟩ := hlimitImage
  refine ⟨kappaLimit, hkappaLimit, subseq, hsubseq, ?_⟩
  have hback := e.symm.continuous.continuousAt.tendsto.comp htendsto
  have hlimitBack : e.symm limitImage = kappaLimit := by
    rw [← hkappaLimitImage, e.symm_apply_apply]
  rw [hlimitBack] at hback
  apply hback.congr'
  exact Eventually.of_forall (fun n => by
    simp only [Function.comp_apply, e.symm_apply_apply])

end SequentialProkhorov

end DiscreteTime

end

end UniformRandomMALA
