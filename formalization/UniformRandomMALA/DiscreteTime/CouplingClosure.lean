import UniformRandomMALA.DiscreteTime.ProkhorovBridge

/-!
# Closure of endpoint-coupling estimates under weak convergence

The Portmanteau inequality is one-sided: upper bounds pass directly to the
limit for open sets, not for closed sets.  For the closed distance tail
`{(x,y) | r <= dist x y}`, the elementary replacement is to assume the
finite laws satisfy the same bound at a slightly smaller threshold
`r - eta`.  The open set `{(x,y) | r - eta < dist x y}` then carries the
bound through the weak limit and contains the desired closed tail.
-/

namespace UniformRandomMALA

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section

namespace DiscreteTime

section OpenBounds

variable {Omega : Type*} [MeasurableSpace Omega] [TopologicalSpace Omega]
  [OpensMeasurableSpace Omega] [HasOuterApproxClosed Omega]

/-- A uniform upper bound on the mass of an open set passes to a weak limit
of probability measures.  This is the direction of Portmanteau used for
coupling tails with threshold slack. -/
theorem measure_open_le_of_tendsto_of_forall_le
    {mu : ℕ → ProbabilityMeasure Omega} {muLimit : ProbabilityMeasure Omega}
    (hmu : Tendsto mu atTop (nhds muLimit))
    {G : Set Omega} (hG : IsOpen G) {c : ℝ≥0∞}
    (hbound : ∀ n, (mu n : Measure Omega) G ≤ c) :
    (muLimit : Measure Omega) G ≤ c := by
  calc
    (muLimit : Measure Omega) G ≤
        atTop.liminf (fun n => (mu n : Measure Omega) G) :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hmu hG
    _ ≤ c := by
      apply Filter.liminf_le_of_le
      · exact ⟨0, Eventually.of_forall (fun _ => by simp)⟩
      · intro b hb
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hbound n)

/-- A uniform bound on violations of a closed relation passes to a weak
limit, since the violation set is the open complement of the relation. -/
theorem measure_compl_closed_le_of_tendsto_of_forall_le
    {mu : ℕ → ProbabilityMeasure Omega} {muLimit : ProbabilityMeasure Omega}
    (hmu : Tendsto mu atTop (nhds muLimit))
    {R : Set Omega} (hR : IsClosed R) {c : ℝ≥0∞}
    (hbound : ∀ n, (mu n : Measure Omega) Rᶜ ≤ c) :
    (muLimit : Measure Omega) Rᶜ ≤ c :=
  measure_open_le_of_tendsto_of_forall_le hmu hR.isOpen_compl hbound

/-- Probability-one support on a closed relation passes to a weak limit. -/
theorem measure_closed_eq_one_of_tendsto_of_forall_eq_one
    {mu : ℕ → ProbabilityMeasure Omega} {muLimit : ProbabilityMeasure Omega}
    (hmu : Tendsto mu atTop (nhds muLimit))
    {R : Set Omega} (hR : IsClosed R)
    (hsupport : ∀ n, (mu n : Measure Omega) R = 1) :
    (muLimit : Measure Omega) R = 1 := by
  have hcompl : ∀ n, (mu n : Measure Omega) Rᶜ ≤ 0 := by
    intro n
    exact ((prob_compl_eq_zero_iff hR.measurableSet).2 (hsupport n)).le
  have hlimitCompl : (muLimit : Measure Omega) Rᶜ = 0 := by
    exact nonpos_iff_eq_zero.mp
      (measure_compl_closed_le_of_tendsto_of_forall_le hmu hR hcompl)
  exact (prob_compl_eq_zero_iff hR.measurableSet).mp hlimitCompl

end OpenBounds

section DistanceTails

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace (X × X)]

/-- A uniform bound on a strict distance tail passes directly through weak
convergence, because the strict tail is open. -/
theorem measure_dist_gt_le_of_tendsto_of_forall_le
    {kappa : ℕ → ProbabilityMeasure (X × X)}
    {kappaLimit : ProbabilityMeasure (X × X)}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    {r : ℝ} {c : ℝ≥0∞}
    (hbound : ∀ n,
      (kappa n : Measure (X × X)) {z : X × X | r < dist z.1 z.2} ≤ c) :
    (kappaLimit : Measure (X × X))
        {z : X × X | r < dist z.1 z.2} ≤ c := by
  apply measure_open_le_of_tendsto_of_forall_le hkappa
  · exact isOpen_lt continuous_const (continuous_fst.dist continuous_snd)
  · exact hbound

/-- A closed distance-tail estimate passes to the weak limit when the finite
estimates are available at a strictly smaller threshold.  This is the exact
Portmanteau-friendly form needed by a discretization argument. -/
theorem measure_dist_ge_le_of_tendsto_of_threshold_slack
    {kappa : ℕ → ProbabilityMeasure (X × X)}
    {kappaLimit : ProbabilityMeasure (X × X)}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    {r eta : ℝ} (heta : 0 < eta) {c : ℝ≥0∞}
    (hbound : ∀ n,
      (kappa n : Measure (X × X))
        {z : X × X | r - eta ≤ dist z.1 z.2} ≤ c) :
    (kappaLimit : Measure (X × X))
        {z : X × X | r ≤ dist z.1 z.2} ≤ c := by
  calc
    (kappaLimit : Measure (X × X))
        {z : X × X | r ≤ dist z.1 z.2} ≤
        (kappaLimit : Measure (X × X))
          {z : X × X | r - eta < dist z.1 z.2} := by
      apply measure_mono
      intro z hz
      change r ≤ dist z.1 z.2 at hz
      change r - eta < dist z.1 z.2
      linarith
    _ ≤ c := measure_dist_gt_le_of_tendsto_of_forall_le hkappa (fun n => by
      exact (measure_mono (fun z hz => by
        change r - eta < dist z.1 z.2 at hz
        change r - eta ≤ dist z.1 z.2
        exact hz.le)).trans (hbound n))

end DistanceTails

section FixedMarginalCouplings

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [OpensMeasurableSpace (X × X)]

/-- A weak limit of finite endpoint couplings retains both fixed marginals
and a distance-tail estimate supplied with threshold slack. -/
theorem weak_limit_coupling_of_fixed_marginals_with_tail_slack
    {kappa : ℕ → ProbabilityMeasure (X × X)}
    {kappaLimit : ProbabilityMeasure (X × X)}
    {mu nu : ProbabilityMeasure X}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hfst : ∀ n,
      (kappa n : Measure (X × X)).fst = (mu : Measure X))
    (hsnd : ∀ n,
      (kappa n : Measure (X × X)).snd = (nu : Measure X))
    {r eta : ℝ} (heta : 0 < eta) {c : ℝ≥0∞}
    (htail : ∀ n,
      (kappa n : Measure (X × X))
        {z : X × X | r - eta ≤ dist z.1 z.2} ≤ c) :
    (kappaLimit : Measure (X × X)).fst = (mu : Measure X) ∧
      (kappaLimit : Measure (X × X)).snd = (nu : Measure X) ∧
      (kappaLimit : Measure (X × X))
        {z : X × X | r ≤ dist z.1 z.2} ≤ c := by
  refine ⟨?_, ?_, ?_⟩
  · exact fst_eq_of_probabilityMeasure_tendsto
      hkappa tendsto_const_nhds hfst
  · exact snd_eq_of_probabilityMeasure_tendsto
      hkappa tendsto_const_nhds hsnd
  · exact measure_dist_ge_le_of_tendsto_of_threshold_slack
      hkappa heta htail

end FixedMarginalCouplings

section SymmetricCouplingComposition

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [OpensMeasurableSpace (X × X)]
  [BorelSpace (X × X)]

/-- Composition theorem for a selected weakly convergent coupling
subsequence.  Fixed marginals, swap invariance, and a tail estimate with
threshold slack all survive in the limiting coupling. -/
theorem weak_limit_symmetric_coupling_of_fixed_marginals_with_tail_slack
    {kappa : ℕ → ProbabilityMeasure (X × X)}
    {kappaLimit : ProbabilityMeasure (X × X)}
    {mu nu : ProbabilityMeasure X}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hfst : ∀ n,
      (kappa n : Measure (X × X)).fst = (mu : Measure X))
    (hsnd : ∀ n,
      (kappa n : Measure (X × X)).snd = (nu : Measure X))
    (hsymm : ∀ n,
      Measure.map Prod.swap (kappa n : Measure (X × X)) =
        (kappa n : Measure (X × X)))
    {r eta : ℝ} (heta : 0 < eta) {c : ℝ≥0∞}
    (htail : ∀ n,
      (kappa n : Measure (X × X))
        {z : X × X | r - eta ≤ dist z.1 z.2} ≤ c) :
    (kappaLimit : Measure (X × X)).fst = (mu : Measure X) ∧
      (kappaLimit : Measure (X × X)).snd = (nu : Measure X) ∧
      Measure.map Prod.swap (kappaLimit : Measure (X × X)) =
        (kappaLimit : Measure (X × X)) ∧
      (kappaLimit : Measure (X × X))
        {z : X × X | r ≤ dist z.1 z.2} ≤ c := by
  have hcoupling := weak_limit_coupling_of_fixed_marginals_with_tail_slack
    hkappa hfst hsnd heta htail
  exact ⟨hcoupling.1, hcoupling.2.1,
    map_swap_eq_self_of_probabilityMeasure_tendsto hkappa hsymm,
    hcoupling.2.2⟩

/-- Squared-distance version of the selected-subsequence composition
theorem.  A uniform bound `E dist² <= delta³` gives a closed-tail bound at
the slightly larger threshold `delta + eta`.  The limiting coupling then
also witnesses the corresponding Levy--Prokhorov bound between its fixed
marginals. -/
theorem weak_limit_symmetric_coupling_of_fixed_marginals_with_sq_control
    {kappa : ℕ → ProbabilityMeasure (X × X)}
    {kappaLimit : ProbabilityMeasure (X × X)}
    {mu nu : ProbabilityMeasure X}
    (hkappa : Tendsto kappa atTop (nhds kappaLimit))
    (hfst : ∀ n,
      (kappa n : Measure (X × X)).fst = (mu : Measure X))
    (hsnd : ∀ n,
      (kappa n : Measure (X × X)).snd = (nu : Measure X))
    (hsymm : ∀ n,
      Measure.map Prod.swap (kappa n : Measure (X × X)) =
        (kappa n : Measure (X × X)))
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta)
    (hsecond : ∀ n,
      (∫⁻ z : X × X, ENNReal.ofReal (dist z.1 z.2 ^ 2)
        ∂(kappa n : Measure (X × X))) ≤ ENNReal.ofReal (delta ^ 3)) :
    (kappaLimit : Measure (X × X)).fst = (mu : Measure X) ∧
      (kappaLimit : Measure (X × X)).snd = (nu : Measure X) ∧
      Measure.map Prod.swap (kappaLimit : Measure (X × X)) =
        (kappaLimit : Measure (X × X)) ∧
      (kappaLimit : Measure (X × X))
        {z : X × X | delta + eta ≤ dist z.1 z.2} ≤
          ENNReal.ofReal delta ∧
      levyProkhorovEDist (mu : Measure X) (nu : Measure X) ≤
        ENNReal.ofReal (delta + eta) := by
  have htail (n : ℕ) :
      (kappa n : Measure (X × X))
        {z : X × X | (delta + eta) - eta ≤ dist z.1 z.2} ≤
          ENNReal.ofReal delta := by
    simpa only [add_sub_cancel_right] using
      coupling_tail_le_of_lintegral_sq_le_cube
        (kappa n : Measure (X × X)) hdelta (hsecond n)
  have hlimit :=
    weak_limit_symmetric_coupling_of_fixed_marginals_with_tail_slack
      hkappa hfst hsnd hsymm heta htail
  refine ⟨hlimit.1, hlimit.2.1, hlimit.2.2.1, hlimit.2.2.2, ?_⟩
  apply levyProkhorovEDist_le_of_coupling_tail
    (mu : Measure X) (nu : Measure X)
    (kappaLimit : Measure (X × X)) hlimit.1 hlimit.2.1
    (by linarith : 0 ≤ delta + eta)
  exact hlimit.2.2.2.trans
    (ENNReal.ofReal_le_ofReal (by linarith : delta ≤ delta + eta))

end SymmetricCouplingComposition

end DiscreteTime

end

end UniformRandomMALA
