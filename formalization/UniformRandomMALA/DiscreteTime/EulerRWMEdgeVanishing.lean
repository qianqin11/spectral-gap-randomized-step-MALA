import UniformRandomMALA.DiscreteTime.EulerRWMVanishingStep
import UniformRandomMALA.DiscreteTime.EulerRWMEdgeCoupling

/-!
# From pair-chain energy to a vanishing edge-coupling cost

This file is the finite-measure bridge between the real-valued energy used
by the Euler--RWM recurrence and the `ENNReal` cost used by the endpoint-edge
coupling.  It also packages a strictly positive error schedule whose cube
dominates that cost.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete

variable {d : ℕ}

/-- Forgetting the retained initial point gives exactly the stationary pair
chain law used by the recurrence. -/
theorem map_snd_retainedInitialEulerRWMPairMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure.map Prod.snd (retainedInitialEulerRWMPairMeasure V δ n) =
      stationaryEulerRWMPairChainLaw V δ n := by
  change (retainedInitialEulerRWMPairMeasure V δ n).snd =
    stationaryEulerRWMPairChainLaw V δ n
  rw [retainedInitialEulerRWMPairMeasure, Measure.snd_compProd]
  unfold diagonalStartedEulerRWMPairKernel stationaryEulerRWMPairChainLaw
  calc
    (eulerRWMPairChainKernel V δ n ∘ₖ Kernel.copy (State d)) ∘ₘ
        (V.target : Measure (State d)) =
        eulerRWMPairChainKernel V δ n ∘ₘ
          (Kernel.copy (State d) ∘ₘ
            (V.target : Measure (State d))) := by
      rw [Measure.comp_assoc]
    _ = eulerRWMPairChainKernel V δ n ∘ₘ
          diagonalTargetPairLaw V := by
      congr 1
      rw [Kernel.copy, Measure.deterministic_comp_eq_map]
      rfl

/-- The retained-initial `ENNReal` cost is the `ofReal` of the Bochner
energy.  The step assumptions are used only to obtain integrability of the
finite pair-chain energy. -/
theorem lintegral_retainedInitial_pairCost_eq_ofReal_energy
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L) :
    (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V δ n) =
      ENNReal.ofReal
        (∫ xy, pairSquaredDistance xy
          ∂stationaryEulerRWMPairChainLaw V δ n) := by
  have hcost : Measurable (fun xy : State d × State d =>
      ENNReal.ofReal (pairSquaredDistance xy)) :=
    ENNReal.measurable_ofReal.comp measurable_pairSquaredDistance
  calc
    (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V δ n) =
        ∫⁻ xy : State d × State d,
          ENNReal.ofReal (pairSquaredDistance xy)
          ∂Measure.map Prod.snd
            (retainedInitialEulerRWMPairMeasure V δ n) := by
      rw [lintegral_map hcost measurable_snd]
      rfl
    _ = ∫⁻ xy : State d × State d,
          ENNReal.ofReal (pairSquaredDistance xy)
          ∂stationaryEulerRWMPairChainLaw V δ n := by
      rw [map_snd_retainedInitialEulerRWMPairMeasure]
    _ = ENNReal.ofReal
        (∫ xy, pairSquaredDistance xy
          ∂stationaryEulerRWMPairChainLaw V δ n) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_pairSquaredDistance_stationaryEulerRWMPairChainLaw
          V δ hδ hδ1 hδL n)
        (ae_of_all _ fun xy => by
          exact sq_nonneg ‖xy.1 - xy.2‖)]

/-! ## A positive cube-dominating schedule -/

/-- Fixed-horizon step size after an integer offset.  The offset lets all
members of the sequence, rather than merely an eventual tail, lie in the
small-step regime. -/
def fixedHorizonOffsetStep (h : ℝ) (N n : ℕ) : ℝ :=
  h / ((n + N : ℕ) : ℝ)

/-- Number of steps paired with `fixedHorizonOffsetStep`. -/
def fixedHorizonOffsetSteps (N n : ℕ) : ℕ := n + N

/-- Real-valued terminal mean-square discrepancy for the offset schedule. -/
def fixedHorizonOffsetEnergy
    (V : FirstOrderPotential d) (h : ℝ) (N n : ℕ) : ℝ :=
  ∫ xy, pairSquaredDistance xy
    ∂stationaryEulerRWMPairChainLaw V
      (fixedHorizonOffsetStep h N n) (fixedHorizonOffsetSteps N n)

/-- A strictly positive error schedule.  The fourth-root term handles
energies below one, the energy itself handles energies above one, and the
last summand enforces strict positivity. -/
def fixedHorizonOffsetEpsilon
    (V : FirstOrderPotential d) (h : ℝ) (N n : ℕ) : ℝ :=
  fixedHorizonOffsetEnergy V h N n +
    Real.sqrt (Real.sqrt (fixedHorizonOffsetEnergy V h N n)) +
    1 / (((n + 1 : ℕ) : ℝ))

lemma fixedHorizonOffsetStep_pos
    (h : ℝ) (N n : ℕ) (hh : 0 < h) (hN : 1 ≤ N) :
    0 < fixedHorizonOffsetStep h N n := by
  unfold fixedHorizonOffsetStep
  exact div_pos hh (by positivity)

lemma fixedHorizonOffsetStep_le_at_zero
    (h : ℝ) (N n : ℕ) (hh : 0 < h) (hN : 1 ≤ N) :
    fixedHorizonOffsetStep h N n ≤ h / (N : ℝ) := by
  unfold fixedHorizonOffsetStep
  apply div_le_div_of_nonneg_left hh.le
  · exact_mod_cast hN
  · exact_mod_cast (show N ≤ n + N by omega)

lemma fixedHorizonOffset_horizon
    (h : ℝ) (N n : ℕ) (hN : 1 ≤ N) :
    (fixedHorizonOffsetSteps N n : ℝ) *
        fixedHorizonOffsetStep h N n = h := by
  unfold fixedHorizonOffsetSteps fixedHorizonOffsetStep
  field_simp

/-- The offset fixed-horizon energies inherit the vanishing-step limit. -/
theorem tendsto_fixedHorizonOffsetEnergy
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h)
    (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fixedHorizonOffsetEnergy V h N) atTop (nhds 0) := by
  have hbase :=
    tendsto_stationaryEulerRWMPairChain_energy_fixedHorizon V h hh
  have hshift := hbase.comp (tendsto_add_atTop_nat (N - 1))
  apply Tendsto.congr' _ hshift
  exact Eventually.of_forall fun n => by
    have hindex : n + (N - 1) + 1 = n + N := by omega
    simp only [fixedHorizonOffsetEnergy, fixedHorizonOffsetStep,
      fixedHorizonOffsetSteps, Function.comp_apply, hindex]

lemma fixedHorizonOffsetEnergy_nonneg
    (V : FirstOrderPotential d) (h : ℝ) (N n : ℕ) :
    0 ≤ fixedHorizonOffsetEnergy V h N n := by
  unfold fixedHorizonOffsetEnergy
  exact integral_nonneg fun _ => sq_nonneg _

/-- Elementary real inequality behind the positive error schedule. -/
lemma le_cube_self_add_sqrt_sqrt_add
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    a ≤ (a + Real.sqrt (Real.sqrt a) + r) ^ 3 := by
  let q := Real.sqrt (Real.sqrt a)
  have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hq2 : q ^ 2 = Real.sqrt a := Real.sq_sqrt hs0
  have hq4 : q ^ 4 = a := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = (Real.sqrt a) ^ 2 := by rw [hq2]
      _ = a := hs2
  have hqeps : q ≤ a + q + r := by linarith
  have hqpow : q ^ 3 ≤ (a + q + r) ^ 3 :=
    pow_le_pow_left₀ hq0 hqeps 3
  by_cases ha1 : a ≤ 1
  · have hs1 : Real.sqrt a ≤ 1 := by nlinarith
    have hq1 : q ≤ 1 := by nlinarith
    have haq : a ≤ q ^ 3 := by
      rw [← hq4]
      calc
        q ^ 4 = q ^ 3 * q := by ring
        _ ≤ q ^ 3 * 1 := mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 3)
        _ = q ^ 3 := by ring
    simpa only [q] using haq.trans hqpow
  · have ha1' : 1 ≤ a := le_of_not_ge ha1
    have haa : a ≤ a ^ 3 := by nlinarith [sq_nonneg a]
    have haeps : a ≤ a + q + r := by linarith
    have hapow : a ^ 3 ≤ (a + q + r) ^ 3 :=
      pow_le_pow_left₀ ha haeps 3
    simpa only [q] using haa.trans hapow

lemma fixedHorizonOffsetEpsilon_pos
    (V : FirstOrderPotential d) (h : ℝ) (N n : ℕ) :
    0 < fixedHorizonOffsetEpsilon V h N n := by
  unfold fixedHorizonOffsetEpsilon
  have ha := fixedHorizonOffsetEnergy_nonneg V h N n
  have hs := Real.sqrt_nonneg
    (Real.sqrt (fixedHorizonOffsetEnergy V h N n))
  have hr : 0 < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  linarith

theorem tendsto_fixedHorizonOffsetEpsilon
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h)
    (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fixedHorizonOffsetEpsilon V h N) atTop (nhds 0) := by
  have henergy := tendsto_fixedHorizonOffsetEnergy V h hh N hN
  have hrecip : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 1)
  change Tendsto (fun n =>
    fixedHorizonOffsetEnergy V h N n +
      Real.sqrt (Real.sqrt (fixedHorizonOffsetEnergy V h N n)) +
      1 / (((n + 1 : ℕ) : ℝ))) atTop (nhds 0)
  simpa only [Real.sqrt_zero, add_zero] using
    (henergy.add henergy.sqrt.sqrt).add hrecip

lemma fixedHorizonOffsetEnergy_le_epsilon_cube
    (V : FirstOrderPotential d) (h : ℝ) (N n : ℕ) :
    fixedHorizonOffsetEnergy V h N n ≤
      fixedHorizonOffsetEpsilon V h N n ^ 3 := by
  exact le_cube_self_add_sqrt_sqrt_add
    (fixedHorizonOffsetEnergy V h N n)
    (1 / (((n + 1 : ℕ) : ℝ)))
    (fixedHorizonOffsetEnergy_nonneg V h N n) (by positivity)

/-- The retained-initial edge-coupling cost is bounded by the cube of the
positive vanishing schedule at every index. -/
theorem lintegral_fixedHorizonOffset_pairCost_le_epsilon_cube
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h)
    (N : ℕ) (hN : 1 ≤ N)
    (hstepOne : h / (N : ℝ) ≤ 1)
    (hstepL : h / (N : ℝ) ≤ 2 / V.L)
    (n : ℕ) :
    (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V
          (fixedHorizonOffsetStep h N n)
          (fixedHorizonOffsetSteps N n)) ≤
      ENNReal.ofReal (fixedHorizonOffsetEpsilon V h N n ^ 3) := by
  have hδpos := fixedHorizonOffsetStep_pos h N n hh hN
  have hδbase := fixedHorizonOffsetStep_le_at_zero h N n hh hN
  rw [lintegral_retainedInitial_pairCost_eq_ofReal_energy
    V (fixedHorizonOffsetStep h N n) (fixedHorizonOffsetSteps N n)
    hδpos (hδbase.trans hstepOne) (hδbase.trans hstepL)]
  exact ENNReal.ofReal_le_ofReal
    (fixedHorizonOffsetEnergy_le_epsilon_cube V h N n)

/-- An elementary Archimedean choice of offset puts every step size in the
two small-step regimes needed by the recurrence. -/
lemma exists_fixedHorizonOffset_smallSteps
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, 1 ≤ N ∧ h / (N : ℝ) ≤ 1 ∧
      h / (N : ℝ) ≤ 2 / V.L := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max h (h * V.L / 2))
  have hhN : h < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hscaledN : h * V.L / 2 < (N : ℝ) :=
    (le_max_right _ _).trans_lt hN
  have hNpos : 0 < (N : ℝ) := hh.trans hhN
  have hNone : 1 ≤ N := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      subst N
      norm_num at hNpos)
  refine ⟨N, hNone, ?_, ?_⟩
  · exact (div_le_one hNpos).2 hhN.le
  · apply (div_le_iff₀ hNpos).2
    have hprod : h * V.L ≤ 2 * (N : ℝ) := by linarith
    calc
      h ≤ 2 * (N : ℝ) / V.L := (le_div_iff₀ V.hL).2 hprod
      _ = (2 / V.L) * (N : ℝ) := by ring

/-- Fully packaged positive vanishing schedule for every positive horizon.
The chosen natural offset is existential but completely elementary (the
Archimedean property of `ℕ ⊆ ℝ`). -/
theorem exists_positive_vanishing_fixedHorizonOffsetSchedule
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ n, 0 < fixedHorizonOffsetEpsilon V h N n) ∧
      Tendsto (fixedHorizonOffsetEpsilon V h N) atTop (nhds 0) ∧
      ∀ n,
        (∫⁻ z : State d × (State d × State d),
          ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
          ∂retainedInitialEulerRWMPairMeasure V
            (fixedHorizonOffsetStep h N n)
            (fixedHorizonOffsetSteps N n)) ≤
          ENNReal.ofReal (fixedHorizonOffsetEpsilon V h N n ^ 3) := by
  obtain ⟨N, hN, hstepOne, hstepL⟩ :=
    exists_fixedHorizonOffset_smallSteps V h hh
  refine ⟨N, hN, fixedHorizonOffsetEpsilon_pos V h N,
    tendsto_fixedHorizonOffsetEpsilon V h hh N hN, ?_⟩
  exact lintegral_fixedHorizonOffset_pairCost_le_epsilon_cube
    V h hh N hN hstepOne hstepL

/-- For every positive horizon, the elementary offset schedule admits a
single subsequence along which both the finite Euler edge laws and the
stationary RWM edge laws converge to the same symmetric self-coupling of the
target.  The positive vanishing error schedule and its cube cost bound are
retained explicitly in the conclusion. -/
theorem exists_common_tendsto_subseq_fixedHorizonEulerRWMEdgeLaws_with_structure
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, ∃ epsilon : ℕ → ℝ,
      1 ≤ N ∧
      (∀ n, 0 < epsilon n) ∧
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ n,
        (∫⁻ z : State d × (State d × State d),
          ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
          ∂retainedInitialEulerRWMPairMeasure V
            (fixedHorizonOffsetStep h N n)
            (fixedHorizonOffsetSteps N n)) ≤
          ENNReal.ofReal (epsilon n ^ 3)) ∧
      ∃ sigma ∈ closure (Set.range (fun n =>
          finiteRWMEdgeLaw V
            (fixedHorizonOffsetStep h N n)
            (fixedHorizonOffsetSteps N n))),
        ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
          Tendsto
            ((fun n => finiteRWMEdgeLaw V
              (fixedHorizonOffsetStep h N n)
              (fixedHorizonOffsetSteps N n)) ∘ subseq)
            atTop (nhds sigma) ∧
          Tendsto
            ((fun n => finiteEulerEdgeLaw V
              (fixedHorizonOffsetStep h N n)
              (fixedHorizonOffsetSteps N n)) ∘ subseq)
            atTop (nhds sigma) ∧
          Measure.map Prod.swap
            (sigma : Measure (State d × State d)) =
            (sigma : Measure (State d × State d)) ∧
          (sigma : Measure (State d × State d)).fst =
            (V.target : Measure (State d)) ∧
          (sigma : Measure (State d × State d)).snd =
            (V.target : Measure (State d)) := by
  obtain ⟨N, hN, hepsilonPos, hepsilonZero, hcost⟩ :=
    exists_positive_vanishing_fixedHorizonOffsetSchedule V h hh
  obtain ⟨sigma, hsigma, subseq, hsubseq, hrwm, heuler,
      hswap, hfst, hsnd⟩ :=
    exists_common_tendsto_subseq_finiteEulerEdgeLaw_finiteRWMEdgeLaw_with_structure
      V (fixedHorizonOffsetStep h N) (fixedHorizonOffsetSteps N)
        (fixedHorizonOffsetEpsilon V h N)
        hepsilonPos hepsilonZero hcost
  exact ⟨N, fixedHorizonOffsetEpsilon V h N, hN,
    hepsilonPos, hepsilonZero, hcost, sigma, hsigma, subseq, hsubseq,
    hrwm, heuler, hswap, hfst, hsnd⟩

end DiscreteTime
end
end UniformRandomMALA
