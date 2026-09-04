import UniformRandomMALA.Concrete.PotentialCentering
import UniformRandomMALA.DiscreteTime.FiniteEnergy
import UniformRandomMALA.DiscreteTime.FiniteGaussianLikelihood
import UniformRandomMALA.DiscreteTime.GaussianMaximum
import UniformRandomMALA.DiscreteTime.ProductEnergyMGF

/-!
# A concrete finite-Euler energy exponential estimate

This file assembles the deterministic time-summed Gronwall estimate, the
finite Gaussian partial-sum MGF, and the target potential-gap estimate.  All
randomness lives on an ordinary product of the target measure and a finite
product of standard Gaussian measures.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace DiscreteTime

open Concrete Finset

section Pathwise

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Totalized innovation sequence associated with a finite innovation
tuple. -/
def finiteInnovationNat (z : Fin n → State d) (k : ℕ) : State d :=
  if hk : k < n then z ⟨k, hk⟩ else 0

/-- Scaled Gaussian partial sum before Euler time `k`. -/
def finiteGaussianPartialSum (delta : ℝ) (z : Fin n → State d)
    (k : ℕ) : State d :=
  Real.sqrt delta • ∑ j ∈ range k, finiteInnovationNat z j

/-- Frozen-gradient forcing in the telescoped Euler recursion. -/
def finiteFrozenForcing (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) (k : ℕ) : State d :=
  -((k : ℝ) * delta) • V.gradU x0 +
    Real.sqrt 2 • finiteGaussianPartialSum delta z k

@[simp] lemma finiteInnovationNat_of_lt
    (z : Fin n → State d) {k : ℕ} (hk : k < n) :
    finiteInnovationNat z k = z ⟨k, hk⟩ := by
  simp [finiteInnovationNat, hk]

@[simp] lemma finiteInnovationNat_of_not_lt
    (z : Fin n → State d) {k : ℕ} (hk : ¬k < n) :
    finiteInnovationNat z k = 0 := by
  simp [finiteInnovationNat, hk]

/-- Before a valid finite time, the totalized natural-number sum is exactly
the sum over the corresponding strict lower interval in `Fin n`. -/
lemma sum_range_finiteInnovationNat_eq_sum_Iio
    (z : Fin n → State d) (k : Fin n) :
    (∑ j ∈ range (k : ℕ), finiteInnovationNat z j) =
      ∑ i ∈ Finset.Iio k, z i := by
  apply Finset.sum_bij
    (fun j hj => (⟨j, lt_trans (mem_range.mp hj) k.isLt⟩ : Fin n))
  · intro j hj
    simp only [mem_Iio]
    exact Fin.mk_lt_mk.mpr (mem_range.mp hj)
  · intro j₁ hj₁ j₂ hj₂ heq
    exact Fin.ext_iff.mp heq
  · intro i hi
    refine ⟨i, ?_, ?_⟩
    · exact mem_range.mpr (Fin.mk_lt_mk.mp (mem_Iio.mp hi))
    · exact Fin.ext rfl
  · intro j hj
    simp [finiteInnovationNat,
      lt_trans (mem_range.mp hj) k.isLt]

/-- One-step recursion written with the totalized innovation. -/
lemma finiteEulerState_succ_eq_innovationNat
    (delta : ℝ) (x0 : State d) (z : Fin n → State d) (k : ℕ) :
    finiteEulerState V delta x0 z (k + 1) =
      finiteEulerState V delta x0 z k -
        delta • V.gradU (finiteEulerState V delta x0 z k) +
          Real.sqrt (2 * delta) • finiteInnovationNat z k := by
  change finiteEulerStep V delta (finiteEulerState V delta x0 z k)
      (if hk : k < n then z ⟨k, hk⟩ else 0) = _
  simp only [finiteEulerStep, finiteInnovationNat]

/-- Exact telescoping identity for the finite Euler recursion, with the
gradient frozen at the initial point and the residual kept as a finite sum.
-/
lemma finiteEulerState_telescope
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (x0 : State d) (z : Fin n → State d) : ∀ k : ℕ,
    finiteEulerState V delta x0 z k - x0 =
      finiteFrozenForcing V delta x0 z k -
        delta • (∑ j ∈ range k,
          (V.gradU (finiteEulerState V delta x0 z j) - V.gradU x0)) := by
  intro k
  induction k with
  | zero => simp [finiteFrozenForcing, finiteGaussianPartialSum]
  | succ k ih =>
      rw [finiteEulerState_succ_eq_innovationNat]
      simp only [finiteFrozenForcing, finiteGaussianPartialSum] at ih ⊢
      simp only [sum_range_succ, smul_add, smul_smul] at ih ⊢
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show finiteEulerState V delta x0 z k -
          delta • V.gradU (finiteEulerState V delta x0 z k) +
            (Real.sqrt 2 * Real.sqrt delta) • finiteInnovationNat z k - x0 =
          (finiteEulerState V delta x0 z k - x0) -
            delta • V.gradU (finiteEulerState V delta x0 z k) +
              (Real.sqrt 2 * Real.sqrt delta) • finiteInnovationNat z k by
        module]
      rw [ih]
      module

/-- Concrete deterministic energy bound for the explicit finite Euler path.
The Gaussian term is the time-summed square of the scaled innovation partial
sums, not their maximum. -/
theorem finiteEulerEnergy_le_frozenGradient_add_partialSums
    (delta h : ℝ) (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : V.L * h ≤ 1)
    (x0 : State d) (z : Fin n → State d) :
    finiteEulerEnergy V delta x0 z ≤
      8 * (Real.exp 1) ^ 2 * h ^ 3 * ‖V.gradU x0‖ ^ 2 +
        16 * (Real.exp 1) ^ 2 *
          (delta * ∑ k ∈ range n,
            ‖finiteGaussianPartialSum delta z k‖ ^ 2) := by
  let a : ℕ → ℝ := fun k =>
    ‖finiteEulerState V delta x0 z k - x0‖
  let b : ℕ → ℝ := fun k => ‖finiteFrozenForcing V delta x0 z k‖
  let s : ℕ → ℝ := fun k => ‖finiteGaussianPartialSum delta z k‖
  have ha : ∀ k, 0 ≤ a k := fun k => norm_nonneg _
  have hb : ∀ k, 0 ≤ b k := fun k => norm_nonneg _
  have hs : ∀ k, 0 ≤ s k := fun k => norm_nonneg _
  have hstep : ∀ k : ℕ,
      a k ≤ b k + V.L * (delta * ∑ j ∈ range k, a j) := by
    intro k
    apply euler_deviation_le_of_telescoping
      (fun j => finiteEulerState V delta x0 z j) V.gradU
      (finiteFrozenForcing V delta x0 z) V.L delta k hdelta
    · exact finiteEulerState_telescope V delta hdelta x0 z k
    · intro j hj
      have hLip := V.grad_lipschitz.norm_sub_le
        (finiteEulerState V delta x0 z j) x0
      change ‖V.gradU (finiteEulerState V delta x0 z j) - V.gradU x0‖ ≤
        V.L * ‖finiteEulerState V delta x0 z j - x0‖ at hLip
      exact hLip
  have hforcing : ∀ k ∈ range n,
      b k ≤ (k : ℝ) * delta * ‖V.gradU x0‖ + Real.sqrt 2 * s k := by
    intro k hk
    have hkdelta : 0 ≤ (k : ℝ) * delta :=
      mul_nonneg (Nat.cast_nonneg _) hdelta
    change ‖finiteFrozenForcing V delta x0 z k‖ ≤ _
    rw [finiteFrozenForcing]
    calc
      ‖-((k : ℝ) * delta) • V.gradU x0 +
          Real.sqrt 2 • finiteGaussianPartialSum delta z k‖ ≤
          ‖-((k : ℝ) * delta) • V.gradU x0‖ +
            ‖Real.sqrt 2 • finiteGaussianPartialSum delta z k‖ :=
        norm_add_le _ _
      _ = (k : ℝ) * delta * ‖V.gradU x0‖ +
          Real.sqrt 2 * ‖finiteGaussianPartialSum delta z k‖ := by
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hkdelta,
          norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg 2)]
  have henergy := finite_euler_path_energy_le_full_horizon
    a b s V.L ‖V.gradU x0‖ delta h n V.hL.le (norm_nonneg _) hdelta
    ha hb hs hhorizon hsmall hstep hforcing
  unfold finiteEulerEnergy
  change delta * ∑ k : Fin n, (a k) ^ 2 ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun k => (a k) ^ 2) n]
  simpa only [s] using henergy

/-- Joint measurability of the Euler state in its initial point and finite
innovation tuple. -/
lemma measurable_finiteEulerState_uncurry
    (delta : ℝ) (k : ℕ) :
    Measurable (fun p : State d × (Fin n → State d) =>
      finiteEulerState V delta p.1 p.2 k) := by
  induction k with
  | zero => simpa [finiteEulerState] using
      (measurable_fst : Measurable
        (fun p : State d × (Fin n → State d) => p.1))
  | succ k ih =>
      rw [show (fun p : State d × (Fin n → State d) =>
          finiteEulerState V delta p.1 p.2 (k + 1)) =
        fun p => finiteEulerStep V delta
          (finiteEulerState V delta p.1 p.2 k)
          (if hk : k < n then p.2 ⟨k, hk⟩ else 0) by
            funext p
            rw [finiteEulerState]]
      have hz : Measurable (fun p : State d × (Fin n → State d) =>
          if hk : k < n then p.2 ⟨k, hk⟩ else 0) := by
        by_cases hk : k < n
        · simp only [hk, dite_true]
          convert (measurable_pi_apply (⟨k, hk⟩ : Fin n)).comp
            measurable_snd using 1
          funext p
          rfl
        · simp [hk]
      exact (measurable_finiteEulerStep V delta).comp (ih.prodMk hz)

/-- Joint measurability of the concrete finite Euler path energy. -/
lemma measurable_finiteEulerEnergy_uncurry (delta : ℝ) :
    Measurable (fun p : State d × (Fin n → State d) =>
      finiteEulerEnergy V delta p.1 p.2) := by
  unfold finiteEulerEnergy
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro k hk
  exact ((continuous_norm.measurable.comp
    ((measurable_finiteEulerState_uncurry V delta k).sub measurable_fst)).pow_const 2)

end Pathwise

section GaussianEnergy

variable {d n : ℕ}

/-- Exact finite-grid Jensen bound for the energy of the Gaussian partial
sums that appear in the frozen Euler forcing. -/
theorem integral_exp_finiteGaussianPartialSum_energy_le
    (hn : 0 < n) (delta lambda : ℝ) (hdelta : 0 ≤ delta)
    (hThreshold : ∀ k : Fin n,
      (lambda * ((n : ℝ) * delta)) *
        (delta * ((Finset.Iio k).card : ℝ)) < 1 / 2) :
    (∫ z : Fin n → State d,
      Real.exp (lambda * (delta * ∑ k ∈ range n,
        ‖finiteGaussianPartialSum delta z k‖ ^ 2))
      ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) ≤
      (∑ k : Fin n,
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
          (Real.pi / (1 / 2 -
            (lambda * ((n : ℝ) * delta)) *
              (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ) := by
  let ν : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let Z : Fin n → (Fin n → State d) → State d := fun i z => z i
  let S : Fin n → (Fin n → State d) → State d := fun k z =>
    Real.sqrt delta • ∑ i ∈ Finset.Iio k, Z i z
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_pi_apply i
  have hIndep : iIndepFun Z ν := by
    exact iIndepFun_pi (X := fun _ : Fin n => id)
      (fun _ => aemeasurable_id)
  have hLaw : ∀ i, Measure.map (Z i) ν = stdGaussian (State d) := by
    intro i
    exact (measurePreserving_eval
      (fun _ : Fin n => stdGaussian (State d)) i).map_eq
  have hS : ∀ k, Measurable (S k) := by
    intro k
    exact (Finset.measurable_sum (Finset.Iio k)
      fun i _ => hZ i).const_smul (Real.sqrt delta : ℝ)
  have hmap : ∀ k, Measure.map (S k) ν =
      Measure.map (fun z : State d =>
        (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ)) • z)
        (stdGaussian (State d)) := by
    intro k
    exact map_sqrt_smul_finsetSum_eq_scaled_stdGaussian
      ν Z (Finset.Iio k) delta (fun i _ => hZ i)
      (hIndep.restrict _) (fun i _ => hLaw i)
  have hc : ∀ k : Fin n,
      (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ)) ^ 2 =
        delta * ((Finset.Iio k).card : ℝ) := by
    intro k
    rw [mul_pow, Real.sq_sqrt hdelta,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hInt : ∀ k, Integrable (fun z =>
      Real.exp (lambda * ((n : ℝ) * delta) * ‖S k z‖ ^ 2)) ν := by
    intro k
    apply integrable_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
      ν (S k) (hS k) (lambda * ((n : ℝ) * delta))
      (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ))
    · rw [hc k]
      exact hThreshold k
    · exact hmap k
  have hJ := integral_exp_mul_step_sum_le_average_one_time
    ν n hn lambda delta (fun k z => ‖S k z‖ ^ 2)
    (fun k => by fun_prop) hInt
  have hsum : (fun z : Fin n → State d => ∑ k : Fin n, ‖S k z‖ ^ 2) =
      fun z => ∑ k ∈ range n, ‖finiteGaussianPartialSum delta z k‖ ^ 2 := by
    funext z
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k < n := mem_range.mp hk
    simp only [hkn, dite_true]
    change ‖Real.sqrt delta • ∑ i ∈ Finset.Iio (⟨k, hkn⟩ : Fin n), z i‖ ^ 2 = _
    rw [← sum_range_finiteInnovationNat_eq_sum_Iio z ⟨k, hkn⟩]
    rfl
  change (∫ z, Real.exp
      (lambda * (delta * ∑ k ∈ range n,
        ‖finiteGaussianPartialSum delta z k‖ ^ 2)) ∂ν) ≤ _
  have hexponent : (fun z : Fin n → State d =>
      lambda * delta * ∑ k : Fin n, ‖S k z‖ ^ 2) =
      fun z => lambda * (delta * ∑ k ∈ range n,
        ‖finiteGaussianPartialSum delta z k‖ ^ 2) := by
    funext z
    rw [congrFun hsum z]
    ring
  have hexp : (fun z : Fin n → State d =>
      Real.exp (lambda * delta * ∑ k : Fin n, ‖S k z‖ ^ 2)) =
      fun z => Real.exp (lambda * (delta * ∑ k ∈ range n,
        ‖finiteGaussianPartialSum delta z k‖ ^ 2)) := by
    funext z
    rw [congrFun hexponent z]
  rw [hexp] at hJ
  refine hJ.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
    ν (S k) (hS k) (lambda * ((n : ℝ) * delta))
    (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ))
    (by rw [hc k]; exact hThreshold k) (hmap k), hc k]
  rw [finrank_euclideanSpace_fin]

/-- Integrability companion to
`integral_exp_finiteGaussianPartialSum_energy_le`. -/
theorem integrable_exp_finiteGaussianPartialSum_energy
    (hn : 0 < n) (delta lambda : ℝ) (hdelta : 0 ≤ delta)
    (hThreshold : ∀ k : Fin n,
      (lambda * ((n : ℝ) * delta)) *
        (delta * ((Finset.Iio k).card : ℝ)) < 1 / 2) :
    Integrable (fun z : Fin n → State d =>
      Real.exp (lambda * (delta * ∑ k ∈ range n,
        ‖finiteGaussianPartialSum delta z k‖ ^ 2)))
      (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
  let ν : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let Z : Fin n → (Fin n → State d) → State d := fun i z => z i
  let S : Fin n → (Fin n → State d) → State d := fun k z =>
    Real.sqrt delta • ∑ i ∈ Finset.Iio k, Z i z
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_pi_apply i
  have hIndep : iIndepFun Z ν := by
    exact iIndepFun_pi (X := fun _ : Fin n => id)
      (fun _ => aemeasurable_id)
  have hLaw : ∀ i, Measure.map (Z i) ν = stdGaussian (State d) := by
    intro i
    exact (measurePreserving_eval
      (fun _ : Fin n => stdGaussian (State d)) i).map_eq
  have hS : ∀ k, Measurable (S k) := by
    intro k
    exact (Finset.measurable_sum (Finset.Iio k)
      fun i _ => hZ i).const_smul (Real.sqrt delta : ℝ)
  have hmap : ∀ k, Measure.map (S k) ν =
      Measure.map (fun z : State d =>
        (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ)) • z)
        (stdGaussian (State d)) := by
    intro k
    exact map_sqrt_smul_finsetSum_eq_scaled_stdGaussian
      ν Z (Finset.Iio k) delta (fun i _ => hZ i)
      (hIndep.restrict _) (fun i _ => hLaw i)
  have hc : ∀ k : Fin n,
      (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ)) ^ 2 =
        delta * ((Finset.Iio k).card : ℝ) := by
    intro k
    rw [mul_pow, Real.sq_sqrt hdelta,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  let q : Fin n → (Fin n → State d) → ℝ := fun k z =>
    lambda * ((n : ℝ) * delta) * ‖S k z‖ ^ 2
  have hqMeas : ∀ k ∈ (Finset.univ : Finset (Fin n)), Measurable (q k) := by
    intro k _
    exact (measurable_const.mul ((hS k).norm.pow_const 2))
  have hqInt : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun z => Real.exp (q k z)) ν := by
    intro k _
    apply integrable_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
      ν (S k) (hS k) (lambda * ((n : ℝ) * delta))
      (Real.sqrt delta * Real.sqrt ((Finset.Iio k).card : ℝ))
    · rw [hc k]
      exact hThreshold k
    · exact hmap k
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have havg := integrable_exp_finset_average ν
    (Finset.univ : Finset (Fin n)) Finset.univ_nonempty q hqMeas hqInt
  simp only [Finset.card_univ, Fintype.card_fin] at havg
  apply havg.congr
  exact ae_of_all _ fun z => by
    change Real.exp ((∑ k, q k z) / (n : ℝ)) = _
    congr 1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hscale : (∑ k : Fin n, q k z) / (n : ℝ) =
        lambda * delta * ∑ k : Fin n, ‖S k z‖ ^ 2 := by
      change (∑ k, lambda * ((n : ℝ) * delta) * ‖S k z‖ ^ 2) /
        (n : ℝ) = _
      rw [← Finset.mul_sum]
      field_simp
    rw [hscale]
    have hsumz : (∑ k : Fin n, ‖S k z‖ ^ 2) =
        ∑ k ∈ range n, ‖finiteGaussianPartialSum delta z k‖ ^ 2 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k < n := mem_range.mp hk
      simp only [hkn, dite_true]
      change ‖Real.sqrt delta •
        ∑ i ∈ Finset.Iio (⟨k, hkn⟩ : Fin n), z i‖ ^ 2 = _
      rw [← sum_range_finiteInnovationNat_eq_sum_Iio z ⟨k, hkn⟩]
      rfl
    rw [hsumz]
    ring

end GaussianEnergy

section TargetEnergy

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Integrability form of the target gradient-square exponential estimate.
-/
theorem integrable_exp_gradU_norm_sq
    (c : ℝ) (hc : 0 ≤ c) (hsmall : 2 * V.L * c < 1) :
    Integrable (fun x : State d => Real.exp (c * ‖V.gradU x‖ ^ 2))
      (V.target : Measure (State d)) := by
  let s : ℝ := 2 * V.L * c
  have hs : s < 1 := by simpa [s] using hsmall
  have hMajor := V.integrable_exp_potentialGap s hs
  apply hMajor.mono
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (V.continuous_gradU.norm.pow 2))).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hg := V.gradU_norm_sq_le_potentialGap x
      have hcHg := mul_le_mul_of_nonneg_left hg hc
      dsimp [s]
      nlinarith

end TargetEnergy

section ScalarBounds

/-- Elementary reciprocal estimate used to simplify the exact Gaussian and
target MGF factors. -/
lemma inv_one_sub_le_exp_two_mul {u : ℝ}
    (hu0 : 0 ≤ u) (huHalf : u ≤ 1 / 2) :
    (1 - u)⁻¹ ≤ Real.exp (2 * u) := by
  have hden : 0 < 1 - u := by linarith
  have hfrac : u / (1 - u) ≤ 2 * u := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hinvSub : (1 - u)⁻¹ - 1 = u / (1 - u) := by
    field_simp [ne_of_gt hden]
    <;> ring
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at hlog
  rw [hinvSub] at hlog
  calc
    (1 - u)⁻¹ = Real.exp (-Real.log (1 - u)) := by
      rw [Real.exp_neg, Real.exp_log hden]
    _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (hlog.trans hfrac)

/-- Natural powers of the reciprocal estimate. -/
lemma inv_one_sub_pow_le_exp_two_mul (d : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (huHalf : u ≤ 1 / 2) :
    ((1 - u) ^ d)⁻¹ ≤ Real.exp (2 * u * d) := by
  rw [← inv_pow]
  calc
    ((1 - u)⁻¹) ^ d ≤ (Real.exp (2 * u)) ^ d := by
      exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith))
        (inv_one_sub_le_exp_two_mul hu0 huHalf) d
    _ = Real.exp (2 * u * d) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The exact one-time Gaussian square-MGF factor is bounded by an
exponential retaining its linear dependence on the MGF parameter. -/
lemma gaussian_quadratic_factor_le_exp_two_mul {b : ℝ}
    (hb0 : 0 ≤ b) (hbQuarter : b ≤ 1 / 4) :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - b)) ≤ Real.exp (2 * b) := by
  have hden : 0 < 1 / 2 - b := by linarith
  have htwoPi : 0 ≤ 2 * Real.pi := by positivity
  have hquot : 0 ≤ Real.pi / (1 / 2 - b) :=
    div_nonneg Real.pi_pos.le hden.le
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ *
    Real.sqrt (Real.pi / (1 / 2 - b))
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcsq : c ^ 2 = (1 - 2 * b)⁻¹ := by
    dsimp [c]
    rw [mul_pow, inv_pow, Real.sq_sqrt htwoPi, Real.sq_sqrt hquot]
    field_simp [Real.pi_ne_zero, ne_of_gt hden]
    <;> ring
  have hinv : (1 - 2 * b)⁻¹ ≤ Real.exp (4 * b) := by
    convert inv_one_sub_le_exp_two_mul (u := 2 * b) (by positivity) (by linarith) using 1
    ring
  have hexpSq : (Real.exp (2 * b)) ^ 2 = Real.exp (4 * b) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : c ^ 2 ≤ (Real.exp (2 * b)) ^ 2 := by
    rw [hcsq, hexpSq]
    exact hinv
  have hexp0 : 0 ≤ Real.exp (2 * b) := (Real.exp_pos _).le
  nlinarith

/-- Powered form of `gaussian_quadratic_factor_le_exp_two_mul`. -/
lemma gaussian_quadratic_factor_pow_le_exp (d : ℕ) {b : ℝ}
    (hb0 : 0 ≤ b) (hbQuarter : b ≤ 1 / 4) :
    ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - b))) ^ d ≤
      Real.exp (2 * b * d) := by
  calc
    ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - b))) ^ d ≤
        (Real.exp (2 * b)) ^ d := by
      exact pow_le_pow_left₀ (by positivity)
        (gaussian_quadratic_factor_le_exp_two_mul hb0 hbQuarter) d
    _ = Real.exp (2 * b * d) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end ScalarBounds

section Assembly

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Integrability of the finite Euler energy exponential under the exact
target and one-time Gaussian thresholds.  This is stated separately from the
integral estimate because the Bochner integral itself is defined to be zero
for nonintegrable functions. -/
theorem integrable_exp_finiteEulerEnergy_of_thresholds
    (hn : 0 < n) (delta h lambda : ℝ)
    (hdelta : 0 ≤ delta) (hlambda : 0 ≤ lambda)
    (hhorizon : (n : ℝ) * delta = h)
    (hEuler : V.L * h ≤ 1)
    (hTarget :
      2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3)) < 1)
    (hGaussian : ∀ k : Fin n,
      ((lambda * (16 * (Real.exp 1) ^ 2)) *
          ((n : ℝ) * delta)) *
        (delta * ((Finset.Iio k).card : ℝ)) < 1 / 2) :
    Integrable (fun p : State d × (Fin n → State d) =>
      Real.exp (lambda * finiteEulerEnergy V delta p.1 p.2))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) := by
  let ν : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let J : State d × (Fin n → State d) → ℝ := fun p =>
    finiteEulerEnergy V delta p.1 p.2
  let f : State d → ℝ := fun x => ‖V.gradU x‖ ^ 2
  let g : (Fin n → State d) → ℝ := fun z =>
    delta * ∑ k ∈ range n, ‖finiteGaussianPartialSum delta z k‖ ^ 2
  let A : ℝ := 8 * (Real.exp 1) ^ 2 * h ^ 3
  let B : ℝ := 16 * (Real.exp 1) ^ 2
  have hpath : ∀ p : State d × (Fin n → State d),
      J p ≤ A * f p.1 + B * g p.2 := by
    intro p
    have hbound := finiteEulerEnergy_le_frozenGradient_add_partialSums
      V delta h hdelta hhorizon hEuler p.1 p.2
    simpa only [J, A, B, f, g] using hbound
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hh : 0 ≤ h := by rw [← hhorizon]; positivity
    positivity
  have hf : Integrable (fun x => Real.exp (lambda * A * f x))
      (V.target : Measure (State d)) := by
    have := integrable_exp_gradU_norm_sq V (lambda * A)
      (mul_nonneg hlambda hA0) (by simpa [A] using hTarget)
    simpa only [f, mul_assoc] using this
  have hg : Integrable (fun z => Real.exp (lambda * B * g z)) ν := by
    have := integrable_exp_finiteGaussianPartialSum_energy
      (d := d) hn delta (lambda * B) hdelta (by
        intro k
        simpa only [B, mul_assoc] using hGaussian k)
    simpa only [g, mul_assoc] using this
  have hmajor : Integrable (fun p : State d × (Fin n → State d) =>
      Real.exp (lambda * A * f p.1) * Real.exp (lambda * B * g p.2))
      ((V.target : Measure (State d)).prod ν) := hf.mul_prod hg
  have hleftMeas : AEStronglyMeasurable (fun p => Real.exp (lambda * J p))
      ((V.target : Measure (State d)).prod ν) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable.comp_aemeasurable
        (measurable_finiteEulerEnergy_uncurry V delta).aemeasurable
  have hpoint : ∀ p : State d × (Fin n → State d),
      Real.exp (lambda * J p) ≤
        Real.exp (lambda * A * f p.1) * Real.exp (lambda * B * g p.2) := by
    intro p
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left (hpath p) hlambda
    nlinarith
  have hleft : Integrable (fun p => Real.exp (lambda * J p))
      ((V.target : Measure (State d)).prod ν) := by
    apply hmajor.mono hleftMeas
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_of_pos
          (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
      exact hpoint p
  simpa only [J, ν] using hleft

/-- Fully concrete exponential-moment bound for the finite Euler path energy
on the product of the stationary initial law and `n` independent standard
Gaussian innovations.

The two smallness assumptions are exactly those required by the target
gradient-square MGF and by each one-time Gaussian partial-sum MGF. -/
theorem integral_exp_finiteEulerEnergy_le
    (hn : 0 < n) (delta h lambda : ℝ)
    (hdelta : 0 ≤ delta) (hlambda : 0 ≤ lambda)
    (hhorizon : (n : ℝ) * delta = h)
    (hEuler : V.L * h ≤ 1)
    (hTarget :
      2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3)) < 1)
    (hGaussian : ∀ k : Fin n,
      ((lambda * (16 * (Real.exp 1) ^ 2)) *
          ((n : ℝ) * delta)) *
        (delta * ((Finset.Iio k).card : ℝ)) < 1 / 2) :
    (∫ p : State d × (Fin n → State d),
      Real.exp (lambda * finiteEulerEnergy V delta p.1 p.2)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      (((1 - 2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3))) ^ d)⁻¹) *
      ((∑ k : Fin n,
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
          (Real.pi / (1 / 2 -
            ((lambda * (16 * (Real.exp 1) ^ 2)) *
                ((n : ℝ) * delta)) *
              (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ)) := by
  let ν : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let J : State d × (Fin n → State d) → ℝ := fun p =>
    finiteEulerEnergy V delta p.1 p.2
  let f : State d → ℝ := fun x => ‖V.gradU x‖ ^ 2
  let g : (Fin n → State d) → ℝ := fun z =>
    delta * ∑ k ∈ range n, ‖finiteGaussianPartialSum delta z k‖ ^ 2
  let A : ℝ := 8 * (Real.exp 1) ^ 2 * h ^ 3
  let B : ℝ := 16 * (Real.exp 1) ^ 2
  have hpath : ∀ p : State d × (Fin n → State d),
      J p ≤ A * f p.1 + B * g p.2 := by
    intro p
    have hbound := finiteEulerEnergy_le_frozenGradient_add_partialSums
      V delta h hdelta hhorizon hEuler p.1 p.2
    simpa only [J, A, B, f, g] using hbound
  have hJmeas : AEStronglyMeasurable J
      ((V.target : Measure (State d)).prod ν) :=
    (measurable_finiteEulerEnergy_uncurry V delta).aestronglyMeasurable
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hh : 0 ≤ h := by rw [← hhorizon]; positivity
    positivity
  have hB0 : 0 ≤ B := by positivity
  have hf : Integrable (fun x => Real.exp (lambda * A * f x))
      (V.target : Measure (State d)) := by
    have := integrable_exp_gradU_norm_sq V (lambda * A)
      (mul_nonneg hlambda hA0) (by simpa [A] using hTarget)
    simpa only [f, mul_assoc] using this
  have hg : Integrable (fun z => Real.exp (lambda * B * g z)) ν := by
    have := integrable_exp_finiteGaussianPartialSum_energy
      (d := d) hn delta (lambda * B) hdelta (by
        intro k
        simpa only [B, mul_assoc] using hGaussian k)
    simpa only [g, mul_assoc] using this
  have hprod := integral_exp_productEnergy_le
    (V.target : Measure (State d)) ν J f g lambda A B
    hlambda hpath hJmeas hf hg
  have htargetBound :
      (∫ x, Real.exp (lambda * A * f x)
          ∂(V.target : Measure (State d))) ≤
        ((1 - 2 * V.L * (lambda * A)) ^ d)⁻¹ := by
    simpa only [f, mul_assoc] using
      V.integral_exp_gradU_norm_sq_le (lambda * A)
        (mul_nonneg hlambda hA0) (by simpa [A] using hTarget)
  have hgaussianBound :
      (∫ z, Real.exp (lambda * B * g z) ∂ν) ≤
        (∑ k : Fin n,
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
            (Real.pi / (1 / 2 -
              ((lambda * B) * ((n : ℝ) * delta)) *
                (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ) := by
    simpa only [g, mul_assoc] using
      integral_exp_finiteGaussianPartialSum_energy_le
        (d := d) hn delta (lambda * B) hdelta (by
          intro k
          simpa only [B, mul_assoc] using hGaussian k)
  have htargetNonneg :
      0 ≤ ((1 - 2 * V.L * (lambda * A)) ^ d)⁻¹ := by
    apply inv_nonneg.mpr
    apply pow_nonneg
    exact (sub_pos.mpr (by simpa [A] using hTarget)).le
  calc
    (∫ p, Real.exp (lambda * finiteEulerEnergy V delta p.1 p.2)
        ∂(V.target : Measure (State d)).prod
          (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) =
        ∫ p, Real.exp (lambda * J p)
          ∂(V.target : Measure (State d)).prod ν := by rfl
    _ ≤ (∫ x, Real.exp (lambda * A * f x)
          ∂(V.target : Measure (State d))) *
        ∫ z, Real.exp (lambda * B * g z) ∂ν := hprod
    _ ≤ ((1 - 2 * V.L * (lambda * A)) ^ d)⁻¹ *
        ∫ z, Real.exp (lambda * B * g z) ∂ν :=
      mul_le_mul_of_nonneg_right htargetBound (integral_nonneg fun _ => (Real.exp_pos _).le)
    _ ≤ ((1 - 2 * V.L * (lambda * A)) ^ d)⁻¹ *
        ((∑ k : Fin n,
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
            (Real.pi / (1 / 2 -
              ((lambda * B) * ((n : ℝ) * delta)) *
                (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hgaussianBound htargetNonneg
    _ = _ := by rfl

/-- Paper-style consequence of `integral_exp_finiteEulerEnergy_le` with one
dimension-free smallness condition on the MGF parameter.  The exponent is
linear in `lambda`, quadratic in the time horizon, and linear in dimension.
-/
theorem integral_exp_finiteEulerEnergy_le_exp
    (hn : 0 < n) (delta h lambda : ℝ)
    (hdelta : 0 ≤ delta) (hlambda : 0 ≤ lambda)
    (hhorizon : (n : ℝ) * delta = h)
    (hEuler : V.L * h ≤ 1)
    (hsmall : 64 * (Real.exp 1) ^ 2 * lambda * h ^ 2 ≤ 1) :
    (∫ p : State d × (Fin n → State d),
      Real.exp (lambda * finiteEulerEnergy V delta p.1 p.2)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      Real.exp (64 * (Real.exp 1) ^ 2 * lambda * h ^ 2 * d) := by
  let uT : ℝ := 2 * V.L *
    (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3))
  let bMax : ℝ :=
    (lambda * (16 * (Real.exp 1) ^ 2)) * h ^ 2
  let b : Fin n → ℝ := fun k =>
    ((lambda * (16 * (Real.exp 1) ^ 2)) *
        ((n : ℝ) * delta)) *
      (delta * ((Finset.Iio k).card : ℝ))
  have hh : 0 ≤ h := by
    rw [← hhorizon]
    positivity
  have hbase : bMax ≤ 1 / 4 := by
    dsimp [bMax]
    nlinarith
  have hbMax0 : 0 ≤ bMax := by
    dsimp [bMax]
    positivity
  have huT0 : 0 ≤ uT := by
    dsimp [uT]
    exact mul_nonneg (mul_nonneg (by norm_num) V.hL.le)
      (mul_nonneg hlambda (by positivity))
  have huTQuarter : uT ≤ 1 / 4 := by
    calc
      uT = (V.L * h) * bMax := by
        dsimp [uT, bMax]
        ring
      _ ≤ 1 * (1 / 4) :=
        mul_le_mul hEuler hbase hbMax0 (by norm_num)
      _ = 1 / 4 := by norm_num
  have hpartial : ∀ k : Fin n,
      delta * ((Finset.Iio k).card : ℝ) ≤ h := by
    intro k
    have hcard : ((Finset.Iio k).card : ℝ) ≤ (n : ℝ) := by
      rw [Fin.card_Iio]
      exact_mod_cast Nat.le_of_lt k.isLt
    calc
      delta * ((Finset.Iio k).card : ℝ) ≤ delta * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hdelta
      _ = h := by rw [mul_comm, hhorizon]
  have hb0 : ∀ k, 0 ≤ b k := by
    intro k
    dsimp [b]
    positivity
  have hbMax : ∀ k, b k ≤ bMax := by
    intro k
    dsimp [b, bMax]
    rw [hhorizon]
    calc
      (lambda * (16 * Real.exp 1 ^ 2) * h) *
          (delta * ↑(Finset.Iio k).card) ≤
          (lambda * (16 * Real.exp 1 ^ 2) * h) * h :=
        mul_le_mul_of_nonneg_left (hpartial k) (by positivity)
      _ = lambda * (16 * Real.exp 1 ^ 2) * h ^ 2 := by ring
  have hbQuarter : ∀ k, b k ≤ 1 / 4 := fun k =>
    (hbMax k).trans hbase
  have hTarget :
      2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3)) < 1 := by
    change uT < 1
    exact huTQuarter.trans_lt (by norm_num)
  have hGaussian : ∀ k : Fin n,
      ((lambda * (16 * (Real.exp 1) ^ 2)) *
          ((n : ℝ) * delta)) *
        (delta * ((Finset.Iio k).card : ℝ)) < 1 / 2 := by
    intro k
    change b k < 1 / 2
    exact (hbQuarter k).trans_lt (by norm_num)
  have hExact := integral_exp_finiteEulerEnergy_le V hn delta h lambda
    hdelta hlambda hhorizon hEuler hTarget hGaussian
  have htargetFactor :
      (((1 - 2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3))) ^ d)⁻¹) ≤
        Real.exp (2 * uT * d) := by
    simpa only [uT] using
      inv_one_sub_pow_le_exp_two_mul d huT0
        (huTQuarter.trans (by norm_num))
  have hgaussianTerm : ∀ k : Fin n,
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
        (Real.pi / (1 / 2 -
          ((lambda * (16 * (Real.exp 1) ^ 2)) *
              ((n : ℝ) * delta)) *
            (delta * ((Finset.Iio k).card : ℝ))))) ^ d ≤
        Real.exp (2 * bMax * d) := by
    intro k
    calc
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
        (Real.pi / (1 / 2 -
          ((lambda * (16 * (Real.exp 1) ^ 2)) *
              ((n : ℝ) * delta)) *
            (delta * ((Finset.Iio k).card : ℝ))))) ^ d ≤
          Real.exp (2 * b k * d) := by
        exact gaussian_quadratic_factor_pow_le_exp d (hb0 k) (hbQuarter k)
      _ ≤ Real.exp (2 * bMax * d) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbMax k) (by norm_num))
          (Nat.cast_nonneg d)
  have hgaussianAverage :
      ((∑ k : Fin n,
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
          (Real.pi / (1 / 2 -
            ((lambda * (16 * (Real.exp 1) ^ 2)) *
                ((n : ℝ) * delta)) *
              (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ)) ≤
        Real.exp (2 * bMax * d) := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hn)]
    calc
      (∑ k : Fin n,
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
          (Real.pi / (1 / 2 -
            ((lambda * (16 * (Real.exp 1) ^ 2)) *
                ((n : ℝ) * delta)) *
              (delta * ((Finset.Iio k).card : ℝ))))) ^ d) ≤
          ∑ _k : Fin n, Real.exp (2 * bMax * d) :=
        Finset.sum_le_sum fun k _ => hgaussianTerm k
      _ = Real.exp (2 * bMax * d) * (n : ℝ) := by
        simp [mul_comm]
  have hproduct :
      (((1 - 2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3))) ^ d)⁻¹) *
      ((∑ k : Fin n,
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
          (Real.pi / (1 / 2 -
            ((lambda * (16 * (Real.exp 1) ^ 2)) *
                ((n : ℝ) * delta)) *
              (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ)) ≤
        Real.exp (2 * uT * d) * Real.exp (2 * bMax * d) := by
    exact mul_le_mul htargetFactor hgaussianAverage
      (by positivity) (by positivity)
  calc
    (∫ p : State d × (Fin n → State d),
      Real.exp (lambda * finiteEulerEnergy V delta p.1 p.2)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
        (((1 - 2 * V.L *
          (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3))) ^ d)⁻¹) *
        ((∑ k : Fin n,
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
            (Real.pi / (1 / 2 -
              ((lambda * (16 * (Real.exp 1) ^ 2)) *
                  ((n : ℝ) * delta)) *
                (delta * ((Finset.Iio k).card : ℝ))))) ^ d) / (n : ℝ)) :=
      hExact
    _ ≤ Real.exp (2 * uT * d) * Real.exp (2 * bMax * d) := hproduct
    _ = Real.exp ((2 * uT + 2 * bMax) * d) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (64 * (Real.exp 1) ^ 2 * lambda * h ^ 2 * d) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg d)
      calc
        2 * uT + 2 * bMax =
            32 * (Real.exp 1) ^ 2 * lambda * h ^ 2 * (V.L * h + 1) := by
          dsimp [uT, bMax]
          ring
        _ ≤ 32 * (Real.exp 1) ^ 2 * lambda * h ^ 2 * (1 + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        _ = 64 * (Real.exp 1) ^ 2 * lambda * h ^ 2 := by ring

/-- Integrability companion to
`integral_exp_finiteEulerEnergy_le_exp`, under exactly the same hypotheses.
-/
theorem integrable_exp_finiteEulerEnergy
    (hn : 0 < n) (delta h lambda : ℝ)
    (hdelta : 0 ≤ delta) (hlambda : 0 ≤ lambda)
    (hhorizon : (n : ℝ) * delta = h)
    (hEuler : V.L * h ≤ 1)
    (hsmall : 64 * (Real.exp 1) ^ 2 * lambda * h ^ 2 ≤ 1) :
    Integrable (fun p : State d × (Fin n → State d) =>
      Real.exp (lambda * finiteEulerEnergy V delta p.1 p.2))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) := by
  let q : ℝ := 16 * (Real.exp 1) ^ 2 * lambda * h ^ 2
  have hh : 0 ≤ h := by
    rw [← hhorizon]
    positivity
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqQuarter : q ≤ 1 / 4 := by
    dsimp [q]
    nlinarith
  have hTarget :
      2 * V.L *
        (lambda * (8 * (Real.exp 1) ^ 2 * h ^ 3)) < 1 := by
    calc
      2 * V.L * (lambda * (8 * Real.exp 1 ^ 2 * h ^ 3)) =
          (V.L * h) * q := by
        dsimp [q]
        ring
      _ ≤ 1 * (1 / 4) :=
        mul_le_mul hEuler hqQuarter hq0 (by norm_num)
      _ < 1 := by norm_num
  have hpartial : ∀ k : Fin n,
      delta * ((Finset.Iio k).card : ℝ) ≤ h := by
    intro k
    have hcard : ((Finset.Iio k).card : ℝ) ≤ (n : ℝ) := by
      rw [Fin.card_Iio]
      exact_mod_cast Nat.le_of_lt k.isLt
    calc
      delta * ((Finset.Iio k).card : ℝ) ≤ delta * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hdelta
      _ = h := by rw [mul_comm, hhorizon]
  have hGaussian : ∀ k : Fin n,
      ((lambda * (16 * (Real.exp 1) ^ 2)) *
          ((n : ℝ) * delta)) *
        (delta * ((Finset.Iio k).card : ℝ)) < 1 / 2 := by
    intro k
    calc
      ((lambda * (16 * Real.exp 1 ^ 2)) * ((n : ℝ) * delta)) *
          (delta * ↑(Finset.Iio k).card) =
          (lambda * (16 * Real.exp 1 ^ 2) * h) *
            (delta * ↑(Finset.Iio k).card) := by rw [hhorizon]
      _ ≤ (lambda * (16 * Real.exp 1 ^ 2) * h) * h :=
        mul_le_mul_of_nonneg_left (hpartial k) (by positivity)
      _ = q := by
        dsimp [q]
        ring
      _ < 1 / 2 := hqQuarter.trans_lt (by norm_num)
  exact integrable_exp_finiteEulerEnergy_of_thresholds V hn delta h lambda
    hdelta hlambda hhorizon hEuler hTarget hGaussian

end Assembly

end DiscreteTime

end


end UniformRandomMALA
