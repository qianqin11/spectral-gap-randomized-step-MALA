import UniformRandomMALA.Concrete.StationaryVariance
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Pairing the finite stationary variance sequence

The algebra separates increasing sums of positive paired covariances from
the decreasing even covariance sequence. This treats a reversible chain
without a positive-gap assumption.
-/

namespace UniformRandomMALA.Concrete

open Filter Finset
open scoped Topology ENNReal

noncomputable section

def covariancePairSum (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (c (2 * k) + c (2 * k + 1))

def covarianceCesaroVariance (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, covarianceIncrement c k

theorem covariancePairSum_succ (c : ℕ → ℝ) (n : ℕ) :
    covariancePairSum c (n + 1) = covariancePairSum c n + c (2 * n) + c (2 * n + 1) := by
  simp only [covariancePairSum, Finset.sum_range_succ]
  ring

theorem covarianceIncrement_succ (c : ℕ → ℝ) (n : ℕ) :
    covarianceIncrement c (n + 1) = covarianceIncrement c n + 2 * c (n + 1) := by
  simp only [covarianceIncrement, Finset.sum_range_succ]
  ring

theorem covarianceIncrement_even (c : ℕ → ℝ) (n : ℕ) :
    covarianceIncrement c (2 * n) = 2 * covariancePairSum c n - c 0 + 2 * c (2 * n) := by
  induction n with
  | zero => simp [covarianceIncrement, covariancePairSum]; ring
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      covarianceIncrement_succ, covarianceIncrement_succ, ih, covariancePairSum_succ]
    congr 1
    ring

theorem covarianceIncrement_odd (c : ℕ → ℝ) (n : ℕ) :
    covarianceIncrement c (2 * n + 1) = 2 * covariancePairSum c (n + 1) - c 0 := by
  rw [covarianceIncrement_succ, covarianceIncrement_even, covariancePairSum_succ]
  ring

theorem sum_covarianceIncrement_even (c : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), covarianceIncrement c k) =
      4 * (∑ k ∈ Finset.range n, covariancePairSum c k) +
      2 * (∑ k ∈ Finset.range n, c (2 * k)) + 2 * covariancePairSum c n - 2 * n * c 0 := by
  induction n with
  | zero => simp [covariancePairSum]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      covarianceIncrement_even, covarianceIncrement_odd,
      Finset.sum_range_succ, Finset.sum_range_succ, covariancePairSum_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem covarianceCesaroVariance_even (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    covarianceCesaroVariance c (2 * n) =
      2 * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, covariancePairSum c k) +
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, c (2 * k)) +
      (n : ℝ)⁻¹ * covariancePairSum c n - c 0 := by
  rw [covarianceCesaroVariance, sum_covarianceIncrement_even]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hn]
  ring

theorem covarianceCesaroVariance_succ (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    covarianceCesaroVariance c (n + 1) =
      (n : ℝ) / (n + 1) * covarianceCesaroVariance c n +
        covarianceIncrement c n / (n + 1) := by
  simp only [covarianceCesaroVariance, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem covariancePairSum_mono {c : ℕ → ℝ}
    (hpair : ∀ n, 0 ≤ c (2 * n) + c (2 * n + 1)) : Monotone (covariancePairSum c) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [covariancePairSum_succ]
  linarith [hpair n]

theorem covariancePairSum_nonneg {c : ℕ → ℝ}
    (hpair : ∀ n, 0 ≤ c (2 * n) + c (2 * n + 1)) (n : ℕ) :
    0 ≤ covariancePairSum c n :=
  Finset.sum_nonneg fun k _ => hpair k

/-- Convergence on both parity subsequences is convergence of the entire
sequence. This filter form also applies to divergence to positive infinity. -/
theorem tendsto_atTop_of_even_odd {β : Type*} {F : Filter β} {f : ℕ → β}
    (he : Tendsto (fun n => f (2 * n)) atTop F)
    (ho : Tendsto (fun n => f (2 * n + 1)) atTop F) : Tendsto f atTop F := by
  apply Filter.tendsto_def.2
  intro s hs
  obtain ⟨ne, hne⟩ := Filter.eventually_atTop.1 (he.eventually hs)
  obtain ⟨no, hno⟩ := Filter.eventually_atTop.1 (ho.eventually hs)
  refine Filter.eventually_atTop.2 ⟨2 * max ne no, fun n hn => ?_⟩
  have hdiv : max ne no ≤ n / 2 := by omega
  have hnmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hnmod with hm | hm
  · have hid : n = 2 * (n / 2) := by omega
    rw [hid]
    exact hne _ ((le_max_left _ _).trans hdiv)
  · have hid : n = 2 * (n / 2) + 1 := by omega
    rw [hid]
    exact hno _ ((le_max_right _ _).trans hdiv)

theorem covarianceCesaroVariance_even_tendsto {c : ℕ → ℝ} {S l : ℝ}
    (hS : Tendsto (covariancePairSum c) atTop (𝓝 S))
    (hl : Tendsto (fun n => c (2 * n)) atTop (𝓝 l)) :
    Tendsto (fun n => covarianceCesaroVariance c (2 * n)) atTop (𝓝 (2 * S + l - c 0)) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (((hS.cesaro.const_mul 2).add hl.cesaro).add (hinv.mul hS)).sub_const (c 0)
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  exact (covarianceCesaroVariance_even c hn).symm

/-- The paired-covariance decomposition gives a genuine variance limit,
including when the original covariance series does not converge. -/
theorem covarianceCesaroVariance_tendsto {c : ℕ → ℝ} {S l : ℝ}
    (hS : Tendsto (covariancePairSum c) atTop (𝓝 S))
    (hl : Tendsto (fun n => c (2 * n)) atTop (𝓝 l)) :
    Tendsto (covarianceCesaroVariance c) atTop (𝓝 (2 * S + l - c 0)) := by
  have he := covarianceCesaroVariance_even_tendsto hS hl
  apply tendsto_atTop_of_even_odd he
  have hdenom : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith [show (0 : ℝ) ≤ n by positivity])
      tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (2 * (n : ℝ)) / (2 * n + 1)) atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hdenom.const_div_atTop 1)
    simp only [sub_zero] at h
    convert h using 1
    ext n
    have hne : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hi : Tendsto (fun n => covarianceIncrement c (2 * n)) atTop (𝓝 (2 * S - c 0 + 2 * l)) := by
    simpa only [covarianceIncrement_even] using
      ((hS.const_mul 2).sub_const (c 0)).add (hl.const_mul 2)
  have h := (hratio.mul he).add (hi.div_atTop hdenom)
  simp only [one_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  convert (covarianceCesaroVariance_succ c (n := 2 * n) (Nat.mul_ne_zero (by norm_num) hn)).symm using 1
  norm_num

theorem monotone_nonneg_cesaro_atTop {S : ℕ → ℝ} (hmono : Monotone S)
    (hzero : ∀ n, 0 ≤ S n) (hS : Tendsto S atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, S k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hS.eventually (eventually_ge_atTop (2 * max b 0)))
  refine Filter.eventually_atTop.2 ⟨max (2 * N) 1, fun n hn => ?_⟩
  have hNn : N ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hprefix : 0 ≤ ∑ k ∈ Finset.range N, S k := Finset.sum_nonneg fun k _ => hzero k
  have htail : (n - N : ℕ) * (2 * max b 0) ≤ ∑ k ∈ Finset.range (n - N), S (N + k) := by
    calc
      (n - N : ℕ) * (2 * max b 0) =
          ∑ k ∈ Finset.range (n - N), (2 * max b 0) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k _ => (hN N le_rfl).trans (hmono (by omega))
  have hsum : (n : ℝ) * max b 0 ≤ ∑ k ∈ Finset.range n, S k := by
    have hdecomp : (∑ k ∈ Finset.range n, S k) =
        (∑ k ∈ Finset.range N, S k) + ∑ k ∈ Finset.range (n - N), S (N + k) := by
      simpa only [Nat.add_sub_of_le hNn] using Finset.sum_range_add S N (n - N)
    rw [hdecomp]
    rw [Nat.cast_sub hNn] at htail
    have htwon : (2 : ℝ) * N ≤ n := by exact_mod_cast (show 2 * N ≤ n by omega)
    nlinarith [le_max_right b 0]
  calc
    b ≤ max b 0 := le_max_left _ _
    _ ≤ (∑ k ∈ Finset.range n, S k) / n := (le_div_iff₀ hnR).2 (by simpa [mul_comm] using hsum)
    _ = _ := by ring

theorem covarianceCesaroVariance_atTop {c : ℕ → ℝ}
    (hpair : ∀ n, 0 ≤ c (2 * n) + c (2 * n + 1))
    (heven : ∀ n, 0 ≤ c (2 * n))
    (hS : Tendsto (covariancePairSum c) atTop atTop) :
    Tendsto (covarianceCesaroVariance c) atTop atTop := by
  have hces := monotone_nonneg_cesaro_atTop (covariancePairSum_mono hpair)
    (covariancePairSum_nonneg hpair) hS
  have hbase := (hces.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_add
    (tendsto_const_nhds (x := -c 0))
  have he : Tendsto (fun n => covarianceCesaroVariance c (2 * n)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hbase
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [covarianceCesaroVariance_even c hn]
    have hi : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hq := mul_nonneg hi (covariancePairSum_nonneg hpair n)
    have hc := mul_nonneg hi (Finset.sum_nonneg (s := Finset.range n)
      (fun k _ => heven k))
    linarith
  apply tendsto_atTop_of_even_odd he
  have hdenom : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith [show (0 : ℝ) ≤ n by positivity])
      tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (2 * (n : ℝ)) / (2 * n + 1)) atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hdenom.const_div_atTop 1)
    simp only [sub_zero] at h
    convert h using 1
    ext n
    have hne : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hodd := (hratio.pos_mul_atTop zero_lt_one he).atTop_add (hdenom.const_div_atTop (-c 0))
  apply tendsto_atTop_mono' atTop _ hodd
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  have hinc : -c 0 ≤ covarianceIncrement c (2 * n) := by
    rw [covarianceIncrement_even]
    linarith [covariancePairSum_nonneg hpair n, heven n]
  have hdiv := div_le_div_of_nonneg_right hinc (show (0 : ℝ) ≤ 2 * n + 1 by positivity)
  rw [covarianceCesaroVariance_succ c (n := 2 * n) (Nat.mul_ne_zero (by norm_num) hn)]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- A nonnegative finite variance sequence with positive covariance pairs
and decreasing even covariances has a genuine limit in `[0,∞]`. -/
theorem exists_covarianceCesaroVariance_extended_limit {c : ℕ → ℝ}
    (hpair : ∀ n, 0 ≤ c (2 * n) + c (2 * n + 1))
    (heven : ∀ n, 0 ≤ c (2 * n))
    (hanti : Antitone (fun n => c (2 * n))) :
    ∃ σ : ℝ≥0∞, Tendsto (fun n => ENNReal.ofReal (covarianceCesaroVariance c n)) atTop (𝓝 σ) := by
  have hbdd : BddBelow (Set.range (fun n => c (2 * n))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact heven n
  have hl := tendsto_atTop_ciInf hanti hbdd
  rcases tendsto_atTop_of_monotone (covariancePairSum_mono hpair) with hS | ⟨S, hS⟩
  · exact ⟨∞, ENNReal.tendsto_ofReal_atTop.comp (covarianceCesaroVariance_atTop hpair heven hS)⟩
  · exact ⟨_, ENNReal.tendsto_ofReal (covarianceCesaroVariance_tendsto hS hl)⟩

/-- Every finite positive paired-covariance sum gives a lower bound on the
actual extended variance limit. -/
theorem covarianceCesaroVariance_limsup_ge_pairSum {c : ℕ → ℝ}
    (hpair : ∀ n, 0 ≤ c (2 * n) + c (2 * n + 1))
    (heven : ∀ n, 0 ≤ c (2 * n))
    (hanti : Antitone (fun n => c (2 * n))) (N : ℕ) :
    ENNReal.ofReal (2 * covariancePairSum c N - c 0) ≤
      limsup (fun n => ENNReal.ofReal (covarianceCesaroVariance c n)) atTop := by
  have hbdd : BddBelow (Set.range (fun n => c (2 * n))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact heven n
  have hl := tendsto_atTop_ciInf hanti hbdd
  have hl0 : 0 ≤ ⨅ n, c (2 * n) := ge_of_tendsto hl (Filter.Eventually.of_forall heven)
  rcases tendsto_atTop_of_monotone (covariancePairSum_mono hpair) with hS | ⟨S, hS⟩
  · have ht := ENNReal.tendsto_ofReal_atTop.comp (covarianceCesaroVariance_atTop hpair heven hS)
    simp only [Function.comp_def] at ht
    rw [ht.limsup_eq]
    exact le_top
  · have ht := ENNReal.tendsto_ofReal (covarianceCesaroVariance_tendsto hS hl)
    rw [ht.limsup_eq]
    have hNS : covariancePairSum c N ≤ S := ge_of_tendsto hS
      (Filter.eventually_atTop.2 ⟨N, fun n hn => covariancePairSum_mono hpair hn⟩)
    apply ENNReal.ofReal_le_ofReal
    linarith

end
end UniformRandomMALA.Concrete
