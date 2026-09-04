import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Deterministic finite-path energy bounds

This file isolates the deterministic part of the finite Euler-chain energy
estimate.  There is no probability theory here.  The main input is a pathwise
comparison of the form

`a k ≤ B + c * ∑ j in range k, a j`.

The conclusions give a pointwise Gronwall bound and a bound for the finite
quadratic energy `delta * ∑ k in range n, (a k)^2`.  In the Euler application,
`a k = ‖X k - X 0‖`, `c = L * delta`, and `B` is the sum of the frozen drift
and Gaussian-walk maxima.
-/

namespace UniformRandomMALA

noncomputable section

namespace DiscreteTime

open Finset

/-- Finite nonnegative-kernel Schur estimate.  It is the elementary
finite-dimensional form of Young's convolution inequality needed below. -/
theorem finset_schur_sq_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℝ) (f : κ → ℝ) (R C : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ K i j)
    (hR : ∀ i ∈ s, ∑ j ∈ t, K i j ≤ R)
    (hC : ∀ j ∈ t, ∑ i ∈ s, K i j ≤ C)
    (hR0 : 0 ≤ R) :
    ∑ i ∈ s, (∑ j ∈ t, K i j * f j) ^ 2 ≤
      R * C * ∑ j ∈ t, (f j) ^ 2 := by
  have hrow : ∀ i ∈ s,
      (∑ j ∈ t, K i j * f j) ^ 2 ≤
        R * ∑ j ∈ t, K i j * (f j) ^ 2 := by
    intro i hi
    have hcs : (∑ j ∈ t, K i j * f j) ^ 2 ≤
        (∑ j ∈ t, K i j) * ∑ j ∈ t, K i j * (f j) ^ 2 := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul t
      · exact fun j hj ↦ hK i hi j hj
      · exact fun j hj ↦ mul_nonneg (hK i hi j hj) (sq_nonneg (f j))
      · intro j hj
        ring_nf
        exact le_rfl
    calc
      (∑ j ∈ t, K i j * f j) ^ 2 ≤
          (∑ j ∈ t, K i j) * ∑ j ∈ t, K i j * (f j) ^ 2 := hcs
      _ ≤ R * ∑ j ∈ t, K i j * (f j) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (hR i hi)
          (sum_nonneg fun j hj ↦ mul_nonneg (hK i hi j hj) (sq_nonneg (f j)))
  calc
    ∑ i ∈ s, (∑ j ∈ t, K i j * f j) ^ 2 ≤
        ∑ i ∈ s, R * ∑ j ∈ t, K i j * (f j) ^ 2 :=
      sum_le_sum hrow
    _ = R * ∑ j ∈ t, (∑ i ∈ s, K i j) * (f j) ^ 2 := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [sum_mul]
    _ ≤ R * ∑ j ∈ t, C * (f j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hR0
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hC j hj) (sq_nonneg (f j))
    _ = R * C * ∑ j ∈ t, (f j) ^ 2 := by
      rw [← mul_sum]
      ring

/-- Explicit convolution solution of an affine one-step recursion. -/
theorem affine_recursion_convolution
    (s b : ℕ → ℝ) (q : ℝ)
    (hq : 0 ≤ q)
    (hs0 : s 0 ≤ 0)
    (hstep : ∀ k : ℕ, s (k + 1) ≤ q * s k + b k) :
    ∀ k : ℕ, s k ≤ ∑ j ∈ range k, q ^ (k - 1 - j) * b j := by
  intro k
  induction k with
  | zero => simpa using hs0
  | succ k ih =>
      have hmul := mul_le_mul_of_nonneg_left ih hq
      calc
        s (k + 1) ≤ q * s k + b k := hstep k
        _ ≤ q * (∑ j ∈ range k, q ^ (k - 1 - j) * b j) + b k :=
          by simpa [add_comm] using add_le_add_right hmul (b k)
        _ = ∑ j ∈ range (k + 1), q ^ (k + 1 - 1 - j) * b j := by
          rw [sum_range_succ, mul_sum]
          congr 1
          · apply sum_congr rfl
            intro j hj
            have hjk : j < k := mem_range.mp hj
            have hexp : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
            rw [hexp, pow_succ]
            ring
          · simp

/-- Explicit convolution form of the cumulative-sum Gronwall comparison. -/
theorem discrete_gronwall_convolution
    (a b : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hstep : ∀ k : ℕ, a k ≤ b k + c * ∑ j ∈ range k, a j) :
    ∀ k : ℕ, a k ≤ b k +
      c * ∑ j ∈ range k, (1 + c) ^ (k - 1 - j) * b j := by
  let s : ℕ → ℝ := fun k ↦ ∑ j ∈ range k, a j
  have hs0 : s 0 ≤ 0 := by simp [s]
  have hs_step : ∀ k : ℕ, s (k + 1) ≤ (1 + c) * s k + b k := by
    intro k
    have hk := hstep k
    dsimp [s] at hk ⊢
    rw [sum_range_succ]
    nlinarith
  have hs := affine_recursion_convolution s b (1 + c)
    (by positivity) hs0 hs_step
  intro k
  have hmul := mul_le_mul_of_nonneg_left (hs k) hc
  dsimp [s] at hmul
  exact (hstep k).trans (by simpa [add_comm] using add_le_add_right hmul (b k))

/-- Extending a sum from `range k` to `range n` by zero, when `k ≤ n`. -/
theorem sum_range_ite_lt
    (f : ℕ → ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (∑ j ∈ range n, if j < k then f j else 0) = ∑ j ∈ range k, f j := by
  calc
    (∑ j ∈ range n, if j < k then f j else 0) =
        ∑ j ∈ range k, if j < k then f j else 0 := by
      symm
      apply sum_subset (range_mono hkn)
      intro j hjn hjk
      have hnot : ¬j < k := by simpa using hjk
      simp [hnot]
    _ = ∑ j ∈ range k, f j := by
      apply sum_congr rfl
      intro j hj
      simp [mem_range.mp hj]

/-- The lower-triangular kernel in the explicit Gronwall convolution. -/
def gronwallKernel (c : ℝ) (k j : ℕ) : ℝ :=
  if j < k then c * (1 + c) ^ (k - 1 - j) else 0

theorem gronwallKernel_nonneg
    (c : ℝ) (hc : 0 ≤ c) (k j : ℕ) :
    0 ≤ gronwallKernel c k j := by
  simp only [gronwallKernel]
  split_ifs
  · positivity
  · exact le_rfl

/-- Every entry of the finite Volterra kernel has a uniform elementary
bound. -/
theorem gronwallKernel_le
    (c : ℝ) (n k j : ℕ) (hc : 0 ≤ c) (hk : k < n) :
    gronwallKernel c k j ≤ c * (1 + c) ^ n := by
  by_cases hjk : j < k
  · rw [gronwallKernel, if_pos hjk]
    apply mul_le_mul_of_nonneg_left _ hc
    apply pow_le_pow_right₀ (by linarith)
    omega
  · rw [gronwallKernel, if_neg hjk]
    positivity

/-- Row and column sums of the finite Volterra kernel are at most
`(1+c)^n` under the small-horizon condition `n*c ≤ 1`.  This deliberately
uses a coarse entrywise bound; no geometric-series division is needed. -/
theorem gronwallKernel_sum_le
    (c : ℝ) (n : ℕ) (hc : 0 ≤ c) (hsmall : (n : ℝ) * c ≤ 1) :
    (∀ k ∈ range n,
      ∑ j ∈ range n, gronwallKernel c k j ≤ (1 + c) ^ n) ∧
    (∀ j ∈ range n,
      ∑ k ∈ range n, gronwallKernel c k j ≤ (1 + c) ^ n) := by
  have hentry : ∀ k ∈ range n, ∀ j ∈ range n,
      gronwallKernel c k j ≤ c * (1 + c) ^ n := by
    intro k hk j hj
    exact gronwallKernel_le c n k j hc (mem_range.mp hk)
  constructor
  · intro k hk
    calc
      ∑ j ∈ range n, gronwallKernel c k j ≤
          ∑ _j ∈ range n, c * (1 + c) ^ n :=
        sum_le_sum (fun j hj ↦ hentry k hk j hj)
      _ = ((n : ℝ) * c) * (1 + c) ^ n := by simp; ring
      _ ≤ 1 * (1 + c) ^ n :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (1 + c) ^ n := one_mul _
  · intro j hj
    calc
      ∑ k ∈ range n, gronwallKernel c k j ≤
          ∑ _k ∈ range n, c * (1 + c) ^ n :=
        sum_le_sum (fun k hk ↦ hentry k hk j hj)
      _ = ((n : ℝ) * c) * (1 + c) ^ n := by simp; ring
      _ ≤ 1 * (1 + c) ^ n :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (1 + c) ^ n := one_mul _

/-- The zero-extended kernel sum is exactly the convolution appearing in
`discrete_gronwall_convolution`. -/
theorem gronwallKernel_sum_mul_eq
    (b : ℕ → ℝ) (c : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (∑ j ∈ range n, gronwallKernel c k j * b j) =
      c * ∑ j ∈ range k, (1 + c) ^ (k - 1 - j) * b j := by
  calc
    (∑ j ∈ range n, gronwallKernel c k j * b j) =
        ∑ j ∈ range n,
          if j < k then c * ((1 + c) ^ (k - 1 - j) * b j) else 0 := by
      apply sum_congr rfl
      intro j hj
      by_cases hjk : j < k
      · simp [gronwallKernel, hjk]
        ring
      · simp [gronwallKernel, hjk]
    _ = ∑ j ∈ range k, c * ((1 + c) ^ (k - 1 - j) * b j) :=
      sum_range_ite_lt
        (fun j ↦ c * ((1 + c) ^ (k - 1 - j) * b j)) hkn
    _ = c * ∑ j ∈ range k, (1 + c) ^ (k - 1 - j) * b j := by
      rw [mul_sum]

/-- `ℓ²` bound for the finite lower-triangular Gronwall convolution. -/
theorem gronwall_convolution_sq_sum_le
    (b : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hsmall : (n : ℝ) * c ≤ 1) :
    ∑ k ∈ range n,
        (∑ j ∈ range n, gronwallKernel c k j * b j) ^ 2 ≤
      (1 + c) ^ n * (1 + c) ^ n * ∑ j ∈ range n, (b j) ^ 2 := by
  obtain ⟨hrow, hcol⟩ := gronwallKernel_sum_le c n hc hsmall
  exact finset_schur_sq_le (range n) (range n)
    (gronwallKernel c) b ((1 + c) ^ n) ((1 + c) ^ n)
    (fun i hi j hj ↦ gronwallKernel_nonneg c hc i j)
    hrow hcol (by positivity)

/-- Young/Gronwall bound for the full path.  Unlike a maximum estimate, this
controls the time-summed square directly. -/
theorem discrete_gronwall_sum_sq_le
    (a b : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (ha : ∀ k : ℕ, 0 ≤ a k)
    (hb : ∀ k : ℕ, 0 ≤ b k)
    (hsmall : (n : ℝ) * c ≤ 1)
    (hstep : ∀ k : ℕ, a k ≤ b k + c * ∑ j ∈ range k, a j) :
    ∑ k ∈ range n, (a k) ^ 2 ≤
      2 * (1 + (1 + c) ^ n * (1 + c) ^ n) *
        ∑ k ∈ range n, (b k) ^ 2 := by
  let v : ℕ → ℝ := fun k ↦
    ∑ j ∈ range n, gronwallKernel c k j * b j
  have hv_nonneg : ∀ k : ℕ, 0 ≤ v k := by
    intro k
    exact sum_nonneg fun j hj ↦
      mul_nonneg (gronwallKernel_nonneg c hc k j) (hb j)
  have hav : ∀ k ∈ range n, a k ≤ b k + v k := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt (mem_range.mp hk)
    calc
      a k ≤ b k + c * ∑ j ∈ range k,
          (1 + c) ^ (k - 1 - j) * b j :=
        discrete_gronwall_convolution a b c hc hstep k
      _ = b k + v k := by
        change b k + c * ∑ j ∈ range k,
            (1 + c) ^ (k - 1 - j) * b j =
          b k + ∑ j ∈ range n, gronwallKernel c k j * b j
        rw [gronwallKernel_sum_mul_eq b c hk_le]
  have hpoint : ∀ k ∈ range n,
      (a k) ^ 2 ≤ 2 * (b k) ^ 2 + 2 * (v k) ^ 2 := by
    intro k hk
    have hsquare := (sq_le_sq₀ (ha k)
      (add_nonneg (hb k) (hv_nonneg k))).2 (hav k hk)
    nlinarith [sq_nonneg (b k - v k)]
  have hconv : ∑ k ∈ range n, (v k) ^ 2 ≤
      (1 + c) ^ n * (1 + c) ^ n *
        ∑ j ∈ range n, (b j) ^ 2 := by
    simpa only [v] using gronwall_convolution_sq_sum_le b c n hc hsmall
  calc
    ∑ k ∈ range n, (a k) ^ 2 ≤
        ∑ k ∈ range n, (2 * (b k) ^ 2 + 2 * (v k) ^ 2) :=
      sum_le_sum hpoint
    _ = 2 * (∑ k ∈ range n, (b k) ^ 2) +
        2 * (∑ k ∈ range n, (v k) ^ 2) := by
      simp_rw [sum_add_distrib, ← mul_sum]
    _ ≤ 2 * (∑ k ∈ range n, (b k) ^ 2) +
        2 * ((1 + c) ^ n * (1 + c) ^ n *
          ∑ k ∈ range n, (b k) ^ 2) := by gcongr
    _ = 2 * (1 + (1 + c) ^ n * (1 + c) ^ n) *
        ∑ k ∈ range n, (b k) ^ 2 := by ring

/-- Universal-constant version of `discrete_gronwall_sum_sq_le`. -/
theorem discrete_gronwall_sum_sq_le_exp_one
    (a b : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (ha : ∀ k : ℕ, 0 ≤ a k)
    (hb : ∀ k : ℕ, 0 ≤ b k)
    (hsmall : (n : ℝ) * c ≤ 1)
    (hstep : ∀ k : ℕ, a k ≤ b k + c * ∑ j ∈ range k, a j) :
    ∑ k ∈ range n, (a k) ^ 2 ≤
      4 * (Real.exp 1) ^ 2 * ∑ k ∈ range n, (b k) ^ 2 := by
  have hbase : 1 + c ≤ Real.exp c := by
    simpa [add_comm] using Real.add_one_le_exp c
  have hpow : (1 + c) ^ n ≤ (Real.exp c) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hq : (1 + c) ^ n ≤ Real.exp 1 := by
    calc
      (1 + c) ^ n ≤ (Real.exp c) ^ n := hpow
      _ = Real.exp ((n : ℝ) * c) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp 1 := (Real.exp_le_exp).2 hsmall
  have hq0 : 0 ≤ (1 + c) ^ n := by positivity
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hqq : (1 + c) ^ n * (1 + c) ^ n ≤
      Real.exp 1 * Real.exp 1 :=
    mul_le_mul hq hq hq0 he0
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcoeff : 2 * (1 + (1 + c) ^ n * (1 + c) ^ n) ≤
      4 * (Real.exp 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp 1 - 1)]
  calc
    ∑ k ∈ range n, (a k) ^ 2 ≤
        2 * (1 + (1 + c) ^ n * (1 + c) ^ n) *
          ∑ k ∈ range n, (b k) ^ 2 :=
      discrete_gronwall_sum_sq_le a b c n hc ha hb hsmall hstep
    _ ≤ 4 * (Real.exp 1) ^ 2 * ∑ k ∈ range n, (b k) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff
        (sum_nonneg fun k hk ↦ sq_nonneg (b k))

/-- Finite Hardy-type estimate for cumulative sums.  This is the key to the
short absorption proof of the Euler energy bound. -/
theorem cumulative_sum_sq_energy_le
    (a : ℕ → ℝ) (delta h : ℝ) (n : ℕ)
    (hdelta : 0 ≤ delta) (hhorizon : (n : ℝ) * delta = h) :
    delta * ∑ k ∈ range n, (delta * ∑ j ∈ range k, a j) ^ 2 ≤
      h ^ 2 * (delta * ∑ k ∈ range n, (a k) ^ 2) := by
  have htotal : 0 ≤ ∑ j ∈ range n, (a j) ^ 2 :=
    sum_nonneg fun j hj ↦ sq_nonneg (a j)
  have hh : 0 ≤ h := by rw [← hhorizon]; positivity
  have hpoint : ∀ k ∈ range n,
      (delta * ∑ j ∈ range k, a j) ^ 2 ≤
        h * (delta * ∑ j ∈ range n, (a j) ^ 2) := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt (mem_range.mp hk)
    have hcs0 := sum_mul_sq_le_sq_mul_sq (range k)
      (fun _j : ℕ ↦ (1 : ℝ)) a
    have hcs : (∑ j ∈ range k, a j) ^ 2 ≤
        (k : ℝ) * ∑ j ∈ range k, (a j) ^ 2 := by
      simpa using hcs0
    have hsubset : ∑ j ∈ range k, (a j) ^ 2 ≤
        ∑ j ∈ range n, (a j) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (range_mono hk_le)
        (fun j hjn hjk ↦ sq_nonneg (a j))
    have hcs_total : (∑ j ∈ range k, a j) ^ 2 ≤
        (k : ℝ) * ∑ j ∈ range n, (a j) ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_left hsubset (Nat.cast_nonneg k))
    have hktime : (k : ℝ) * delta ≤ h := by
      rw [← hhorizon]
      exact mul_le_mul_of_nonneg_right ((Nat.cast_le).2 hk_le) hdelta
    calc
      (delta * ∑ j ∈ range k, a j) ^ 2 =
          delta ^ 2 * (∑ j ∈ range k, a j) ^ 2 := by ring
      _ ≤ delta ^ 2 *
          ((k : ℝ) * ∑ j ∈ range n, (a j) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs_total (sq_nonneg delta)
      _ = ((k : ℝ) * delta) *
          (delta * ∑ j ∈ range n, (a j) ^ 2) := by ring
      _ ≤ h * (delta * ∑ j ∈ range n, (a j) ^ 2) :=
        mul_le_mul_of_nonneg_right hktime (mul_nonneg hdelta htotal)
  calc
    delta * ∑ k ∈ range n, (delta * ∑ j ∈ range k, a j) ^ 2 ≤
        delta * ∑ _k ∈ range n,
          h * (delta * ∑ j ∈ range n, (a j) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hpoint) hdelta
    _ = h ^ 2 * (delta * ∑ k ∈ range n, (a k) ^ 2) := by
      simp
      calc
        delta * ((n : ℝ) * (h * (delta * ∑ j ∈ range n, (a j) ^ 2))) =
            ((n : ℝ) * delta) *
              (h * (delta * ∑ j ∈ range n, (a j) ^ 2)) := by ring
        _ = h * (h * (delta * ∑ j ∈ range n, (a j) ^ 2)) := by
          rw [hhorizon]
        _ = h ^ 2 * (delta * ∑ j ∈ range n, (a j) ^ 2) := by ring

/-- Absorption form of the finite Euler energy estimate.  It avoids both a
path maximum and an explicit convolution estimate. -/
theorem finite_energy_absorption
    (a b : ℕ → ℝ) (L delta h : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hdelta : 0 ≤ delta)
    (ha : ∀ k : ℕ, 0 ≤ a k) (hb : ∀ k : ℕ, 0 ≤ b k)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : L * h ≤ 1 / 2)
    (hstep : ∀ k : ℕ,
      a k ≤ b k + L * (delta * ∑ j ∈ range k, a j)) :
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
      4 * (delta * ∑ k ∈ range n, (b k) ^ 2) := by
  let J : ℝ := delta * ∑ k ∈ range n, (a k) ^ 2
  let B : ℝ := delta * ∑ k ∈ range n, (b k) ^ 2
  let C : ℝ := delta * ∑ k ∈ range n,
    (delta * ∑ j ∈ range k, a j) ^ 2
  have hJ0 : 0 ≤ J := by
    exact mul_nonneg hdelta (sum_nonneg fun k hk ↦ sq_nonneg (a k))
  have hB0 : 0 ≤ B := by
    exact mul_nonneg hdelta (sum_nonneg fun k hk ↦ sq_nonneg (b k))
  have hC0 : 0 ≤ C := by
    exact mul_nonneg hdelta (sum_nonneg fun k hk ↦ sq_nonneg _)
  have hpoint : ∀ k ∈ range n,
      (a k) ^ 2 ≤ 2 * (b k) ^ 2 +
        2 * L ^ 2 * (delta * ∑ j ∈ range k, a j) ^ 2 := by
    intro k hk
    have hcum : 0 ≤ delta * ∑ j ∈ range k, a j :=
      mul_nonneg hdelta (sum_nonneg fun j hj ↦ ha j)
    have hupper0 : 0 ≤ b k + L * (delta * ∑ j ∈ range k, a j) :=
      add_nonneg (hb k) (mul_nonneg hL hcum)
    have hsquare := (sq_le_sq₀ (ha k) hupper0).2 (hstep k)
    nlinarith [sq_nonneg (b k - L * (delta * ∑ j ∈ range k, a j))]
  have hJB : J ≤ 2 * B + 2 * L ^ 2 * C := by
    dsimp [J, B, C]
    calc
      delta * ∑ k ∈ range n, (a k) ^ 2 ≤
          delta * ∑ k ∈ range n,
            (2 * (b k) ^ 2 +
              2 * L ^ 2 * (delta * ∑ j ∈ range k, a j) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hpoint) hdelta
      _ = 2 * (delta * ∑ k ∈ range n, (b k) ^ 2) +
          2 * L ^ 2 *
            (delta * ∑ k ∈ range n,
              (delta * ∑ j ∈ range k, a j) ^ 2) := by
        simp_rw [sum_add_distrib, ← mul_sum]
        ring
  have hC : C ≤ h ^ 2 * J := by
    dsimp [C, J]
    exact cumulative_sum_sq_energy_le a delta h n hdelta hhorizon
  have hJL : J ≤ 2 * B + 2 * L ^ 2 * h ^ 2 * J := by
    calc
      J ≤ 2 * B + 2 * L ^ 2 * C := hJB
      _ ≤ 2 * B + 2 * L ^ 2 * (h ^ 2 * J) := by
        gcongr
      _ = 2 * B + 2 * L ^ 2 * h ^ 2 * J := by ring
  have hh : 0 ≤ h := by rw [← hhorizon]; positivity
  have hcoef : 2 * L ^ 2 * h ^ 2 ≤ 1 / 2 := by
    have hLh0 : 0 ≤ L * h := mul_nonneg hL hh
    nlinarith [sq_nonneg (L * h - 1 / 2)]
  have habsorb : J ≤ 2 * B + (1 / 2) * J := by
    calc
      J ≤ 2 * B + 2 * L ^ 2 * h ^ 2 * J := hJL
      _ ≤ 2 * B + (1 / 2) * J := by
        have hz := mul_le_mul_of_nonneg_right hcoef hJ0
        linarith
  dsimp [J, B] at habsorb ⊢
  nlinarith

/-- Quadratic-energy bound for the frozen-drift forcing
`k*delta*G + sqrt 2 * s k`. -/
theorem frozen_forcing_energy_le
    (b s : ℕ → ℝ) (G delta h : ℝ) (n : ℕ)
    (hG : 0 ≤ G) (hdelta : 0 ≤ delta)
    (hb : ∀ k : ℕ, 0 ≤ b k) (hs : ∀ k : ℕ, 0 ≤ s k)
    (hhorizon : (n : ℝ) * delta = h)
    (hbound : ∀ k ∈ range n,
      b k ≤ (k : ℝ) * delta * G + Real.sqrt 2 * s k) :
    delta * ∑ k ∈ range n, (b k) ^ 2 ≤
      2 * h ^ 3 * G ^ 2 +
        4 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by
  have hh : 0 ≤ h := by rw [← hhorizon]; positivity
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hpoint : ∀ k ∈ range n,
      (b k) ^ 2 ≤ 2 * (h * G) ^ 2 + 4 * (s k) ^ 2 := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt (mem_range.mp hk)
    have hktime : (k : ℝ) * delta ≤ h := by
      rw [← hhorizon]
      exact mul_le_mul_of_nonneg_right ((Nat.cast_le).2 hk_le) hdelta
    have hdrift : 0 ≤ (k : ℝ) * delta * G := by positivity
    have hnoise : 0 ≤ Real.sqrt 2 * s k := mul_nonneg hsqrt (hs k)
    have hsum : 0 ≤ (k : ℝ) * delta * G + Real.sqrt 2 * s k :=
      add_nonneg hdrift hnoise
    have hbsq := (sq_le_sq₀ (hb k) hsum).2 (hbound k hk)
    have hdrift_le : (k : ℝ) * delta * G ≤ h * G :=
      mul_le_mul_of_nonneg_right hktime hG
    have hdrift_sq := (sq_le_sq₀ hdrift (mul_nonneg hh hG)).2 hdrift_le
    calc
      (b k) ^ 2 ≤
          ((k : ℝ) * delta * G + Real.sqrt 2 * s k) ^ 2 := hbsq
      _ ≤ 2 * ((k : ℝ) * delta * G) ^ 2 +
          2 * (Real.sqrt 2 * s k) ^ 2 := by
        nlinarith [sq_nonneg ((k : ℝ) * delta * G - Real.sqrt 2 * s k)]
      _ ≤ 2 * (h * G) ^ 2 + 2 * (Real.sqrt 2 * s k) ^ 2 := by
        gcongr
      _ = 2 * (h * G) ^ 2 + 4 * (s k) ^ 2 := by
        simp_rw [mul_pow]
        rw [hsqrt_sq]
        ring
  calc
    delta * ∑ k ∈ range n, (b k) ^ 2 ≤
        delta * ∑ k ∈ range n,
          (2 * (h * G) ^ 2 + 4 * (s k) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hpoint) hdelta
    _ = 2 * h ^ 3 * G ^ 2 +
        4 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by
      simp_rw [sum_add_distrib, ← mul_sum]
      simp
      calc
        delta * (2 * ((n : ℝ) * (h * G) ^ 2) +
            4 * ∑ k ∈ range n, (s k) ^ 2) =
          ((n : ℝ) * delta) * (2 * (h * G) ^ 2) +
            4 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by ring
        _ = h * (2 * (h * G) ^ 2) +
            4 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by
          rw [hhorizon]
        _ = 2 * h ^ 3 * G ^ 2 +
            4 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by ring

/-- Complete deterministic estimate used by the finite Euler proof.  The
random-walk input has been reduced to its time-averaged square; no maximum
appears. -/
theorem finite_euler_path_energy_le
    (a b s : ℕ → ℝ) (L G delta h : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (hdelta : 0 ≤ delta)
    (ha : ∀ k : ℕ, 0 ≤ a k) (hb : ∀ k : ℕ, 0 ≤ b k)
    (hs : ∀ k : ℕ, 0 ≤ s k)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : L * h ≤ 1 / 2)
    (hstep : ∀ k : ℕ,
      a k ≤ b k + L * (delta * ∑ j ∈ range k, a j))
    (hforcing : ∀ k ∈ range n,
      b k ≤ (k : ℝ) * delta * G + Real.sqrt 2 * s k) :
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
      8 * h ^ 3 * G ^ 2 +
        16 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by
  calc
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
        4 * (delta * ∑ k ∈ range n, (b k) ^ 2) :=
      finite_energy_absorption a b L delta h n hL hdelta ha hb
        hhorizon hsmall hstep
    _ ≤ 4 * (2 * h ^ 3 * G ^ 2 +
        4 * (delta * ∑ k ∈ range n, (s k) ^ 2)) := by
      gcongr
      exact frozen_forcing_energy_le b s G delta h n hG hdelta hb hs
        hhorizon hforcing
    _ = 8 * h ^ 3 * G ^ 2 +
        16 * (delta * ∑ k ∈ range n, (s k) ^ 2) := by ring

/-- Full-horizon version under the paper's assumption `L*h ≤ 1`.  This uses
the finite Schur/convolution estimate rather than absorption, and hence does
not lose a factor two in the admissible horizon. -/
theorem finite_euler_path_energy_le_full_horizon
    (a b s : ℕ → ℝ) (L G delta h : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (hdelta : 0 ≤ delta)
    (ha : ∀ k : ℕ, 0 ≤ a k) (hb : ∀ k : ℕ, 0 ≤ b k)
    (hs : ∀ k : ℕ, 0 ≤ s k)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : L * h ≤ 1)
    (hstep : ∀ k : ℕ,
      a k ≤ b k + L * (delta * ∑ j ∈ range k, a j))
    (hforcing : ∀ k ∈ range n,
      b k ≤ (k : ℝ) * delta * G + Real.sqrt 2 * s k) :
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
      8 * (Real.exp 1) ^ 2 * h ^ 3 * G ^ 2 +
        16 * (Real.exp 1) ^ 2 *
          (delta * ∑ k ∈ range n, (s k) ^ 2) := by
  have hc : 0 ≤ L * delta := mul_nonneg hL hdelta
  have hcsmall : (n : ℝ) * (L * delta) ≤ 1 := by
    calc
      (n : ℝ) * (L * delta) = L * ((n : ℝ) * delta) := by ring
      _ = L * h := by rw [hhorizon]
      _ ≤ 1 := hsmall
  have hstep' : ∀ k : ℕ,
      a k ≤ b k + (L * delta) * ∑ j ∈ range k, a j := by
    intro k
    simpa [mul_assoc] using hstep k
  calc
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
        delta * (4 * (Real.exp 1) ^ 2 *
          ∑ k ∈ range n, (b k) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (discrete_gronwall_sum_sq_le_exp_one a b (L * delta) n
          hc ha hb hcsmall hstep') hdelta
    _ = 4 * (Real.exp 1) ^ 2 *
        (delta * ∑ k ∈ range n, (b k) ^ 2) := by ring
    _ ≤ 4 * (Real.exp 1) ^ 2 *
        (2 * h ^ 3 * G ^ 2 +
          4 * (delta * ∑ k ∈ range n, (s k) ^ 2)) := by
      gcongr
      exact frozen_forcing_energy_le b s G delta h n hG hdelta hb hs
        hhorizon hforcing
    _ = 8 * (Real.exp 1) ^ 2 * h ^ 3 * G ^ 2 +
        16 * (Real.exp 1) ^ 2 *
          (delta * ∑ k ∈ range n, (s k) ^ 2) := by ring

/-- Normed-space bridge from the telescoped Euler identity to the scalar
recurrence required by `finite_energy_absorption`. -/
theorem euler_deviation_le_of_telescoping
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (g : E → E) (forcing : ℕ → E)
    (L delta : ℝ) (k : ℕ)
    (hdelta : 0 ≤ delta)
    (htelescope :
      x k - x 0 = forcing k -
        delta • (∑ j ∈ range k, (g (x j) - g (x 0))))
    (hlip : ∀ j ∈ range k,
      ‖g (x j) - g (x 0)‖ ≤ L * ‖x j - x 0‖) :
    ‖x k - x 0‖ ≤ ‖forcing k‖ +
      L * (delta * ∑ j ∈ range k, ‖x j - x 0‖) := by
  have hnormsum :
      ‖∑ j ∈ range k, (g (x j) - g (x 0))‖ ≤
        ∑ j ∈ range k, ‖g (x j) - g (x 0)‖ :=
    norm_sum_le (range k) fun j ↦ g (x j) - g (x 0)
  have hlipsum : ∑ j ∈ range k, ‖g (x j) - g (x 0)‖ ≤
      ∑ j ∈ range k, L * ‖x j - x 0‖ :=
    sum_le_sum hlip
  rw [htelescope]
  calc
    ‖forcing k - delta • (∑ j ∈ range k, (g (x j) - g (x 0)))‖ ≤
        ‖forcing k‖ +
          ‖delta • (∑ j ∈ range k, (g (x j) - g (x 0)))‖ :=
      norm_sub_le _ _
    _ = ‖forcing k‖ + delta *
        ‖∑ j ∈ range k, (g (x j) - g (x 0))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdelta]
    _ ≤ ‖forcing k‖ +
        delta * ∑ j ∈ range k, ‖g (x j) - g (x 0)‖ := by
      gcongr
    _ ≤ ‖forcing k‖ +
        delta * ∑ j ∈ range k, L * ‖x j - x 0‖ := by
      gcongr
    _ = ‖forcing k‖ +
        L * (delta * ∑ j ∈ range k, ‖x j - x 0‖) := by
      rw [← mul_sum]
      ring
/-- Cumulative-sum form of the discrete Gronwall inequality.  This formulation
matches directly the comparison between an Euler path and its frozen-drift
counterpart. -/
theorem discrete_gronwall_sum
    (a : ℕ → ℝ) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 ≤ c)
    (ha : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ, a k ≤ B + c * ∑ j ∈ range k, a j) :
    ∀ k : ℕ, a k ≤ B * (1 + c) ^ k := by
  let s : ℕ → ℝ := fun k ↦ B + c * ∑ j ∈ range k, a j
  have hs_nonneg : ∀ k : ℕ, 0 ≤ s k := by
    intro k
    exact add_nonneg hB (mul_nonneg hc (sum_nonneg fun i _ ↦ ha i))
  have ha_le_s : ∀ k : ℕ, a k ≤ s k := hstep
  have hs_step : ∀ k : ℕ, s (k + 1) ≤ (1 + c) * s k := by
    intro k
    have hmul := mul_le_mul_of_nonneg_left (ha_le_s k) hc
    dsimp [s] at hmul ⊢
    rw [sum_range_succ]
    nlinarith
  have hs_bound : ∀ k : ℕ, s k ≤ B * (1 + c) ^ k := by
    intro k
    induction k with
    | zero => simp [s]
    | succ k ih =>
        have hbase : 0 ≤ 1 + c := by positivity
        calc
          s (k + 1) ≤ (1 + c) * s k := hs_step k
          _ ≤ (1 + c) * (B * (1 + c) ^ k) :=
            mul_le_mul_of_nonneg_left ih hbase
          _ = B * (1 + c) ^ (k + 1) := by rw [pow_succ]; ring
  intro k
  exact (ha_le_s k).trans (hs_bound k)

/-- Exponential version of `discrete_gronwall_sum`. -/
theorem discrete_gronwall_sum_exp
    (a : ℕ → ℝ) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 ≤ c)
    (ha : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ, a k ≤ B + c * ∑ j ∈ range k, a j) :
    ∀ k : ℕ, a k ≤ B * Real.exp ((k : ℝ) * c) := by
  intro k
  have hone : 1 + c ≤ Real.exp c := by
    simpa [add_comm] using Real.add_one_le_exp c
  have hpow : (1 + c) ^ k ≤ (Real.exp c) ^ k :=
    pow_le_pow_left₀ (by positivity) hone k
  calc
    a k ≤ B * (1 + c) ^ k :=
      discrete_gronwall_sum a B c hB hc ha hstep k
    _ ≤ B * (Real.exp c) ^ k := mul_le_mul_of_nonneg_left hpow hB
    _ = B * Real.exp ((k : ℝ) * c) := by rw [Real.exp_nat_mul]

/-- Uniform path bound up to a finite horizon. -/
theorem discrete_gronwall_sum_exp_horizon
    (a : ℕ → ℝ) (B c : ℝ) (n : ℕ)
    (hB : 0 ≤ B) (hc : 0 ≤ c)
    (ha : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ, a k ≤ B + c * ∑ j ∈ range k, a j) :
    ∀ k ≤ n, a k ≤ B * Real.exp ((n : ℝ) * c) := by
  intro k hk
  have hkc : (k : ℝ) * c ≤ (n : ℝ) * c := by
    exact mul_le_mul_of_nonneg_right ((Nat.cast_le).2 hk) hc
  calc
    a k ≤ B * Real.exp ((k : ℝ) * c) :=
      discrete_gronwall_sum_exp a B c hB hc ha hstep k
    _ ≤ B * Real.exp ((n : ℝ) * c) := by
      exact mul_le_mul_of_nonneg_left
        ((Real.exp_le_exp).2 hkc) hB

/-- The cumulative comparison also controls the finite quadratic path
energy. -/
theorem finite_quadratic_energy_le
    (a : ℕ → ℝ) (B c delta : ℝ) (n : ℕ)
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (ha : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ, a k ≤ B + c * ∑ j ∈ range k, a j) :
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
      delta * (n : ℝ) * (B * Real.exp ((n : ℝ) * c)) ^ 2 := by
  have hbound_nonneg : 0 ≤ B * Real.exp ((n : ℝ) * c) := by positivity
  have hsum : ∑ k ∈ range n, (a k) ^ 2 ≤
      ∑ _k ∈ range n, (B * Real.exp ((n : ℝ) * c)) ^ 2 := by
    apply sum_le_sum
    intro k hk
    apply (sq_le_sq₀ (ha k) hbound_nonneg).2
    exact discrete_gronwall_sum_exp_horizon a B c n hB hc ha hstep k
      (Nat.le_of_lt (mem_range.mp hk))
  calc
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
        delta * ∑ _k ∈ range n,
          (B * Real.exp ((n : ℝ) * c)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum hdelta
    _ = delta * (n : ℝ) *
        (B * Real.exp ((n : ℝ) * c)) ^ 2 := by
      simp [mul_assoc]

/-- If the cumulative Gronwall coefficient over the whole horizon is at most
one, the path energy is bounded by a universal exponential constant. -/
theorem finite_quadratic_energy_le_of_horizon
    (a : ℕ → ℝ) (B c delta h : ℝ) (n : ℕ)
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (ha : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ, a k ≤ B + c * ∑ j ∈ range k, a j)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : (n : ℝ) * c ≤ 1) :
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
      h * (B * Real.exp 1) ^ 2 := by
  have hexp : Real.exp ((n : ℝ) * c) ≤ Real.exp 1 :=
    (Real.exp_le_exp).2 hsmall
  have hmul : B * Real.exp ((n : ℝ) * c) ≤ B * Real.exp 1 :=
    mul_le_mul_of_nonneg_left hexp hB
  have hleft := finite_quadratic_energy_le
    a B c delta n hB hc hdelta ha hstep
  have hh_nonneg : 0 ≤ h := by rw [← hhorizon]; positivity
  calc
    delta * ∑ k ∈ range n, (a k) ^ 2 ≤
        delta * (n : ℝ) *
          (B * Real.exp ((n : ℝ) * c)) ^ 2 := hleft
    _ = h * (B * Real.exp ((n : ℝ) * c)) ^ 2 := by rw [mul_comm delta]; rw [hhorizon]
    _ ≤ h * (B * Real.exp 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (by positivity) (by positivity)).2 hmul) hh_nonneg

end DiscreteTime

end

end UniformRandomMALA
