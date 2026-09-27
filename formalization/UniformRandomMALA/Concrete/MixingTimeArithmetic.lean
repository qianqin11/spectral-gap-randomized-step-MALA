import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# From geometric convergence to a mixing-time bound

These elementary estimates retain the zero-step case and the endpoint
contraction factor zero. The probabilistic application supplies the error
sequence using actual kernel iterates and total variation.
-/

namespace UniformRandomMALA.Concrete

noncomputable section

/-- First natural time at which an error is at most the tolerance, with
value infinity if no such time exists. -/
def mixingTimeOfErrors (error : ℕ → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨅ n : {n : ℕ // error n ≤ ε}, (n.val : ℕ∞)

theorem mixingTimeOfErrors_le {error : ℕ → ℝ} {ε : ℝ} {n : ℕ}
    (hn : error n ≤ ε) : mixingTimeOfErrors error ε ≤ (n : ℕ∞) :=
  iInf_le_of_le ⟨n, hn⟩ le_rfl

/-- The logarithmic factor in Corollary 2.5 (`cor:mixing`), where `M` is
the centered initial-density L² norm. -/
def mixingLog (M ε : ℝ) : ℝ := Real.log (max 1 (M / (2 * ε)))

theorem mixingLog_nonneg (M ε : ℝ) : 0 ≤ mixingLog M ε :=
  Real.log_nonneg (le_max_left _ _)

theorem mixingLog_eq_zero {M ε : ℝ} (hε : 0 < ε) (hM : M ≤ 2 * ε) :
    mixingLog M ε = 0 := by
  unfold mixingLog
  rw [max_eq_left ((div_le_one (by positivity : 0 < 2 * ε)).2 hM), Real.log_one]

theorem one_sub_pow_le_exp {g : ℝ} (hg : g ≤ 1) (n : ℕ) :
    (1 - g) ^ n ≤ Real.exp (-g * n) := by
  calc
    (1 - g) ^ n ≤ (Real.exp (-g)) ^ n := by
      gcongr
      exact Real.one_sub_le_exp_neg g
    _ = Real.exp (-g * n) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem amplitude_mul_exp_le {M ε g : ℝ} (hε : 0 < ε) (hg : 0 < g)
    (n : ℕ) (hn : mixingLog M ε / g ≤ n) :
    M / 2 * Real.exp (-g * n) ≤ ε := by
  have hq : 0 < max 1 (M / (2 * ε)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hratio := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp
    (le_max_right 1 (M / (2 * ε)))
  have hamp : M / 2 ≤ ε * Real.exp (mixingLog M ε) := by
    rw [mixingLog, Real.exp_log hq]
    nlinarith
  have htime := (div_le_iff₀ hg).mp hn
  calc
    M / 2 * Real.exp (-g * n) ≤
        (ε * Real.exp (mixingLog M ε)) * Real.exp (-g * n) :=
      mul_le_mul_of_nonneg_right hamp (Real.exp_pos _).le
    _ = ε * Real.exp (mixingLog M ε - g * n) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by nlinarith)) hε.le
    _ = ε := mul_one _

theorem amplitude_mul_geometric_le {M ε g : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε) (hg : 0 < g) (hg1 : g ≤ 1)
    (n : ℕ) (hn : mixingLog M ε / g ≤ n) :
    M / 2 * (1 - g) ^ n ≤ ε :=
  (mul_le_mul_of_nonneg_left (one_sub_pow_le_exp hg1 n) (by positivity)).trans
    (amplitude_mul_exp_le hε hg n hn)

/-- Geometric decay gives the ceiling bound, including an initially
accurate distribution (`mixingLog = 0`) and a zero contraction factor. -/
theorem mixingTimeOfErrors_le_of_geometric
    {error : ℕ → ℝ} {M ε g : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε) (hg : 0 < g) (hg1 : g ≤ 1)
    (herror : ∀ n, error n ≤ M / 2 * (1 - g) ^ n) :
    mixingTimeOfErrors error ε ≤ (⌈mixingLog M ε / g⌉₊ : ℕ∞) := by
  apply mixingTimeOfErrors_le
  exact (herror _).trans
    (amplitude_mul_geometric_le hM hε hg hg1 _ (Nat.le_ceil _))

/-- Replacing a positive gap by a proved lower bound only increases the
ceiling estimate. -/
theorem mixingSteps_mono {M ε lower gap : ℝ}
    (hlower : 0 < lower) (hle : lower ≤ gap) :
    ⌈mixingLog M ε / gap⌉₊ ≤ ⌈mixingLog M ε / lower⌉₊ := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left (mixingLog_nonneg M ε) hlower hle

end

end UniformRandomMALA.Concrete
