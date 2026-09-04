import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite recursion bounds for the Euler--RWM coupling

The endpoint-coalescence proof ends with a deterministic affine recursion.
These lemmas isolate that induction from all probability theory.  The error
per step has size `B * δ * sqrt δ`; over `n` steps with `nδ = h`, the
resulting bound has the required `sqrt δ` factor.
-/

namespace UniformRandomMALA

noncomputable section

namespace DiscreteTime

/-- A coarse finite discrete Gronwall estimate sufficient for the coupling.
It avoids division by `q - 1`, which is useful at `q = 1`. -/
theorem affine_recursion_bound
    (a : ℕ → ℝ) (q b : ℝ)
    (hq : 1 ≤ q) (hb : 0 ≤ b)
    (ha0 : a 0 ≤ 0)
    (hstep : ∀ k : ℕ, a (k + 1) ≤ q * a k + b) :
    ∀ n : ℕ, a n ≤ (n : ℝ) * b * q ^ n := by
  intro n
  induction n with
  | zero => simpa using ha0
  | succ n ih =>
      have hq0 : 0 ≤ q := le_trans (by norm_num) hq
      have hmul : q * a n ≤ q * ((n : ℝ) * b * q ^ n) :=
        mul_le_mul_of_nonneg_left ih hq0
      have hpow : 1 ≤ q ^ (n + 1) := one_le_pow₀ hq
      calc
        a (n + 1) ≤ q * a n + b := hstep n
        _ ≤ q * ((n : ℝ) * b * q ^ n) + b :=
          by simpa [add_comm] using add_le_add_right hmul b
        _ = (n : ℝ) * b * q ^ (n + 1) + b := by
          rw [pow_succ]
          ring
        _ ≤ ((n + 1 : ℕ) : ℝ) * b * q ^ (n + 1) := by
          rw [Nat.cast_add, Nat.cast_one]
          nlinarith [mul_nonneg hb (sub_nonneg.mpr hpow)]

/-- The form used after the conditional coupling calculation. -/
theorem coupling_recursion_bound
    (a : ℕ → ℝ) (c delta B : ℝ)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hB : 0 ≤ B)
    (ha0 : a 0 ≤ 0)
    (hstep : ∀ k : ℕ,
      a (k + 1) ≤
        (1 + c * delta) * a k + B * delta * Real.sqrt delta) :
    ∀ n : ℕ,
      a n ≤ (n : ℝ) * (B * delta * Real.sqrt delta) *
        (1 + c * delta) ^ n := by
  apply affine_recursion_bound a (1 + c * delta)
  · exact le_add_of_nonneg_right (mul_nonneg hc hdelta)
  · positivity
  · exact ha0
  · exact hstep

/-- Substituting `nδ = h` exposes the `sqrt δ` endpoint error. -/
theorem coupling_recursion_bound_fixed_horizon
    (a : ℕ → ℝ) (c delta B h : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hB : 0 ≤ B)
    (ha0 : a 0 ≤ 0)
    (hstep : ∀ k : ℕ,
      a (k + 1) ≤
        (1 + c * delta) * a k + B * delta * Real.sqrt delta)
    (hhorizon : (n : ℝ) * delta = h) :
    a n ≤ B * h * Real.sqrt delta * (1 + c * delta) ^ n := by
  calc
    a n ≤ (n : ℝ) * (B * delta * Real.sqrt delta) *
        (1 + c * delta) ^ n :=
      coupling_recursion_bound a c delta B hc hdelta hB ha0 hstep n
    _ = B * h * Real.sqrt delta * (1 + c * delta) ^ n := by
      rw [← hhorizon]
      ring

end DiscreteTime

end

end UniformRandomMALA
