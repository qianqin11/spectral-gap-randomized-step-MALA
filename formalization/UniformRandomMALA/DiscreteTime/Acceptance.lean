import UniformRandomMALA.BaillonHaddad
import Mathlib.Analysis.Complex.Exponential

/-!
# Elementary inequalities for the discrete-time proof

This file contains the scalar estimates used to compare one Euler step with
one Gaussian random-walk Metropolis step.  There is no filtration, stochastic
integral, or continuous-time process in these statements.

The paper uses the sharper bound
`|r - (1 - exp (-r))| ≤ r^2 / 2` for `r ≥ 0`.  The coarser constant `1`
proved below is sufficient for every subsequent estimate and has a shorter,
more robust formal proof.
-/

namespace UniformRandomMALA

noncomputable section

namespace DiscreteTime

/-- The positive-part map on `ℝ` is one-Lipschitz. -/
theorem abs_posPart_sub_posPart_le (u q : ℝ) :
    |max u 0 - max q 0| ≤ |u - q| := by
  simpa [Real.dist_eq] using
    (LipschitzWith.dist_le_mul (LipschitzWith.id.max_const (0 : ℝ)) u q)

/-- Pointwise estimate behind the Metropolis--Hastings meet argument.  If
`F` and `Fswap` are the two endpoint likelihoods, the rejected density is
`F - min F Fswap`, and it is controlled by their deviations from one. -/
theorem meet_rejection_le_deviations (F Fswap : ℝ) :
    0 ≤ F - min F Fswap ∧
      F - min F Fswap ≤ |F - 1| + |Fswap - 1| := by
  constructor
  · exact sub_nonneg.mpr (min_le_left F Fswap)
  · by_cases h : F ≤ Fswap
    · rw [min_eq_left h, sub_self]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · rw [min_eq_right (le_of_not_ge h)]
      calc
        F - Fswap ≤ |F - Fswap| := le_abs_self _
        _ = |(F - 1) - (Fswap - 1)| := by congr 1 <;> ring
        _ ≤ |F - 1| + |Fswap - 1| := abs_sub _ _

/-- For `r ≥ 0`, replacing `1 - exp (-r)` by its linearization `r`
costs at most `r²`. -/
theorem exp_rejection_linear_error_le_sq {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ r - (1 - Real.exp (-r)) ∧
      r - (1 - Real.exp (-r)) ≤ r ^ 2 := by
  constructor
  · have h := Real.one_sub_le_exp_neg r
    linarith
  · by_cases hr1 : r ≤ 1
    · have habs : |(-r : ℝ)| ≤ 1 := by
        rw [abs_neg, abs_of_nonneg hr]
        exact hr1
      have h := Real.abs_exp_sub_one_sub_id_le habs
      have hnonneg : 0 ≤ Real.exp (-r) - 1 + r := by
        linarith [Real.one_sub_le_exp_neg r]
      have h' : |Real.exp (-r) - 1 + r| ≤ r ^ 2 := by
        simpa [sub_eq_add_neg] using h
      rw [abs_of_nonneg hnonneg] at h'
      nlinarith
    · have hone : 1 ≤ r := le_of_not_ge hr1
      have hexp : Real.exp (-r) ≤ 1 := by
        exact (Real.exp_le_one_iff.mpr (by linarith))
      nlinarith [sq_nonneg (r - 1)]

/-- The rejection probability of a scalar Metropolis test depends only on
the positive part of the log-energy increment. -/
theorem one_sub_min_one_exp_neg (u : ℝ) :
    1 - min 1 (Real.exp (-u)) =
      1 - Real.exp (-(max u 0)) := by
  by_cases hu : u ≤ 0
  · have hneg : 0 ≤ -u := neg_nonneg.mpr hu
    have hexp : 1 ≤ Real.exp (-u) := (Real.one_le_exp_iff.mpr hneg)
    simp [max_eq_right hu, min_eq_left hexp]
  · have hu0 : 0 ≤ u := le_of_not_ge hu
    have hexp : Real.exp (-u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0)
    simp [max_eq_left hu0, min_eq_right hexp]

/-- First-order linearization of the scalar Metropolis rejection
probability. -/
theorem metropolis_rejection_linearization (u q : ℝ) :
    |(1 - min 1 (Real.exp (-u))) - max q 0| ≤
      |u - q| + (max u 0) ^ 2 := by
  rw [one_sub_min_one_exp_neg]
  have hu : 0 ≤ max u 0 := le_max_right _ _
  have hlin := exp_rejection_linear_error_le_sq hu
  have hpos := abs_posPart_sub_posPart_le u q
  calc
    |(1 - Real.exp (-(max u 0))) - max q 0| =
        |((1 - Real.exp (-(max u 0))) - max u 0) +
          (max u 0 - max q 0)| := by congr 1 <;> ring
    _ ≤
        |(1 - Real.exp (-(max u 0))) - max u 0| +
          |max u 0 - max q 0| :=
      abs_add_le _ _
    _ ≤ (max u 0) ^ 2 + |u - q| := by
      have habs :
          |(1 - Real.exp (-(max u 0))) - max u 0| ≤
            (max u 0) ^ 2 := by
        rw [abs_sub_comm, abs_of_nonneg hlin.1]
        exact hlin.2
      exact add_le_add habs hpos
    _ = |u - q| + (max u 0) ^ 2 := add_comm _ _

/-- Version used after the smoothness estimate
`|u-q| ≤ (L/2)‖s‖²`.  The universal constant is deliberately kept coarse. -/
theorem smooth_metropolis_rejection_linearization
    (u q L stepNormSq : ℝ)
    (hL : 0 ≤ L) (hs : 0 ≤ stepNormSq)
    (hsmooth : |u - q| ≤ (L / 2) * stepNormSq) :
    |(1 - min 1 (Real.exp (-u))) - max q 0| ≤
      (L / 2) * stepNormSq +
        (|q| + (L / 2) * stepNormSq) ^ 2 := by
  have hcoef : 0 ≤ (L / 2) * stepNormSq := mul_nonneg (by positivity) hs
  have huabs : |u| ≤ |q| + (L / 2) * stepNormSq := by
    calc
      |u| = |(u - q) + q| := by congr 1 <;> ring
      _ ≤ |u - q| + |q| := abs_add_le _ _
      _ ≤ (L / 2) * stepNormSq + |q| := by
        simpa [add_comm] using add_le_add_right hsmooth |q|
      _ = |q| + (L / 2) * stepNormSq := add_comm _ _
  have hupos : max u 0 ≤ |q| + (L / 2) * stepNormSq := by
    calc
      max u 0 ≤ |u| := by
        by_cases hu : 0 ≤ u
        · simp [max_eq_left hu, abs_of_nonneg hu]
        · have hu' : u ≤ 0 := le_of_not_ge hu
          simp [max_eq_right hu', abs_nonneg]
      _ ≤ _ := huabs
  have hsq : (max u 0) ^ 2 ≤
      (|q| + (L / 2) * stepNormSq) ^ 2 := by
    exact (sq_le_sq₀ (le_max_right u 0)
      (add_nonneg (abs_nonneg q) hcoef)).2 hupos
  calc
    |(1 - min 1 (Real.exp (-u))) - max q 0| ≤
        |u - q| + (max u 0) ^ 2 :=
      metropolis_rejection_linearization u q
    _ ≤ (L / 2) * stepNormSq +
        (|q| + (L / 2) * stepNormSq) ^ 2 :=
      add_le_add hsmooth hsq

/-- Algebraic one-step stability estimate for the Euler map.  Here
`distanceSq`, `gradDiffSq`, and `innerTerm` stand for
`‖x-y‖²`, `‖g(x)-g(y)‖²`, and `⟪x-y,g(x)-g(y)⟫`. -/
theorem euler_map_almost_nonexpansive_sq
    (L delta distanceSq gradDiffSq innerTerm : ℝ)
    (hdelta : 0 ≤ delta) (hmono : 0 ≤ innerTerm)
    (hlip : gradDiffSq ≤ L ^ 2 * distanceSq) :
    distanceSq - 2 * delta * innerTerm + delta ^ 2 * gradDiffSq ≤
      (1 + L ^ 2 * delta ^ 2) * distanceSq := by
  have hcross : -2 * delta * innerTerm ≤ 0 := by
    have hprod := mul_nonneg hdelta hmono
    nlinarith
  calc
    distanceSq - 2 * delta * innerTerm + delta ^ 2 * gradDiffSq ≤
        distanceSq + delta ^ 2 * gradDiffSq := by linarith
    _ ≤ distanceSq + delta ^ 2 * (L ^ 2 * distanceSq) := by
      have hscaled := mul_le_mul_of_nonneg_left hlip (sq_nonneg delta)
      linarith
    _ = (1 + L ^ 2 * delta ^ 2) * distanceSq := by ring

end DiscreteTime

end

end UniformRandomMALA
