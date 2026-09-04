import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Elementary expansion of the Metropolis rejection profile

For an energy increment `u`, the Metropolis rejection probability is

`1 - min 1 (exp (-u))`.

The Euler/RWM comparison only needs to compare this scalar function with
the positive part of its first-order approximation.  The estimates below
are global and deterministic.  They use the elementary local exponential
remainder from Mathlib and a separate large-`u` estimate; no Taylor theorem
for random variables is required.

We keep a harmless constant `1` in front of the quadratic term instead of
the sharper `1 / 2`.  The proof of Proposition 3.2 only uses the order of
the remainder, and this version is substantially easier to reuse in Lean.
-/

namespace UniformRandomMALA

noncomputable section

namespace DiscreteTime

/-- Rejection probability as a deterministic function of an energy
increment. -/
def rejectionProfile (u : ℝ) : ℝ :=
  1 - min 1 (Real.exp (-u))

@[fun_prop]
theorem continuous_rejectionProfile : Continuous rejectionProfile := by
  unfold rejectionProfile
  fun_prop

theorem rejectionProfile_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    rejectionProfile u = 0 := by
  rw [rejectionProfile, min_eq_left]
  · ring
  · exact Real.one_le_exp (by linarith)

theorem rejectionProfile_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    rejectionProfile u = 1 - Real.exp (-u) := by
  rw [rejectionProfile, min_eq_right]
  exact Real.exp_le_one_iff.2 (by linarith)

theorem rejectionProfile_nonneg (u : ℝ) : 0 ≤ rejectionProfile u := by
  by_cases hu : 0 ≤ u
  · rw [rejectionProfile_of_nonneg hu]
    exact sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith))
  · rw [rejectionProfile_of_nonpos (le_of_not_ge hu)]

theorem rejectionProfile_le_one (u : ℝ) : rejectionProfile u ≤ 1 := by
  unfold rejectionProfile
  have hmin : 0 ≤ min 1 (Real.exp (-u)) :=
    le_min zero_le_one (Real.exp_pos _).le
  linarith

/-- The rejection profile differs from the positive part by at most a
quadratic remainder, uniformly over the real line. -/
theorem abs_rejectionProfile_sub_posPart_le_sq (u : ℝ) :
    |rejectionProfile u - max u 0| ≤ u ^ 2 := by
  by_cases hu : 0 ≤ u
  · rw [rejectionProfile_of_nonneg hu, max_eq_left hu]
    by_cases hu1 : u ≤ 1
    · have hlocal := Real.abs_exp_sub_one_sub_id_le
          (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; exact hu1)
      calc
        |1 - Real.exp (-u) - u| =
            |-(Real.exp (-u) - 1 - (-u))| := by
          congr 1
          ring
        _ = |Real.exp (-u) - 1 - (-u)| := abs_neg _
        _ ≤ (-u) ^ 2 := hlocal
        _ = u ^ 2 := by ring
    · have hlarge : 1 ≤ u := le_of_not_ge hu1
      have hexp_nonneg : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
      have hexp_le : Real.exp (-u) ≤ 1 :=
        Real.exp_le_one_iff.2 (by linarith)
      have hlinear : 1 - Real.exp (-u) ≤ u := by
        have h := Real.add_one_le_exp (-u)
        linarith
      rw [abs_of_nonpos (by linarith)]
      have hu_sq : u ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
      linarith
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [rejectionProfile_of_nonpos hu', max_eq_right hu', sub_zero, abs_zero]
    exact sq_nonneg u

/-- Compare the exact rejection profile at `u` with the positive part of
an arbitrary first-order approximation `q`. -/
theorem abs_rejectionProfile_sub_posPart_le
    (u q : ℝ) :
    |rejectionProfile u - max q 0| ≤
      |u - q| + (|q| + |u - q|) ^ 2 := by
  have htri :
      |rejectionProfile u - max q 0| ≤
        |rejectionProfile u - max u 0| + |max u 0 - max q 0| := by
    calc
      |rejectionProfile u - max q 0| =
          |(rejectionProfile u - max u 0) + (max u 0 - max q 0)| := by
        congr 1
        ring
      _ ≤ |rejectionProfile u - max u 0| + |max u 0 - max q 0| :=
        abs_add_le _ _
  have hpos : |max u 0 - max q 0| ≤ |u - q| :=
    abs_max_sub_max_le_abs u q 0
  have huabs : |u| ≤ |q| + |u - q| := by
    calc
      |u| = |q + (u - q)| := by ring_nf
      _ ≤ |q| + |u - q| := abs_add_le _ _
  have hsq : u ^ 2 ≤ (|q| + |u - q|) ^ 2 := by
    rw [← sq_abs u]
    exact (sq_le_sq₀ (abs_nonneg u) (by positivity)).2 huabs
  calc
    |rejectionProfile u - max q 0| ≤
        |rejectionProfile u - max u 0| + |max u 0 - max q 0| := htri
    _ ≤ u ^ 2 + |u - q| :=
      add_le_add (abs_rejectionProfile_sub_posPart_le_sq u) hpos
    _ ≤ (|q| + |u - q|) ^ 2 + |u - q| := add_le_add hsq le_rfl
    _ = |u - q| + (|q| + |u - q|) ^ 2 := add_comm _ _

/-- Version with a supplied deterministic bound on the energy remainder.
This is the form applied with
`r = (L / 2) * ‖s‖²`. -/
theorem abs_rejectionProfile_sub_posPart_le_of_abs_sub_le
    (u q r : ℝ) (hr : 0 ≤ r) (huq : |u - q| ≤ r) :
    |rejectionProfile u - max q 0| ≤ r + (|q| + r) ^ 2 := by
  refine (abs_rejectionProfile_sub_posPart_le u q).trans ?_
  have hsum : |q| + |u - q| ≤ |q| + r := add_le_add le_rfl huq
  have hsq : (|q| + |u - q|) ^ 2 ≤ (|q| + r) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
  exact add_le_add huq hsq

/-- Polynomial simplification used after substituting a scaled Gaussian
increment.  This isolates all nonlinear arithmetic from the probabilistic
integral. -/
theorem scaled_rejection_polynomial_bound
    (a A b r : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (ha2 : a ^ 2 ≤ 2) :
    (A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2) * (a * r) ≤
      a ^ 3 * ((A + 2 * b ^ 2) * r ^ 3 + 4 * A ^ 2 * r ^ 5) := by
  let X := b * (a * r)
  let Y := A * (a * r) ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hxy : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (X - Y)]
  have hscale : 0 ≤ a * r := mul_nonneg ha hr
  calc
    (A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2) * (a * r) =
        (A * (a * r) ^ 2 + (X + Y) ^ 2) * (a * r) := by
      simp only [X, Y]
    _ ≤ (A * (a * r) ^ 2 + (2 * X ^ 2 + 2 * Y ^ 2)) * (a * r) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hxy) hscale
    _ = a ^ 3 *
        ((A + 2 * b ^ 2) * r ^ 3 + 2 * A ^ 2 * a ^ 2 * r ^ 5) := by
      simp only [X, Y]
      ring
    _ ≤ a ^ 3 *
        ((A + 2 * b ^ 2) * r ^ 3 + 4 * A ^ 2 * r ^ 5) := by
      have ha3 : 0 ≤ a ^ 3 := by positivity
      apply mul_le_mul_of_nonneg_left _ ha3
      apply add_le_add le_rfl
      have hA2r : 0 ≤ A ^ 2 * r ^ 5 := by positivity
      nlinarith

/-- Polynomial simplification for the conditional second moment of a
Bernoulli rejection displacement.  The hypothesis `a ≤ 2` is the coarse
consequence of `a = sqrt (2 δ)` and `δ ≤ 1`. -/
theorem scaled_rejection_secondMoment_polynomial_bound
    (a A b r : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    (b * (a * r) + A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2) * (a * r) ^ 2 ≤
      a ^ 3 *
        (b * r ^ 3 + (2 * A + 4 * b ^ 2) * r ^ 4 +
          16 * A ^ 2 * r ^ 6) := by
  let X := b * (a * r)
  let Y := A * (a * r) ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hxy : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (X - Y)]
  have ht2 : 0 ≤ (a * r) ^ 2 := sq_nonneg _
  calc
    (b * (a * r) + A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2) * (a * r) ^ 2 =
        (X + Y + (X + Y) ^ 2) * (a * r) ^ 2 := by
      simp only [X, Y]
    _ ≤ (X + Y + (2 * X ^ 2 + 2 * Y ^ 2)) * (a * r) ^ 2 :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hxy) ht2
    _ = a ^ 3 *
        (b * r ^ 3 + (A * a + 2 * b ^ 2 * a) * r ^ 4 +
          2 * A ^ 2 * a ^ 3 * r ^ 6) := by
      simp only [X, Y]
      ring
    _ ≤ a ^ 3 *
        (b * r ^ 3 + (2 * A + 4 * b ^ 2) * r ^ 4 +
          16 * A ^ 2 * r ^ 6) := by
      have ha3 : 0 ≤ a ^ 3 := by positivity
      apply mul_le_mul_of_nonneg_left _ ha3
      have hAa : A * a ≤ 2 * A :=
        by simpa [mul_comm] using mul_le_mul_of_nonneg_left ha2 hA
      have hb2a : 2 * b ^ 2 * a ≤ 4 * b ^ 2 := by
        nlinarith [sq_nonneg b]
      have ha3le : a ^ 3 ≤ 8 := by nlinarith [sq_nonneg a, sq_nonneg (a - 2)]
      have hA2a3 : 2 * A ^ 2 * a ^ 3 ≤ 16 * A ^ 2 := by
        nlinarith [sq_nonneg A]
      have hr4 : 0 ≤ r ^ 4 := by positivity
      have hr6 : 0 ≤ r ^ 6 := by positivity
      nlinarith

end DiscreteTime

end

end UniformRandomMALA
