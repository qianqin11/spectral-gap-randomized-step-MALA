import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Basic

/-!
# Positive quadratic forms and squared-norm contraction

These scalar lemmas turn positivity and a Rayleigh bound for a symmetric
form into a squared-norm contraction.  The bounded-observable Markov-kernel
argument supplies the form and its integral identities; no operator or
spectral-theorem assumptions enter these algebraic steps.
-/

namespace UniformRandomMALA.Concrete

/-- Cauchy--Schwarz for a positive quadratic form, expressed in terms of its
two diagonal entries and its symmetric off-diagonal entry. -/
theorem bilinear_cauchy_schwarz_of_quadratic_nonneg {U Z V : ℝ}
    (h : ∀ t : ℝ, 0 ≤ U + 2 * t * Z + t ^ 2 * V) :
    Z ^ 2 ≤ U * V := by
  have hd : discrim V (2 * Z) U ≤ 0 := discrim_le_zero (fun t => by
    nlinarith only [h t])
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- The scalar step in the norm estimate for a positive symmetric map.
Here `X = ‖f‖²`, `Z = ‖Mf‖²`, `U = ⟪Mf, f⟫`, and
`V = ⟪M(Mf), Mf⟫`.  Cauchy--Schwarz for the positive form gives
`Z² ≤ U * V`, and the two Rayleigh estimates give the contraction. -/
theorem sq_norm_contraction_of_positive_form {X Z U V a : ℝ}
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (ha : 0 ≤ a)
    (_hU : 0 ≤ U) (hV : 0 ≤ V)
    (hCS : Z ^ 2 ≤ U * V) (hUX : U ≤ a * X) (hVZ : V ≤ a * Z) :
    Z ≤ a ^ 2 * X := by
  have hprod : U * V ≤ (a * X) * (a * Z) :=
    mul_le_mul hUX hVZ hV (mul_nonneg ha hX)
  by_cases hz : Z = 0
  · simpa only [hz] using mul_nonneg (sq_nonneg a) hX
  · have hzpos : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
    apply (mul_le_mul_iff_of_pos_right hzpos).mp
    nlinarith only [hCS.trans hprod]

end UniformRandomMALA.Concrete
