import UniformRandomMALA.BaillonHaddad

/-!
# Numerical constants appearing in overlap and defective conductance
-/

namespace UniformRandomMALA

noncomputable section

lemma sixty_seven_over_ninety_six_lt_three_quarters :
    (67 : ℝ) / 96 < 3 / 4 := by norm_num

lemma seventeen_times_two_pow_neg_thirteen_lt_half :
    (17 : ℝ) / (2 : ℝ) ^ 13 < 1 / 2 := by norm_num

lemma thirty_three_times_two_pow_neg_thirteen_lt_one_over_128 :
    (33 : ℝ) / (2 : ℝ) ^ 13 < 1 / 128 := by norm_num

/-- The elementary truncation inequality used in defective conductance. -/
lemma min_one_sixteenth
    (x : ℝ) (hx : 0 ≤ x) :
    min 1 x / 16 ≤ min 1 (x / 16) := by
  by_cases hxone : x ≤ 1
  · have hxdiv : x / 16 ≤ 1 := by linarith
    rw [min_eq_right hxone, min_eq_right hxdiv]
  · have honex : 1 ≤ x := le_of_not_ge hxone
    rw [min_eq_left honex]
    apply le_min
    · norm_num
    · linarith

/-- Numeric comparison in the globally safe overlap estimate. -/
lemma safe_overlap_numeric :
    2 * (1 - Real.exp (-(1 / 4 : ℝ))) + 1 / 32 < 3 / 4 := by
  have hexp : 1 + (-(1 / 4 : ℝ)) ≤ Real.exp (-(1 / 4 : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (-(1 / 4 : ℝ))
  norm_num at hexp ⊢
  linarith

/-- The Markov-good-set overlap constant in the moment-indexed argument. -/
lemma moment_overlap_numeric :
    (1 / 3 : ℝ) + 1 / 32 + 1 / 3 = 67 / 96 := by norm_num

end

end UniformRandomMALA
