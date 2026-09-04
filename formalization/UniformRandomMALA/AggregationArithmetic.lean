import UniformRandomMALA.DefectiveArithmetic

/-!
# Pointwise arithmetic in the aggregation lemma

The coarea and measure-theoretic parts of `thm:aggregation` remain in the
kernel interface.  The final median split is elementary and is proved here
without assumptions on measures or kernels.
-/

namespace UniformRandomMALA

noncomputable section

/-- Positive part of `x-b`. -/
def positivePartAt (b x : ℝ) : ℝ := max (x - b) 0

/-- Negative part of `x-b`, written as a nonnegative number. -/
def negativePartAt (b x : ℝ) : ℝ := max (b - x) 0

lemma positivePartAt_nonneg (b x : ℝ) : 0 ≤ positivePartAt b x := by
  unfold positivePartAt
  exact le_max_right _ _

lemma negativePartAt_nonneg (b x : ℝ) : 0 ≤ negativePartAt b x := by
  unfold negativePartAt
  exact le_max_right _ _

/-- Signed reconstruction of a centered scalar from its two parts. -/
theorem positive_sub_negative (b x : ℝ) :
    positivePartAt b x - negativePartAt b x = x - b := by
  unfold positivePartAt negativePartAt
  by_cases h : x ≤ b
  · have hxb : x - b ≤ 0 := sub_nonpos.mpr h
    have hbx : 0 ≤ b - x := sub_nonneg.mpr h
    rw [max_eq_right hxb, max_eq_left hbx]
    ring
  · have hbxlt : b < x := lt_of_not_ge h
    have hxb : 0 ≤ x - b := sub_nonneg.mpr (le_of_lt hbxlt)
    have hbx : b - x ≤ 0 := sub_nonpos.mpr (le_of_lt hbxlt)
    rw [max_eq_left hxb, max_eq_right hbx]
    ring

/-- Orthogonal scalar decomposition around the median level. -/
theorem centered_square_split (b x : ℝ) :
    (x - b) ^ 2 =
      positivePartAt b x ^ 2 + negativePartAt b x ^ 2 := by
  unfold positivePartAt negativePartAt
  by_cases h : x ≤ b
  · have hxb : x - b ≤ 0 := sub_nonpos.mpr h
    have hbx : 0 ≤ b - x := sub_nonneg.mpr h
    rw [max_eq_right hxb, max_eq_left hbx]
    ring
  · have hbxlt : b < x := lt_of_not_ge h
    have hxb : 0 ≤ x - b := sub_nonneg.mpr (le_of_lt hbxlt)
    have hbx : b - x ≤ 0 := sub_nonpos.mpr (le_of_lt hbxlt)
    rw [max_eq_left hxb, max_eq_right hbx]
    ring

/--
The pointwise edge-energy inequality used after subtracting a median:
positive and negative parts cannot together create more squared variation
than the original function.
-/
theorem median_parts_edge_energy
    (b x y : ℝ) :
    (positivePartAt b x - positivePartAt b y) ^ 2 +
        (negativePartAt b x - negativePartAt b y) ^ 2 ≤
      (x - y) ^ 2 := by
  unfold positivePartAt negativePartAt
  by_cases hx : x ≤ b
  · have hxp : x - b ≤ 0 := sub_nonpos.mpr hx
    have hxn : 0 ≤ b - x := sub_nonneg.mpr hx
    by_cases hy : y ≤ b
    · have hyp : y - b ≤ 0 := sub_nonpos.mpr hy
      have hyn : 0 ≤ b - y := sub_nonneg.mpr hy
      rw [max_eq_right hxp, max_eq_left hxn,
        max_eq_right hyp, max_eq_left hyn]
      ring_nf
      norm_num
    · have hby : b < y := lt_of_not_ge hy
      have hyp : 0 ≤ y - b := sub_nonneg.mpr (le_of_lt hby)
      have hyn : b - y ≤ 0 := sub_nonpos.mpr (le_of_lt hby)
      rw [max_eq_right hxp, max_eq_left hxn,
        max_eq_left hyp, max_eq_right hyn]
      nlinarith
  · have hbx : b < x := lt_of_not_ge hx
    have hxp : 0 ≤ x - b := sub_nonneg.mpr (le_of_lt hbx)
    have hxn : b - x ≤ 0 := sub_nonpos.mpr (le_of_lt hbx)
    by_cases hy : y ≤ b
    · have hyp : y - b ≤ 0 := sub_nonpos.mpr hy
      have hyn : 0 ≤ b - y := sub_nonneg.mpr hy
      rw [max_eq_left hxp, max_eq_right hxn,
        max_eq_right hyp, max_eq_left hyn]
      nlinarith
    · have hby : b < y := lt_of_not_ge hy
      have hyp : 0 ≤ y - b := sub_nonneg.mpr (le_of_lt hby)
      have hyn : b - y ≤ 0 := sub_nonpos.mpr (le_of_lt hby)
      rw [max_eq_left hxp, max_eq_right hxn,
        max_eq_left hyp, max_eq_right hyn]
      ring_nf
      norm_num

end

end UniformRandomMALA
