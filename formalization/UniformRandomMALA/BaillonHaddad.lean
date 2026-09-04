import UniformRandomMALA.Arithmetic

/-!
# Baillon--Haddad consequences used by MALA

The functional-analytic Baillon--Haddad theorem itself remains an imported
convex-analysis input.  The two algebraic consequences used in the paper
are proved here from its scalar inequalities:

1. cocoercivity makes the proposal mean map nonexpansive for `h ≤ 2/L`;
2. the one-sided inequality gives the safe Metropolis log-ratio lower bound.
-/

namespace UniformRandomMALA

noncomputable section

/-- Algebra behind nonexpansiveness of `x ↦ x - h ∇U(x)`. -/
theorem proposal_mean_nonexpansive_sq
    (L h distanceSq gradDiffSq inner : ℝ)
    (hL : 0 < L) (hh : 0 ≤ h) (hhL : h ≤ 2 / L)
    (hgrad : 0 ≤ gradDiffSq)
    (hcocoercive : gradDiffSq / L ≤ inner) :
    distanceSq - 2 * h * inner + h ^ 2 * gradDiffSq ≤ distanceSq := by
  have hcoef : h ^ 2 ≤ 2 * h / L := by
    calc
      h ^ 2 = h * h := by ring
      _ ≤ h * (2 / L) := mul_le_mul_of_nonneg_left hhL hh
      _ = 2 * h / L := by ring
  have hinner : 2 * h * (gradDiffSq / L) ≤ 2 * h * inner := by
    exact mul_le_mul_of_nonneg_left hcocoercive (by positivity)
  have hquad : h ^ 2 * gradDiffSq ≤ (2 * h / L) * gradDiffSq := by
    exact mul_le_mul_of_nonneg_right hcoef hgrad
  have hquadInner : h ^ 2 * gradDiffSq ≤ 2 * h * inner := by
    calc
      h ^ 2 * gradDiffSq ≤ (2 * h / L) * gradDiffSq := hquad
      _ = 2 * h * (gradDiffSq / L) := by ring
      _ ≤ 2 * h * inner := hinner
  linarith

/--
Scalar completion-of-the-square step in the globally safe acceptance proof.
`cross` stands for `⟨Z, g_Y-g_x⟩` and the last hypothesis is Cauchy--Schwarz.
-/
theorem one_sided_bh_safe_log_lower
    (L h breg gradNorm zNorm cross : ℝ)
    (hL : 0 < L) (hh : 0 ≤ h) (hhL : h ≤ 1 / L)
    (hgrad : 0 ≤ gradNorm) (hz : 0 ≤ zNorm)
    (hbh1 : gradNorm ^ 2 / (2 * L) ≤ breg)
    (hcross : cross ≤ zNorm * gradNorm) :
    -(L * h / 2) * zNorm ^ 2 ≤
      breg - h / 4 * gradNorm ^ 2 - Real.sqrt (h / 2) * cross := by
  let s : ℝ := Real.sqrt (h / 2)
  have hsarg : 0 ≤ h / 2 := by positivity
  have hs2 : s ^ 2 = h / 2 := by
    dsimp [s]
    simpa using Real.sq_sqrt hsarg
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hcoef : 1 / (4 * L) ≤ 1 / (2 * L) - h / 4 := by
    have hquarter : h / 4 ≤ (1 / L) / 4 :=
      div_le_div_of_nonneg_right hhL (by norm_num)
    calc
      1 / (4 * L) = 1 / (2 * L) - (1 / L) / 4 := by
        field_simp [ne_of_gt hL]
        <;> ring
      _ ≤ 1 / (2 * L) - h / 4 := sub_le_sub_left hquarter _
  have hbhcoarse :
      gradNorm ^ 2 / (4 * L) ≤ breg - h / 4 * gradNorm ^ 2 := by
    have hsq : 0 ≤ gradNorm ^ 2 := sq_nonneg gradNorm
    have hscaled := mul_le_mul_of_nonneg_right hcoef hsq
    have hrewrite :
        (1 / (2 * L) - h / 4) * gradNorm ^ 2 =
          gradNorm ^ 2 / (2 * L) - h / 4 * gradNorm ^ 2 := by ring
    calc
      gradNorm ^ 2 / (4 * L) = 1 / (4 * L) * gradNorm ^ 2 := by ring
      _ ≤ (1 / (2 * L) - h / 4) * gradNorm ^ 2 := hscaled
      _ = gradNorm ^ 2 / (2 * L) - h / 4 * gradNorm ^ 2 := hrewrite
      _ ≤ breg - h / 4 * gradNorm ^ 2 :=
        sub_le_sub_right hbh1 _
  have hcrossScaled : s * cross ≤ s * (zNorm * gradNorm) :=
    mul_le_mul_of_nonneg_left hcross hsnonneg
  have hidentity :
      gradNorm ^ 2 / (4 * L) - s * (zNorm * gradNorm) +
          (L * h / 2) * zNorm ^ 2 =
        (gradNorm - 2 * L * s * zNorm) ^ 2 / (4 * L) := by
    have hh_eq : h = 2 * s ^ 2 := by nlinarith [hs2]
    field_simp [ne_of_gt hL]
    rw [hh_eq]
    ring
  have hcompletion :
      0 ≤ gradNorm ^ 2 / (4 * L) - s * (zNorm * gradNorm) +
          (L * h / 2) * zNorm ^ 2 := by
    rw [hidentity]
    positivity
  have hrearranged :
      -(L * h / 2) * zNorm ^ 2 ≤
        gradNorm ^ 2 / (4 * L) - s * (zNorm * gradNorm) := by
    linarith
  calc
    -(L * h / 2) * zNorm ^ 2 ≤
        gradNorm ^ 2 / (4 * L) - s * (zNorm * gradNorm) := hrearranged
    _ ≤ gradNorm ^ 2 / (4 * L) - s * cross :=
      sub_le_sub_left hcrossScaled _
    _ ≤ (breg - h / 4 * gradNorm ^ 2) - s * cross :=
      sub_le_sub_right hbhcoarse _
    _ = breg - h / 4 * gradNorm ^ 2 - Real.sqrt (h / 2) * cross := by
      rfl

end

end UniformRandomMALA
