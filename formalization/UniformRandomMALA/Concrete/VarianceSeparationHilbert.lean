import UniformRandomMALA.Concrete.StationaryVarianceResolvent
import UniformRandomMALA.Concrete.PositiveContraction

/-!
# Lower variance bounds from the Poisson equation

The positive Dirichlet form of a self-adjoint contraction gives the
reciprocal-energy lower bound used in Corollary 2.7
(`cor:variance-separation`). The proof is Hilbert-space Cauchy--Schwarz;
no worst-case variance identity is assumed.
-/

namespace UniformRandomMALA.Concrete

open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Dirichlet quadratic form of a contraction is nonnegative. -/
theorem inner_sub_operator_nonneg (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (x : E) :
    0 ≤ ⟪x, x - P x⟫ := by
  have hp : ‖P x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using (P.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hP (norm_nonneg x))
  have hi := (real_inner_le_norm x (P x)).trans
    (mul_le_mul_of_nonneg_left hp (norm_nonneg x))
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith

/-- Cauchy--Schwarz for the genuine Dirichlet form `I-P`. -/
theorem dirichlet_inner_cauchy_schwarz
    (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hsym : P.toLinearMap.IsSymmetric)
    (f u : E) :
    ⟪f, u - P u⟫ ^ 2 ≤ ⟪f, f - P f⟫ * ⟪u, u - P u⟫ := by
  apply bilinear_cauchy_schwarz_of_quadratic_nonneg
  intro t
  have h := inner_sub_operator_nonneg P hP (f + t • u)
  have hsym' : ⟪P u, f⟫ = ⟪u, P f⟫ := hsym u f
  have hcross : ⟪u, f - P f⟫ = ⟪f, u - P u⟫ := by
    rw [inner_sub_right, inner_sub_right, ← hsym']
    congr 1 <;> exact real_inner_comm _ _
  have heq : (f + t • u) - P (f + t • u) =
      (f - P f) + t • (u - P u) := by
    simp only [map_add, map_smul, smul_sub]
    abel
  rw [heq] at h
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hcross] at h
  nlinarith

/-- A unit-norm Poisson observable has positive Dirichlet energy, and its
Poisson variance is at least `2/energy - 1`. -/
theorem poissonSolution_variance_lower
    (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hsym : P.toLinearMap.IsSymmetric)
    {f u : E} (hf : ‖f‖ = 1) (hu : u - P u = f) :
    0 < ⟪f, f - P f⟫ ∧
      2 / ⟪f, f - P f⟫ - 1 ≤ 2 * ⟪f, u⟫ - ‖f‖ ^ 2 := by
  have hc := dirichlet_inner_cauchy_schwarz P hP hsym f u
  rw [hu, real_inner_self_eq_norm_sq, hf] at hc
  have hsymfu : ⟪u, f⟫ = ⟪f, u⟫ := real_inner_comm _ _
  rw [hsymfu] at hc
  norm_num only [one_pow] at hc
  have he : 0 < ⟪f, f - P f⟫ := by
    have hn := inner_sub_operator_nonneg P hP f
    by_contra h
    have hz : ⟪f, f - P f⟫ = 0 := le_antisymm (le_of_not_gt h) hn
    rw [hz, zero_mul] at hc
    norm_num at hc
  refine ⟨he, ?_⟩
  have hi : 1 / ⟪f, f - P f⟫ ≤ ⟪f, u⟫ :=
    (div_le_iff₀ he).2 (by simpa only [mul_comm] using hc)
  rw [hf, show 2 / ⟪f, f - P f⟫ = 2 * (1 / ⟪f, f - P f⟫) by ring]
  nlinarith

/-- The constructed resolvent variance satisfies the reciprocal-energy
lower bound whenever the contraction has a positive right gap. -/
theorem poissonResolvent_variance_lower [CompleteSpace E]
    (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hsym : P.toLinearMap.IsSymmetric)
    (f : E) (hf : ‖f‖ = 1)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hgap : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫) :
    0 < ⟪f, f - P f⟫ ∧
      2 / ⟪f, f - P f⟫ - 1 ≤
        2 * ⟪f, poissonResolvent P f⟫ - ‖f‖ ^ 2 :=
  poissonSolution_variance_lower P hP hsym hf
    (poissonResolvent_sub P (norm_halfLazyOperator_lt_one P hP ha ha2 hgap) f)

end
end UniformRandomMALA.Concrete
