import UniformRandomMALA.Concrete.NonconvexPotential

/-! # Basic dimension and drift bounds for the nonconvex appendix class -/

namespace UniformRandomMALA.Concrete.NonconvexPotential

variable {d : ℕ} (V : NonconvexPotential d)

include V in
lemma dimension_real_pos : 0 < (d : ℝ) := by exact_mod_cast V.hd

include V in
lemma dimension_real_one : 1 ≤ (d : ℝ) := by exact_mod_cast V.hd

lemma grad_lipschitz : LipschitzWith ⟨V.L, V.hL.le⟩ V.gradU := V.gradient_lipschitz

end UniformRandomMALA.Concrete.NonconvexPotential
