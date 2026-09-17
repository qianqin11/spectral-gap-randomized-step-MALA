import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform-random MALA: common imports

This project formalizes the main results of Qian Qin's
*A global spectral gap for Metropolis-adjusted Langevin algorithm with a
uniformly randomized step size*.  The checked public route constructs its
stochastic-analysis and geometric inputs in Lean; older typed interfaces are
retained as modular compatibility APIs.
-/

namespace UniformRandomMALA

noncomputable section

open Real

end

end UniformRandomMALA
