import UniformRandomMALA.Scales
import UniformRandomMALA.DiscreteTime.MovingReference

/-!
# Discrete-time stationary rejection proof graph

This file records the current elementary proof of the stationary MALA
rejection estimate.  Its objects are finite Euler chains, finite Gaussian
likelihood products, stationary random-walk Metropolis endpoint laws, and a
weak endpoint limit.  In particular, no Brownian motion, stochastic integral,
SDE, Euler--Maruyama convergence theorem, or Ethier--Kurtz diffusion limit
occurs in the dependency graph below.

The quantitative leaf estimates are deliberately exposed as propositions.
Concrete pieces already proved elsewhere include the scalar acceptance
linearization, the reversible Gaussian RWM kernel, and the full
moving-reference `L^p` closure theorem.  The fields below mark the exact
remaining analytic probability lemmas rather than concealing them with proof
placeholders.
-/

namespace UniformRandomMALA

noncomputable section

namespace DiscreteTime

/-- Numerical summaries attached to the finite discrete-time construction.
The natural-number argument is the number of Euler/RWM steps. -/
structure StationaryRejectionObjects where
  discreteEnergyMGF : ℝ → ℝ → ℕ → ℝ
  discreteEnergyLp : ℝ → ℝ → ℕ → ℝ
  gaussianProductMean : ℝ → ℝ → ℕ → ℝ
  likelihoodLp : ℝ → ℝ → ℕ → ℝ
  centeredLikelihoodLp : ℝ → ℝ → ℕ → ℝ
  endpointLikelihoodLp : ℝ → ℝ → ℕ → ℝ
  endpointCouplingMSE : ℝ → ℕ → ℝ
  limitingLikelihoodLp : ℝ → ℝ → ℝ
  rejectionLp : ℝ → ℝ → ℝ
  rwmEndpointSymmetric : ℝ → ℕ → Prop
  limitingEndpointSymmetric : ℝ → Prop

/-- Lean-side finite-energy input replacing the continuous Appendix B route. -/
def FiniteEulerEnergy
    (p : Parameters) (o : StationaryRejectionObjects) : Prop :=
  ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ 0 < C ∧
    (∀ h lambda : ℝ, ∀ n : ℕ,
      0 < h → 0 < n → p.L * h ≤ 1 →
      0 ≤ lambda → lambda ≤ c₀ / h ^ 2 →
      o.discreteEnergyMGF h lambda n ≤
        2 * Real.exp (C₀ * lambda * h ^ 2 * p.d)) ∧
    (∀ h moment : ℝ, ∀ n : ℕ,
      0 < h → 0 < n → p.L * h ≤ 1 → 1 ≤ moment →
      o.discreteEnergyLp h moment n ≤ C * h ^ 2 * (p.d + moment))

/-- Lean-side finite-product comparison, including the exact finite Gaussian
product identity and bounds uniform in the number of steps. -/
def FiniteGaussianLikelihood
    (p : Parameters) (o : StationaryRejectionObjects) : Prop :=
  (∀ beta h : ℝ, ∀ n : ℕ, 0 < h → 0 < n →
      o.gaussianProductMean beta h n = 1) ∧
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ h moment : ℝ, ∀ n : ℕ,
      0 < h → 0 < n → 2 ≤ moment →
      h ≤ c / (p.L * Real.sqrt (moment * (p.d + moment))) →
      o.likelihoodLp h (2 * moment) n ≤ C ∧
      o.centeredLikelihoodLp h moment n ≤
        C * p.L * h * Real.sqrt (moment * (p.d + moment))

/-- Conditioning a finite likelihood product on the two endpoints contracts
its centered `Lᵖ` norm.  This is a finite-product conditional Jensen step. -/
def EndpointLikelihoodContraction
    (o : StationaryRejectionObjects) : Prop :=
  ∀ h moment : ℝ, ∀ n : ℕ,
    1 ≤ moment →
    o.endpointLikelihoodLp h moment n ≤
      o.centeredLikelihoodLp h moment n

/-- Direct coupling of the finite Euler and stationary RWM endpoints.  The
epsilon formulation is equivalent to convergence of the mean-square error to
zero and avoids importing any continuous-time convergence API. -/
def EulerRWMEndpointCoalescence
    (o : StationaryRejectionObjects) : Prop :=
  (∀ h : ℝ, 0 < h → ∀ n : ℕ, 0 < n →
      o.rwmEndpointSymmetric h n) ∧
  ∀ h : ℝ, 0 < h → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      o.endpointCouplingMSE h n ≤ epsilon

/-- Tightness, Prokhorov subsequence selection, and preservation of symmetry
in the weak endpoint limit.  Once the two weak limits have been constructed,
`centeredRNDeriv_memLp_of_weakLimit` supplies the formerly missing
moving-reference `Lᵖ` step unconditionally. -/
def SymmetricMovingReferenceLimit
    (p : Parameters) (o : StationaryRejectionObjects) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ h moment : ℝ, 0 < h → 2 ≤ moment →
      h ≤ c / (p.L * Real.sqrt (moment * (p.d + moment))) →
      o.limitingEndpointSymmetric h ∧
      o.limitingLikelihoodLp h moment ≤
        C * p.L * h * Real.sqrt (moment * (p.d + moment))

/-- The stationary rejection estimate, Proposition B.1 in the current draft. -/
def StationaryRejectionBound
    (p : Parameters) (o : StationaryRejectionObjects) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ h moment : ℝ, 0 < h → 2 ≤ moment →
      h ≤ c / (p.L * Real.sqrt (moment * (p.d + moment))) →
      o.rejectionLp h moment ≤
        C * p.L * h * Real.sqrt (moment * (p.d + moment))

/-- The MH accepted-flow meet identity and conditional Jensen turn the
symmetric limiting endpoint likelihood into the stationary rejection bound. -/
def MetropolisMeetRejection
    (p : Parameters) (o : StationaryRejectionObjects) : Prop :=
  SymmetricMovingReferenceLimit p o → StationaryRejectionBound p o

/-- The source-order dependency graph of the elementary proof.  Every bridge
accepts the theorem(s) it uses, so a proof term cannot silently jump from the
finite construction to the limiting rejection estimate. -/
structure StationaryRejectionInterfaces
    (p : Parameters) (o : StationaryRejectionObjects) where
  finiteEulerEnergy : FiniteEulerEnergy p o
  finiteGaussianLikelihood :
    FiniteEulerEnergy p o → FiniteGaussianLikelihood p o
  endpointLikelihoodContraction :
    FiniteGaussianLikelihood p o → EndpointLikelihoodContraction o
  eulerRWMEndpointCoalescence : EulerRWMEndpointCoalescence o
  symmetricMovingReferenceLimit :
    FiniteGaussianLikelihood p o →
    EndpointLikelihoodContraction o →
    EulerRWMEndpointCoalescence o →
      SymmetricMovingReferenceLimit p o
  metropolisMeetRejection : MetropolisMeetRejection p o

namespace StationaryRejectionInterfaces

/-- Assemble Proposition B.1 along the fully discrete/weak-limit route. -/
theorem stationaryRejection
    (p : Parameters) (o : StationaryRejectionObjects)
    (a : StationaryRejectionInterfaces p o) :
    StationaryRejectionBound p o := by
  let hLikelihood : FiniteGaussianLikelihood p o :=
    a.finiteGaussianLikelihood a.finiteEulerEnergy
  let hEndpoint : EndpointLikelihoodContraction o :=
    a.endpointLikelihoodContraction hLikelihood
  let hLimit : SymmetricMovingReferenceLimit p o :=
    a.symmetricMovingReferenceLimit hLikelihood hEndpoint
      a.eulerRWMEndpointCoalescence
  exact a.metropolisMeetRejection hLimit

end StationaryRejectionInterfaces

end DiscreteTime

end

end UniformRandomMALA
