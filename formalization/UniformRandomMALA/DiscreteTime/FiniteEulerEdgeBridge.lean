import UniformRandomMALA.Concrete.FiniteEulerEndpointContraction
import UniformRandomMALA.DiscreteTime.FiniteGaussianEndpointLaw
import UniformRandomMALA.DiscreteTime.EulerRWMEdgeCoupling
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Identifying the two finite Euler edge constructions

The likelihood construction uses an explicit `Fin n` tuple of Gaussian
innovations.  The Euler--RWM coupling uses a finite iterate of a Markov
kernel whose noise also contains an unused uniform coordinate.  This file
proves directly that their Euler endpoint laws agree.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete

variable {d : Nat}

/-- One Euler transition, packaged as a Markov kernel. -/
def explicitEulerKernel (V : FirstOrderPotential d) (delta : Real) :
    Kernel (State d) (State d) :=
  Kernel.map
    (Kernel.id ×ₖ Kernel.const (State d) (stdGaussian (State d)))
    (Function.uncurry (explicitEulerUpdate V delta))

instance explicitEulerKernel_isMarkovKernel
    (V : FirstOrderPotential d) (delta : Real) :
    IsMarkovKernel (explicitEulerKernel V delta) := by
  unfold explicitEulerKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_uncurry_explicitEulerUpdate V delta)

lemma lintegral_explicitEulerKernel
    (V : FirstOrderPotential d) (delta : Real) (x : State d)
    {g : State d -> ENNReal} (hg : Measurable g) :
    (∫⁻ y, g y ∂explicitEulerKernel V delta x) =
      ∫⁻ z, g (explicitEulerUpdate V delta x z)
        ∂stdGaussian (State d) := by
  rw [explicitEulerKernel,
    Kernel.lintegral_map _ (measurable_uncurry_explicitEulerUpdate V delta) x hg]
  change (∫⁻ p : State d × State d,
      g (explicitEulerUpdate V delta p.1 p.2)
        ∂(Kernel.id ×ₖ Kernel.const (State d) (stdGaussian (State d))) x) = _
  rw [Kernel.lintegral_id_prod
    (f := fun p => g (explicitEulerUpdate V delta p.1 p.2))
    (hg.comp (measurable_uncurry_explicitEulerUpdate V delta))
    (Kernel.const (State d) (stdGaussian (State d))) x]
  rfl

lemma map_fst_eulerRWMPairLaw
    (V : FirstOrderPotential d) (delta : Real) (xy : State d × State d) :
    Measure.map Prod.fst (eulerRWMPairLaw V delta xy) =
      explicitEulerKernel V delta xy.1 := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg measurable_fst]
  rw [eulerRWMPairLaw]
  calc
    (∫⁻ a : State d × State d, g a.1
        ∂Measure.map (eulerRWMPairUpdate V delta xy) (gaussianUniformNoise d)) =
        ∫⁻ zu, g (eulerRWMPairUpdate V delta xy zu).1
          ∂gaussianUniformNoise d := by
      simpa only [Function.comp_apply] using
        (lintegral_map (hg.comp measurable_fst)
          (measurable_eulerRWMPairUpdate V delta xy))
    _ = _ := by
      rw [lintegral_explicitEulerKernel V delta xy.1 hg]
      change (∫⁻ zu : State d × Set.Icc (0 : Real) 1,
          g (explicitEulerUpdate V delta xy.1 zu.1)
            ∂(stdGaussian (State d)).prod volume) = _
      rw [lintegral_prod]
      · simp
      · exact (hg.comp ((Measurable.of_uncurry_left
          (measurable_uncurry_explicitEulerUpdate V delta)).comp
            measurable_fst)).aemeasurable

lemma map_fst_eulerRWMPairKernel
    (V : FirstOrderPotential d) (delta : Real) (xy : State d × State d) :
    Measure.map Prod.fst (eulerRWMPairKernel V delta xy) =
      explicitEulerKernel V delta xy.1 := by
  rw [eulerRWMPairKernel_apply_eq_pairLaw]
  exact map_fst_eulerRWMPairLaw V delta xy

lemma fst_eulerRWMPairKernel
    (V : FirstOrderPotential d) (delta : Real) :
    Kernel.fst (eulerRWMPairKernel V delta) =
      explicitEulerKernel V delta ∘ₖ
        Kernel.deterministic Prod.fst measurable_fst := by
  rw [Kernel.fst_eq]
  ext xy : 1
  rw [Kernel.map_apply _ measurable_fst]
  rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  exact map_fst_eulerRWMPairKernel V delta xy

/-- First-coordinate analogue of `snd_finiteKernelIterate`. -/
lemma fst_finiteKernelIterate
    {E : Type*} [MeasurableSpace E]
    (C : Kernel (E × E) (E × E)) (P : Kernel E E)
    (hCP : Kernel.fst C =
      P ∘ₖ Kernel.deterministic Prod.fst measurable_fst) :
    forall n, Kernel.fst (finiteKernelIterate C n) =
      finiteKernelIterate P n ∘ₖ
        Kernel.deterministic Prod.fst measurable_fst := by
  intro n
  induction n with
  | zero =>
      simp only [finiteKernelIterate, Kernel.fst_eq]
      rw [<- Kernel.deterministic_comp_eq_map measurable_fst,
        Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
      simp only [finiteKernelIterate]
      rw [Kernel.fst_comp, hCP, Kernel.comp_assoc,
        Kernel.deterministic_comp_eq_map measurable_fst,
        <- Kernel.fst_eq, ih, <- Kernel.comp_assoc]

lemma fst_eulerRWMPairChainKernel
    (V : FirstOrderPotential d) (delta : Real) (n : Nat) :
    Kernel.fst (eulerRWMPairChainKernel V delta n) =
      finiteKernelIterate (explicitEulerKernel V delta) n ∘ₖ
        Kernel.deterministic Prod.fst measurable_fst := by
  unfold eulerRWMPairChainKernel
  exact fst_finiteKernelIterate (eulerRWMPairKernel V delta)
    (explicitEulerKernel V delta) (fst_eulerRWMPairKernel V delta) n

lemma map_fst_eulerRWMPairChainKernel
    (V : FirstOrderPotential d) (delta : Real) (n : Nat)
    (xy : State d × State d) :
    Measure.map Prod.fst (eulerRWMPairChainKernel V delta n xy) =
      finiteKernelIterate (explicitEulerKernel V delta) n xy.1 := by
  change Kernel.fst (eulerRWMPairChainKernel V delta n) xy = _
  rw [fst_eulerRWMPairChainKernel,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]

lemma fst_diagonalStartedEulerRWMPairKernel
    (V : FirstOrderPotential d) (delta : Real) (n : Nat) :
    Kernel.fst (diagonalStartedEulerRWMPairKernel V delta n) =
      finiteKernelIterate (explicitEulerKernel V delta) n := by
  ext x : 1
  rw [Kernel.fst_apply]
  unfold diagonalStartedEulerRWMPairKernel
  rw [Kernel.copy, Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply, map_fst_eulerRWMPairChainKernel]
  rfl

/-- The explicit `Fin n` Euler recursion has the same law as the finite
iterate of the one-step Euler kernel.  The proof is a literal finite Tonelli
induction after splitting a tuple into its head and tail. -/
theorem map_finiteEulerEndpointRec_eq_finiteKernelIterate
    (V : FirstOrderPotential d) (delta : Real) (n : Nat) (x : State d) :
    Measure.map (finiteEulerEndpointRec V delta x)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
      finiteKernelIterate (explicitEulerKernel V delta) n x := by
  induction n generalizing x with
  | zero =>
      rw [finiteKernelIterate, Kernel.id_apply]
      ext s hs
      rw [Measure.map_apply
        (measurable_finiteEulerEndpointRec V delta x 0) hs]
      by_cases hx : x ∈ s
      · simp [finiteEulerEndpointRec, Measure.dirac_apply' _ hs, hx]
      · simp [finiteEulerEndpointRec, Measure.dirac_apply' _ hs, hx]
  | succ n ih =>
      apply Measure.ext_of_lintegral
      intro g hg
      rw [lintegral_map hg
        (measurable_finiteEulerEndpointRec V delta x (n + 1))]
      let e : (Fin (n + 1) -> State d) ≃ᵐ
          State d × (Fin n -> State d) :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => State d) 0
      let F : State d × (Fin n -> State d) -> ENNReal := fun p =>
        g (finiteEulerEndpointRec V delta x (e.symm p))
      have hF : Measurable F :=
        hg.comp ((measurable_finiteEulerEndpointRec V delta x (n + 1)).comp
          e.symm.measurable)
      let G : State d -> ENNReal := fun x' =>
        ∫⁻ y, g y ∂finiteKernelIterate (explicitEulerKernel V delta) n x'
      have hG : Measurable G := hg.lintegral_kernel
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => stdGaussian (State d)) (0 : Fin (n + 1))
      calc
        (∫⁻ z, g (finiteEulerEndpointRec V delta x z)
            ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d))) =
            ∫⁻ z, F (e z)
              ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d)) := by
                apply lintegral_congr
                intro z
                simp [F]
        _ = ∫⁻ p, F p ∂(stdGaussian (State d)).prod
              (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
                exact hmp.lintegral_comp hF
        _ = ∫⁻ z0, ∫⁻ ztail, F (z0, ztail)
              ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))
              ∂stdGaussian (State d) := by
                exact lintegral_prod F hF.aemeasurable
        _ = ∫⁻ z0, G (explicitEulerUpdate V delta x z0)
              ∂stdGaussian (State d) := by
                apply lintegral_congr
                intro z0
                simp only [F, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
                  Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk,
                  finiteEulerEndpointRec, Fin.cons_zero, Fin.tail_cons,
                  Fin.zero_succAbove, cast_eq]
                change (∫⁻ ztail,
                    g (finiteEulerEndpointRec V delta
                      (explicitEulerUpdate V delta x z0) ztail)
                    ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
                  G (explicitEulerUpdate V delta x z0)
                rw [← lintegral_map hg
                  (measurable_finiteEulerEndpointRec V delta
                    (explicitEulerUpdate V delta x z0) n)]
                rw [ih (explicitEulerUpdate V delta x z0)]
        _ = ∫⁻ x', G x' ∂explicitEulerKernel V delta x := by
              exact (lintegral_explicitEulerKernel V delta x hG).symm
        _ = ∫⁻ y, g y ∂
              (finiteKernelIterate (explicitEulerKernel V delta) n ∘ₖ
                explicitEulerKernel V delta) x := by
              exact (Kernel.lintegral_comp
                (finiteKernelIterate (explicitEulerKernel V delta) n)
                (explicitEulerKernel V delta) x hg).symm
        _ = ∫⁻ y, g y ∂
              finiteKernelIterate (explicitEulerKernel V delta) (n + 1) x := by
              rw [finiteKernelIterate_comp_self, finiteKernelIterate]

/-- The explicit-noise edge law used by the likelihood proof is exactly the
kernel-iterate Euler edge law used by the Euler--RWM coupling. -/
theorem finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure
    (V : FirstOrderPotential d) (delta : Real) (n : Nat) :
    finiteEulerLikelihoodEdgeLaw V n delta =
      finiteEulerEdgeMeasure V delta n := by
  let gamma : Measure (Fin n -> State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let edge : State d × (Fin n -> State d) -> State d × State d :=
    finiteEulerLikelihoodEdgeMap V delta
  have hedge : Measurable edge :=
    measurable_finiteEulerLikelihoodEdgeMap V delta
  apply Measure.ext_of_lintegral
  intro f hf
  rw [finiteEulerLikelihoodEdgeLaw, lintegral_map hf hedge]
  change (∫⁻ p, f (p.1, finiteEulerEndpointRec V delta p.1 p.2)
      ∂(V.target : Measure (State d)).prod gamma) = _
  rw [lintegral_prod]
  · rw [finiteEulerEdgeMeasure, Measure.lintegral_compProd hf]
    apply lintegral_congr
    intro x
    let fx : State d -> ENNReal := fun y => f (x, y)
    have hfx : Measurable fx := hf.comp
      (measurable_const.prodMk measurable_id)
    calc
      (∫⁻ z, f (x, finiteEulerEndpointRec V delta x z) ∂gamma) =
          ∫⁻ y, fx y ∂Measure.map (finiteEulerEndpointRec V delta x) gamma := by
            symm
            exact lintegral_map hfx
              (measurable_finiteEulerEndpointRec V delta x n)
      _ = ∫⁻ y, fx y ∂
          finiteKernelIterate (explicitEulerKernel V delta) n x := by
            rw [map_finiteEulerEndpointRec_eq_finiteKernelIterate]
      _ = ∫⁻ y, f (x, y) ∂
          Kernel.fst (diagonalStartedEulerRWMPairKernel V delta n) x := by
            rw [fst_diagonalStartedEulerRWMPairKernel]
  · exact (hf.comp (measurable_fst.prodMk
      (measurable_finiteEulerEndpointRec_joint V delta n))).aemeasurable

/-- Under `n * delta = h`, the likelihood-tilted edge is the concrete MALA
proposal edge.  This restates the finite Gaussian endpoint theorem in the
stable edge-law vocabulary of `FiniteEulerEndpointContraction`. -/
theorem finiteEulerLikelihoodTiltedEdgeLaw_eq_compProd_gaussianDensityProposal
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 <= delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    finiteEulerLikelihoodTiltedEdgeLaw V n delta =
      (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h := by
  unfold finiteEulerLikelihoodTiltedEdgeLaw finiteEulerTiltedJointMeasure
    finiteEulerBaseJointMeasure finiteEulerJointDensity
    finiteEulerLikelihoodEdgeMap
  exact map_finiteEulerTiltedEdge_eq_compProd_gaussianDensityProposal
    V delta h hdelta hh htime

/-! ## Absolute continuity and the concrete endpoint density

The likelihood tilt is already a `withDensity` operation before the
endpoint map is applied.  Absolute continuity is therefore preserved by
the measurable endpoint map.  This avoids constructing any conditional
expectation or disintegration at the endpoint level.
-/

/-- The likelihood-tilted endpoint edge law is absolutely continuous with
respect to the un-tilted finite Euler endpoint edge law. -/
theorem finiteEulerLikelihoodTiltedEdgeLaw_absolutelyContinuous
    (V : FirstOrderPotential d) (delta : Real) (n : Nat) :
    finiteEulerLikelihoodTiltedEdgeLaw V n delta ≪
      finiteEulerLikelihoodEdgeLaw V n delta := by
  unfold finiteEulerLikelihoodTiltedEdgeLaw finiteEulerTiltedJointMeasure
    finiteEulerLikelihoodEdgeLaw
  exact (withDensity_absolutelyContinuous
      (finiteEulerBaseJointMeasure (n := n) V)
      (finiteEulerJointDensity (n := n) V delta)).map
    (measurable_finiteEulerLikelihoodEdgeMap (n := n) V delta)

/-- Under the time-matching identity, the concrete frozen-drift proposal
edge is absolutely continuous with respect to the explicit finite Euler
edge law used in the likelihood argument. -/
theorem compProd_gaussianDensityProposal_absolutelyContinuous_finiteEulerLikelihoodEdgeLaw
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h ≪
      finiteEulerLikelihoodEdgeLaw V n delta := by
  rw [← finiteEulerLikelihoodTiltedEdgeLaw_eq_compProd_gaussianDensityProposal
    V delta h n hdelta hh htime]
  exact finiteEulerLikelihoodTiltedEdgeLaw_absolutelyContinuous V delta n

/-- Kernel-iterate form of the preceding absolute-continuity statement. -/
theorem compProd_gaussianDensityProposal_absolutelyContinuous_finiteEulerEdgeMeasure
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h ≪
      finiteEulerEdgeMeasure V delta n := by
  rw [← finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure V delta n]
  exact
    compProd_gaussianDensityProposal_absolutelyContinuous_finiteEulerLikelihoodEdgeLaw
      V delta h n hdelta hh htime

/-- The concrete proposal edge is recovered from the finite Euler edge by
its Radon--Nikodym derivative.  This is the canonical `ENNReal`-valued
density form of the endpoint likelihood identity. -/
theorem compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_rnDeriv
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
      (finiteEulerEdgeMeasure V delta n).withDensity
        (((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
          (finiteEulerEdgeMeasure V delta n)) := by
  symm
  exact Measure.withDensity_rnDeriv_eq _ _
    (compProd_gaussianDensityProposal_absolutelyContinuous_finiteEulerEdgeMeasure
      V delta h n hdelta hh htime)

/-- The endpoint density used by the finite likelihood moment bounds is
literally the concrete proposal/Euler-edge Radon--Nikodym derivative after
the two edge-law identifications. -/
theorem finiteEulerLikelihoodEndpointRNDensity_eq_compProd_gaussianDensityProposal_rnDeriv
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    finiteEulerLikelihoodEndpointRNDensity V n delta =
      ((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
        (finiteEulerEdgeMeasure V delta n) := by
  unfold finiteEulerLikelihoodEndpointRNDensity
  rw [finiteEulerLikelihoodTiltedEdgeLaw_eq_compProd_gaussianDensityProposal
      V delta h n hdelta hh htime,
    finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure V delta n]

/-- Reconstruction of the concrete proposal edge using the endpoint density
that appears in the finite likelihood moment estimates. -/
theorem compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_endpointRNDensity
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
      (finiteEulerEdgeMeasure V delta n).withDensity
        (finiteEulerLikelihoodEndpointRNDensity V n delta) := by
  rw [finiteEulerLikelihoodEndpointRNDensity_eq_compProd_gaussianDensityProposal_rnDeriv
    V delta h n hdelta hh htime]
  exact compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_rnDeriv
    V delta h n hdelta hh htime

/-- Real-valued presentation of the concrete endpoint density.  The
`ofReal ∘ toReal` replacement is valid almost everywhere because a
Radon--Nikodym derivative of a sigma-finite measure is finite almost
everywhere. -/
theorem compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_toReal_rnDeriv
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
      (finiteEulerEdgeMeasure V delta n).withDensity (fun e =>
        ENNReal.ofReal
          ((((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
            (finiteEulerEdgeMeasure V delta n) e).toReal)) := by
  letI : Fact (0 < h) := ⟨hh⟩
  calc
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
        (finiteEulerEdgeMeasure V delta n).withDensity
          (((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
            (finiteEulerEdgeMeasure V delta n)) :=
      compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_rnDeriv
        V delta h n hdelta hh htime
    _ = (finiteEulerEdgeMeasure V delta n).withDensity (fun e =>
          ENNReal.ofReal
            ((((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
              (finiteEulerEdgeMeasure V delta n) e).toReal)) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top
          ((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h)
          (finiteEulerEdgeMeasure V delta n)] with e he
      exact (ENNReal.ofReal_toReal he.ne).symm

/-- Real-valued reconstruction stated with the finite endpoint density used
by all downstream moment bounds. -/
theorem compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_toReal_endpointRNDensity
    (V : FirstOrderPotential d) (delta h : Real) (n : Nat)
    (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : Real) * delta = h) :
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
      (finiteEulerEdgeMeasure V delta n).withDensity (fun e =>
        ENNReal.ofReal
          ((finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal)) := by
  rw [finiteEulerLikelihoodEndpointRNDensity_eq_compProd_gaussianDensityProposal_rnDeriv
    V delta h n hdelta hh htime]
  exact
    compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_toReal_rnDeriv
      V delta h n hdelta hh htime

end DiscreteTime
end
end UniformRandomMALA
