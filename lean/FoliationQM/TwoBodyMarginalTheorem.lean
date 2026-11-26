module

public import FoliationQM.TwoBodyKahlerStationarity
public import FoliationQM.TwoBodyWaveContinuity
public import FoliationQM.TwoBodyRegularHistories
public import FoliationQM.TwoBodyHamiltonianRealization

/-!
# The local marginal equation and remote independence

Stationary waves give an ordinary time derivative of the observed Born integral.
On a Schwartz remote fiber the remote boundary term vanishes. The strong
propagator comparison identifies the scalar marginal histories for regular
representatives satisfying the stated differentiation conditions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyMarginalTheorem

open MeasureTheory LorentzCoordinates ObserverGaussianFisher TwoBodyCoordinates MarginalParameterIntegral
open TwoBodyEulerLagrange TwoBodyWaveContinuity JointL2Sections JointSubsystemUnitary
open scoped BigOperators

/-- A stationary C² wave obeys the physical marginal equation on each Schwartz remote fiber
where the time density and the first-particle currents satisfy the local differentiation bounds. -/
theorem stationary_marginal {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) {V : Point → ℝ} {ψ : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 2 ψ) (hstat : ComplexStationary h m₁ m₂ V ψ)
    {t : ℝ} {x : Spatial} (u : SchwartzMap Spatial ℂ) (hu : ∀ y, ψ ((t,x),y) = u y)
    (hq : RegularAt (fun s y => born ψ (s,y)) (t,x))
    (hj : ∀ i, RegularAt (fun s y => flux h m₁ (leftAxis i) ψ (s,y)) (t,x)) :
    deriv (fun r => ∫ y, ‖ψ ((r,x),y)‖ ^ 2) t +
      (∑ i, fderiv ℝ (fun z => ∫ y, flux h m₁ (leftAxis i) ψ ((t,z),y)) x (axes i)) = 0 := by
  let q := fun s y => born ψ (s,y)
  let j := fun i s y => flux h m₁ (leftAxis i) ψ (s,y)
  have he (i : Fin 3) : (fun y => flux h m₂ (rightAxis i) ψ ((t,x),y)) =
      fun y => (h/m₂) * (star (u y) * fderiv ℝ (fun w => u w) y (axes i)).im := by
    funext y
    unfold flux rightAxis
    rw [← remote_fderiv (hψ.differentiable (by norm_num) _) (axes i), funext hu, hu y]
  have heq := (complex_iff h m₁ m₂ hV hψ).mp hstat
  have result := marginal_of_schrodinger hh m₁ m₂ V hq hj (fun _ => hψ.contDiffAt)
    (fun i => he i ▸ RemoteFluxDivergence.schwartz_wave_current_integrable h m₂ u i)
    (fun i => he i ▸ RemoteFluxDivergence.schwartz_wave_current_deriv_integrable h m₂ u i (axes i))
    (.of_forall fun y => heq ((t,x),y))
  have ht : deriv (fun r => ∫ y, q (r,x) y) t = fderiv ℝ (marginal q) (t,x) baseTime := by
    rw [(marginal_hasFDerivAt hq).fderiv]
    exact ((marginal_hasFDerivAt hq).comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt.deriv
  have hx (i) : fderiv ℝ (fun z => ∫ y, j i (t,z) y) x (axes i) =
      fderiv ℝ (marginal (j i)) (t,x) (baseAxis i) := by
    rw [(marginal_hasFDerivAt (hj i)).fderiv]
    exact congrArg (fun L : Spatial →L[ℝ] ℝ => L (axes i))
      (((marginal_hasFDerivAt (hj i)).comp x (hasFDerivAt_prodMk_right t x)).fderiv)
  change deriv (fun r => ∫ y, q (r,x) y) t + (∑ i, fderiv ℝ (fun z => ∫ y, j i (t,z) y) x (axes i)) = 0
  rw [ht]
  simp_rw [hx]
  exact result

/-- Two differential Hamiltonian realizations with a common retained evolution
give equal physical density and current histories at every retained position and
in every direction for regular scalar representatives of one initial joint state. -/
theorem no_signaling {h m₁ m₂ s : ℝ} {V₁ V₂ V₃ : ℝ → Spatial → ℝ}
    {U V W : ℝ → Remote ≃ₗᵢ[ℂ] Remote} {P Q : ℝ → Joint ≃ₗᵢ[ℂ] Joint}
    (D : TwoBodyHamiltonianRealization.DifferentialEvolution h m₁ m₂ s V₁ V₂ U V P)
    (E : TwoBodyHamiltonianRealization.DifferentialEvolution h m₁ m₂ s V₁ V₃ U W Q)
    (ψ : Joint) (f g : ℝ → Spatial × Spatial → ℂ)
    (hf : ∀ t, TwoBodyRegularHistories.Regular (f t)) (hg : ∀ t, TwoBodyRegularHistories.Regular (g t))
    (hF : ∀ t, (hf t).joint.toLp (f t) = P t ψ) (hG : ∀ t, (hg t).joint.toLp (g t) = Q t ψ)
    (x v : Spatial) :
    (fun t => TwoBodyRegularHistories.observed h m₁ (f t) x v) =
      fun t => TwoBodyRegularHistories.observed h m₁ (g t) x v := by
  apply TwoBodyRegularHistories.factor_histories U V W ψ f g hf hg
  · intro t
    rw [hF, TwoBodyHamiltonianRealization.factorization D]
  · intro t
    rw [hG, TwoBodyHamiltonianRealization.factorization E]

end FoliationQM.TwoBodyMarginalTheorem
