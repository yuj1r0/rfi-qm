module

public import FoliationQM.TwoBodyCoordinates
public import FoliationQM.MarginalParameterIntegral
public import FoliationQM.RemoteFluxDivergence

/-!
# Local continuity for the observed first-particle marginal

Integrate the joint conservation law over the whole discarded spatial
variable. Actual directional derivatives of the marginal are obtained
by dominated differentiation. Integration by parts removes the remote
divergence for integrable fluxes and integrable directional derivatives.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyMarginalContinuity

open MeasureTheory LorentzCoordinates TwoBodyCoordinates MarginalParameterIntegral ObserverGaussianFisher
open scoped BigOperators

/-- Joint time derivative plus the two spatial divergences. -/
def residual (ρ : Point → ℝ) (J K : Fin 3 → Point → ℝ) (p : Point) : ℝ :=
  Dt ρ p + (∑ i, D₁ i (J i) p) + ∑ i, D₂ i (K i) p

/-- At one retained spacetime point the a.e. joint conservation law implies
the marginal conservation law with actual derivatives of the two marginal integrals. -/
theorem marginal_continuity {q : Base → Spatial → ℝ} {j k : Fin 3 → Base → Spatial → ℝ}
    {b : Base} (hq : RegularAt q b) (hj : ∀ i, RegularAt (j i) b)
    (hk : ∀ i, Differentiable ℝ (k i b)) (hi : ∀ i, Integrable (k i b))
    (hd : ∀ i, Integrable (fun y => fderiv ℝ (k i b) y (axes i)))
    (hc : ∀ᵐ y, MarginalParameterIntegral.partial q b y baseTime +
      (∑ i, MarginalParameterIntegral.partial (j i) b y (baseAxis i)) +
      RemoteFluxDivergence.divergence (fun i => k i b) y = 0) :
    fderiv ℝ (marginal q) b baseTime +
      (∑ i, fderiv ℝ (marginal (j i)) b (baseAxis i)) = 0 := by
  have hsum : Integrable (fun y => ∑ i, MarginalParameterIntegral.partial (j i) b y (baseAxis i)) :=
    integrable_finsetSum _ fun i _ => integrable_partial_apply (hj i) (baseAxis i)
  have hdiv : Integrable (RemoteFluxDivergence.divergence (fun i => k i b)) :=
    integrable_finsetSum _ fun i _ => hd i
  have hret : Integrable (fun y => MarginalParameterIntegral.partial q b y baseTime +
      ∑ i, MarginalParameterIntegral.partial (j i) b y (baseAxis i)) :=
    (integrable_partial_apply hq baseTime).add hsum
  have he := integral_congr_ae hc
  rw [integral_add hret hdiv, integral_add (integrable_partial_apply hq baseTime) hsum,
    integral_finsetSum _ (fun i _ => integrable_partial_apply (hj i) (baseAxis i)),
    RemoteFluxDivergence.integral_divergence_zero _ hk hi hd] at he
  simp only [add_zero, integral_zero] at he
  simpa only [marginal_fderiv_apply hq, fun i => marginal_fderiv_apply (hj i) (baseAxis i)] using he

/-- At a retained time and position, the conservation law uses the ordinary
time derivative and the spatial divergence at fixed time. -/
theorem time_and_space {q : Base → Spatial → ℝ} {j k : Fin 3 → Base → Spatial → ℝ}
    {t : ℝ} {x : Spatial} (hq : RegularAt q (t,x)) (hj : ∀ i, RegularAt (j i) (t,x))
    (hk : ∀ i, Differentiable ℝ (k i (t,x))) (hi : ∀ i, Integrable (k i (t,x)))
    (hd : ∀ i, Integrable (fun y => fderiv ℝ (k i (t,x)) y (axes i)))
    (hc : ∀ᵐ y, MarginalParameterIntegral.partial q (t,x) y baseTime +
      (∑ i, MarginalParameterIntegral.partial (j i) (t,x) y (baseAxis i)) +
      RemoteFluxDivergence.divergence (fun i => k i (t,x)) y = 0) :
    deriv (fun s => ∫ y, q (s,x) y) t +
      (∑ i, fderiv ℝ (fun z => ∫ y, j i (t,z) y) x (axes i)) = 0 := by
  have ht : deriv (fun s => ∫ y, q (s,x) y) t = fderiv ℝ (marginal q) (t,x) baseTime := by
    rw [(marginal_hasFDerivAt hq).fderiv]
    exact ((marginal_hasFDerivAt hq).comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt.deriv
  have hx (i) : fderiv ℝ (fun z => ∫ y, j i (t,z) y) x (axes i) =
      fderiv ℝ (marginal (j i)) (t,x) (baseAxis i) := by
    rw [(marginal_hasFDerivAt (hj i)).fderiv]
    exact congrArg (fun L : Spatial →L[ℝ] ℝ => L (axes i))
      (((marginal_hasFDerivAt (hj i)).comp x (hasFDerivAt_prodMk_right t x)).fderiv)
  simp only [ht,hx]
  exact marginal_continuity hq hj hk hi hd hc

/-- The full seven-dimensional coordinate PDE projects to the physical marginal
equation at a retained spacetime point where its integrals may be differentiated. -/
theorem of_joint {ρ : Point → ℝ} {J K : Fin 3 → Point → ℝ} {b : Base}
    (hq : RegularAt (fun s y => ρ (s,y)) b)
    (hj : ∀ i, RegularAt (fun s y => J i (s,y)) b)
    (hρ : ∀ y, DifferentiableAt ℝ ρ (b,y))
    (hJ : ∀ i y, DifferentiableAt ℝ (J i) (b,y))
    (hK : ∀ i y, DifferentiableAt ℝ (K i) (b,y))
    (hi : ∀ i, Integrable (fun y => K i (b,y)))
    (hd : ∀ i, Integrable (fun y => fderiv ℝ (fun z => K i (b,z)) y (axes i)))
    (hc : ∀ᵐ y, residual ρ J K (b,y) = 0) :
    fderiv ℝ (fun s => ∫ y, ρ (s,y)) b baseTime +
      (∑ i, fderiv ℝ (fun s => ∫ y, J i (s,y)) b (baseAxis i)) = 0 := by
  apply marginal_continuity (k := fun i s y => K i (s,y)) hq hj
    (fun i y => (hK i y).comp y ((differentiableAt_const _).prodMk differentiableAt_id)) hi hd
  filter_upwards [hc] with y hy
  simpa only [residual, Dt, D₁, D₂, timeAxis, leftAxis, rightAxis,
    MarginalParameterIntegral.partial, RemoteFluxDivergence.divergence,
    base_fderiv (hρ y), fun i => base_fderiv (hJ i y) (baseAxis i),
    fun i => remote_fderiv (hK i y) (axes i)] using hy

/-- Rapid remote decay of a scalar wave discharges the remote flux assumptions
in the local marginal equation using the actual Schrödinger current. -/
theorem of_schwartz_remote (hbar m : ℝ) (ψ : SchwartzMap Spatial ℂ)
    {q : Base → Spatial → ℝ} {j : Fin 3 → Base → Spatial → ℝ} {t : ℝ} {x : Spatial}
    (hq : RegularAt q (t,x)) (hj : ∀ i, RegularAt (j i) (t,x))
    (hc : ∀ᵐ y, MarginalParameterIntegral.partial q (t,x) y baseTime +
      (∑ i, MarginalParameterIntegral.partial (j i) (t,x) y (baseAxis i)) +
      RemoteFluxDivergence.divergence (fun i z =>
        (hbar/m) * (star (ψ z) * fderiv ℝ (fun w => ψ w) z (axes i)).im) y = 0) :
    deriv (fun s => ∫ y, q (s,x) y) t +
      (∑ i, fderiv ℝ (fun z => ∫ y, j i (t,z) y) x (axes i)) = 0 :=
  time_and_space (k := fun i _ y => RemoteFluxDivergence.schwartzCurrent hbar m ψ i y) hq hj
    (fun i => (RemoteFluxDivergence.schwartzCurrent hbar m ψ i).differentiable)
    (RemoteFluxDivergence.schwartz_wave_current_integrable hbar m ψ)
    (fun i => RemoteFluxDivergence.schwartz_wave_current_deriv_integrable hbar m ψ i (axes i)) hc

end FoliationQM.TwoBodyMarginalContinuity
