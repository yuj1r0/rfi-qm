module
public import FoliationQM.ObserverGaussianFisher
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Vanishing integrated remote flux on three-dimensional space

In the first-particle marginal continuity equation, v13 integrates the divergence of the
second particle's current over its full spatial slice. Integration by parts against one
proves the cancellation from integrability of the components and their coordinate
derivatives. Schwartz wavefunctions supply both hypotheses for the Schrödinger current.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RemoteFluxDivergence

open MeasureTheory LorentzCoordinates ObserverGaussianFisher
open scoped BigOperators

/-- The Cartesian divergence of a real remote flux on the spatial slice. -/
def divergence (J : Fin 3 → Spatial → ℝ) (y : Spatial) : ℝ :=
  ∑ i, fderiv ℝ (J i) y (axes i)

/-- Integration by parts against one on the full slice for a differentiable scalar flux. -/
theorem integral_directional_zero (g : Spatial → ℝ) (v : Spatial)
    (hg : Differentiable ℝ g) (hi : Integrable g)
    (hd : Integrable (fun y => fderiv ℝ g y v)) : (∫ y, fderiv ℝ g y v) = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Spatial => (1 : ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hd) (by simpa using hi)
    (fun _ _ => differentiableAt_const _) (fun y _ => hg y)
  simpa using h

/-- The remote divergence is integrable when all three coordinate derivatives are. -/
theorem integrable_divergence (J : Fin 3 → Spatial → ℝ)
    (hd : ∀ i, Integrable (fun y => fderiv ℝ (J i) y (axes i))) :
    Integrable (divergence J) :=
  integrable_finsetSum _ (fun i _ => hd i)

/-- The full-space integrated divergence vanishes for integrable differentiable currents
with integrable coordinate derivatives. -/
theorem integral_divergence_zero (J : Fin 3 → Spatial → ℝ)
    (hdiff : ∀ i, Differentiable ℝ (J i)) (hi : ∀ i, Integrable (J i))
    (hd : ∀ i, Integrable (fun y => fderiv ℝ (J i) y (axes i))) :
    (∫ y, divergence J y) = 0 := by
  unfold divergence
  rw [integral_finsetSum _ (fun i _ => hd i)]
  simp only [integral_directional_zero _ _ (hdiff _) (hi _) (hd _), Finset.sum_const_zero]

/-- The derivative of a real Schwartz component in any fixed spatial direction is integrable. -/
theorem schwartz_integrable_directional (g : SchwartzMap Spatial ℝ) (v : Spatial) :
    Integrable (fun y => fderiv ℝ (fun w => g w) y v) :=
  (LineDeriv.lineDerivOp v g).integrable

/-- Rapid decay of the components gives zero total divergence. -/
theorem schwartz_integral_divergence_zero (J : Fin 3 → SchwartzMap Spatial ℝ) :
    (∫ y, divergence (fun i => J i) y) = 0 :=
  integral_divergence_zero _ (fun i => (J i).differentiable) (fun i => (J i).integrable)
    (fun i => schwartz_integrable_directional (J i) (axes i))

/-- Compactly supported continuously differentiable components also have zero total divergence. -/
theorem compact_integral_divergence_zero (J : Fin 3 → Spatial → ℝ)
    (hJ : ∀ i, ContDiff ℝ 1 (J i)) (hc : ∀ i, HasCompactSupport (J i)) :
    (∫ y, divergence J y) = 0 :=
  integral_divergence_zero _ (fun i => (hJ i).differentiable (by norm_num))
    (fun i => (hJ i).continuous.integrable_of_hasCompactSupport (hc i))
    (fun i => (((hJ i).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hc i).fderiv_apply ℝ (axes i)))

/-- The Cartesian Schrödinger current of a Schwartz wave as real Schwartz components. -/
def schwartzCurrent (hbar m : ℝ) (ψ : SchwartzMap Spatial ℂ) (i : Fin 3) :
    SchwartzMap Spatial ℝ :=
  let pair := SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
    (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap ψ)
    (LineDeriv.lineDerivOp (axes i) ψ)
  (hbar / m) • SchwartzMap.postcompCLM Complex.imCLM pair

/-- Evaluation gives the usual imaginary part of the wave times its coordinate derivative. -/
theorem schwartzCurrent_apply (hbar m : ℝ) (ψ : SchwartzMap Spatial ℂ) (i : Fin 3)
    (y : Spatial) : schwartzCurrent hbar m ψ i y =
    (hbar / m) * (star (ψ y) * fderiv ℝ (fun w => ψ w) y (axes i)).im := rfl

/-- Each current component of the wave is integrable on the remote slice. -/
theorem schwartz_wave_current_integrable (hbar m : ℝ) (ψ : SchwartzMap Spatial ℂ) (i : Fin 3) :
    Integrable (fun y => (hbar / m) * (star (ψ y) * fderiv ℝ (fun w => ψ w) y (axes i)).im) :=
  (schwartzCurrent hbar m ψ i).integrable

/-- Each directional derivative of each actual current component is integrable. -/
theorem schwartz_wave_current_deriv_integrable (hbar m : ℝ) (ψ : SchwartzMap Spatial ℂ)
    (i : Fin 3) (v : Spatial) :
    Integrable (fun y => fderiv ℝ
      (fun z => (hbar / m) * (star (ψ z) * fderiv ℝ (fun w => ψ w) z (axes i)).im) y v) :=
  schwartz_integrable_directional (schwartzCurrent hbar m ψ i) v

/-- The remote Schrödinger current of a Schwartz wave gives zero integrated divergence. -/
theorem schwartz_wave_flux_zero (hbar m : ℝ) (ψ : SchwartzMap Spatial ℂ) :
    (∫ y, divergence
      (fun i z => (hbar / m) * (star (ψ z) * fderiv ℝ (fun w => ψ w) z (axes i)).im) y) = 0 :=
  schwartz_integral_divergence_zero (schwartzCurrent hbar m ψ)

end FoliationQM.RemoteFluxDivergence
