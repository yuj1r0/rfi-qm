module
public import FoliationQM.PolarDiracDensity
public import FoliationQM.ReconstructedFrameConnection
/-!
# Symmetric Dirac density of original reconstructed spinor fields

Sources: v13 `eq:dirac_polar_lagrangian_main` and `thm:dirac_lift` (i).
The stipulated symmetric field density uses actual Frechet derivatives.
A local determinant-one field supplies the real frame, inverse, isometry
and real generator coefficients, so its polar density follows with no
supplied frame or generator expansion. Neighborhood equality transfers
this identity to the original field and its canonical reconstructed frame.
The final theorem constructs local factors from C1 strict regularity alone.
The displayed density has no amplitude-gradient term. This local identity
does not establish a stationary-action equivalence or derive a Dirac equation.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.ReconstructedDiracDensity
open DiracMatrices SpinorMatrix SpecialLinearSpin DiracFieldDensity
open PolarSpinorDifferential PolarConnectionContraction RealLorentzFrame
open SpecialLinearConnection SpecialLinearSpinDifferential
open ReconstructedFrameGeometry ReconstructedFrameConnection SpinorRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual neighborhood equality of spinor fields identifies both their values and derivatives, hence their symmetric Dirac densities. -/
theorem fieldDensity_congr {psi phi : E → Spinor} {x : E}
    (he : psi =ᶠ[𝓝 x] phi) (hbar c m : ℝ) (directions : Fin 4 → E) :
    fieldDensity hbar c m psi x directions = fieldDensity hbar c m phi x directions := by
  simp only [fieldDensity, he.fderiv_eq, he.eq_of_nhds]

/-- A locally determinant-one differentiable polar field has the exact symmetric Dirac density with its actual constructed frame and coefficients. -/
theorem fieldDensity_specialLinear {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (directions : Fin 4 → E) (hbar c m : ℝ) :
    fieldDensity hbar c m (polarField rho beta (fun y => spin (A y))) x directions =
      ((rho x * (canonicalContraction hbar c (SpecialLinearFrame.frame (A x))
        (fun mu => bodyOmega A x (directions mu)) -
        (hbar*c/2)*(∑ mu, inverseCoefficients (SpecialLinearFrame.frame (A x)) mu 3 *
          fderiv ℝ beta x (directions mu)) - m*c^2*Real.cos (beta x)) : ℝ) : ℂ) :=
  PolarDiracDensity.fieldDensity_polar hrho hbeta (differentiableAt_spin_field hA) hpos
    (spin_isUnit _ hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y => spin_gamma5_commute (A y)))
    (hdet.mono (fun y hy => spin_dirac_isometry (A y) hy))
    (SpecialLinearFrame.frame_expansion _ hdet.self_of_nhds) directions
    (fun mu => bodyOmega A x (directions mu)) (fun mu => body_eq_generator hA hdet (directions mu))
    hbar c m

/-- The faithful real density has the exact canonical, chiral and mass expression for actual determinant-one polar fields. -/
theorem fieldDensityRe_specialLinear {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (directions : Fin 4 → E) (hbar c m : ℝ) :
    fieldDensityRe hbar c m (polarField rho beta (fun y => spin (A y))) x directions =
      rho x * (canonicalContraction hbar c (SpecialLinearFrame.frame (A x))
        (fun mu => bodyOmega A x (directions mu)) -
        (hbar*c/2)*(∑ mu, inverseCoefficients (SpecialLinearFrame.frame (A x)) mu 3 *
          fderiv ℝ beta x (directions mu)) - m*c^2*Real.cos (beta x)) :=
  congrArg Complex.re (fieldDensity_specialLinear hrho hbeta hA hpos hdet directions hbar c m)

/-- The symmetric density of an original locally reconstructed spinor uses its canonical real frame and derived connection, with no amplitude-gradient term. -/
theorem fieldDensity_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x)
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = PolarSpinorBilinears.polarSpinor (rho y) (beta y) (spin (A y)))
    (directions : Fin 4 → E) (hbar c m : ℝ) :
    fieldDensity hbar c m psi x directions =
      ((rho x * (canonicalContraction hbar c (reconstructedFrame (psi x))
        (fun mu => bodyOmega A x (directions mu)) -
        (hbar*c/2)*(∑ mu, inverseCoefficients (reconstructedFrame (psi x)) mu 3 *
          fderiv ℝ beta x (directions mu)) - m*c^2*Real.cos (beta x)) : ℝ) : ℂ) := by
  have heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y)) := he.mono (fun _ h => h.2.2)
  rw [fieldDensity_congr heq hbar c m directions,
    fieldDensity_specialLinear hrho hbeta hA he.self_of_nhds.1
      (he.mono (fun _ h => h.2.1)) directions hbar c m, frame_of_local_polar he]

/-- The original field real density has the same exact canonical-frame expression under actual local polar equality. -/
theorem fieldDensityRe_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x)
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = PolarSpinorBilinears.polarSpinor (rho y) (beta y) (spin (A y)))
    (directions : Fin 4 → E) (hbar c m : ℝ) :
    fieldDensityRe hbar c m psi x directions =
      rho x * (canonicalContraction hbar c (reconstructedFrame (psi x))
        (fun mu => bodyOmega A x (directions mu)) -
        (hbar*c/2)*(∑ mu, inverseCoefficients (reconstructedFrame (psi x)) mu 3 *
          fderiv ℝ beta x (directions mu)) - m*c^2*Real.cos (beta x)) :=
  congrArg Complex.re (fieldDensity_of_local_polar hrho hbeta hA he directions hbar c m)

/-- Every C1 original spinor field at a strictly regular value has constructed local factors giving its actual symmetric Dirac density in the canonical frame. -/
theorem exists_reconstructed_dirac_density {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ 1 psi x) (hreg : Regular (psi x))
    (directions : Fin 4 → E) (hbar c m : ℝ) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ 1 beta x ∧ ContDiffAt ℝ 1 A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = PolarSpinorBilinears.polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      fieldDensity hbar c m psi x directions =
        ((invariantDensity (psi x) * (canonicalContraction hbar c (reconstructedFrame (psi x))
          (fun mu => bodyOmega A x (directions mu)) -
          (hbar*c/2)*(∑ mu, inverseCoefficients (reconstructedFrame (psi x)) mu 3 *
            fderiv ℝ beta x (directions mu)) - m*c^2*Real.cos (beta x)) : ℝ) : ℂ) := by
  obtain ⟨beta, A, hrho, hbeta, hA, _hL, he⟩ := LocalPolarFields.exists_local_polar_fields 1 hpsi hreg
  exact ⟨beta, A, hbeta, hA, he, fieldDensity_of_local_polar hrho.differentiableAt_one
    hbeta.differentiableAt_one hA.differentiableAt_one he directions hbar c m⟩
end FoliationQM.ReconstructedDiracDensity
