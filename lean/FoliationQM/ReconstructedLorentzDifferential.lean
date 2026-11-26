module
public import FoliationQM.ReconstructedPolarDifferential
public import FoliationQM.SpecialLinearConnection
/-!
# Actual Lorentz-generator derivatives of original regular spinor fields

Sources: v13 `eq:d_psi_polar_main`, `eq:d_psibar_polar_main`, and the local
reconstruction in `prop:takabayasi`. The local determinant-one matrix
constraint gives explicit real antisymmetric Lorentz coefficients of the
actual body and spatial connections. Substituting those proved expansions
into the genuine polar Frechet derivative gives the source column and
Dirac-adjoint row formulas for the original field.

The final theorem constructs the local angle and determinant-one matrix
fields from C1 regularity of the original spinor field alone. No polar
representation, real frame, derivative, or generator expansion is supplied
as a premise. The density is the original scalar-pseudoscalar invariant.
The quarter-normalized generator uses the established upper-index sigma
basis; the equivalent body formulation retains its actual representative
conjugation. A global smooth angle, abstract Spin classification, and
variational equivalences are not asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.ReconstructedLorentzDifferential
open DiracMatrices SpinorMatrix SpecialLinearSpin
open PolarSpinorBilinears PolarSpinorDifferential MatrixDifferential
open ReconstructedPolarDifferential SpecialLinearConnection CliffordCommutators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual local determinant-one polar data gives the original spinor derivative with the explicitly derived real spatial Lorentz generator. -/
theorem fderiv_of_local_polar_generator {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) (v : E) :
    fderiv ℝ psi x v =
      (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
        (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 +
        generator (spatialOmega A x v)).mulVec (psi x) := by
  rw [fderiv_of_local_polar hrho hbeta hA hpos hdet.self_of_nhds heq v,
    spatial_eq_generator hA hdet v]

/-- The actual original Dirac-adjoint derivative has the same half-log and chiral signs and the negative constructed spatial Lorentz generator. -/
theorem fderiv_adjoint_of_local_polar_generator {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) (v : E) :
    fderiv ℝ (fun y => spinorAdjoint (psi y)) x v =
      Matrix.vecMul (spinorAdjoint (psi x))
        (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 -
          generator (spatialOmega A x v)) := by
  rw [fderiv_adjoint_of_local_polar hrho hbeta hA hpos hdet heq v,
    spatial_eq_generator hA hdet v]

/-- The same genuine original column derivative can be written using the constructed body coefficients with their actual representative conjugation. -/
theorem fderiv_of_local_polar_body_generator {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) (v : E) :
    fderiv ℝ psi x v =
      (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
        (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 +
        spin (A x) * generator (bodyOmega A x v) * (spin (A x))⁻¹).mulVec (psi x) := by
  rw [fderiv_of_local_polar_generator hrho hbeta hA hpos hdet heq v,
    generators_conjugate hA hdet v]

/-- The actual original adjoint-row derivative has the negative genuinely conjugated body generator, with no assumed connection expansion. -/
theorem fderiv_adjoint_of_local_polar_body_generator {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (heq : psi =ᶠ[𝓝 x] polarField rho beta (fun y => spin (A y))) (v : E) :
    fderiv ℝ (fun y => spinorAdjoint (psi y)) x v =
      Matrix.vecMul (spinorAdjoint (psi x))
        (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 -
          spin (A x) * generator (bodyOmega A x v) * (spin (A x))⁻¹) := by
  rw [fderiv_adjoint_of_local_polar_generator hrho hbeta hA hpos hdet heq v,
    generators_conjugate hA hdet v]

open SpinorRegularity

/-- Every C1 spinor field at a strict regular value has constructed local polar fields whose explicit real Lorentz coefficients give both genuine original-field derivatives, with no supplied polar, frame or generator data. -/
theorem exists_reconstructed_lorentz_derivatives {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ 1 psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ 1 beta x ∧ ContDiffAt ℝ 1 A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      (∀ v : E, fderiv ℝ psi x v =
        (((fderiv ℝ (fun y => Real.log (invariantDensity (psi y))) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 +
          generator (spatialOmega A x v)).mulVec (psi x)) ∧
      (∀ v : E, fderiv ℝ (fun y => spinorAdjoint (psi y)) x v =
        Matrix.vecMul (spinorAdjoint (psi x))
          (((fderiv ℝ (fun y => Real.log (invariantDensity (psi y))) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
            (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 -
            generator (spatialOmega A x v))) := by
  obtain ⟨beta, A, hbeta, hA, hevent, hcolumn, hrow⟩ :=
    exists_reconstructed_derivative_and_adjoint hpsi hreg
  have hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1 := hevent.mono (fun _ hy => hy.2.1)
  refine ⟨beta, A, hbeta, hA, hevent, ?_, ?_⟩
  · intro v
    rw [hcolumn v, spatial_eq_generator hA.differentiableAt_one hdet v]
  · intro v
    rw [hrow v, spatial_eq_generator hA.differentiableAt_one hdet v]

end FoliationQM.ReconstructedLorentzDifferential
