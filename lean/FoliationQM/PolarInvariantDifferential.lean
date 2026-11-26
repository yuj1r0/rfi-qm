module
public import FoliationQM.RegularPolarReconstruction
public import FoliationQM.SpinorMatrixSmooth
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
/-!
# Actual derivatives of the reconstructed invariant density and angle

Source: the regular inverse in v13 `prop:takabayasi`, `eq:takabayasi_polar`,
and the density/angle derivatives used in `lem:maurer_cartan`.
On the explicit determinant slit-plane branch, the real Frechet derivative
of the complex logarithm supplies the actual log-density and full-angle
derivatives. The determinant is the established scalar plus i times
pseudoscalar, so its real and imaginary derivative components yield the
explicit invariant formulas with positive density squared in the denominator.

All derivatives are actual Frechet derivatives of the spinor field and its
invariants. The field is differentiable and the branch condition is explicit;
no derivative array or final polar decomposition is supplied as a premise.
No global principal-angle smoothness, frame connection classification or
variational equation is inferred from these inverse-coordinate identities.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.PolarInvariantDifferential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The actual complex logarithm of a real-differentiable field has the reciprocal-scaled Frechet derivative on the slit plane. -/
theorem hasFDerivAt_log {z : E → ℂ} {dz : E →L[ℝ] ℂ} {x : E}
    (hz : HasFDerivAt z dz x) (hcut : z x ∈ Complex.slitPlane) :
    HasFDerivAt (fun y => Complex.log (z y)) ((z x)⁻¹ • dz) x := by
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, Function.comp_def] using! (Complex.hasStrictFDerivAt_log_real hcut).hasFDerivAt.comp x hz
/-- The actual log-norm derivative is the real component of the reciprocal-scaled complex field derivative. -/
theorem hasFDerivAt_log_norm {z : E → ℂ} {dz : E →L[ℝ] ℂ} {x : E}
    (hz : HasFDerivAt z dz x) (hcut : z x ∈ Complex.slitPlane) :
    HasFDerivAt (fun y => Real.log ‖z y‖) (Complex.reCLM.comp ((z x)⁻¹ • dz)) x := by
  have hl := hasFDerivAt_log hz hcut
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] using
    Complex.reCLM.hasFDerivAt.comp x hl
/-- The actual principal-argument derivative is the imaginary component of the reciprocal-scaled complex field derivative on its slit-plane branch. -/
theorem hasFDerivAt_arg {z : E → ℂ} {dz : E →L[ℝ] ℂ} {x : E}
    (hz : HasFDerivAt z dz x) (hcut : z x ∈ Complex.slitPlane) :
    HasFDerivAt (fun y => Complex.arg (z y)) (Complex.imCLM.comp ((z x)⁻¹ • dz)) x := by
  have hl := hasFDerivAt_log hz hcut
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    Complex.imCLM.hasFDerivAt.comp x hl
/-- The actual log-norm directional derivative is the real part of the complex derivative divided by its nonzero field value. -/
theorem fderiv_log_norm_apply {z : E → ℂ} {x : E}
    (hz : DifferentiableAt ℝ z x) (hcut : z x ∈ Complex.slitPlane) (v : E) :
    fderiv ℝ (fun y => Real.log ‖z y‖) x v = (fderiv ℝ z x v / z x).re := by
  rw [(hasFDerivAt_log_norm hz.hasFDerivAt hcut).fderiv]
  simp [ContinuousLinearMap.comp_apply, div_eq_mul_inv, mul_comm]
/-- The actual principal-argument directional derivative is the imaginary part of the complex derivative divided by its field value. -/
theorem fderiv_arg_apply {z : E → ℂ} {x : E}
    (hz : DifferentiableAt ℝ z x) (hcut : z x ∈ Complex.slitPlane) (v : E) :
    fderiv ℝ (fun y => Complex.arg (z y)) x v = (fderiv ℝ z x v / z x).im := by
  rw [(hasFDerivAt_arg hz.hasFDerivAt hcut).fderiv]
  simp [ContinuousLinearMap.comp_apply, div_eq_mul_inv, mul_comm]
open DiracMatrices SpinorMatrix SpinorRegularity RegularPolarReconstruction
private theorem differentiableAt_detField {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) :
    DifferentiableAt ℝ (fun y => Matrix.det (toMatrix (psi y))) x :=
  ((SpinorMatrixSmooth.contDiff_spinorDet 1).differentiable (by norm_num)).differentiableAt.comp x hpsi

/-- The reconstructed actual log-density derivative is the real part of the derivative of the spinor determinant divided by that determinant. -/
theorem fderiv_logDensity_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hcut : Matrix.det (toMatrix (psi x)) ∈ Complex.slitPlane)
    (v : E) :
    fderiv ℝ (fun y => Real.log (invariantDensity (psi y))) x v =
      (fderiv ℝ (fun y => Matrix.det (toMatrix (psi y))) x v /
        Matrix.det (toMatrix (psi x))).re := by
  simpa only [norm_det_toMatrix] using fderiv_log_norm_apply (differentiableAt_detField hpsi) hcut v

/-- The reconstructed full-angle derivative is the imaginary part of the actual determinant logarithmic derivative on the stated branch. -/
theorem fderiv_determinantPhase_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hcut : Matrix.det (toMatrix (psi x)) ∈ Complex.slitPlane)
    (v : E) :
    fderiv ℝ (fun y => determinantPhase (psi y)) x v =
      (fderiv ℝ (fun y => Matrix.det (toMatrix (psi y))) x v /
        Matrix.det (toMatrix (psi x))).im :=
  fderiv_arg_apply (differentiableAt_detField hpsi) hcut v

private theorem fderiv_scalar_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (v : E) :
    fderiv ℝ (fun y => scalar (psi y)) x v =
      (fderiv ℝ (fun y => Matrix.det (toMatrix (psi y))) x v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x (differentiableAt_detField hpsi).hasFDerivAt
  have h' : HasFDerivAt (fun y => scalar (psi y))
      (Complex.reCLM.comp (fderiv ℝ (fun y => Matrix.det (toMatrix (psi y))) x)) x := by
    simpa only [Function.comp_def, Complex.reCLM_apply, det_toMatrix_re] using h
  rw [h'.fderiv]
  rfl

private theorem fderiv_pseudoscalar_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (v : E) :
    fderiv ℝ (fun y => pseudoscalar (psi y)) x v =
      (fderiv ℝ (fun y => Matrix.det (toMatrix (psi y))) x v).im := by
  have h := Complex.imCLM.hasFDerivAt.comp x (differentiableAt_detField hpsi).hasFDerivAt
  have h' : HasFDerivAt (fun y => pseudoscalar (psi y))
      (Complex.imCLM.comp (fderiv ℝ (fun y => Matrix.det (toMatrix (psi y))) x)) x := by
    simpa only [Function.comp_def, Complex.imCLM_apply, det_toMatrix_im] using h
  rw [h'.fderiv]
  rfl

/-- The actual log-density derivative equals the scalar/pseudoscalar radial derivative divided by the strict invariant density squared. -/
theorem fderiv_logDensity_invariants {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hcut : Matrix.det (toMatrix (psi x)) ∈ Complex.slitPlane)
    (v : E) :
    fderiv ℝ (fun y => Real.log (invariantDensity (psi y))) x v =
      (scalar (psi x) * fderiv ℝ (fun y => scalar (psi y)) x v +
        pseudoscalar (psi x) * fderiv ℝ (fun y => pseudoscalar (psi y)) x v) /
          (invariantDensity (psi x))^2 := by
  rw [fderiv_logDensity_apply hpsi hcut, Complex.div_re, Complex.normSq_eq_norm_sq,
    norm_det_toMatrix, det_toMatrix_re, det_toMatrix_im,
    fderiv_scalar_apply hpsi, fderiv_pseudoscalar_apply hpsi]
  ring

/-- The actual full-angle derivative equals the oriented scalar/pseudoscalar angular derivative divided by the strict invariant density squared. -/
theorem fderiv_determinantPhase_invariants {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hcut : Matrix.det (toMatrix (psi x)) ∈ Complex.slitPlane)
    (v : E) :
    fderiv ℝ (fun y => determinantPhase (psi y)) x v =
      (scalar (psi x) * fderiv ℝ (fun y => pseudoscalar (psi y)) x v -
        pseudoscalar (psi x) * fderiv ℝ (fun y => scalar (psi y)) x v) /
          (invariantDensity (psi x))^2 := by
  rw [fderiv_determinantPhase_apply hpsi hcut, Complex.div_im, Complex.normSq_eq_norm_sq,
    norm_det_toMatrix, det_toMatrix_re, det_toMatrix_im,
    fderiv_scalar_apply hpsi, fderiv_pseudoscalar_apply hpsi]
  ring
end FoliationQM.PolarInvariantDifferential
