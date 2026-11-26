module

public import FoliationQM.CurvedHessianOverlap
public import FoliationQM.CurvedScalarGradient
public import FoliationQM.CurvedCovariantDerivative

/-!
# Metric gradients, covariant Hessians and differentiation of the mass shell

The gradient is raised with the actual inverse metric. Differentiating its
metric-lowering identity and using the Koszul connection identifies its
covariant derivative with the genuine scalar Hessian. Symmetry of that
Hessian then relates gradient acceleration to half the gradient of its
indefinite metric square, as required for v13's quantum-force identity.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedGradientHessian

open LorentzMatrixGroup RNCHalfDensityJet CurvedGradientCovariance
  CurvedScalarAtlasOverlap CurvedHessianOverlap
open CurvedScalarGradient CurvedCovariantDerivative

variable {g : Covector → Mat4} {f : Covector → ℝ} {x : Covector}

/-- Differentiating the actual differential evaluated on a fixed vector gives the corresponding mixed second derivative. -/
theorem derivative_differential (hf : ContDiffAt ℝ 2 f x) (u v : Covector) :
    fderiv ℝ (fun y => fderiv ℝ f y u) x v = fderiv ℝ (fderiv ℝ f) x v u := by
  have H := (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp x
    (hf.fderiv_right (m := 1) (by decide)).differentiableAt_one.hasFDerivAt
  exact congrArg (fun L : Covector →L[ℝ] ℝ => L v) H.fderiv

/-- Symmetry of the actual second differential and of the Koszul connection gives a symmetric scalar covariant Hessian. -/
theorem hess_symmetric (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hf : ContDiffAt ℝ 2 f x) (u v : Covector) :
    hess g f x u v = hess g f x v u := by
  simp only [hess, hf.isSymmSndFDerivAt (by simp) u v, connection_symmetric hg hs u v]

/-- The covariant derivative of the actual raised gradient lowers to the scalar covariant Hessian. -/
theorem form_covDeriv_grad (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) (u v : Covector) :
    form (g x) u (covDeriv g (grad g f) x v) = hess g f x v u := by
  have hgrad := differentiableAt_grad hg hu hf
  have he : (fun y => form (g y) u (grad g f y)) =ᶠ[𝓝 x]
      fun y => fderiv ℝ f y u := by
    filter_upwards [eventually_isUnit hg.continuousAt hu] with y hy
    exact form_gradient ((g y).isUnit_iff_isUnit_det.mp hy) u
  have H := metric_compatibility hg hs hu (differentiableAt_const (c := u)) hgrad v
  change fderiv ℝ (fun y => form (g y) u (grad g f y)) x v = _ at H
  rw [he.fderiv_eq, derivative_differential hf u v] at H
  have hc := covDeriv_const g u x v
  rw [hc, form_gradient hu] at H
  unfold hess
  linarith only [H]

/-- Differentiating the inverse-metric phase-gradient square gives twice its metric pairing with the covariant gradient derivative. -/
theorem pairing_derivative (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) (v : Covector) :
    fderiv ℝ (pairing g f f) x v =
      2 * form (g x) (grad g f x) (covDeriv g (grad g f) x v) := by
  have he : (fun y => form (g y) (grad g f y) (grad g f y)) =ᶠ[𝓝 x]
      pairing g f f := by
    filter_upwards [eventually_isUnit hg.continuousAt hu] with y hy
    exact form_grad_self ((g y).isUnit_iff_isUnit_det.mp hy) f
  have H := norm_derivative hg hs hu (differentiableAt_grad hg hu hf) v
  rw [he.fderiv_eq] at H
  exact H

/-- The derivative of the actual gradient square is twice the covariant Hessian paired with the raised gradient. -/
theorem pairing_derivative_hess (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) (v : Covector) :
    fderiv ℝ (pairing g f f) x v = 2 * hess g f x v (grad g f x) := by
  rw [pairing_derivative hg hs hu hf v, form_covDeriv_grad hg hs hu hf]

/-- The acceleration of an actual metric gradient is half the raised derivative of its indefinite metric square. -/
theorem acceleration_grad (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) :
    acceleration g (grad g f) x = (1 / 2 : ℝ) • grad g (pairing g f f) x := by
  apply eq_of_form_eq hu
  intro v
  rw [map_smul, smul_eq_mul, form_gradient hu]
  calc
    form (g x) v (acceleration g (grad g f) x) = hess g f x (grad g f x) v :=
      form_covDeriv_grad hg hs hu hf v (grad g f x)
    _ = hess g f x v (grad g f x) := hess_symmetric hg hs hf _ _
    _ = (1 / 2 : ℝ) * fderiv ℝ (pairing g f f) x v := by
      rw [pairing_derivative_hess hg hs hu hf v]
      ring

/-- Coordinate components of gradient acceleration use every entry of the actual inverse metric and differential. -/
theorem acceleration_grad_components (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) (a : Fin 4) :
    acceleration g (grad g f) x a = (1 / 2 : ℝ) *
      ∑ b, (g x)⁻¹ a b * fderiv ℝ (pairing g f f) x (RNCCoordinateConnection.axis b) := by
  rw [acceleration_grad hg hs hu hf]
  rfl

end FoliationQM.CurvedGradientHessian
