module

public import FoliationQM.CurvedScalarAtlasOverlap
public import FoliationQM.CurvedMetricDerivatives

/-!
# The actual scalar gradient of a coordinate metric

The gradient raises the genuine scalar differential with the inverse
metric. Its lowering identity and regularity follow from matrix inversion
and the actual first and second Fréchet derivatives. The metric square
agrees with the established inverse-metric gradient pairing.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedScalarGradient

open LorentzMatrixGroup RNCCoordinateConnection RNCHalfDensityJet CurvedGradientCovariance
  CurvedScalarAtlasOverlap
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar gradient, obtained by raising the coordinate differential with the inverse metric. -/
def grad (g : Covector → Mat4) (f : Covector → ℝ) (x : Covector) : Covector :=
  (g x)⁻¹.mulVec (components f x)

variable {g : Covector → Mat4} {f k : Covector → ℝ} {x : Covector}

/-- Lowering a scalar gradient with the nonsingular metric recovers its actual differential. -/
theorem form_gradient (hu : IsUnit (g x).det) (u : Covector) :
    form (g x) u (grad g f x) = fderiv ℝ f x u := by
  rw [RNCLorentzContraction.form_eq_pairing, grad, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, apply_components]
  rfl

/-- The inverse-metric pairing is the first differential evaluated on the other gradient, without a nonsingularity premise. -/
theorem pairing_eq_fderiv_grad (g : Covector → Mat4) (f k : Covector → ℝ) (x : Covector) :
    pairing g f k x = fderiv ℝ f x (grad g k x) := by
  rw [pairing, RNCLorentzContraction.form_eq_pairing,
    apply_components (fderiv ℝ f x) (grad g k x)]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A gradient's metric square equals its inverse-metric differential pairing. -/
theorem form_grad_self (hu : IsUnit (g x).det) (f : Covector → ℝ) :
    form (g x) (grad g f x) (grad g f x) = pairing g f f x := by
  rw [form_gradient hu, pairing_eq_fderiv_grad]

/-- Lowering the second gradient gives the pairing with the corresponding reversed covector order. -/
theorem form_grad_cross (hu : IsUnit (g x).det) (f k : Covector → ℝ) :
    form (g x) (grad g f x) (grad g k x) = pairing g k f x := by
  rw [form_gradient hu, pairing_eq_fderiv_grad]

/-- Continuous metric data remain invertible on a neighborhood of every invertible metric value. -/
theorem eventually_isUnit (hg : ContinuousAt g x) (hu : IsUnit (g x).det) :
    ∀ᶠ y in 𝓝 x, IsUnit (g y) :=
  hg.eventually (Units.isOpen.mem_nhds ((g x).isUnit_iff_isUnit_det.mpr hu))

/-- The metric determinant remains a unit near an invertible continuous metric value. -/
theorem eventually_isUnit_det (hg : ContinuousAt g x) (hu : IsUnit (g x).det) :
    ∀ᶠ y in 𝓝 x, IsUnit (g y).det :=
  (eventually_isUnit hg hu).mono fun y hy => (g y).isUnit_iff_isUnit_det.mp hy

/-- A differentiable metric and a locally C² scalar give an actually differentiable gradient. -/
theorem differentiableAt_grad (hg : DifferentiableAt ℝ g x) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (grad g f) x := by
  have hi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x :=
    (LorentzCayleySmooth.contDiffAt_inverse 1 ((g x).isUnit_iff_isUnit_det.mpr hu)).differentiableAt_one.comp x hg
  have hdf := (hf.fderiv_right (m := 1) (by decide)).differentiableAt_one
  apply differentiableAt_pi.mpr
  intro i
  change DifferentiableAt ℝ (fun y => ∑ j, (g y)⁻¹ i j * fderiv ℝ f y (axis j)) x
  apply DifferentiableAt.fun_sum
  intro j _
  let entry : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  exact (entry.differentiableAt.comp x hi).fun_mul
    ((ContinuousLinearMap.apply ℝ ℝ (axis j)).differentiableAt.comp x hdf)

/-- A locally C¹ metric and locally C² scalar give a locally C¹ actual gradient. -/
theorem contDiffAt_grad (hg : ContDiffAt ℝ 1 g x) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (grad g f) x := by
  have hi : ContDiffAt ℝ 1 (fun y => (g y)⁻¹) x :=
    (LorentzCayleySmooth.contDiffAt_inverse 1 ((g x).isUnit_iff_isUnit_det.mpr hu)).comp x hg
  have hdf := hf.fderiv_right (m := 1) (by decide)
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun y => ∑ j, (g y)⁻¹ i j * fderiv ℝ f y (axis j)) x
  apply ContDiffAt.sum
  intro j _
  let entry : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  exact (entry.contDiff.contDiffAt.comp x hi).mul
    ((ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.contDiffAt.comp x hdf)

/-- Pairing two C² scalar differentials through a C¹ metric gives a C¹ scalar field. -/
theorem contDiffAt_pairing (hg : ContDiffAt ℝ 1 g x) (hu : IsUnit (g x).det)
    (hf : ContDiffAt ℝ 2 f x) (hk : ContDiffAt ℝ 2 k x) :
    ContDiffAt ℝ 1 (pairing g f k) x := by
  have he : pairing g f k = fun y => fderiv ℝ f y (grad g k y) :=
    funext (pairing_eq_fderiv_grad g f k)
  rw [he]
  exact (hf.fderiv_right (m := 1) (by decide)).clm_apply (contDiffAt_grad hg hu hk)

/-- The gradient of a constant scalar field vanishes in every metric. -/
theorem grad_const (g : Covector → Mat4) (c : ℝ) (x : Covector) :
    grad g (fun _ => c) x = 0 := by
  have hc : components (fun _ : Covector => c) x = 0 := by
    funext i
    change fderiv ℝ (fun _ : Covector => c) x (axis i) = 0
    simp
  rw [grad, hc, Matrix.mulVec_zero]

/-- A fixed real scalar multiple of a differentiable field has the correspondingly scaled gradient. -/
theorem grad_const_mul (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    grad g (fun y => c * f y) x = c • grad g f x := by
  have hd := hf.hasFDerivAt.const_mul c
  have hc : components (fun y => c * f y) x = c • components f x := by
    funext i
    change fderiv ℝ (fun y => c * f y) x (axis i) = c * fderiv ℝ f x (axis i)
    rw [hd.fderiv]
    rfl
  rw [grad, hc, Matrix.mulVec_smul]
  rfl

end FoliationQM.CurvedScalarGradient
