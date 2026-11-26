module

public import FoliationQM.AuxiliaryMetricEnergy
public import FoliationQM.CurvedGradientCovariance

/-!
# Positive metric energy under regular coordinate changes

Source: v13 `thm:wallstrom` Part (c) and `eq:weak_pde_cutoff_bound`,
component kinds A and C. The actual positive volume density and inverse-metric
differential energy transform by the absolute Jacobian. Integrability is
transported before the corresponding integral identity is used. These are
coordinate identities; adapted nodal charts and normal distance are separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.AuxiliaryMetricPullback

open MeasureTheory Set LorentzMatrixGroup AuxiliaryMetricEnergy
open RNCCoordinateVolumeChange RNCCoordinateConnection CurvedGradientCovariance
open scoped Matrix.Norms.Operator

/-- The positive metric volume density gains the absolute coordinate Jacobian. -/
theorem density_pullMatrix (J H : Mat4) :
    density (pullMatrix J H) = |J.det| * density H := by
  rw [density, det_pullMatrix, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

/-- Pullback by a nonsingular Jacobian preserves positive definiteness. -/
theorem posDef_pullMatrix {H J : Mat4} (hH : H.PosDef) (hJ : IsUnit J.det) :
    (pullMatrix J H).PosDef := by
  have hu : IsUnit J := J.isUnit_iff_isUnit_det.mpr hJ
  simpa only [pullMatrix, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mpr hH

private theorem realEnergy_eq_form (H : Mat4) (a : Covector) :
    realEnergy H a = RNCHalfDensityJet.form H⁻¹ a a := by
  simp only [realEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum,
    RNCHalfDensityJet.form_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Transforming both the metric and a covector leaves its dual energy unchanged. -/
theorem realEnergy_pullMatrix (H J : Mat4) (hJ : IsUnit J.det) (a : Covector) :
    realEnergy (pullMatrix J H) (J.transpose.mulVec a) = realEnergy H a := by
  simpa only [realEnergy_eq_form] using pairing_matrices H J hJ a a

/-- The pulled positive density uses the determinant of the actual differential. -/
theorem density_pullMetric (H : Covector → Mat4) (φ : Covector → Covector)
    (D : Covector → Covector →L[ℝ] Covector) (x : Covector) :
    density (pullMetric H φ D x) = |(D x).det| * density (H (φ x)) := by
  rw [pullMetric, density_pullMatrix, det_jacobianMatrix]

/-- The actual differential of a composed real scalar has invariant dual energy. -/
theorem realEnergy_pullback (H : Covector → Mat4) {φ : Covector → Covector}
    {D : Covector → Covector →L[ℝ] Covector} {x : Covector}
    (hφ : HasFDerivAt φ (D x) x) (hD : IsUnit (D x).det) {f : Covector → ℝ}
    (hf : DifferentiableAt ℝ f (φ x)) :
    realEnergy (pullMetric H φ D x) (components (f ∘ φ) x) =
      realEnergy (H (φ x)) (components f (φ x)) := by
  rw [components_pullback hφ hf]
  exact realEnergy_pullMatrix _ _ (by simpa only [det_jacobianMatrix] using hD) _

private theorem complexEnergy_components (H : Mat4) {f : Covector → ℂ} {x : Covector}
    (hf : DifferentiableAt ℝ f x) :
    complexEnergy H (fun i => fderiv ℝ f x (axis i)) =
      realEnergy H (components (fun y => (f y).re) x) +
        realEnergy H (components (fun y => (f y).im) x) := by
  have hr : components (fun y => (f y).re) x =
      fun i => (fderiv ℝ f x (axis i)).re := by
    ext i
    change fderiv ℝ (fun y => (f y).re) x (axis i) = (fderiv ℝ f x (axis i)).re
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      Complex.reCLM_apply] using
      congrArg (fun L : Covector →L[ℝ] ℝ => L (axis i))
        (Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  have hi : components (fun y => (f y).im) x =
      fun i => (fderiv ℝ f x (axis i)).im := by
    ext i
    change fderiv ℝ (fun y => (f y).im) x (axis i) = (fderiv ℝ f x (axis i)).im
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      Complex.imCLM_apply] using
      congrArg (fun L : Covector →L[ℝ] ℝ => L (axis i))
        (Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  rw [hr, hi]
  rfl

/-- Real and imaginary differential covariance gives the actual complex energy law. -/
theorem complexEnergy_pullback (H : Covector → Mat4) {φ : Covector → Covector}
    {D : Covector → Covector →L[ℝ] Covector} {x : Covector}
    (hφ : HasFDerivAt φ (D x) x) (hD : IsUnit (D x).det) {f : Covector → ℂ}
    (hf : DifferentiableAt ℝ f (φ x)) :
    complexEnergy (pullMetric H φ D x) (fun i => fderiv ℝ (f ∘ φ) x (axis i)) =
      complexEnergy (H (φ x)) (fun i => fderiv ℝ f (φ x) (axis i)) := by
  rw [complexEnergy_components _ (hf.comp x hφ.differentiableAt),
    complexEnergy_components _ hf]
  exact congrArg₂ (· + ·)
    (realEnergy_pullback H hφ hD (Complex.reCLM.differentiableAt.comp _ hf))
    (realEnergy_pullback H hφ hD (Complex.imCLM.differentiableAt.comp _ hf))

/-- Density times the actual real differential energy transforms by the absolute Jacobian. -/
theorem weighted_realEnergy_pullback (H : Covector → Mat4) {φ : Covector → Covector}
    {D : Covector → Covector →L[ℝ] Covector} {x : Covector}
    (hφ : HasFDerivAt φ (D x) x) (hD : IsUnit (D x).det) {f : Covector → ℝ}
    (hf : DifferentiableAt ℝ f (φ x)) :
    density (pullMetric H φ D x) * realEnergy (pullMetric H φ D x)
        (components (f ∘ φ) x) =
      |(D x).det| * (density (H (φ x)) * realEnergy (H (φ x)) (components f (φ x))) := by
  rw [density_pullMetric, realEnergy_pullback H hφ hD hf, mul_assoc]

/-- The density-weighted actual complex differential obeys the same Jacobian law. -/
theorem weighted_complexEnergy_pullback (H : Covector → Mat4) {φ : Covector → Covector}
    {D : Covector → Covector →L[ℝ] Covector} {x : Covector}
    (hφ : HasFDerivAt φ (D x) x) (hD : IsUnit (D x).det) {f : Covector → ℂ}
    (hf : DifferentiableAt ℝ f (φ x)) :
    density (pullMetric H φ D x) * complexEnergy (pullMetric H φ D x)
        (fun i => fderiv ℝ (f ∘ φ) x (axis i)) =
      |(D x).det| * (density (H (φ x)) * complexEnergy (H (φ x))
        (fun i => fderiv ℝ f (φ x) (axis i))) := by
  rw [density_pullMetric, complexEnergy_pullback H hφ hD hf, mul_assoc]

variable {s : Set Covector} {φ : Covector → Covector}
  {D : Covector → Covector →L[ℝ] Covector}

/-- Genuine integrability of real differential energy is equivalent in regular injective coordinates. -/
theorem realEnergy_integrableOn_pullback_iff (H : Covector → Mat4) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : InjOn φ s)
    (hD : ∀ x ∈ s, IsUnit (D x).det) {f : Covector → ℝ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x)) :
    IntegrableOn (fun y => density (H y) * realEnergy (H y) (components f y)) (φ '' s) volume ↔
      IntegrableOn (fun x => density (pullMetric H φ D x) *
        realEnergy (pullMetric H φ D x) (components (f ∘ φ) x)) s volume := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  simpa only [smul_eq_mul] using
    (weighted_realEnergy_pullback H (hφ x hx) (hD x hx) (hf x hx)).symm

/-- Actual target integrability supplies source integrability before the real energy integral identity. -/
theorem realEnergy_integral_transport (H : Covector → Mat4) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : InjOn φ s)
    (hD : ∀ x ∈ s, IsUnit (D x).det) {f : Covector → ℝ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x))
    (hi : IntegrableOn (fun y => density (H y) * realEnergy (H y) (components f y))
      (φ '' s) volume) :
    IntegrableOn (fun x => density (pullMetric H φ D x) *
        realEnergy (pullMetric H φ D x) (components (f ∘ φ) x)) s volume ∧
      (∫ x in s, density (pullMetric H φ D x) *
        realEnergy (pullMetric H φ D x) (components (f ∘ φ) x)) =
        ∫ y in φ '' s, density (H y) * realEnergy (H y) (components f y) := by
  have hsource := (realEnergy_integrableOn_pullback_iff H hs hφ hinj hD hf).mp hi
  refine ⟨hsource, ?_⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  simpa only [smul_eq_mul] using
    weighted_realEnergy_pullback H (hφ x hx) (hD x hx) (hf x hx)

/-- Genuine integrability of the complex differential energy is transported in both directions. -/
theorem complexEnergy_integrableOn_pullback_iff (H : Covector → Mat4) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : InjOn φ s)
    (hD : ∀ x ∈ s, IsUnit (D x).det) {f : Covector → ℂ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x)) :
    IntegrableOn (fun y => density (H y) * complexEnergy (H y)
      (fun i => fderiv ℝ f y (axis i))) (φ '' s) volume ↔
      IntegrableOn (fun x => density (pullMetric H φ D x) * complexEnergy (pullMetric H φ D x)
        (fun i => fderiv ℝ (f ∘ φ) x (axis i))) s volume := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  simpa only [smul_eq_mul] using
    (weighted_complexEnergy_pullback H (hφ x hx) (hD x hx) (hf x hx)).symm

/-- Target complex energy integrability yields source integrability and the exact energy integral. -/
theorem complexEnergy_integral_transport (H : Covector → Mat4) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : InjOn φ s)
    (hD : ∀ x ∈ s, IsUnit (D x).det) {f : Covector → ℂ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x))
    (hi : IntegrableOn (fun y => density (H y) * complexEnergy (H y)
      (fun i => fderiv ℝ f y (axis i))) (φ '' s) volume) :
    IntegrableOn (fun x => density (pullMetric H φ D x) * complexEnergy (pullMetric H φ D x)
        (fun i => fderiv ℝ (f ∘ φ) x (axis i))) s volume ∧
      (∫ x in s, density (pullMetric H φ D x) * complexEnergy (pullMetric H φ D x)
        (fun i => fderiv ℝ (f ∘ φ) x (axis i))) =
        ∫ y in φ '' s, density (H y) * complexEnergy (H y)
          (fun i => fderiv ℝ f y (axis i)) := by
  have hsource := (complexEnergy_integrableOn_pullback_iff H hs hφ hinj hD hf).mp hi
  refine ⟨hsource, ?_⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  simpa only [smul_eq_mul] using
    weighted_complexEnergy_pullback H (hφ x hx) (hD x hx) (hf x hx)

end FoliationQM.AuxiliaryMetricPullback
