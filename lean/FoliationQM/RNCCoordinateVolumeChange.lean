module

public import FoliationQM.RNCVolumeDensity
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Coordinate change of the metric volume and half-density

For the metric determinant in v13 `lem:rnc_half_density`, pulling back a
metric multiplies its volume factor by the absolute coordinate Jacobian.
Thus a scalar integrated against metric volume has the same integral in
both charts. The square of a scalar amplitude dressed by the half-density
obeys the same transformation law.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCCoordinateVolumeChange

open LorentzMatrixGroup RNCVolumeDensity MeasureTheory Set
open scoped ENNReal

/-- The coordinate pullback of a metric at a point with Jacobian matrix `J`. -/
def pullMatrix (J G : Mat4) : Mat4 := J.transpose * G * J

/-- A covariant two-tensor gains two determinant factors under pullback. -/
theorem det_pullMatrix (J G : Mat4) : (pullMatrix J G).det = J.det ^ 2 * G.det := by
  simp only [pullMatrix, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Coordinate volume transforms by the absolute Jacobian determinant. -/
theorem volume_pullMatrix (J G : Mat4) :
    volumeFactor (pullMatrix J G) = |J.det| * volumeFactor G := by
  rw [volumeFactor, det_pullMatrix, ← mul_neg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

/-- The metric multiplier of a scalar amplitude transforms by the square root of the Jacobian. -/
theorem weight_pullMatrix (J G : Mat4) :
    metricWeight (pullMatrix J G) = Real.sqrt |J.det| * metricWeight G := by
  rw [metricWeight, volume_pullMatrix, Real.sqrt_mul (abs_nonneg _)]
  rfl

/-- The square of the dressed amplitude acquires exactly the absolute Jacobian. -/
theorem amplitude_sq_pullMatrix (J G : Mat4) (A : ℝ) :
    (metricWeight (pullMatrix J G) * A) ^ 2 = |J.det| * (metricWeight G * A) ^ 2 := by
  rw [weight_pullMatrix, mul_assoc, mul_pow, Real.sq_sqrt (abs_nonneg _)]

/-- The matrix of a chart differential in the standard coordinate basis. -/
def jacobianMatrix (L : Covector →L[ℝ] Covector) : Mat4 := LinearMap.toMatrix' L.toLinearMap

/-- The determinant of the coordinate matrix is the determinant used in change of variables. -/
theorem det_jacobianMatrix (L : Covector →L[ℝ] Covector) :
    (jacobianMatrix L).det = L.det :=
  LinearMap.det_toMatrix' L.toLinearMap

/-- Pull back a metric field by the coordinate function and its differential. -/
def pullMetric (g : Covector → Mat4) (φ : Covector → Covector)
    (D : Covector → Covector →L[ℝ] Covector) (x : Covector) : Mat4 :=
  pullMatrix (jacobianMatrix (D x)) (g (φ x))

/-- The local volume factor is precisely the weight in the change-of-variables theorem. -/
theorem volume_pullMetric (g : Covector → Mat4) (φ : Covector → Covector)
    (D : Covector → Covector →L[ℝ] Covector) (x : Covector) :
    volumeFactor (pullMetric g φ D x) = |(D x).det| * volumeFactor (g (φ x)) := by
  rw [pullMetric, volume_pullMatrix, det_jacobianMatrix]

variable {s : Set Covector} {φ : Covector → Covector} {D : Covector → Covector →L[ℝ] Covector}

/-- Integration against metric volume on a chart image agrees with integration
against pulled-back metric volume on the measurable source. -/
theorem integral_pullMetric (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt φ (D x) s x) (hφ : InjOn φ s)
    (g : Covector → Mat4) (f : Covector → ℝ) :
    (∫ y in φ '' s, volumeFactor (g y) * f y) =
      ∫ x in s, volumeFactor (pullMetric g φ D x) * f (φ x) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hD hφ]
  simp only [smul_eq_mul, volume_pullMetric, mul_assoc]

/-- The change-of-variables identity using the canonical within-derivative of a chart. -/
theorem integral_pullMetric_fderivWithin (hs : MeasurableSet s)
    (hφd : DifferentiableOn ℝ φ s) (hφ : InjOn φ s) (g : Covector → Mat4) (f : Covector → ℝ) :
    (∫ y in φ '' s, volumeFactor (g y) * f y) =
      ∫ x in s, volumeFactor (pullMetric g φ (fderivWithin ℝ φ s) x) * f (φ x) :=
  integral_pullMetric hs (fun x hx => (hφd x hx).hasFDerivWithinAt) hφ g f

/-- The nonnegative integral transforms with the same pulled-back volume factor. -/
theorem lintegral_pullMetric (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt φ (D x) s x) (hφ : InjOn φ s)
    (g : Covector → Mat4) (f : Covector → ℝ≥0∞) :
    (∫⁻ y in φ '' s, ENNReal.ofReal (volumeFactor (g y)) * f y) =
      ∫⁻ x in s, ENNReal.ofReal (volumeFactor (pullMetric g φ D x)) * f (φ x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hD hφ]
  simp only [volume_pullMetric, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

end FoliationQM.RNCCoordinateVolumeChange
