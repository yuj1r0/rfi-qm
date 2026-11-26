module

public import FoliationQM.RNCHalfDensityProduct
public import FoliationQM.RNCScalarWaveCenter

/-!
# Curvature coefficient of the centered DeWitt half-density ordering

Theorem 9.2 selects the symmetric second-order expression at the event. Its
value contains the local scalar-curvature term. Evaluating the first-order
gradient of the same weighted amplitude at that event gives the usual
metric gradient. The two evaluations are performed on actual fields.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.RNCDeWittOrdering

open LorentzMatrixGroup RNCCoordinateConnection RNCNormalChart RNCVolumeDensity
open RNCCoordinateCurvature PolarSecondDifferential

/-- The coordinate amplitude after applying the metric half-density multiplier. -/
def amplitude (g : Covector → Mat4) (R : Covector → ℝ) (y : Covector) : ℝ :=
  metricWeight (g y) * R y

/-- The chosen symmetric ordering in tangent coordinates at the center. -/
def symmetricKinetic (ℏ : ℝ) (g : Covector → Mat4) (R : Covector → ℝ) : ℝ :=
  -(ℏ ^ 2) * amplitude g R 0 * box (amplitude g R) axis 0

/-- The first-order scalar kinetic density using the actual inverse metric entries at the event. -/
def gradientKinetic (ℏ : ℝ) (g : Covector → Mat4) (R : Covector → ℝ) : ℝ :=
  ℏ ^ 2 * ∑ i, ∑ j, (g 0)⁻¹ i j * fderiv ℝ R 0 (axis i) * fderiv ℝ R 0 (axis j)

variable {g : Covector → Mat4} {R : Covector → ℝ}

/-- The normal-center value of the half-density amplitude equals the scalar amplitude. -/
theorem amplitude_zero (h : IsNormal g) (R : Covector → ℝ) : amplitude g R 0 = R 0 := by
  simp only [amplitude, h.metric_center, center_values.2, one_mul]

/-- At the center the raw first-order gradient kinetic density receives no local curvature correction. -/
theorem raw_gradient (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hR : ContDiffAt ℝ 2 R 0) (ℏ : ℝ) :
    gradientKinetic ℏ g (amplitude g R) = gradientKinetic ℏ g R := by
  have hd : fderiv ℝ (amplitude g R) 0 = fderiv ℝ R 0 := RNCHalfDensityProduct.gradient_weighted h hg hR
  simp only [gradientKinetic, hd]

/-- The symmetric ordering contributes positive ℏ² scalar curvature times R²/6 to the local action density. -/
theorem symmetric_center (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0)
    (hR : ContDiffAt ℝ 2 R 0) (ℏ : ℝ) :
    symmetricKinetic ℏ g R = -(ℏ ^ 2) * R 0 * RNCScalarWaveCenter.wave g R 0 +
      (ℏ ^ 2 / 6) * scalar g 0 * (R 0) ^ 2 := by
  have hb : box (amplitude g R) axis 0 = box R axis 0 - R 0 * scalar g 0 / 6 :=
    RNCHalfDensityProduct.box_weighted h hg hR
  rw [symmetricKinetic, amplitude_zero h, hb, RNCScalarWaveCenter.wave_center h (hg.differentiableAt (by decide)) hR]
  ring

/-- With R = √ρ the geometric term in the centered density is exactly +ℏ² Scal ρ/6. -/
theorem density_center (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) {ρ : Covector → ℝ}
    (hρ : ContDiffAt ℝ 2 ρ 0) (hp : 0 < ρ 0) (ℏ : ℝ) :
    symmetricKinetic ℏ g (fun y => Real.sqrt (ρ y)) =
      -(ℏ ^ 2) * Real.sqrt (ρ 0) * RNCScalarWaveCenter.wave g (fun y => Real.sqrt (ρ y)) 0 +
      (ℏ ^ 2 / 6) * scalar g 0 * ρ 0 := by
  rw [symmetric_center h hg (hρ.sqrt hp.ne')]
  rw [Real.sq_sqrt hp.le]

/-- On a nonzero curvature-density probe the centered ordering determines the coefficient uniquely. -/
theorem coefficient_unique (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0)
    (hR : ContDiffAt ℝ 2 R 0) {ℏ ξ : ℝ} (hb : ℏ ≠ 0) (hc : scalar g 0 ≠ 0) (hr : R 0 ≠ 0)
    (hξ : symmetricKinetic ℏ g R = -(ℏ ^ 2) * R 0 * RNCScalarWaveCenter.wave g R 0 +
      ℏ ^ 2 * ξ * scalar g 0 * (R 0) ^ 2) : ξ = 1 / 6 := by
  have he := (symmetric_center h hg hR ℏ).symm.trans hξ
  have hz : (ξ - 1 / 6) * (ℏ ^ 2 * scalar g 0 * R 0 ^ 2) = 0 := by linarith only [he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hb) hc) (pow_ne_zero _ hr)))

end FoliationQM.RNCDeWittOrdering
