module

public import FoliationQM.RNCVolumeTaylor

/-!
# Scalar divergence and the wave operator at the normal center

The scalar d'Alembertian in v13 Lemma 9.1 differentiates the inverse-metric
gradient multiplied by the actual volume factor. Both metric coefficients are
stationary at the radial normal center. The remaining four second derivatives
carry the signs of the inverse Minkowski metric.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCScalarWaveCenter

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCNormalChart
open PolarSecondDifferential RNCVolumeDensity
open scoped Matrix.Norms.Operator

variable {g : Covector → Mat4} {f : Covector → ℝ}

/-- Raising the index of the actual scalar differential gives its contravariant coordinate gradient. -/
def raisedGradient (g : Covector → Mat4) (f : Covector → ℝ) (x : Covector) (i : Fin 4) : ℝ :=
  ∑ j, (g x)⁻¹ i j * fderiv ℝ f x (axis j)

/-- The coordinate flux for scalar divergence includes the metric volume multiplier. -/
def flux (g : Covector → Mat4) (f : Covector → ℝ) (x : Covector) (i : Fin 4) : ℝ :=
  volumeFactor (g x) * raisedGradient g f x i

/-- The metric scalar wave operator is the coordinate divergence of the volume-weighted gradient divided by the volume. -/
def wave (g : Covector → Mat4) (f : Covector → ℝ) (x : Covector) : ℝ :=
  (volumeFactor (g x))⁻¹ * ∑ i, fderiv ℝ (fun y => flux g f y i) x (axis i)

/-- Contracting two actual scalar differentials uses the inverse metric. -/
def gradientPairing (g : Covector → Mat4) (f q : Covector → ℝ) (x : Covector) : ℝ :=
  ∑ i, fderiv ℝ f x (axis i) * raisedGradient g q x i

/-- The inverse metric equals the Minkowski matrix at the orthonormal center. -/
theorem inverse_center (h : IsNormal g) : (g 0)⁻¹ = eta := by
  rw [h.metric_center, Matrix.inv_eq_left_inv eta_sq]

/-- Inverting the metric preserves its vanishing first derivative at the normal center. -/
theorem inverse_hasFDerivAt_zero (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) :
    HasFDerivAt (fun y => (g y)⁻¹) (0 : Covector →L[ℝ] Mat4) 0 := by
  have hi := (LorentzCayleySmooth.contDiffAt_inverse 1 (center_unit h)).differentiableAt_one.hasFDerivAt
  have hd := (hi.differentiableAt.comp 0 hg).hasFDerivAt
  rw [RNCCriticalComposition.gradient_comp_critical hg hi.differentiableAt (metric_gradient_zero h hg)] at hd
  exact hd

/-- Raising the differential index at the center multiplies each component by its signature sign. -/
theorem raisedGradient_center (h : IsNormal g) (f : Covector → ℝ) (i : Fin 4) :
    raisedGradient g f 0 i = sign i * fderiv ℝ f 0 (axis i) := by
  simp [raisedGradient, inverse_center h, eta, Matrix.diagonal_apply, ite_mul]

/-- The inverse-metric gradient contraction becomes the explicit (+---) Minkowski pairing at the center. -/
theorem gradientPairing_center (h : IsNormal g) (f q : Covector → ℝ) :
    gradientPairing g f q 0 = minkowski (fun i => fderiv ℝ f 0 (axis i))
      (fun i => fderiv ℝ q 0 (axis i)) := by
  simp [gradientPairing, raisedGradient_center h, minkowski, Fin.sum_univ_succ, sign]
  ring

/-- The derivative of each flux component at the normal center is the signed derivative
of the corresponding scalar partial, evaluated before taking its divergence. -/
theorem hasFDerivAt_flux_center (h : IsNormal g) (hg : DifferentiableAt ℝ g 0)
    (hf : ContDiffAt ℝ 2 f 0) (i : Fin 4) :
    HasFDerivAt (fun y => flux g f y i)
      (sign i • fderiv ℝ (fun y => fderiv ℝ f y (axis i)) 0) 0 := by
  let entry (j : Fin 4) : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hprod (j : Fin 4) : HasFDerivAt (fun y => (g y)⁻¹ i j * fderiv ℝ f y (axis j))
      (eta i j • fderiv ℝ (fun y => fderiv ℝ f y (axis j)) 0) 0 := by
    have he : HasFDerivAt (fun y => (g y)⁻¹ i j) (0 : Covector →L[ℝ] ℝ) 0 := by
      convert! (entry j).hasFDerivAt.comp 0 (inverse_hasFDerivAt_zero h hg) using 1
    have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y (axis j)) 0 :=
      (ContinuousLinearMap.apply ℝ ℝ (axis j)).differentiableAt.comp 0
        ((hf.fderiv_right (m := 1) (by decide)).differentiableAt_one)
    simpa only [inverse_center h, smul_zero, add_zero] using he.fun_mul hd.hasFDerivAt
  have hsum : HasFDerivAt (fun y => raisedGradient g f y i)
      (∑ j, eta i j • fderiv ℝ (fun y => fderiv ℝ f y (axis j)) 0) 0 :=
    HasFDerivAt.fun_sum fun j _ => hprod j
  have hv := RNCVolumeTaylor.volume_value_gradient h hg
  have hneg : (g 0).det < 0 := by rw [h.metric_center, eta_det]; norm_num
  have hvol : HasFDerivAt (volumeFactor ∘ g) (0 : Covector →L[ℝ] ℝ) 0 := by
    rw [← hv.2]
    exact ((RNCMetricHalfDensity.volume_smooth hneg 1).differentiableAt_one.comp 0 hg).hasFDerivAt
  have hV : volumeFactor (g 0) = 1 := hv.1
  simpa [flux, eta, Matrix.diagonal_apply, ite_smul, hV] using hvol.fun_mul hsum

/-- The actual metric-divergence wave operator specializes at the center to the signed four-coordinate d'Alembertian. -/
theorem wave_center (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) (hf : ContDiffAt ℝ 2 f 0) :
    wave g f 0 = box f axis 0 := by
  simp only [wave, h.metric_center, center_values.1, inv_one, one_mul,
    (hasFDerivAt_flux_center h hg hf _).fderiv, smul_apply, smul_eq_mul]
  have hd (i : Fin 4) : secondDirectionalDerivative f (axis i) 0 =
      fderiv ℝ (fun y => fderiv ℝ f y (axis i)) 0 (axis i) := rfl
  simp [box, hd, Fin.sum_univ_succ, sign]
  ring

end FoliationQM.RNCScalarWaveCenter
