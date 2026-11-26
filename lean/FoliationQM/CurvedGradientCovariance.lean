module

public import FoliationQM.RNCCoordinateVolumeChange
public import FoliationQM.RNCLorentzContraction
public import FoliationQM.RNCCoordinateConnection

/-!
# Coordinate covariance of the inverse-metric gradient pairing

In Theorem 9.2 the two scalar differentials transform by the transpose of
the Jacobian. Contracting against the inverse of the pulled-back metric
cancels both Jacobian factors, including for non-orthogonal coordinates.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedGradientCovariance

open LorentzMatrixGroup RNCCoordinateVolumeChange RNCCoordinateConnection RNCHalfDensityJet

/-- The coordinate components of the actual differential of a real scalar. -/
def components (f : Covector → ℝ) (x : Covector) : Covector := fun i => fderiv ℝ f x (axis i)

/-- The inverse-metric pairing of two real scalar fields. -/
def pairing (g : Covector → Mat4) (f k : Covector → ℝ) (x : Covector) : ℝ :=
  form (g x)⁻¹ (components f x) (components k x)

/-- A differential is reconstructed by pairing its coordinate components with the input direction. -/
theorem apply_components (L : Covector →L[ℝ] ℝ) (v : Covector) :
    L v = ∑ j, v j * L (axis j) := by
  calc
    _ = L (∑ j, v j • axis j) := congrArg _ (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- The gradient components of a pulled-back scalar transform with the transpose Jacobian. -/
theorem components_pullback {f : Covector → ℝ} {φ : Covector → Covector} {x : Covector}
    {D : Covector →L[ℝ] Covector} (hφ : HasFDerivAt φ D x) (hf : DifferentiableAt ℝ f (φ x)) :
    components (f ∘ φ) x = (jacobianMatrix D).transpose.mulVec (components f (φ x)) := by
  ext i
  change fderiv ℝ (f ∘ φ) x (axis i) = _
  rw [(hf.hasFDerivAt.comp x hφ).fderiv, ContinuousLinearMap.comp_apply, apply_components]
  rfl

/-- Pulling back a metric and both covectors leaves their inverse-metric contraction unchanged. -/
theorem pairing_matrices (G J : Mat4) (hu : IsUnit J.det) (p q : Covector) :
    form (pullMatrix J G)⁻¹ (J.transpose.mulVec p) (J.transpose.mulVec q) = form G⁻¹ p q := by
  have ht : IsUnit J.transpose.det := by simpa using hu
  rw [RNCLorentzContraction.form_pullback, Matrix.transpose_transpose]
  congr 1
  simp only [pullMatrix, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- The local scalar kinetic pairing is invariant under an arbitrary regular coordinate change. -/
theorem pairing_pullback (g : Covector → Mat4) {φ : Covector → Covector}
    {D : Covector → Covector →L[ℝ] Covector} {x : Covector} (hφ : HasFDerivAt φ (D x) x)
    (hu : IsUnit (jacobianMatrix (D x)).det) {f k : Covector → ℝ}
    (hf : DifferentiableAt ℝ f (φ x)) (hk : DifferentiableAt ℝ k (φ x)) :
    pairing (pullMetric g φ D) (f ∘ φ) (k ∘ φ) x = pairing g f k (φ x) := by
  unfold pairing
  rw [components_pullback hφ hf, components_pullback hφ hk]
  exact pairing_matrices _ _ hu _ _

/-- Metric-volume integrals of the scalar gradient pairing agree across a regular injective coordinate change. -/
theorem integral_pairing_pullback (g : Covector → Mat4) {s : Set Covector} (hs : MeasurableSet s)
    {φ : Covector → Covector} {D : Covector → Covector →L[ℝ] Covector}
    (hφ : ∀ x ∈ s, HasFDerivAt φ (D x) x) (hinj : Set.InjOn φ s)
    (hu : ∀ x ∈ s, IsUnit (jacobianMatrix (D x)).det) {f k : Covector → ℝ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f (φ x)) (hk : ∀ x ∈ s, DifferentiableAt ℝ k (φ x)) :
    (∫ y in φ '' s, RNCVolumeDensity.volumeFactor (g y) * pairing g f k y) =
      ∫ x in s, RNCVolumeDensity.volumeFactor (pullMetric g φ D x) *
        pairing (pullMetric g φ D) (f ∘ φ) (k ∘ φ) x := by
  rw [integral_pullMetric hs (fun x hx => (hφ x hx).hasFDerivWithinAt) hinj]
  apply MeasureTheory.setIntegral_congr_fun hs
  intro x hx
  exact congrArg (fun t : ℝ => RNCVolumeDensity.volumeFactor (pullMetric g φ D x) * t)
    (pairing_pullback g (hφ x hx) (hu x hx) (hf x hx) (hk x hx)).symm

end FoliationQM.CurvedGradientCovariance
