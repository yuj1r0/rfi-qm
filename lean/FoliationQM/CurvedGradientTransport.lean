module

public import FoliationQM.CurvedScalarGradient

/-!
# Coordinate transport of the actual raised scalar gradient

Raising the pulled-back scalar differential with the pulled-back inverse
metric cancels the actual invertible coordinate Jacobian. The matrix
identity needs no additional metric regularity or nonsingularity premise.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedGradientTransport

open LorentzMatrixGroup RNCCoordinateVolumeChange CurvedGradientCovariance CurvedScalarGradient
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- Congruence pullback and index raising cancel an invertible coordinate Jacobian. -/
theorem grad_matrices (G J : Mat4) (hJ : IsUnit J.det) (u : Covector) :
    J.mulVec ((pullMatrix J G)⁻¹.mulVec (J.transpose.mulVec u)) = G⁻¹.mulVec u := by
  have hJt : IsUnit J.transpose.det := by simpa only [Matrix.det_transpose] using hJ
  have hm : J * (pullMatrix J G)⁻¹ * J.transpose = G⁻¹ := by
    rw [pullMatrix, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc
      J * (J⁻¹ * (G⁻¹ * J.transpose⁻¹)) * J.transpose =
          (J * J⁻¹) * G⁻¹ * (J.transpose⁻¹ * J.transpose) := by
        simp only [Matrix.mul_assoc]
      _ = G⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hJ, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]

variable {g k : Covector → Mat4} {φ : Covector → Covector}
  {D : Covector → Covector →L[ℝ] Covector} {f f' : Covector → ℝ} {x : Covector}

/-- The actual derivative of a regular coordinate change transports the raised gradient to the target gradient. -/
theorem grad_pullback (g : Covector → Mat4) (hφ : HasFDerivAt φ (D x) x)
    (hJ : IsUnit (jacobianMatrix (D x)).det) (hf : DifferentiableAt ℝ f (φ x)) :
    D x (grad (pullMetric g φ D) (f ∘ φ) x) = grad g f (φ x) := by
  have hj (v : Covector) : (jacobianMatrix (D x)).mulVec v = D x v :=
    LinearMap.toMatrix'_mulVec _ _
  rw [← hj, grad, components_pullback hφ hf]
  exact grad_matrices (g (φ x)) (jacobianMatrix (D x)) hJ (components f (φ x))

/-- Replacing actual metric and scalar representatives by equal germs preserves the raised gradient. -/
theorem grad_germ (hg : g =ᶠ[𝓝 x] k) (hf : f =ᶠ[𝓝 x] f') :
    grad g f x = grad k f' x := by
  unfold grad
  rw [hg.self_of_nhds]
  congr 1
  funext i
  exact congrArg (fun L : Covector →L[ℝ] ℝ => L (RNCCoordinateConnection.axis i))
    (hf.fderiv_eq (𝕜 := ℝ))

end FoliationQM.CurvedGradientTransport
