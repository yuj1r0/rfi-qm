module

public import FoliationQM.CurvedScalarAtlasOverlap
public import FoliationQM.CurvedWaveOperator
public import FoliationQM.RNCCriticalComposition

/-!
# Nonlinear chart covariance of the scalar covariant Hessian

The second derivative of the transition in the pulled-back scalar field
cancels the inhomogeneous term of the actual coordinate connection. The
remaining tensor transforms by the first derivative in both slots.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.CurvedHessianOverlap

open LorentzMatrixGroup RNCCoordinateConnection CurvedScalarAtlasOverlap RNCCoordinateVolumeChange
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate expression for the covariant Hessian in two arbitrary, constant tangent directions. -/
def hess (g : Covector → Mat4) (f : Covector → F) (x u v : Covector) : F :=
  fderiv ℝ (fderiv ℝ f) x u v - fderiv ℝ f x (connection g x u v)

/-- Evaluation on coordinate axes gives the ordinary indexed covariant scalar Hessian. -/
theorem hess_axis (g : Covector → Mat4) (f : Covector → F) (x : Covector) (i j : Fin 4) :
    hess g f x (axis i) (axis j) = CurvedWaveOperator.covariantHessian g f x i j := by
  unfold hess CurvedWaveOperator.covariantHessian
  congr 1
  let v := connection g x (axis i) (axis j)
  calc
    _ = fderiv ℝ f x (∑ k, v k • axis k) := congrArg _ (pi_eq_sum_univ' v)
    _ = _ := by simp only [v, map_sum, map_smul, connection_axis]

/-- The actual covariant Hessian pulls back tensorially under every regular C² nonlinear chart map. -/
theorem hess_pullback {g : Covector → Mat4} {φ : Covector → Covector} {f : Covector → F} {x : Covector}
    (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x)) (hs : (g (φ x)).IsSymm)
    (hu : IsUnit (g (φ x)).det) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hf : ContDiffAt ℝ 2 f (φ x)) (u v : Covector) :
    hess (pullMetric g φ (fderiv ℝ φ)) (f ∘ φ) x u v =
      hess g f (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  simp only [hess, RNCCriticalComposition.hessian_comp hφ hf,
    fderiv_comp x (hf.differentiableAt (by decide)) (hφ.differentiableAt (by decide)),
    ContinuousLinearMap.comp_apply, connection_pullback hφ hg hs hu hJ, map_add]
  abel

/-- Expressing a contraction of two symmetric matrices as their product trace. -/
theorem contraction_trace (G A : Mat4) (hs : A.IsSymm) :
    (∑ i, ∑ j, G i j * A i j) = (G * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg (G i j * ·) (hs.apply j i)

/-- Contracting two pulled-back tensors cancels an arbitrary nonsingular Jacobian. -/
theorem trace_pullback (G J A : Mat4) (hJ : IsUnit J.det) :
    ((pullMatrix J G)⁻¹ * (J.transpose * A * J)).trace = (G⁻¹ * A).trace := by
  have ht : IsUnit J.transpose.det := by simpa using hJ
  have hm : (pullMatrix J G)⁻¹ * (J.transpose * A * J) = J⁻¹ * (G⁻¹ * A) * J := by
    simp only [pullMatrix, Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J.transpose⁻¹, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
  rw [hm, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul]

end FoliationQM.CurvedHessianOverlap
