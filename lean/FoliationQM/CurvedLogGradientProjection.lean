module

public import FoliationQM.CurvedScalarGradient
public import FoliationQM.LogDensityHessian

/-!
# The actual logarithmic gradient projected orthogonally to a velocity

The projection uses the genuine inverse-metric gradient and scalar
differential. Its full coordinate expression contains the rank-one velocity
term from v13's normalized quantum-force identity. Orthogonality follows
from lowering the gradient and the supplied physical normalization.
The logarithmic conversion is proved by the actual Fréchet chain rule.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedLogGradientProjection

open LorentzMatrixGroup RNCCoordinateConnection RNCHalfDensityJet CurvedGradientCovariance
  CurvedScalarGradient ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator

/-- The raised scalar gradient with its component parallel to a velocity of metric square `c²` removed. -/
def projectedGradient (c : ℝ) (g : Covector → Mat4) (U : Covector → Covector)
    (f : Covector → ℝ) (x : Covector) : Covector :=
  grad g f x - (fderiv ℝ f x (U x) / c ^ 2) • U x

/-- The actual projected gradient has the full inverse-metric minus rank-one velocity contraction in every coordinate. -/
theorem projectedGradient_components (c : ℝ) (g : Covector → Mat4)
    (U : Covector → Covector) (f : Covector → ℝ) (x : Covector) (a : Fin 4) :
    projectedGradient c g U f x a =
      ∑ b, ((g x)⁻¹ a b - U x a * U x b / c ^ 2) * fderiv ℝ f x (axis b) := by
  change (∑ b, (g x)⁻¹ a b * fderiv ℝ f x (axis b)) -
    (fderiv ℝ f x (U x) / c ^ 2) * U x a = _
  rw [apply_components (fderiv ℝ f x) (U x)]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {g : Covector → Mat4} {U : Covector → Covector} {f q : Covector → ℝ}
  {x : Covector} {c : ℝ}

/-- The actual projected gradient is metric-orthogonal to a velocity with physical normalization `g(U,U)=c²`. -/
theorem projectedGradient_orthogonal (hu : IsUnit (g x).det) (hc : c ≠ 0)
    (hnorm : form (g x) (U x) (U x) = c ^ 2) :
    form (g x) (U x) (projectedGradient c g U f x) = 0 := by
  rw [projectedGradient, map_sub, map_smul, smul_eq_mul, form_gradient hu, hnorm]
  field_simp
  ring

/-- The actual derivative of the logarithm of one plus a positive differentiable scalar is its derivative divided by that scalar value. -/
theorem fderiv_log_one_add (hq : DifferentiableAt ℝ q x) (hp : 0 < 1 + q x) :
    fderiv ℝ (fun y => Real.log (1 + q y)) x = (1 + q x)⁻¹ • fderiv ℝ q x :=
  ((hq.hasFDerivAt.const_add 1).log hp.ne').fderiv

/-- Evaluating the genuine logarithmic derivative in any direction gives the exact scalar quotient. -/
theorem fderiv_log_one_add_apply (hq : DifferentiableAt ℝ q x) (hp : 0 < 1 + q x)
    (v : Covector) :
    fderiv ℝ (fun y => Real.log (1 + q y)) x v = fderiv ℝ q x v / (1 + q x) := by
  rw [fderiv_log_one_add hq hp]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Raising the actual logarithmic differential scales the original gradient by the reciprocal of one plus the scalar. -/
theorem grad_log_one_add (g : Covector → Mat4) (hq : DifferentiableAt ℝ q x)
    (hp : 0 < 1 + q x) :
    grad g (fun y => Real.log (1 + q y)) x = (1 + q x)⁻¹ • grad g q x := by
  have hc : components (fun y => Real.log (1 + q y)) x =
      (1 + q x)⁻¹ • components q x := by
    funext i
    change fderiv ℝ (fun y => Real.log (1 + q y)) x (axis i) = _
    rw [fderiv_log_one_add hq hp]
    rfl
  rw [grad, hc, Matrix.mulVec_smul]
  rfl

/-- Projection commutes with the exact reciprocal factor produced by the logarithmic chain rule. -/
theorem projected_log_eq (c : ℝ) (g : Covector → Mat4) (U : Covector → Covector)
    (hq : DifferentiableAt ℝ q x) (hp : 0 < 1 + q x) :
    projectedGradient c g U (fun y => Real.log (1 + q y)) x =
      (1 + q x)⁻¹ • projectedGradient c g U q x := by
  rw [projectedGradient, grad_log_one_add g hq hp, fderiv_log_one_add_apply hq hp]
  simp only [projectedGradient, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

end FoliationQM.CurvedLogGradientProjection
