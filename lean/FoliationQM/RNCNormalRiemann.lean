module

public import FoliationQM.RNCCoordinateCurvature
public import FoliationQM.RNCMetricCompatibilityDerivative

/-!
# The uncontracted curvature coefficient in the normal metric Hessian

For Eq. `rnc_g` in v13 Lemma 9.1, the full quadratic coefficient of the
covariant metric follows from the radial geodesic equation, torsion symmetry,
and differentiated metric compatibility. Retaining both free metric indices
also identifies the last-pair and first-pair antisymmetries and pair exchange
of the lowered curvature at the orthonormal center.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCNormalRiemann

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCCoordinateCurvature
open RNCNormalChart RNCMetricCompatibilityDerivative
open scoped Matrix.Norms.Operator

variable {g : Covector → Mat4}

/-- Lowering the output index of the coordinate curvature uses the actual metric at the point. -/
def loweredRiemann (g : Covector → Mat4) (x : Covector) (i j a b : Fin 4) : ℝ :=
  ∑ r, g x i r * riemann g x r j a b

/-- In an orthonormal frame, lowering the output index multiplies by its Lorentz sign. -/
theorem lowered_center (h : IsNormal g) (i j a b : Fin 4) :
    loweredRiemann g 0 i j a b = sign i * riemann g 0 i j a b := by
  simp [loweredRiemann, h.metric_center, eta, Matrix.diagonal_apply, ite_mul]

/-- Expanding curvature at the normal center gives the difference between actual derivatives of connection coefficients. -/
theorem lowered_center_derivatives (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) (i j a b : Fin 4) :
    loweredRiemann g 0 i j a b = sign i * (dGamma g 0 i b j a - dGamma g 0 i a j b) := by
  rw [lowered_center h, riemann_center h hg]

/-- At the center the two curvature directions are antisymmetric. -/
theorem skew_last (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) (i j a b : Fin 4) :
    loweredRiemann g 0 i j a b = -loweredRiemann g 0 i j b a := by
  rw [lowered_center_derivatives h hg, lowered_center_derivatives h hg]
  ring

/-- Mixed Hessian symmetry and differentiated metric compatibility give antisymmetry in the first pair. -/
theorem skew_first (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (i j a b : Fin 4) :
    loweredRiemann g 0 i j a b = -loweredRiemann g 0 j i a b := by
  have hm := congrArg (fun M : Mat4 => M i j) (hg.isSymmSndFDerivAt (by simp) (axis a) (axis b))
  change (fderiv ℝ (fderiv ℝ g) 0 (axis a) (axis b)) i j =
    (fderiv ℝ (fderiv ℝ g) 0 (axis b) (axis a)) i j at hm
  rw [hessian_metric_entries h hg, hessian_metric_entries h hg] at hm
  simp only [lowered_center_derivatives h (hg.differentiableAt (by decide)), dGamma, mul_sub]
  linarith only [hm]

/-- The first Bianchi identity follows from torsion symmetry of the actual connection derivatives. -/
theorem first_bianchi (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (i j a b : Fin 4) :
    loweredRiemann g 0 i j a b + loweredRiemann g 0 i a b j + loweredRiemann g 0 i b j a = 0 := by
  simp only [lowered_center_derivatives h (hg.differentiableAt (by decide)), dGamma_symmetric h hg]
  ring

/-- At the normal center the lowered curvature is invariant under exchanging the two index pairs. -/
theorem exchange_pairs (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (i j a b : Fin 4) :
    loweredRiemann g 0 i j a b = loweredRiemann g 0 a b i j := by
  have flip (u v w z : Fin 4) :
      loweredRiemann g 0 u v w z = loweredRiemann g 0 v u z w := by
    rw [skew_first h hg u v w z, skew_last h (hg.differentiableAt (by decide)) v u w z, neg_neg]
  have h₁ := first_bianchi h hg i j a b
  have h₂ := first_bianchi h hg j i b a
  have h₃ := first_bianchi h hg a b i j
  have h₄ := first_bianchi h hg b a j i
  simp only [flip] at h₁ h₂ h₃ h₄ ⊢
  linarith only [h₁, h₂, h₃, h₄]

/-- The radial cyclic identity expresses each lowered Christoffel derivative as a curvature sum. -/
theorem lowered_dGamma (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (i a b c : Fin 4) :
    sign i * dGamma g 0 i b c a =
      -(loweredRiemann g 0 i b c a + loweredRiemann g 0 i c b a) / 3 := by
  have hc : dGamma g 0 i b c a + dGamma g 0 i c a b + dGamma g 0 i a b c = 0 :=
    connection_cyclic h hg i a b c
  have hs := congrArg (fun z : ℝ => sign i * z) hc
  simp only [lowered_center_derivatives h (hg.differentiableAt (by decide)), dGamma_symmetric h hg,
    mul_add, mul_sub, mul_zero] at hs ⊢
  linarith only [hs]

/-- Every mixed entry of the actual normal-coordinate metric Hessian is the symmetrized
curvature coefficient of the covariant metric expansion in v13 Eq. `rnc_g`. -/
theorem hessian_metric_riemann (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b i j : Fin 4) :
    (fderiv ℝ (fderiv ℝ g) 0 (axis a) (axis b)) i j =
      -(loweredRiemann g 0 i a j b + loweredRiemann g 0 i b j a) / 3 := by
  rw [hessian_metric_entries h hg]
  change sign j * dGamma g 0 j b i a + sign i * dGamma g 0 i b j a = _
  rw [lowered_dGamma h hg, lowered_dGamma h hg, exchange_pairs h hg j b i a, skew_first h hg j i b a]
  ring

end FoliationQM.RNCNormalRiemann
