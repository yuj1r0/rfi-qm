module

public import FoliationQM.CurvedConnectionComponents
public import FoliationQM.CurvedHessianOverlap
public import FoliationQM.CurvedRiemannOverlap

/-!
# Ricci contraction and scalar curvature on nonlinear coordinate overlaps

The Ricci pairing is the trace of curvature acting on its first direction.
The trace is invariant under the Jacobian change of tangent basis. This
identifies the actual scalar curvature used in the v13 action on overlaps.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedRicciOverlap

open LorentzMatrixGroup RNCCoordinateConnection RNCCoordinateCurvature
  CurvedConnectionComponents RNCHalfDensityJet RNCCoordinateVolumeChange

/-- The coordinate matrix of the curvature endomorphism `v ↦ R(v,w)u`. -/
def curvatureMatrix (g : Covector → Mat4) (x u w : Covector) : Mat4 :=
  fun r a => ∑ s, ∑ b, u s * w b * riemann g x r s a b

/-- Multiplication by this matrix is the actual curvature in its first direction slot. -/
theorem curvatureMatrix_mulVec {g : Covector → Mat4} {x : Covector}
    (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x)) (u v w : Covector) :
    (curvatureMatrix g x u w).mulVec v = curvature g x u v w := by
  rw [curvature_expansion hg hu]
  ext r
  simp only [curvatureMatrix, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Tracing the curvature endomorphism gives the coordinate Ricci pairing in both remaining slots. -/
theorem curvatureMatrix_trace (g : Covector → Mat4) (x u w : Covector) :
    (curvatureMatrix g x u w).trace = form (ricci g x) u w := by
  simp only [Matrix.trace, Matrix.diag, curvatureMatrix, form_apply, ricci, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem trace_pullback {g k : Covector → Mat4} {x y : Covector} {J : Mat4}
    (hg : ContDiffAt ℝ 2 g y) (hk : ContDiffAt ℝ 2 k x) (hgu : IsUnit (g y))
    (hku : IsUnit (k x)) (hJ : IsUnit J.det)
    (hc : ∀ u v w, J.mulVec (curvature k x u v w) =
      curvature g y (J.mulVec u) (J.mulVec v) (J.mulVec w)) (u w : Covector) :
    form (ricci k x) u w = form (ricci g y) (J.mulVec u) (J.mulVec w) := by
  let A := curvatureMatrix k x u w
  let B := curvatureMatrix g y (J.mulVec u) (J.mulVec w)
  have he : J * A = B * J := by
    ext r a
    have hv := hc u (axis a) w
    rw [← curvatureMatrix_mulVec hk hku, ← curvatureMatrix_mulVec hg hgu,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at hv
    simpa only [axis, Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hv r
  have ha : A = J⁻¹ * B * J := by
    rw [Matrix.mul_assoc, ← he, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
  rw [← curvatureMatrix_trace, ← curvatureMatrix_trace]
  change A.trace = B.trace
  rw [ha, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul]

private theorem contraction_trace (Q A : Mat4) (hQ : Q.IsSymm) :
    (∑ i, ∑ j, Q i j * A i j) = (Q * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hQ.apply i j]

variable {φ : Covector → Covector} {g : Covector → Mat4} {x : Covector}

/-- Ricci transforms by the actual coordinate Jacobian in both covariant slots. -/
theorem ricci_pullback (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) :
    ricci (pullMetric g φ (fderiv ℝ φ)) x =
      (jacobianMatrix (fderiv ℝ φ x)).transpose * ricci g (φ x) * jacobianMatrix (fderiv ℝ φ x) := by
  let J := jacobianMatrix (fderiv ℝ φ x)
  have hp : IsUnit (pullMetric g φ (fderiv ℝ φ) x) := by
    apply (pullMetric g φ (fderiv ℝ φ) x).isUnit_iff_isUnit_det.mpr
    rw [pullMetric, det_pullMatrix]
    exact (hJ.pow 2).mul hu
  have ha (v : Covector) : J.mulVec v = fderiv ℝ φ x v := LinearMap.toMatrix'_mulVec _ _
  have hc (u v w : Covector) : J.mulVec (curvature (pullMetric g φ (fderiv ℝ φ)) x u v w) =
      curvature g (φ x) (J.mulVec u) (J.mulVec v) (J.mulVec w) := by
    simp only [ha]
    exact CurvedRiemannOverlap.curvature_pullback hφ hg hs hu hJ u v w
  ext i j
  have he := trace_pullback hg (CurvedRiemannOverlap.contDiffAt_pullMetric hφ hg)
    ((g (φ x)).isUnit_iff_isUnit_det.mpr hu) hp hJ hc (axis i) (axis j)
  rw [RNCLorentzContraction.form_pullback] at he
  simpa only [axis, form_basis] using he

/-- The coordinate scalar curvature of the metric is unchanged by an arbitrary regular C³ chart transition. -/
theorem scalar_pullback (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) :
    scalar (pullMetric g φ (fderiv ℝ φ)) x = scalar g (φ x) := by
  let J := jacobianMatrix (fderiv ℝ φ x)
  have hsym : (g (φ x)).transpose = g (φ x) := hs.self_of_nhds
  have hp : (pullMetric g φ (fderiv ℝ φ) x).IsSymm := by
    change (J.transpose * g (φ x) * J).transpose = J.transpose * g (φ x) * J
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym, Matrix.mul_assoc]
  rw [scalar, scalar, contraction_trace _ _ hp.inv, contraction_trace _ _ hs.self_of_nhds.inv,
    ricci_pullback hφ hg hs hu hJ]
  exact CurvedHessianOverlap.trace_pullback _ _ _ hJ

/-- The coordinate curvature scalar depends only on the germ of the metric. -/
theorem scalar_congr {g k : Covector → Mat4} {x : Covector} (he : k =ᶠ[𝓝 x] g) :
    scalar k x = scalar g x := by
  have hΓ (r b c : Fin 4) : (fun y => christoffel k y r b c) =ᶠ[𝓝 x]
      fun y => christoffel g y r b c := by
    filter_upwards [he, he.fderiv (𝕜 := ℝ)] with y hy hdy
    simp only [christoffel, lowered, dG, hy, hdy]
  have hd (r b c a : Fin 4) : dGamma k x r b c a = dGamma g x r b c a :=
    congrArg (fun L : Covector →L[ℝ] ℝ => L (axis a)) (hΓ r b c).fderiv_eq
  have hr : ricci k x = ricci g x := by
    ext a b
    simp only [ricci, riemann, hd, fun r b c => (hΓ r b c).self_of_nhds]
  simp only [scalar, he.self_of_nhds, hr]

/-- An actual overlap metric which agrees locally with the pullback has the same
computed scalar curvature as the target coordinate metric. -/
theorem scalar_overlap {k : Covector → Mat4} (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hu : IsUnit (g (φ x)).det) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (he : k =ᶠ[𝓝 x] pullMetric g φ (fderiv ℝ φ)) :
    scalar k x = scalar g (φ x) :=
  (scalar_congr he).trans (scalar_pullback hφ hg hs hu hJ)

end FoliationQM.CurvedRicciOverlap
