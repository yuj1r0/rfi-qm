module

public import FoliationQM.CurvedGradientCovariance

/-!
# The Levi-Civita connection on a nonlinear coordinate overlap

The ordinary second derivative of the coordinate change appears in the
transformation of the Christoffel coefficients. Differentiating the actual
pulled-back metric derives that term from the coordinate Koszul formula.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedScalarAtlasOverlap

open LorentzMatrixGroup RNCCoordinateConnection RNCCoordinateVolumeChange RNCHalfDensityJet
open ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator

/-- The continuous linear assignment from a metric matrix to its coordinate bilinear form. -/
def formMap : Mat4 →L[ℝ] Covector →L[ℝ] Covector →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := form
    map_add' := by intro A B; ext u v; simp [form_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by intro r A; ext u v; simp [form_apply, Finset.mul_sum, mul_assoc] }

/-- Evaluation of the variable metric on two fixed vectors. -/
def metricEntry (u v : Covector) : Mat4 →L[ℝ] ℝ :=
  (apply ℝ ℝ v).comp ((apply ℝ (Covector →L[ℝ] ℝ) u).comp formMap)

/-- The lowered coordinate Koszul formula, linear in its last argument. -/
def koszul (g : Covector → Mat4) (x u v : Covector) : Covector →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (form (dG g x u) v + form (dG g x v) u - (metricEntry u v).comp (fderiv ℝ g x))

/-- The algebraic connection applied to constant vector fields in a coordinate chart. -/
def connection (g : Covector → Mat4) (x u v : Covector) : Covector :=
  (g x)⁻¹.mulVec fun i => koszul g x u v (axis i)

/-- Evaluating the lowered formula exhibits its three derivatives of the metric. -/
theorem koszul_apply (g : Covector → Mat4) (x u v w : Covector) :
    koszul g x u v w =
      (form (dG g x u) v w + form (dG g x v) u w - form (dG g x w) u v) / 2 := by
  change (1 / 2 : ℝ) * (form (dG g x u) v w + form (dG g x v) u w - form (dG g x w) u v) = _
  ring

private def firstCoefficient (g : Covector → Mat4) (x v : Covector) (r : Fin 4) : Covector →L[ℝ] ℝ :=
  ∑ i, ((g x)⁻¹ r i / 2) • ((metricEntry v (axis i)).comp (fderiv ℝ g x) +
    (form (dG g x v)).flip (axis i) - (form (dG g x (axis i))).flip v)

private def secondCoefficient (g : Covector → Mat4) (x u : Covector) (r : Fin 4) : Covector →L[ℝ] ℝ :=
  ∑ i, ((g x)⁻¹ r i / 2) • ((form (dG g x u)).flip (axis i) +
    (metricEntry u (axis i)).comp (fderiv ℝ g x) - form (dG g x (axis i)) u)

private theorem firstCoefficient_apply (g : Covector → Mat4) (x u v : Covector) (r : Fin 4) :
    firstCoefficient g x v r u = connection g x u v r := by
  simp only [firstCoefficient, connection, Matrix.mulVec, dotProduct, sum_apply, smul_apply,
    smul_eq_mul, sub_apply, add_apply, comp_apply, flip_apply, koszul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (g x)⁻¹ r i / 2 * (form (dG g x u) v (axis i) + _ - _) = _
  ring

private theorem secondCoefficient_apply (g : Covector → Mat4) (x u v : Covector) (r : Fin 4) :
    secondCoefficient g x u r v = connection g x u v r := by
  simp only [secondCoefficient, connection, Matrix.mulVec, dotProduct, sum_apply, smul_apply,
    smul_eq_mul, sub_apply, add_apply, comp_apply, flip_apply, koszul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (g x)⁻¹ r i / 2 * (_ + form (dG g x v) u (axis i) - _) = _
  ring

/-- On coordinate axes the bilinear connection is exactly the project's Christoffel coefficient. -/
theorem connection_axis (g : Covector → Mat4) (x : Covector) (b c r : Fin 4) :
    connection g x (axis b) (axis c) r = christoffel g x r b c := by
  unfold connection christoffel
  congr 2
  funext i
  rw [koszul_apply]
  simp only [axis, form_basis, lowered]
  ring

/-- The constant-vector connection contracts both direction components against the coordinate Christoffel symbols. -/
theorem connection_components (g : Covector → Mat4) (x u v : Covector) (r : Fin 4) :
    connection g x u v r = ∑ i, ∑ j, u i * (v j * christoffel g x r i j) := by
  calc
    _ = ∑ i, u i * connection g x (axis i) v r := by
      simpa only [firstCoefficient_apply] using CurvedGradientCovariance.apply_components (firstCoefficient g x v r) u
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← secondCoefficient_apply, CurvedGradientCovariance.apply_components, Finset.mul_sum]
      simp only [secondCoefficient_apply, connection_axis]

/-- Lowering the connection with the actual nondegenerate metric recovers the Koszul functional. -/
theorem form_connection {g : Covector → Mat4} {x : Covector} (hu : IsUnit (g x).det) (u v w : Covector) :
    form (g x) w (connection g x u v) = koszul g x u v w := by
  rw [RNCLorentzContraction.form_eq_pairing, connection, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, CurvedGradientCovariance.apply_components]
  rfl

/-- The matrix assignment to a coordinate differential is itself continuous linear. -/
def jacobianMap : (Covector →L[ℝ] Covector) →L[ℝ] Mat4 :=
  LinearMap.toContinuousLinearMap {
    toFun := jacobianMatrix
    map_add' := by intro A B; ext i j; rfl
    map_smul' := by intro t A; ext i j; rfl }

variable {φ : Covector → Covector} {g : Covector → Mat4} {x : Covector}

/-- A C² transition and a differentiable target metric give a differentiable actual pullback metric. -/
theorem differentiableAt_pullMetric (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x)) :
    DifferentiableAt ℝ (pullMetric g φ (fderiv ℝ φ)) x := by
  let J (y : Covector) := jacobianMatrix (fderiv ℝ φ y)
  have hd : DifferentiableAt ℝ J x := jacobianMap.differentiableAt.comp x
    (hφ.fderiv_right (by decide)).differentiableAt_one
  let transpose : Mat4 →L[ℝ] Mat4 := (Matrix.transposeLinearEquiv (Fin 4) (Fin 4) ℝ ℝ).toLinearMap.toContinuousLinearMap
  exact ((transpose.differentiableAt.comp x hd).mul (hg.comp x (hφ.differentiableAt (by decide)))).mul hd

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The derivative of the pulled-back metric on constant vectors includes derivatives of both Jacobian factors. -/
theorem metric_derivative_pullback (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x))
    (a b c : Covector) :
    form (dG (pullMetric g φ (fderiv ℝ φ)) x a) b c =
      form (dG g (φ x) (fderiv ℝ φ x a)) (fderiv ℝ φ x b) (fderiv ℝ φ x c) +
      form (g (φ x)) (fderiv ℝ (fderiv ℝ φ) x a b) (fderiv ℝ φ x c) +
      form (g (φ x)) (fderiv ℝ φ x b) (fderiv ℝ (fderiv ℝ φ) x a c) := by
  let J := fderiv ℝ φ
  have hj : DifferentiableAt ℝ J x := (hφ.fderiv_right (by decide)).differentiableAt_one
  have he : metricEntry b c ∘ pullMetric g φ J =
      fun y => form (g (φ y)) (J y b) (J y c) := by
    funext y
    change form (pullMatrix (jacobianMatrix (J y)) (g (φ y))) b c = _
    rw [pullMatrix, ← RNCLorentzContraction.form_pullback]
    simp only [jacobianMatrix, LinearMap.toMatrix'_mulVec, coe_coe]
  have hleft := (metricEntry b c).hasFDerivAt.comp x (differentiableAt_pullMetric hφ hg).hasFDerivAt
  let A (y : Covector) := formMap (g (φ y))
  let dA := formMap.comp ((fderiv ℝ g (φ x)).comp (J x))
  have hm : HasFDerivAt (fun M : Mat4 => formMap M) formMap (g (φ x)) := by
    exact ContinuousLinearMap.hasFDerivAt (F := Covector →L[ℝ] Covector →L[ℝ] ℝ) formMap
  have hA : HasFDerivAt A dA x := HasFDerivAt.comp (G := Covector →L[ℝ] Covector →L[ℝ] ℝ) x hm
    (hg.hasFDerivAt.comp x (hφ.differentiableAt (by decide)).hasFDerivAt)
  let D (u : Covector) := (apply ℝ Covector u).comp (fderiv ℝ J x)
  have hD (u : Covector) : HasFDerivAt (fun y => J y u) (D u) x :=
    (apply ℝ Covector u).hasFDerivAt.comp x hj.hasFDerivAt
  have hB : HasFDerivAt (fun y => A y (J y b)) ((A x).comp (D b) + dA.flip (J x b)) x :=
    hA.clm_apply (hD b)
  have hright := hB.clm_apply (hD c)
  have H := congrArg (fun L : Covector →L[ℝ] ℝ => L a) (hleft.fderiv.symm.trans
    ((congrArg (fderiv ℝ · x) he).trans hright.fderiv))
  change _ = _ + _ + _
  change form (dG (pullMetric g φ J) x a) b c =
    form (g (φ x)) (J x b) (fderiv ℝ J x a c) +
    (form (g (φ x)) (fderiv ℝ J x a b) (J x c) +
    form (dG g (φ x) (J x a)) (J x b) (J x c)) at H
  linarith only [H]

/-- A symmetric metric matrix pairs vectors symmetrically. -/
theorem form_symmetric {G : Mat4} (hs : G.IsSymm) (u v : Covector) : form G u v = form G v u := by
  simp only [RNCLorentzContraction.form_eq_pairing]
  simpa only [hs.eq] using Matrix.dotProduct_transpose_mulVec G u v

/-- The nonlinear part of the transformed Koszul formula is precisely the lowered chart Hessian. -/
theorem koszul_pullback (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x))
    (hs : (g (φ x)).IsSymm) (u v w : Covector) :
    koszul (pullMetric g φ (fderiv ℝ φ)) x u v w =
      form (g (φ x)) (fderiv ℝ φ x w) (fderiv ℝ (fderiv ℝ φ) x u v) +
      koszul g (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  simp only [koszul_apply, metric_derivative_pullback hφ hg]
  have hH := hφ.isSymmSndFDerivAt (by simp)
  rw [hH v u, hH w u, hH w v, form_symmetric hs (fderiv ℝ (fderiv ℝ φ) x u v) (fderiv ℝ φ x w),
    form_symmetric hs (fderiv ℝ (fderiv ℝ φ) x u w) (fderiv ℝ φ x v)]
  ring

/-- Pairing with every vector distinguishes vectors for a nondegenerate metric. -/
theorem eq_of_form_eq {G : Mat4} (hu : IsUnit G.det) {u v : Covector}
    (h : ∀ w, form G w u = form G w v) : u = v := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr (G.isUnit_iff_isUnit_det.mpr hu)
  ext i
  simpa only [RNCLorentzContraction.form_eq_pairing, axis, single_one_dotProduct] using h (axis i)

/-- The Levi-Civita transformation law on a nonlinear overlap, derived from the actual pulled-back metric.
The inhomogeneous term is the second Fréchet derivative of the transition. -/
theorem connection_pullback (hφ : ContDiffAt ℝ 2 φ x) (hg : DifferentiableAt ℝ g (φ x))
    (hs : (g (φ x)).IsSymm) (hu : IsUnit (g (φ x)).det)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) (u v : Covector) :
    fderiv ℝ φ x (connection (pullMetric g φ (fderiv ℝ φ)) x u v) =
      fderiv ℝ (fderiv ℝ φ) x u v + connection g (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  let D := fderiv ℝ φ x
  let J := jacobianMatrix D
  have hJu : IsUnit J := J.isUnit_iff_isUnit_det.mpr hJ
  have hpu : IsUnit (pullMetric g φ (fderiv ℝ φ) x).det := by
    rw [pullMetric, det_pullMatrix]
    exact (hJ.pow 2).mul hu
  apply eq_of_form_eq hu
  intro z
  obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hJu z
  have ha (w : Covector) : J.mulVec w = D w := LinearMap.toMatrix'_mulVec _ _
  rw [← hw, ha]
  calc
    form (g (φ x)) (D w) (D (connection (pullMetric g φ (fderiv ℝ φ)) x u v)) =
        form (pullMetric g φ (fderiv ℝ φ) x) w (connection (pullMetric g φ (fderiv ℝ φ)) x u v) := by
          simp only [← ha]
          exact RNCLorentzContraction.form_pullback _ _ _ _
    _ = _ := form_connection hpu u v w
    _ = _ := koszul_pullback hφ hg hs u v w
    _ = _ := by rw [← form_connection hu]; exact (map_add _ _ _).symm

end FoliationQM.CurvedScalarAtlasOverlap
