module
public import FoliationQM.MaurerCartanCurvature
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The actual exterior Maurer–Cartan equations

Source: v13's Maurer–Cartan structure equation following `eq:canonical_P_L`.
The body and spatial connections are bundled as genuine continuous alternating
one-forms. Their exterior derivatives are Mathlib's actual extDeriv. The matrix
wedge square is constructed independently from actual multiplication and finite
alternation; it is not defined using the exterior derivative or a curvature
conclusion. C2 regularity and invertibility imply both structure equations.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
namespace FoliationQM.MaurerCartanForms
open DiracMatrices MatrixDifferential MaurerCartanDifferential MaurerCartanCurvature
local instance : IsNormableSpace ℝ Mat := isNormableSpace_of_finiteDimensional
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Real continuous-linear maps lift to actual continuous alternating one-forms by evaluation on the unique argument. -/
def oneFormLift : (E →L[ℝ] Mat) →L[ℝ] (E [⋀^Fin 1]→L[ℝ] Mat) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := Mat)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

/-- The actual body connection bundled as a real continuous-linear map on directions. -/
def bodyLinear (L : E → Mat) (x : E) : E →L[ℝ] Mat :=
  ((ContinuousLinearMap.mul ℝ Mat) (L x)⁻¹).comp (fderiv ℝ L x)

/-- The actual spatial connection bundled as a real continuous-linear map on directions. -/
def spatialLinear (L : E → Mat) (x : E) : E →L[ℝ] Mat :=
  ((ContinuousLinearMap.mul ℝ Mat).flip (L x)⁻¹).comp (fderiv ℝ L x)

/-- The body Maurer–Cartan field as a genuine continuous alternating one-form. -/
def bodyForm (L : E → Mat) (x : E) : E [⋀^Fin 1]→L[ℝ] Mat := oneFormLift (bodyLinear L x)

/-- The spatial Maurer–Cartan field as a genuine continuous alternating one-form. -/
def spatialForm (L : E → Mat) (x : E) : E [⋀^Fin 1]→L[ℝ] Mat := oneFormLift (spatialLinear L x)

/-- Lifting a continuous-linear map evaluates it on the unique argument. -/
theorem oneFormLift_apply (T : E →L[ℝ] Mat) (v : Fin 1 → E) : oneFormLift T v = T (v 0) := rfl

/-- The bundled body map evaluates to the actual body coefficient. -/
theorem bodyLinear_apply (L : E → Mat) (x v : E) : bodyLinear L x v = body L x v := rfl

/-- The bundled spatial map evaluates to the actual spatial coefficient. -/
theorem spatialLinear_apply (L : E → Mat) (x v : E) : spatialLinear L x v = spatial L x v := rfl

/-- The body one-form evaluates to the actual body coefficient on its argument. -/
theorem bodyForm_apply (L : E → Mat) (x : E) (v : Fin 1 → E) : bodyForm L x v = body L x (v 0) := rfl

/-- The spatial one-form evaluates to the actual spatial coefficient on its argument. -/
theorem spatialForm_apply (L : E → Mat) (x : E) (v : Fin 1 → E) : spatialForm L x v = spatial L x (v 0) := rfl

/-- Actual C2 matrix regularity makes the body continuous-linear-map field differentiable at invertible values. -/
theorem differentiableAt_bodyLinear {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) :
    DifferentiableAt ℝ (bodyLinear L) x := by
  have hdL : DifferentiableAt ℝ L x := hL.differentiableAt (by norm_num)
  have hinv := (hasFDerivAt_inv_field hdL.hasFDerivAt hunit).differentiableAt
  have hdf := (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((ContinuousLinearMap.mul ℝ Mat).differentiableAt.comp x hinv).clm_comp hdf

/-- Actual C2 matrix regularity makes the spatial continuous-linear-map field differentiable at invertible values. -/
theorem differentiableAt_spatialLinear {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) :
    DifferentiableAt ℝ (spatialLinear L) x := by
  have hdL : DifferentiableAt ℝ L x := hL.differentiableAt (by norm_num)
  have hinv := (hasFDerivAt_inv_field hdL.hasFDerivAt hunit).differentiableAt
  have hdf := (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((ContinuousLinearMap.mul ℝ Mat).flip.differentiableAt.comp x hinv).clm_comp hdf

/-- The actual body one-form field is differentiable under the C2 matrix hypotheses. -/
theorem differentiableAt_bodyForm {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) :
    DifferentiableAt ℝ (bodyForm L) x :=
  ((oneFormLift (E := E)).hasFDerivAt.comp x
    (differentiableAt_bodyLinear hL hunit).hasFDerivAt).differentiableAt

/-- The actual spatial one-form field is differentiable under the C2 matrix hypotheses. -/
theorem differentiableAt_spatialForm {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) :
    DifferentiableAt ℝ (spatialForm L) x :=
  ((oneFormLift (E := E)).hasFDerivAt.comp x
    (differentiableAt_spatialLinear hL hunit).hasFDerivAt).differentiableAt

/-- The matrix wedge square, constructed independently by actual multiplication and finite alternation. -/
def wedgeSquare (T : E →L[ℝ] Mat) : E [⋀^Fin 2]→L[ℝ] Mat :=
  let left : Mat →L[ℝ] Mat →L[ℝ] Mat := ContinuousLinearMap.mul ℝ Mat
  let afterT : (Mat →L[ℝ] Mat) →L[ℝ] (E →L[ℝ] Mat) :=
    (ContinuousLinearMap.compL ℝ E Mat Mat).flip T
  let prod : E →L[ℝ] (E →L[ℝ] Mat) := (afterT.comp left).comp T
  ContinuousAlternatingMap.alternatizeUncurryFin (oneFormLift.comp prod)

/-- The independently constructed matrix wedge square is the ordered commutator on each pair. -/
theorem wedgeSquare_apply (T : E →L[ℝ] Mat) (v : Fin 2 → E) :
    wedgeSquare T v = T (v 0) * T (v 1) - T (v 1) * T (v 0) := by
  simp [wedgeSquare, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, oneFormLift, Fin.removeNth, sub_eq_add_neg]

/-- The actual exterior derivative of the body form evaluates to alternating actual directional derivatives. -/
theorem extDeriv_bodyForm_apply {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) (v : Fin 2 → E) :
    extDeriv (bodyForm L) x v =
      fderiv ℝ (fun y => body L y (v 1)) x (v 0) -
      fderiv ℝ (fun y => body L y (v 0)) x (v 1) := by
  rw [extDeriv_apply (differentiableAt_bodyForm hL hunit)]
  simp [bodyForm_apply, Fin.sum_univ_succ, Fin.removeNth, sub_eq_add_neg]

/-- The actual exterior derivative of the spatial form evaluates to alternating actual directional derivatives. -/
theorem extDeriv_spatialForm_apply {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) (v : Fin 2 → E) :
    extDeriv (spatialForm L) x v =
      fderiv ℝ (fun y => spatial L y (v 1)) x (v 0) -
      fderiv ℝ (fun y => spatial L y (v 0)) x (v 1) := by
  rw [extDeriv_apply (differentiableAt_spatialForm hL hunit)]
  simp [spatialForm_apply, Fin.sum_univ_succ, Fin.removeNth, sub_eq_add_neg]

/-- The genuine exterior body Maurer–Cartan equation is dOmega plus its independent matrix wedge square equal to zero. -/
theorem exterior_body_equation {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) :
    extDeriv (bodyForm L) x + wedgeSquare (bodyLinear L x) = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (bodyForm L) x v + wedgeSquare (bodyLinear L x) v = (0 : Mat)
  rw [extDeriv_bodyForm_apply hL hunit, wedgeSquare_apply]
  change fderiv ℝ (fun y => body L y (v 1)) x (v 0) -
    fderiv ℝ (fun y => body L y (v 0)) x (v 1) +
    (body L x (v 0)*body L x (v 1)-body L x (v 1)*body L x (v 0)) = 0
  simpa only [sub_eq_add_neg, add_assoc] using body_curvature hL hunit (v 0) (v 1)

/-- The genuine exterior spatial Maurer–Cartan equation has the opposite wedge-square sign. -/
theorem exterior_spatial_equation {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) :
    extDeriv (spatialForm L) x - wedgeSquare (spatialLinear L x) = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (spatialForm L) x v - wedgeSquare (spatialLinear L x) v = (0 : Mat)
  rw [extDeriv_spatialForm_apply hL hunit, wedgeSquare_apply]
  change fderiv ℝ (fun y => spatial L y (v 1)) x (v 0) -
    fderiv ℝ (fun y => spatial L y (v 0)) x (v 1) -
    (spatial L x (v 0)*spatial L x (v 1)-spatial L x (v 1)*spatial L x (v 0)) = 0
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_comm, add_left_comm]
    using spatial_curvature hL hunit (v 0) (v 1)

end FoliationQM.MaurerCartanForms
