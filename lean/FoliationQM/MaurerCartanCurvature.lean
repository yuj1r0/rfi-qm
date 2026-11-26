module

public import FoliationQM.MaurerCartanDifferential
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Actual Maurer–Cartan curvature from a locally C2 matrix field

Source: v13 `lem:maurer_cartan` and the structure-equation step in the
proof of `thm:dirac_lift`. The body and spatial connections are the actual
inverse-matrix products with the genuine real Frechet derivative of `L`.
Their derivatives use the inverse rule and the actual second derivative.
Local C2 regularity supplies second-derivative symmetry; no flatness or
second-order jet relation is assumed.

The domain is any real normed space. Invertibility is required at the point,
and C2 regularity is local there. The body equation has the positive matrix
commutator and the spatial equation the opposite sign. The exterior-form
packaging and reconstruction of geometric connection coefficients are
separate statements.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.MaurerCartanCurvature
open DiracMatrices MatrixDifferential MaurerCartanDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local C2 regularity makes the genuine matrix-valued derivative field differentiable. -/
theorem differentiableAt_fderiv {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x) :
    DifferentiableAt ℝ (fderiv ℝ L) x :=
  (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- The genuine first derivative evaluated in a fixed direction is differentiable under local C2 regularity. -/
theorem differentiableAt_directional {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x) (w : E) :
    DifferentiableAt ℝ (fun y => fderiv ℝ L y w) x :=
  (differentiableAt_fderiv hL).clm_apply (differentiableAt_const w)

/-- Differentiating the genuine directional derivative evaluates the actual second Frechet derivative in the stated order. -/
theorem fderiv_directional_apply {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ L y w) x v = fderiv ℝ (fderiv ℝ L) x v w := by
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v)
    ((differentiableAt_fderiv hL).hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
  change fderiv ℝ (fun y => fderiv ℝ L y w) x v =
    fderiv ℝ L x 0 + fderiv ℝ (fderiv ℝ L) x v w at hd
  simpa only [map_zero, zero_add] using hd

/-- The actual body-connection derivative is the negative ordered connection product plus inverse times the genuine second derivative. -/
theorem fderiv_body_apply {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x)
    (hunit : IsUnit (L x)) (v w : E) :
    fderiv ℝ (fun y => body L y w) x v =
      -(body L x v*body L x w)+(L x)⁻¹*(fderiv ℝ (fderiv ℝ L) x v w) := by
  have hdiff := hL.differentiableAt (by norm_num)
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v)
    ((hasFDerivAt_inv_field hdiff.hasFDerivAt hunit).mul' (differentiableAt_directional hL w).hasFDerivAt).fderiv
  have hp : fderiv ℝ (fun y => body L y w) x v =
      (L x)⁻¹*(fderiv ℝ (fun y => fderiv ℝ L y w) x v)+
        (-((L x)⁻¹*(fderiv ℝ L x v)*(L x)⁻¹))*(fderiv ℝ L x w) := by
    simpa only [body] using! hd
  rw [hp, fderiv_directional_apply hL v w]
  simp only [body]
  noncomm_ring

/-- The actual C2 body Maurer–Cartan connection has zero curvature with the positive matrix commutator. -/
theorem body_curvature {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x)
    (hunit : IsUnit (L x)) (v w : E) :
    fderiv ℝ (fun y => body L y w) x v - fderiv ℝ (fun y => body L y v) x w +
      body L x v*body L x w-body L x w*body L x v=0 := by
  have hs : fderiv ℝ (fderiv ℝ L) x v w = fderiv ℝ (fderiv ℝ L) x w v := by
    simpa using! hL.isSymmSndFDerivAt (by norm_num) v w
  rw [fderiv_body_apply hL hunit, fderiv_body_apply hL hunit, hs]
  noncomm_ring

/-- The actual spatial-connection derivative is the negative reverse-ordered connection product plus second derivative times inverse. -/
theorem fderiv_spatial_apply {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x)
    (hunit : IsUnit (L x)) (v w : E) :
    fderiv ℝ (fun y => spatial L y w) x v =
      -(spatial L x w*spatial L x v)+(fderiv ℝ (fderiv ℝ L) x v w)*(L x)⁻¹ := by
  have hdiff := hL.differentiableAt (by norm_num)
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v)
    ((differentiableAt_directional hL w).hasFDerivAt.mul' (hasFDerivAt_inv_field hdiff.hasFDerivAt hunit)).fderiv
  have hp : fderiv ℝ (fun y => spatial L y w) x v =
      fderiv ℝ L x w * (-((L x)⁻¹*(fderiv ℝ L x v)*(L x)⁻¹)) +
        (fderiv ℝ (fun y => fderiv ℝ L y w) x v)*(L x)⁻¹ := by
    simpa only [spatial] using! hd
  rw [hp, fderiv_directional_apply hL v w]
  simp only [spatial]
  noncomm_ring

/-- The actual C2 spatial Maurer–Cartan connection has zero curvature with the negative matrix commutator. -/
theorem spatial_curvature {L : E → Mat} {x : E} (hL : ContDiffAt ℝ 2 L x)
    (hunit : IsUnit (L x)) (v w : E) :
    fderiv ℝ (fun y => spatial L y w) x v - fderiv ℝ (fun y => spatial L y v) x w -
      spatial L x v*spatial L x w+spatial L x w*spatial L x v=0 := by
  have hs : fderiv ℝ (fderiv ℝ L) x v w = fderiv ℝ (fderiv ℝ L) x w v := by
    simpa using! hL.isSymmSndFDerivAt (by norm_num) v w
  rw [fderiv_spatial_apply hL hunit, fderiv_spatial_apply hL hunit, hs]
  noncomm_ring

/-- Actual local C2 regularity and invertibility make every body-connection component differentiable. -/
theorem differentiableAt_body_direction {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) (w : E) :
    DifferentiableAt ℝ (fun y => body L y w) x := by
  have hdiff := hL.differentiableAt (by norm_num)
  simpa only [body] using!
    (hasFDerivAt_inv_field hdiff.hasFDerivAt hunit).differentiableAt.mul
      (differentiableAt_directional hL w)

/-- Actual local C2 regularity and invertibility make every spatial-connection component differentiable. -/
theorem differentiableAt_spatial_direction {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (hunit : IsUnit (L x)) (w : E) :
    DifferentiableAt ℝ (fun y => spatial L y w) x := by
  have hdiff := hL.differentiableAt (by norm_num)
  simpa only [spatial] using!
    (differentiableAt_directional hL w).mul
      (hasFDerivAt_inv_field hdiff.hasFDerivAt hunit).differentiableAt

/-- Local C2 regularity derives symmetry of the actual matrix-valued second Frechet derivative. -/
theorem second_fderiv_symmetric {L : E → Mat} {x : E}
    (hL : ContDiffAt ℝ 2 L x) (v w : E) :
    fderiv ℝ (fderiv ℝ L) x v w = fderiv ℝ (fderiv ℝ L) x w v := by
  simpa using! hL.isSymmSndFDerivAt (by norm_num) v w

end FoliationQM.MaurerCartanCurvature
