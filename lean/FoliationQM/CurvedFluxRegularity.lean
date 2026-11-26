module

public import FoliationQM.CurvedWaveDivergence
public import FoliationQM.RNCCoordinateCurvature

/-!
# Local regularity of metric flux, wave and curvature

The local weak equations of v13 involve the differentiated metric flux
and scalar curvature. Their continuity follows from the metric and field
regularity. For the curvature coefficients, one derivative is spent on the
connection and another on its coordinate derivative.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.CurvedFluxRegularity

open LorentzMatrixGroup RNCCoordinateConnection RNCCoordinateCurvature
  RNCVolumeDensity CurvedWaveDivergence

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {g : Covector → Mat4} {f : Covector → F} {x : Covector} {k : WithTop ℕ∞}

private def entry (i j : Fin 4) : Mat4 →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

private theorem inverse_entry (hg : ContDiffAt ℝ k g x) (hu : IsUnit (g x)) (i j : Fin 4) :
    ContDiffAt ℝ k (fun y => (g y)⁻¹ i j) x :=
  (entry i j).contDiff.contDiffAt.comp x ((LorentzCayleySmooth.contDiffAt_inverse k hu).comp x hg)

/-- Each densitized inverse-metric coefficient retains the regularity of the metric. -/
theorem coefficient_contDiffAt (hg : ContDiffAt ℝ k g x) (hd : (g x).det < 0) (i j : Fin 4) :
    ContDiffAt ℝ k (fun y => coefficient g y i j) x :=
  ((RNCMetricHalfDensity.volume_smooth hd k).comp x hg).mul <|
    inverse_entry hg ((g x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd.ne)) i j

/-- A C¹ metric and a C² field give a C¹ flux component with values in the field's real normed space. -/
theorem flux_contDiffAt (hg : ContDiffAt ℝ 1 g x) (hd : (g x).det < 0)
    (hf : ContDiffAt ℝ 2 f x) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun y => flux g f y i) x := by
  apply ContDiffAt.sum
  intro j _
  exact (coefficient_contDiffAt hg hd i j).smul
    ((hf.fderiv_right (m := 1) (by decide)).clm_apply contDiffAt_const)

/-- The wave operator of a C¹ metric acting on a C² field is continuous at the point. -/
theorem wave_continuousAt (hg : ContDiffAt ℝ 1 g x) (hd : (g x).det < 0)
    (hf : ContDiffAt ℝ 2 f x) : ContinuousAt (wave g f) x := by
  have hv : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr hd)).ne'
  apply (((RNCMetricHalfDensity.volume_smooth hd 1).comp x hg).continuousAt.inv₀ hv).smul
  apply ContDiffAt.continuousAt (𝕜 := ℝ) (n := 0)
  apply ContDiffAt.sum
  intro i _
  exact ((flux_contDiffAt hg hd hf i).fderiv_right (m := 0) (by decide)).clm_apply contDiffAt_const

/-- A C^(k+1) invertible metric has C^k Christoffel coefficients. -/
theorem christoffel_contDiffAt (hg : ContDiffAt ℝ (k + 1) g x) (hu : IsUnit (g x))
    (r b c : Fin 4) : ContDiffAt ℝ k (fun y => christoffel g y r b c) x := by
  have hd (a i j : Fin 4) : ContDiffAt ℝ k (fun y => dG g y (axis a) i j) x :=
    (entry i j).contDiff.contDiffAt.comp x (hg.fderiv_right_succ.clm_apply contDiffAt_const)
  simp only [christoffel_eq_sum]
  exact contDiffAt_const.mul (ContDiffAt.sum fun i _ =>
    (inverse_entry (hg.of_le (le_self_add ..)) hu r i).mul
      (((hd b c i).add (hd c b i)).sub (hd i b c)))

/-- The Riemann coefficients retain order k at a point with a C^(k+2) metric. -/
theorem riemann_contDiffAt (hg : ContDiffAt ℝ (k + 1 + 1) g x) (hu : IsUnit (g x))
    (r s a b : Fin 4) : ContDiffAt ℝ k (fun y => riemann g y r s a b) x := by
  have hc (i j l : Fin 4) := christoffel_contDiffAt hg hu i j l
  have hd (i j l m : Fin 4) : ContDiffAt ℝ k (fun y => dGamma g y i j l m) x :=
    (hc i j l).fderiv_right_succ.clm_apply contDiffAt_const
  have hc' (i j l : Fin 4) : ContDiffAt ℝ k (fun y => christoffel g y i j l) x :=
    (hc i j l).of_le le_self_add
  exact ((hd r b s a).sub (hd r a s b)).add (ContDiffAt.sum fun l _ =>
    ((hc' r a l).mul (hc' l b s)).sub ((hc' r b l).mul (hc' l a s)))

/-- Scalar curvature has order k for a C^(k+2) metric invertible at the point. -/
theorem scalar_contDiffAt (hg : ContDiffAt ℝ (k + 1 + 1) g x) (hu : IsUnit (g x)) :
    ContDiffAt ℝ k (scalar g) x := by
  have hRic (s b : Fin 4) : ContDiffAt ℝ k (fun y => ricci g y s b) x :=
    ContDiffAt.sum fun r _ => riemann_contDiffAt hg hu r s r b
  have hg' : ContDiffAt ℝ k g x := hg.of_le (le_trans le_self_add le_self_add)
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (inverse_entry hg' hu i j).mul (hRic i j)

/-- A C² Lorentzian coordinate metric has continuous scalar curvature. -/
theorem scalar_continuousAt (hg : ContDiffAt ℝ 2 g x) (hd : (g x).det < 0) :
    ContinuousAt (scalar g) x :=
  (scalar_contDiffAt (k := 0) (hg.of_le (by decide))
    ((g x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd.ne))).continuousAt

end FoliationQM.CurvedFluxRegularity
