module

public import FoliationQM.RNCRicciHalfDensity

/-!
# The wave operator on a metric half-density times an amplitude

At a normal center the metric half-density has value one and vanishing
gradient. Its Hessian contributes a curvature term to the product with a
space-dependent amplitude. Scalar multiplication permits both real and
complex amplitudes, with no choice of phase.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCHalfDensityProduct

open LorentzMatrixGroup RealLorentzFrame RNCNormalChart RNCCoordinateConnection RNCCoordinateCurvature
open RNCVolumeDensity RNCRicciHalfDensity PolarSecondDifferential
open scoped Topology Matrix.Norms.Operator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E} {f : E → F} {w : E → ℝ}

private theorem hasFDerivAt_direction (hf : ContDiffAt ℝ 2 f x) (v : E) :
    HasFDerivAt (fun y => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
  (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x
    ((hf.fderiv_right (m := 1) (by decide)).differentiableAt_one.hasFDerivAt)

/-- For a locally C² amplitude its second directional derivative evaluates the Hessian twice on that direction. -/
theorem second_direction_hessian (hf : ContDiffAt ℝ 2 f x) (v : E) :
    secondDirectionalDerivative f v x = fderiv ℝ (fderiv ℝ f) x v v := by
  change fderiv ℝ (fun y => fderiv ℝ f y v) x v = _
  rw [(hasFDerivAt_direction hf v).fderiv]
  rfl

/-- A normalized scalar factor with zero gradient preserves the full first differential. -/
theorem gradient_smul_critical (hw : DifferentiableAt ℝ w x) (hf : DifferentiableAt ℝ f x)
    (h₀ : w x = 1) (h₁ : fderiv ℝ w x = 0) :
    fderiv ℝ (fun y => w y • f y) x = fderiv ℝ f x := by
  rw [fderiv_fun_smul hw hf, h₀, h₁, one_smul]
  ext v
  simp

/-- For an arbitrary normed-space amplitude, both mixed first-derivative terms vanish at a critical scalar factor. -/
theorem hessian_smul_critical (hw : ContDiffAt ℝ 2 w x) (hf : ContDiffAt ℝ 2 f x)
    (h₀ : w x = 1) (h₁ : fderiv ℝ w x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => w y • f y)) x u v =
      fderiv ℝ (fderiv ℝ f) x u v + fderiv ℝ (fderiv ℝ w) x u v • f x := by
  have he : (fun y => fderiv ℝ (fun z => w z • f z) y v) =ᶠ[𝓝 x]
      fun y => w y • fderiv ℝ f y v + fderiv ℝ w y v • f y := by
    filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hw,
      PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf] with y hy hz
    simp [fderiv_fun_smul hy hz]
  have hdw := (hw.differentiableAt (by decide)).hasFDerivAt
  have hdf := (hf.differentiableAt (by decide)).hasFDerivAt
  have hr := ((hdw.fun_smul (hasFDerivAt_direction hf v)).fun_add
    ((hasFDerivAt_direction hw v).fun_smul hdf)).congr_of_eventuallyEq he
  have hprod : ContDiffAt ℝ 2 (fun y => w y • f y) x := hw.smul hf
  have hl := hasFDerivAt_direction hprod v
  have hv := congrArg (fun T : E →L[ℝ] F => T u) (hl.unique hr)
  simpa [h₀, h₁] using hv

variable {g : Covector → Mat4} {A : Covector → F} {R : Covector → ℝ}

/-- The metric half-density leaves the amplitude gradient unchanged at the normal center. -/
theorem gradient_weighted_smul (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hA : ContDiffAt ℝ 2 A 0) :
    fderiv ℝ (fun y => (metricWeight ∘ g) y • A y) 0 = fderiv ℝ A 0 := by
  have hd := hg.differentiableAt (by decide)
  have hj := RNCMetricHalfDensity.normal_value_gradient hd h.metric_center (metric_gradient_zero h hd)
  exact gradient_smul_critical ((weight_contDiff h hg).differentiableAt (by decide))
    (hA.differentiableAt (by decide)) hj.1 hj.2

/-- The actual mixed Hessian of the weighted field equals the amplitude Hessian plus the term from the metric. -/
theorem hessian_weighted_smul (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hA : ContDiffAt ℝ 2 A 0)
    (u v : Covector) :
    fderiv ℝ (fderiv ℝ (fun y => (metricWeight ∘ g) y • A y)) 0 u v =
      fderiv ℝ (fderiv ℝ A) 0 u v + fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 u v • A 0 := by
  have hd := hg.differentiableAt (by decide)
  have hj := RNCMetricHalfDensity.normal_value_gradient hd h.metric_center (metric_gradient_zero h hd)
  exact hessian_smul_critical (weight_contDiff h hg) hA hj.1 hj.2 u v

/-- The Lorentz trace contributes minus one sixth of scalar curvature times the field value, including for complex fields. -/
theorem box_weighted_smul (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hA : ContDiffAt ℝ 2 A 0) :
    box (fun y => (metricWeight ∘ g) y • A y) axis 0 = box A axis 0 + (-scalar g 0 / 6) • A 0 := by
  have hw := weight_contDiff h hg
  have hprod : ContDiffAt ℝ 2 (fun y => (metricWeight ∘ g) y • A y) 0 := hw.smul hA
  have hv (v : Covector) : secondDirectionalDerivative (fun y => (metricWeight ∘ g) y • A y) v 0 =
      secondDirectionalDerivative A v 0 + secondDirectionalDerivative (metricWeight ∘ g) v 0 • A 0 := by
    rw [second_direction_hessian hprod, second_direction_hessian hA, second_direction_hessian hw]
    exact hessian_weighted_smul h hg hA v v
  rw [← box_metricWeight h hg]
  simp only [box, hv, sub_smul]
  abel

/-- Ordinary scalar multiplication by the half-density preserves the real amplitude gradient. -/
theorem gradient_weighted (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hR : ContDiffAt ℝ 2 R 0) :
    fderiv ℝ (fun y => (metricWeight ∘ g) y * R y) 0 = fderiv ℝ R 0 :=
  gradient_weighted_smul h hg hR

/-- Mixed product Hessian for a real amplitude in arbitrary coordinate directions. -/
theorem hessian_weighted (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hR : ContDiffAt ℝ 2 R 0)
    (u v : Covector) :
    fderiv ℝ (fderiv ℝ (fun y => (metricWeight ∘ g) y * R y)) 0 u v =
      fderiv ℝ (fderiv ℝ R) 0 u v + R 0 * fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 u v := by
  simpa only [smul_eq_mul, mul_comm (R 0)] using hessian_weighted_smul h hg hR u v

/-- The real amplitude form of the coordinate wave operator with its scalar-curvature correction. -/
theorem box_weighted (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (hR : ContDiffAt ℝ 2 R 0) :
    box (fun y => (metricWeight ∘ g) y * R y) axis 0 = box R axis 0 - R 0 * scalar g 0 / 6 := by
  rw [show box (fun y => (metricWeight ∘ g) y * R y) axis 0 = _ from box_weighted_smul h hg hR,
    smul_eq_mul]
  ring

end FoliationQM.RNCHalfDensityProduct
