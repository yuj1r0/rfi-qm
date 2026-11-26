module

public import FoliationQM.RNCVolumeDensity
public import FoliationQM.RNCDeterminantDifferential
public import FoliationQM.RNCCriticalComposition
public import FoliationQM.RNCMetricNormalization

/-!
# First and second differentials of the Lorentz metric half-density

The fourth root in Lemma 9.1 is a function of the actual metric entries.
Jacobi's determinant formula determines its differential throughout the
negative-determinant domain. At a normal-chart center its Hessian therefore
depends only on the signed trace of the metric's second derivatives.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCMetricHalfDensity

open scoped Matrix.Norms.Operator
open LorentzMatrixGroup RNCVolumeDensity RNCDeterminantDifferential

/-- The positive volume factor is smooth at every metric with negative determinant. -/
theorem volume_smooth {G : Mat4} (hG : G.det < 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k volumeFactor G :=
  ((contDiff_det (Fin 4) k).contDiffAt.neg).sqrt (neg_ne_zero.mpr hG.ne)

/-- The positive fourth root is smooth throughout the Lorentzian determinant domain. -/
theorem weight_smooth {G : Mat4} (hG : G.det < 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k metricWeight G :=
  (volume_smooth hG k).sqrt (Real.sqrt_pos.2 (neg_pos.mpr hG)).ne'

/-- The differential of the coordinate volume factor is half the volume times the inverse-metric trace. -/
theorem volume_differential {G : Mat4} (hG : G.det < 0) (H : Mat4) :
    fderiv ℝ volumeFactor G H = (volumeFactor G / 2) * (G⁻¹ * H).trace := by
  have hd := ((contDiff_det (Fin 4) 1).differentiable_one (x := G)).hasFDerivAt
  have hs := hd.neg.sqrt (neg_ne_zero.mpr hG.ne)
  have hv : 0 < volumeFactor G := Real.sqrt_pos.2 (neg_pos.mpr hG)
  have hsq : (volumeFactor G) ^ 2 = -G.det := Real.sq_sqrt (neg_nonneg.mpr hG.le)
  calc
    _ = (1 / (2 * volumeFactor G)) * (-(G.det * (G⁻¹ * H).trace)) := by
      change fderiv ℝ (fun M : Mat4 => Real.sqrt (-M.det)) G H = _
      calc
        _ = (1 / (2 * volumeFactor G)) * (-(fderiv ℝ Matrix.det G H)) :=
          congrArg (fun L : Mat4 →L[ℝ] ℝ => L H) hs.fderiv
        _ = _ := congrArg (fun a : ℝ => (1 / (2 * volumeFactor G)) * (-a))
          (fderiv_det_apply G H (isUnit_iff_ne_zero.mpr hG.ne))
    _ = _ := by
      rw [← neg_mul, ← hsq]
      field_simp [hv.ne']

/-- The differential of the half-density carries one quarter of the inverse-metric trace. -/
theorem weight_differential {G : Mat4} (hG : G.det < 0) (H : Mat4) :
    fderiv ℝ metricWeight G H = (metricWeight G / 4) * (G⁻¹ * H).trace := by
  have hv : 0 < volumeFactor G := Real.sqrt_pos.2 (neg_pos.mpr hG)
  have hd := ((volume_smooth hG 1).differentiableAt_one.hasFDerivAt).sqrt hv.ne'
  calc
    _ = (1 / (2 * metricWeight G)) * ((volumeFactor G / 2) * (G⁻¹ * H).trace) := by
      change fderiv ℝ (fun M => Real.sqrt (volumeFactor M)) G H = _
      calc
        _ = (1 / (2 * metricWeight G)) * (fderiv ℝ volumeFactor G H) :=
          congrArg (fun L : Mat4 →L[ℝ] ℝ => L H) hd.fderiv
        _ = _ := congrArg (fun a : ℝ => (1 / (2 * metricWeight G)) * a)
          (volume_differential hG H)
    _ = _ := by
      rw [← weight_sq]
      field_simp [(weight_pos hG).ne']
      ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → Mat4} {x : E}

/-- The metric half-density has value one and zero first derivative in a chart with Minkowski metric and vanishing metric differential at the center. -/
theorem normal_value_gradient (hg : DifferentiableAt ℝ g x) (hx : g x = eta)
    (h₁ : fderiv ℝ g x = 0) :
    (metricWeight ∘ g) x = 1 ∧ fderiv ℝ (metricWeight ∘ g) x = 0 := by
  have hneg : (g x).det < 0 := by rw [hx, eta_det]; norm_num
  exact ⟨by simpa only [Function.comp_apply, hx] using center_values.2,
    RNCCriticalComposition.gradient_comp_critical hg (weight_smooth hneg 1).differentiableAt_one h₁⟩

/-- The Hessian of the actual fourth-root weight is a quarter of the Lorentz trace of the metric Hessian at a normal center. -/
theorem normal_hessian (hg : ContDiffAt ℝ 2 g x) (hx : g x = eta)
    (h₁ : fderiv ℝ g x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) x u v =
      (eta * (fderiv ℝ (fderiv ℝ g) x u v)).trace / 4 := by
  have hneg : (g x).det < 0 := by rw [hx, eta_det]; norm_num
  calc
    _ = fderiv ℝ metricWeight (g x) (fderiv ℝ (fderiv ℝ g) x u v) :=
      RNCCriticalComposition.hessian_comp_critical hg (weight_smooth hneg 2) h₁ u v
    _ = _ := by
      have he := weight_differential hneg (fderiv ℝ (fderiv ℝ g) x u v)
      rw [hx, center_values.2, Matrix.inv_eq_left_inv eta_sq] at he
      rw [hx]
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using he

/-- Expanding the trace gives the time Hessian with positive sign and the three spatial Hessians with negative sign. -/
theorem normal_hessian_entries (hg : ContDiffAt ℝ 2 g x) (hx : g x = eta)
    (h₁ : fderiv ℝ g x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) x u v =
      (fderiv ℝ (fderiv ℝ (fun y => g y 0 0)) x u v -
       fderiv ℝ (fderiv ℝ (fun y => g y 1 1)) x u v -
       fderiv ℝ (fderiv ℝ (fun y => g y 2 2)) x u v -
       fderiv ℝ (fderiv ℝ (fun y => g y 3 3)) x u v) / 4 := by
  rw [normal_hessian hg hx h₁]
  exact congrArg (· / 4) <| (congrArg Matrix.trace (RNCMetricNormalization.hessian_normalize_apply hg u v)).symm.trans
    (RNCMetricNormalization.trace_hessian_normalize_entries hg u v)

end FoliationQM.RNCMetricHalfDensity
