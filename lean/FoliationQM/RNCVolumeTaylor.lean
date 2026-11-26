module

public import FoliationQM.RNCRicciHalfDensity

/-!
# The coordinate volume expansion in a normal chart

In v13 Lemma 9.1 the volume factor is the square of the half-density.
At the normalized critical center this doubles the Hessian, giving the
quadratic coefficient −Ric/6 for the actual volume multiplier. Local C³
regularity bounds the remainder uniformly in all coordinate directions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCVolumeTaylor

open LorentzMatrixGroup RNCCoordinateConnection RNCCoordinateCurvature RNCNormalChart
open RNCHalfDensityJet RNCVolumeDensity Asymptotics
open scoped Matrix.Norms.Operator Topology

variable {g : Covector → Mat4}

/-- The actual square-root determinant has the regularity of the metric near the normal center. -/
theorem volume_contDiff (h : IsNormal g) {k : WithTop ℕ∞} (hg : ContDiffAt ℝ k g 0) :
    ContDiffAt ℝ k (volumeFactor ∘ g) 0 :=
  (RNCMetricHalfDensity.volume_smooth (by rw [h.metric_center, eta_det]; norm_num) k).comp 0 hg

/-- The normal-coordinate volume factor equals one and has vanishing first derivative at the center. -/
theorem volume_value_gradient (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) :
    (volumeFactor ∘ g) 0 = 1 ∧ fderiv ℝ (volumeFactor ∘ g) 0 = 0 := by
  have hn : (g 0).det < 0 := by rw [h.metric_center, eta_det]; norm_num
  exact ⟨by simpa only [Function.comp_apply, h.metric_center] using center_values.1,
    RNCCriticalComposition.gradient_comp_critical hg
      (RNCMetricHalfDensity.volume_smooth hn 1).differentiableAt_one (metric_gradient_zero h hg)⟩

/-- Taking the square root at the critical center halves the full volume Hessian. -/
theorem volume_hessian_apply (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (u v : Covector) :
    fderiv ℝ (fderiv ℝ (volumeFactor ∘ g)) 0 u v =
      2 * fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 u v := by
  obtain ⟨hv, hd⟩ := volume_value_gradient h (hg.differentiableAt (by decide))
  have hs : fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 u v =
      fderiv ℝ (fderiv ℝ (volumeFactor ∘ g)) 0 u v / 2 :=
    RNCCriticalComposition.sqrt_hessian_at_one (volume_contDiff h hg) hv hd u v
  linarith only [hs]

/-- The volume Hessian in any pair of coordinate directions is minus one third of the Ricci entry. -/
theorem mixed_hessian (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b : Fin 4) :
    fderiv ℝ (fderiv ℝ (volumeFactor ∘ g)) 0 (axis a) (axis b) = -ricci g 0 a b / 3 := by
  rw [volume_hessian_apply h hg, RNCRicciHalfDensity.mixed_hessian h hg]
  ring

/-- As a bilinear map the volume Hessian is the quadratic-model Hessian with twice the Ricci matrix. -/
theorem full_hessian (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) :
    fderiv ℝ (fderiv ℝ (volumeFactor ∘ g)) 0 = hessian ((2 : ℝ) • ricci g 0) := by
  apply RNCRicciHalfDensity.bilinear_ext_axis
  intro i j
  rw [mixed_hessian h hg, hessian_apply]
  simp only [axis, form_basis, Matrix.smul_apply, smul_eq_mul, RNCRicciHalfDensity.ricci_symmetric h hg j i]
  ring

/-- The square-root metric determinant has the v13 Ricci volume polynomial with a uniform cubic remainder. -/
theorem volume_expansion (h : IsNormal g) (hg : ContDiffAt ℝ 3 g 0) :
    (fun y => volumeFactor (g y) -
      (1 - (1 / 6 : ℝ) * ∑ i, ∑ j, ricci g 0 i j * y i * y j)) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
  obtain ⟨hv, hd⟩ := volume_value_gradient h (hg.differentiableAt (by decide))
  have hr := (RNCExpansionContraction.expansion_iff_jet (A := (2 : ℝ) • ricci g 0)
    (volume_contDiff h hg)).mpr ⟨hv, hd, full_hessian h (hg.of_le (by decide))⟩
  apply hr.congr_left
  intro y
  simp only [Pi.sub_apply, Function.comp_apply, weight_eq, Matrix.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum]
  ring

end FoliationQM.RNCVolumeTaylor
