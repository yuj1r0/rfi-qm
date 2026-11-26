module

public import FoliationQM.GaussianSpatialFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Recovery of spectral values by narrow Gaussian windows

The three-dimensional angular spectrum is averaged around a fixed wave number.
Translation invariance and the volume Jacobian for a dilation turn the average
into an integral against a single Gaussian. Dominated convergence then recovers
each value of a bounded continuous spectrum as the window narrows.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianSpectralApproximation

open GaussianSpatialFourier LorentzCoordinates MeasureTheory Filter
open scoped Topology

/-- The Gaussian average centered at the spatial wave number `u`, with inverse width `R`. -/
def smoothed (F : Spatial → ℝ) (u : Spatial) (R : ℝ) : ℝ :=
  (R ^ 3 / mass 1) * ∫ k, F k * weight (R ^ 2) (k - u)

private theorem weight_inv_smul {R : ℝ} (hR : 0 < R) (z : Spatial) :
    weight (R ^ 2) (R⁻¹ • z) = weight 1 z := by
  have hs : speedSq (R⁻¹ • z) = R⁻¹ ^ 2 * speedSq z := by
    simp only [speedSq, spatialDot, Pi.smul_apply, smul_eq_mul]
    ring
  unfold weight
  rw [hs]
  congr 1
  field_simp [hR.ne']

/-- Translating by the window center and rescaling by its width gives one fixed Gaussian
kernel and absorbs the three-dimensional volume Jacobian. -/
theorem smoothed_eq_rescaled (F : Spatial → ℝ) (u : Spatial) {R : ℝ} (hR : 0 < R) :
    smoothed F u R = (∫ z, weight 1 z * F (u + R⁻¹ • z)) / mass 1 := by
  let f := fun k : Spatial => F k * weight (R ^ 2) (k - u)
  have ht := integral_add_left_eq_self (μ := (volume : Measure Spatial)) f u
  have hs := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Spatial)
    (fun x => f (u + x)) hR.le
  rw [ht] at hs
  have hd : Module.finrank ℝ Spatial = 3 := by simp [Spatial]
  rw [hd, smul_eq_mul] at hs
  have hi : (∫ z, weight 1 z * F (u + R⁻¹ • z)) = R ^ 3 * ∫ k, f k := by
    convert hs using 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => by simp [f, weight_inv_smul hR, mul_comm]
  rw [hi]
  change R ^ 3 / mass 1 * (∫ k, f k) = (R ^ 3 * (∫ k, f k)) / mass 1
  ring

/-- The normalized Gaussian averages of a bounded continuous spectrum converge pointwise
to that spectrum as the inverse width tends to positive infinity. -/
theorem tendsto_smoothed (F : Spatial → ℝ) (hF : Continuous F) {B : ℝ}
    (hb : ∀ k, |F k| ≤ B) (u : Spatial) :
    Tendsto (smoothed F u) atTop (𝓝 (F u)) := by
  have h : Tendsto (fun R : ℝ => ∫ z, weight 1 z * F (u + R⁻¹ • z))
      atTop (𝓝 (∫ z, weight 1 z * F u)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => weight 1 z * B)
    · exact Eventually.of_forall fun R => by
        apply Continuous.aestronglyMeasurable
        unfold weight speedSq spatialDot
        fun_prop
    · exact Eventually.of_forall fun R => ae_of_all _ fun z => by
        have hw : 0 < weight 1 z := Real.exp_pos _
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
        exact mul_le_mul_of_nonneg_left (hb _) hw.le
    · exact (integrable_weight (by norm_num : (0 : ℝ) < 1)).mul_const B
    · apply ae_of_all
      intro z
      have hz : Tendsto (fun R : ℝ => u + R⁻¹ • z) atTop (𝓝 u) := by
        simpa using (tendsto_const_nhds (x := u)).add
          ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const z)
      exact tendsto_const_nhds.mul (hF.continuousAt.tendsto.comp hz)
  have hm := (mass_pos (by norm_num : (0 : ℝ) < 1)).ne'
  have hnorm := h.div_const (mass 1)
  rw [integral_mul_const, integral_weight (by norm_num : (0 : ℝ) < 1),
    mul_div_cancel_left₀ _ hm] at hnorm
  apply hnorm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (smoothed_eq_rescaled F u hR).symm

end FoliationQM.GaussianSpectralApproximation
