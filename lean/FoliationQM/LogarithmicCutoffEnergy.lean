module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The genuine radial energy of a logarithmic cutoff

Source: v13 `eq:log_cutoff_l2_bound`, component kinds C and D. The positive
radial Jacobian is retained in the actual interval integral. Its value and
vanishing limit are proved under `0 < ε < 1`; a radial derivative majorant
then bounds genuine integrable energies. Tubular coordinates and their volume
formula, smooth cutoff construction, and weak extension are separate bridges.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LogarithmicCutoffEnergy

open Filter MeasureTheory Set
open scoped Topology

private theorem sq_le_self {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) : ε ^ 2 ≤ ε := by
  nlinarith [mul_pos hε (sub_pos.mpr hε1)]

private theorem positive_on_annulus {ε r : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hr : r ∈ uIcc (ε ^ 2) ε) : 0 < r := by
  rw [uIcc_of_le (sq_le_self hε hε1)] at hr
  exact lt_of_lt_of_le (sq_pos_of_pos hε) hr.1

/-- The actual logarithmic radial energy density is integrable on its positive transition interval; division never meets a zero radius or logarithm. -/
theorem intervalIntegrable_radial_energy {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun r => r / (r ^ 2 * |Real.log ε| ^ 2)) volume (ε ^ 2) ε := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_id.div ((continuousOn_id.pow 2).mul continuousOn_const) ?_
  intro r hr
  exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (positive_on_annulus hε hε1 hr)))
    (pow_ne_zero 2 (abs_ne_zero.mpr (ne_of_lt (Real.log_neg hε hε1))))

/-- The genuine weighted radial integral from ε² to ε is exactly the reciprocal absolute logarithm, with the codimension-two radial factor retained. -/
theorem radial_energy_eq {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (∫ r in (ε ^ 2)..ε, r / (r ^ 2 * |Real.log ε| ^ 2)) = 1 / |Real.log ε| := by
  have hlog : Real.log ε ≠ 0 := ne_of_lt (Real.log_neg hε hε1)
  calc
    _ = (∫ r in (ε ^ 2)..ε, r⁻¹) / |Real.log ε| ^ 2 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 := ne_of_gt (positive_on_annulus hε hε1 hr)
      field_simp
    _ = 1 / |Real.log ε| := by
      rw [integral_inv_of_pos (sq_pos_of_pos hε) hε,
        Real.log_div (ne_of_gt hε) (pow_ne_zero 2 (ne_of_gt hε)), Real.log_pow,
        abs_of_neg (Real.log_neg hε hε1)]
      norm_num
      field_simp
      ring

/-- The reciprocal absolute logarithm tends to zero as a positive cutoff radius tends to zero, using the actual logarithm's divergence. -/
theorem tendsto_inv_abs_log :
    Tendsto (fun ε : ℝ => 1 / |Real.log ε|) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero).abs
  simpa only [Function.comp_apply, abs_inv, abs_zero, one_div] using h

/-- The genuine radial energy integral tends to zero as ε approaches zero through positive values; its exact formula is used only eventually inside (0,1). -/
theorem tendsto_radial_energy :
    Tendsto (fun ε : ℝ => ∫ r in (ε ^ 2)..ε, r / (r ^ 2 * |Real.log ε| ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_inv_abs_log.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (radial_energy_eq hε.1 hε.2).symm

/-- A genuine integrable radial derivative with the logarithmic pointwise bound has weighted square energy at most C² divided by the absolute logarithm. -/
theorem radial_energy_le {ε C : ℝ} {g : ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C)
    (hg : IntervalIntegrable (fun r => r * (g r) ^ 2) volume (ε ^ 2) ε)
    (hbound : ∀ r ∈ Icc (ε ^ 2) ε, |g r| ≤ C / (r * |Real.log ε|)) :
    (∫ r in (ε ^ 2)..ε, r * (g r) ^ 2) ≤ C ^ 2 / |Real.log ε| := by
  have hab := sq_le_self hε hε1
  have hlog : 0 < |Real.log ε| := abs_pos.mpr (ne_of_lt (Real.log_neg hε hε1))
  calc
    _ ≤ ∫ r in (ε ^ 2)..ε, C ^ 2 * (r / (r ^ 2 * |Real.log ε| ^ 2)) := by
      apply intervalIntegral.integral_mono_on hab hg
        ((intervalIntegrable_radial_energy hε hε1).const_mul (C ^ 2))
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le (sq_pos_of_pos hε) hr.1
      have hs := (sq_le_sq₀ (abs_nonneg (g r))
        (div_nonneg hC (mul_nonneg hr0.le hlog.le))).2 (hbound r hr)
      rw [sq_abs] at hs
      calc
        r * (g r) ^ 2 ≤ r * (C / (r * |Real.log ε|)) ^ 2 := mul_le_mul_of_nonneg_left hs hr0.le
        _ = C ^ 2 * (r / (r ^ 2 * |Real.log ε| ^ 2)) := by ring
    _ = C ^ 2 / |Real.log ε| := by
      rw [intervalIntegral.integral_const_mul, radial_energy_eq hε hε1]
      ring

/-- A nonnegative family bounded by a fixed logarithmic energy majorant vanishes as the positive cutoff radius tends to zero. -/
theorem tendsto_of_logarithmic_bound {E : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ E ε ∧ E ε ≤ C / |Real.log ε|) :
    Tendsto E (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_inv_abs_log.const_mul C
  simp only [mul_zero, mul_one_div] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (hbound.mono fun _ hx => hx.1) (hbound.mono fun _ hx => hx.2)

end FoliationQM.LogarithmicCutoffEnergy
