module

public import FoliationQM.SmoothTransitionDerivativeBound
public import FoliationQM.SmoothLogarithmicCutoffProfile
public import FoliationQM.LogarithmicCutoffEnergy

/-!
# Energy decay for the actual smooth logarithmic cutoff

Source: v13 `eq:log_cutoff_l2_bound`, component kinds C and D. One fixed
transition-derivative bound controls all positive cutoff radii. The actual
derivative of the smooth profile gives a continuous, genuinely integrable
radial energy, whose nonnegative integral tends to zero. Tubular geometry
and its metric and volume comparisons remain separate obligations.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothLogarithmicCutoffEnergy

open Filter MeasureTheory Set
open scoped Topology ContDiff
open SmoothLogarithmicCutoffProfile

/-- One nonnegative constant controls the actual smooth-profile derivative at every positive radius for every cutoff parameter between zero and one. -/
theorem exists_uniform_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ r : ℝ, 0 < r → |deriv (profile ε) r| ≤ C / (r * |Real.log ε|) := by
  obtain ⟨C, hC, hbound⟩ := SmoothTransitionDerivativeBound.exists_uniform_derivative_bound
  refine ⟨C, hC, fun ε h0 h1 r hr => ?_⟩
  rw [(hasDerivAt_profile h0 h1 hr).deriv, abs_div,
    abs_of_pos (mul_pos hr (abs_pos.mpr (Real.log_neg h0 h1).ne))]
  exact div_le_div_of_nonneg_right (hbound _) (mul_nonneg hr.le (abs_nonneg _))

/-- For an admissible cutoff parameter the actual radial derivative-square density is continuous on the whole real line. -/
theorem continuous_radial_energy {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Continuous (fun r : ℝ => r * (deriv (profile ε) r) ^ 2) := by
  exact continuous_id.mul (((contDiff_profile h0 h1).continuous_deriv (by simp)).pow 2)

/-- The actual smooth cutoff's weighted derivative-square is genuinely integrable on its transition interval, by continuity. -/
theorem intervalIntegrable_radial_energy {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntervalIntegrable (fun r : ℝ => r * (deriv (profile ε) r) ^ 2)
      volume (ε ^ 2) ε :=
  (continuous_radial_energy h0 h1).intervalIntegrable _ _

/-- The actual radial energy integral is nonnegative because its interval is positively oriented and its radii and derivative squares are nonnegative. -/
theorem radial_energy_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    0 ≤ ∫ r in (ε ^ 2)..ε, r * (deriv (profile ε) r) ^ 2 := by
  have hab : ε ^ 2 ≤ ε := by nlinarith [mul_pos h0 (sub_pos.mpr h1)]
  apply intervalIntegral.integral_nonneg hab
  intro r hr
  exact mul_nonneg ((sq_nonneg ε).trans hr.1) (sq_nonneg _)

/-- One fixed nonnegative constant bounds every admissible actual smooth-cutoff radial energy by its square divided by the absolute logarithm. -/
theorem exists_radial_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ r in (ε ^ 2)..ε, r * (deriv (profile ε) r) ^ 2) ≤ C ^ 2 / |Real.log ε| := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_derivative_bound
  refine ⟨C, hC, fun ε h0 h1 => ?_⟩
  apply LogarithmicCutoffEnergy.radial_energy_le h0 h1 hC
    (intervalIntegrable_radial_energy h0 h1)
  intro r hr
  exact hbound ε h0 h1 r ((sq_pos_of_pos h0).trans_le hr.1)

/-- The genuine radial energy of the actual smooth cutoff tends to zero as the cutoff parameter tends to zero through positive values. -/
theorem tendsto_radial_energy :
    Tendsto (fun ε : ℝ => ∫ r in (ε ^ 2)..ε, r * (deriv (profile ε) r) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := exists_radial_energy_bound
  apply LogarithmicCutoffEnergy.tendsto_of_logarithmic_bound (C := C ^ 2)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact ⟨radial_energy_nonneg hε.1 hε.2, hbound ε hε.1 hε.2⟩

end FoliationQM.SmoothLogarithmicCutoffEnergy
