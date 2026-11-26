module

public import FoliationQM.SmoothNormalPlaneCutoffSupport
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual polar energy and L² decay of the smooth normal-plane cutoff

Source: v13 `eq:log_cutoff_l2_bound`, component kinds C and D. The genuine
complex polar Jacobian converts the actual derivative energy to the proved
radial integral. Compact support supplies integrability and actual L² membership
before the norm identity and vanishing limit. General tubular geometry and
positive auxiliary-metric comparisons remain separate obligations.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothNormalPlaneCutoffEnergy

open Filter MeasureTheory Set
open scoped Topology ContDiff
open SmoothNormalPlaneCutoff

/-- The actual plane derivative energy is integrable and equals twice pi times the genuine radial energy integral, with the polar Jacobian retained. -/
theorem energy_integral {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Integrable (fun z : ℂ => ‖fderiv ℝ (profile ε) z‖ ^ 2) volume ∧
    (∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2) =
      2 * Real.pi * ∫ r in (ε ^ 2)..ε,
        r * (deriv (SmoothLogarithmicCutoffProfile.profile ε) r) ^ 2 := by
  let H : ℝ → ℝ := fun r =>
    r * (deriv (SmoothLogarithmicCutoffProfile.profile ε) r) ^ 2
  let J : Set ℝ := Ioo (-Real.pi) Real.pi
  have hab : ε ^ 2 ≤ ε := by nlinarith [mul_pos h0 (sub_pos.mpr h1)]
  have hcont : Continuous H := SmoothLogarithmicCutoffEnergy.continuous_radial_energy h0 h1
  have hcompact : HasCompactSupport H := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro r hr
    have hd : deriv (SmoothLogarithmicCutoffProfile.profile ε) r ≠ 0 := by
      intro hd
      exact hr (by simp [H, hd])
    exact SmoothLogarithmicCutoffProfile.support_deriv_subset h0 h1 hd
  have hi : Integrable H volume := hcont.integrable_of_hasCompactSupport hcompact
  have hj : IntegrableOn (fun _ : ℝ => (1 : ℝ)) J volume :=
    integrableOn_const (by simp [J, Real.volume_Ioo])
  have hprod : IntegrableOn (fun p : ℝ × ℝ => H p.1) (Icc (ε ^ 2) ε ×ˢ J)
      (volume.prod volume) := by
    simpa only [IntegrableOn, Measure.prod_restrict, mul_one] using
      (hi.restrict (s := Icc (ε ^ 2) ε)).mul_prod hj
  have hsub : Icc (ε ^ 2) ε ×ˢ J ⊆ Ioi (0 : ℝ) ×ˢ J := by
    intro p hp
    exact ⟨(sq_pos_of_pos h0).trans_le hp.1.1, hp.2⟩
  have hangle : volume.real J = 2 * Real.pi := by
    change volume.real (Ioo (-Real.pi) Real.pi) = 2 * Real.pi
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    ring
  refine ⟨(SmoothNormalPlaneCutoffSupport.derivative_energy_data h0 h1).2.2, ?_⟩
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ J,
        p.1 • ‖fderiv ℝ (profile ε) (Complex.polarCoord.symm p)‖ ^ 2 :=
      (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ J, H p.1 := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      simp only [norm_fderiv_profile h0 h1, Complex.norm_polarCoord_symm,
        abs_of_pos hp.1, sq_abs, smul_eq_mul, H]
    _ = ∫ p in Icc (ε ^ 2) ε ×ˢ J, H p.1 := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (measurableSet_Ioi.prod measurableSet_Ioo) hsub
      intro p hp
      have hd : deriv (SmoothLogarithmicCutoffProfile.profile ε) p.1 = 0 := by
        by_contra hn
        exact hp.2 ⟨SmoothLogarithmicCutoffProfile.support_deriv_subset h0 h1 hn, hp.1.2⟩
      simp [H, hd]
    _ = ∫ r in Icc (ε ^ 2) ε, ∫ _ in J, H r := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod _ hprod
    _ = 2 * Real.pi * ∫ r in (ε ^ 2)..ε, H r := by
      simp_rw [setIntegral_const, hangle, smul_eq_mul]
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- The actual plane derivative belongs to L², and its finite standard L² seminorm is the square root of its genuine derivative-energy integral. -/
theorem derivative_l2_data {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    MemLp (fderiv ℝ (profile ε)) 2 volume ∧
    (eLpNorm (fderiv ℝ (profile ε)) 2 volume).toReal =
      Real.sqrt (∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2) := by
  have hcont : Continuous (fderiv ℝ (profile ε)) :=
    (contDiff_profile h0 h1).continuous_fderiv (by simp)
  have hcompact : HasCompactSupport (fderiv ℝ (profile ε)) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) ε)
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using (support_fderiv_subset h0 h1 hz).2
  have hlp : MemLp (fderiv ℝ (profile ε)) 2 volume :=
    hcont.memLp_of_hasCompactSupport hcompact
  refine ⟨hlp, ?_⟩
  have hn : eLpNorm (fderiv ℝ (profile ε)) 2 volume =
      ENNReal.ofReal (Real.sqrt (∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2)) := by
    simpa [Real.sqrt_eq_rpow, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hlp
  rw [hn, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- One nonnegative constant bounds the actual nonnegative plane energy for every admissible cutoff radius by twice pi times its square over the absolute logarithm. -/
theorem exists_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 ≤ (∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2) ∧
      (∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2) ≤ 2 * Real.pi * C ^ 2 / |Real.log ε| := by
  obtain ⟨C, hC, hbound⟩ := SmoothLogarithmicCutoffEnergy.exists_radial_energy_bound
  refine ⟨C, hC, fun ε h0 h1 => ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩⟩
  rw [(energy_integral h0 h1).2]
  calc
    _ ≤ 2 * Real.pi * (C ^ 2 / |Real.log ε|) :=
      mul_le_mul_of_nonneg_left (hbound ε h0 h1) (by positivity)
    _ = _ := by ring

/-- Both the actual plane derivative energy and its finite standard L² seminorm tend to zero as the cutoff parameter tends to zero through positive values. -/
theorem tendsto_energy_and_l2_norm :
    Tendsto (fun ε : ℝ => ∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => (eLpNorm (fderiv ℝ (profile ε)) 2 volume).toReal) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := exists_energy_bound
  have he : Tendsto (fun ε : ℝ => ∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply LogarithmicCutoffEnergy.tendsto_of_logarithmic_bound (C := 2 * Real.pi * C ^ 2)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hbound ε hε.1 hε.2
  refine ⟨he, ?_⟩
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  have hs0 : Tendsto (fun ε : ℝ => Real.sqrt (∫ z : ℂ, ‖fderiv ℝ (profile ε) z‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by simpa only [Function.comp_def, Real.sqrt_zero] using hs
  apply hs0.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (derivative_l2_data hε.1 hε.2).2.symm

end FoliationQM.SmoothNormalPlaneCutoffEnergy
