module

public import FoliationQM.DeBrogliePhase
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Genuine fixed-velocity nonrelativistic limits

Source: v13 `prop:debroglie`, its equal-time restriction and fixed nonzero
velocity limit as c tends to positive infinity. Subluminality is proved to
hold eventually using the explicit Euclidean speed, and every limit below
is Mathlib's actual `Tendsto` statement.

The spatial gradient is the gradient of the actual uniform-boost phase,
identified by actual Frechet differentiation in `DeBrogliePhase`. Its limit
is (m/ℏ)v, nonzero under positive m and ℏ exactly when the fixed velocity is
nonzero. The zero-velocity family shows that relative speed tending to zero
alone does not imply a nonzero phase-gradient limit. Euclidean magnitudes
always use the coordinate square sum, not the function-space norm.

The clock tilt tends to zero with a finite c²-rescaled limit, while the
clock frequency divided by c² tends to m/ℏ. The exact cancellation connecting
these terms to the spatial wave vector is proved in `DeBrogliePhase`.
The convergence statements concern the spatial gradient and its differential;
no finite limit of the full spacetime phase is asserted.
-/

@[expose] public section
noncomputable section

open Filter
open scoped Topology

namespace FoliationQM.DeBroglieLimit
open LorentzCoordinates DeBrogliePhase

/-- Every fixed spatial velocity is eventually subluminal for positive c, in both Euclidean-speed and squared-speed forms. -/
theorem eventually_physical_domain (v : Spatial) :
    ∀ᶠ c : ℝ in atTop, 0 < c ∧ euclideanSpeed v < c ∧ speedSq v < c ^ 2 := by
  filter_upwards [eventually_gt_atTop (max 0 (euclideanSpeed v))] with c hc
  have hc0 : 0 < c := lt_of_le_of_lt (le_max_left _ _) hc
  have hcv : euclideanSpeed v < c := lt_of_le_of_lt (le_max_right _ _) hc
  exact ⟨hc0, hcv, (euclideanSpeed_lt_iff hc0 v).1 hcv⟩

/-- The explicit Euclidean relative speed tends to zero at fixed laboratory velocity. -/
theorem tendsto_relative_speed_atTop (v : Spatial) :
    Tendsto (fun c : ℝ => euclideanSpeed v / c) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

/-- The squared Euclidean speed ratio tends to zero as c tends to positive infinity. -/
theorem tendsto_speed_ratio_atTop (v : Spatial) :
    Tendsto (fun c : ℝ => speedSq v / c ^ 2) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : 2 ≠ 0))

/-- The actual Lorentz factor tends to one in the fixed-velocity nonrelativistic limit. -/
theorem tendsto_gamma_atTop (v : Spatial) :
    Tendsto (fun c : ℝ => gamma c v) atTop (𝓝 1) := by
  have h : Tendsto (fun c : ℝ => 1 - speedSq v / c ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_speed_ratio_atTop v)
  simpa [gamma] using h.sqrt.inv₀ (by norm_num : Real.sqrt 1 ≠ 0)

/-- The explicit Euclidean speed is a continuous function of the actual spatial vector. -/
theorem continuous_euclideanSpeed : Continuous euclideanSpeed := by
  unfold euclideanSpeed speedSq spatialDot
  fun_prop

/-- Euclidean pairing against a fixed spatial displacement is continuous. -/
theorem continuous_spatialDot_right (dx : Spatial) : Continuous (fun v => spatialDot v dx) := by
  unfold spatialDot
  fun_prop

/-- The actual relativistic spatial momentum tends to the classical momentum m times velocity. -/
theorem tendsto_momentum_atTop (m : ℝ) (v : Spatial) :
    Tendsto (fun c : ℝ => momentum m c v) atTop (𝓝 (m • v)) := by
  simpa only [momentum, one_mul] using ((tendsto_gamma_atTop v).mul_const m).smul_const v

/-- The actual de Broglie wave vector tends to (m/hbar) times the fixed laboratory velocity. -/
theorem tendsto_waveVector_atTop (m h : ℝ) (v : Spatial) :
    Tendsto (fun c : ℝ => waveVector m c h v) atTop (𝓝 ((m / h) • v)) := by
  simpa only [waveVector, smul_smul, div_eq_mul_inv, mul_comm] using
    (tendsto_momentum_atTop m v).const_smul h⁻¹

/-- The actual Euclidean momentum magnitude has the finite limit |m| times Euclidean speed. -/
theorem tendsto_momentum_magnitude_atTop (m : ℝ) (v : Spatial) :
    Tendsto (fun c : ℝ => euclideanSpeed (momentum m c v)) atTop
      (𝓝 (|m| * euclideanSpeed v)) := by
  simpa only [Function.comp_def, euclideanSpeed_smul] using
    continuous_euclideanSpeed.continuousAt.tendsto.comp (tendsto_momentum_atTop m v)

/-- The actual Euclidean wave-vector magnitude has the finite limit |m/hbar| times Euclidean speed. -/
theorem tendsto_waveVector_magnitude_atTop (m h : ℝ) (v : Spatial) :
    Tendsto (fun c : ℝ => euclideanSpeed (waveVector m c h v)) atTop
      (𝓝 (|m / h| * euclideanSpeed v)) := by
  simpa only [Function.comp_def, euclideanSpeed_smul] using
    continuous_euclideanSpeed.continuousAt.tendsto.comp (tendsto_waveVector_atTop m h v)

/-- For positive mass and action scale, the limiting spatial phase gradient is nonzero exactly when velocity is nonzero. -/
theorem limiting_waveVector_ne_zero_iff {m h : ℝ} (hm : 0 < m) (hh : 0 < h) (v : Spatial) :
    (m / h) • v ≠ 0 ↔ v ≠ 0 := by
  simp [hm.ne', hh.ne']

/-- Zero laboratory velocity gives zero actual spatial wave vector at every c. -/
theorem waveVector_zero_velocity (m c h : ℝ) : waveVector m c h 0 = 0 := by
  simp [waveVector, momentum]

/-- A zero-velocity family has relative speed tending to zero but admits no nonzero limiting wave vector. -/
theorem zero_velocity_counterexample (m h : ℝ) :
    Tendsto (fun c : ℝ => euclideanSpeed (0 : Spatial) / c) atTop (𝓝 0) ∧
      (∀ c : ℝ, waveVector m c h 0 = 0) ∧
      ¬ ∃ k : Spatial, k ≠ 0 ∧
        Tendsto (fun c : ℝ => waveVector m c h 0) atTop (𝓝 k) := by
  refine ⟨tendsto_relative_speed_atTop 0, (fun c => waveVector_zero_velocity m c h), ?_⟩
  rintro ⟨k, hk, hlim⟩
  have hz : Tendsto (fun c : ℝ => waveVector m c h 0) atTop (𝓝 (0 : Spatial)) := by
    simpa only [waveVector_zero_velocity] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Spatial)) atTop (𝓝 0))
  exact hk (tendsto_nhds_unique hlim hz)

/-- The actual equal-time proper-clock shift tends to zero in the fixed-velocity limit. -/
theorem tendsto_equal_time_clock_shift_atTop (v dx : Spatial) :
    Tendsto (fun c : ℝ => properTime c v (displacement c 0 dx)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun c : ℝ => -gamma c v * spatialDot v dx / c ^ 2)
      atTop (𝓝 0) :=
    ((tendsto_gamma_atTop v).neg.mul_const (spatialDot v dx)).div_atTop
      (tendsto_pow_atTop (by decide : 2 ≠ 0))
  apply hlim.congr'
  filter_upwards [eventually_physical_domain v] with c hc
  exact (properTime_equal_time hc.1 v dx).symm

/-- For fixed nonzero velocity and positive mass and action scale, the limiting phase slope along velocity is positive. -/
theorem limiting_phase_slope_velocity_pos {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    {v : Spatial} (hv : v ≠ 0) : 0 < spatialDot ((m / h) • v) v := by
  rw [spatialDot_comm, spatialDot_smul_right]
  change 0 < (m / h) * speedSq v
  apply mul_pos (div_pos hm hh)
  exact lt_of_le_of_ne (speedSq_nonneg v) (fun heq => hv ((speedSq_eq_zero_iff v).1 heq.symm))

/-- The gradient defined by actual coordinate derivatives of the spatial phase tends to the classical de Broglie vector. -/
theorem tendsto_spatialGradient_atTop (m h : ℝ) (v x : Spatial) (t : ℝ) :
    Tendsto (fun c : ℝ => spatialGradient m c h v x t) atTop (𝓝 ((m / h) • v)) := by
  simpa only [spatialGradient_eq_waveVector] using tendsto_waveVector_atTop m h v

/-- The actual equal-time Frechet derivative evaluated on any fixed displacement converges to the classical phase differential. -/
theorem tendsto_fderiv_spatialPhase_atTop (m h : ℝ) (v x dx : Spatial) (t : ℝ) :
    Tendsto (fun c : ℝ => fderiv ℝ (fun y => DeBrogliePhase.phase m c h v (t, y)) x dx) atTop
      (𝓝 (spatialDot ((m / h) • v) dx)) := by
  simpa only [Function.comp_def, fderiv_spatialPhase_apply] using
    (continuous_spatialDot_right dx).continuousAt.tendsto.comp (tendsto_waveVector_atTop m h v)

/-- Fixed nonzero velocity and positive mass and action scale give a strictly positive limiting Euclidean wave-vector magnitude. -/
theorem limiting_waveVector_magnitude_pos {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    {v : Spatial} (hv : v ≠ 0) : 0 < euclideanSpeed ((m / h) • v) :=
  euclideanSpeed_pos ((limiting_waveVector_ne_zero_iff hm hh v).2 hv)

/-- A fixed nonzero velocity has nonzero actual wave vector throughout the eventual physical subluminal domain. -/
theorem eventually_waveVector_ne_zero {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    {v : Spatial} (hv : v ≠ 0) : ∀ᶠ c : ℝ in atTop, waveVector m c h v ≠ 0 := by
  filter_upwards [eventually_physical_domain v] with c hc
  exact waveVector_ne_zero hm hc.1 hh hc.2.2 hv

/-- For fixed nonzero velocity, the actual de Broglie wavelength converges to its finite positive classical value. -/
theorem tendsto_wavelength_atTop {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    {v : Spatial} (hv : v ≠ 0) :
    Tendsto (fun c : ℝ => wavelength m c h v) atTop
      (𝓝 (2 * Real.pi * h / (m * euclideanSpeed v))) := by
  have hmag : Tendsto (fun c : ℝ => euclideanSpeed (momentum m c v)) atTop
      (𝓝 (m * euclideanSpeed v)) := by
    simpa only [abs_of_pos hm] using tendsto_momentum_magnitude_atTop m v
  have hden : m * euclideanSpeed v ≠ 0 := (mul_pos hm (euclideanSpeed_pos hv)).ne'
  simpa only [wavelength_eq m _ hh v, div_eq_mul_inv] using
    (hmag.inv₀ hden).const_mul (2 * Real.pi * h)

/-- The c²-rescaled actual equal-time clock tilt tends to minus the Euclidean velocity-displacement pairing. -/
theorem tendsto_scaled_clock_shift_atTop (v dx : Spatial) :
    Tendsto (fun c : ℝ => c ^ 2 * properTime c v (displacement c 0 dx)) atTop
      (𝓝 (-spatialDot v dx)) := by
  have hlim : Tendsto (fun c : ℝ => -gamma c v * spatialDot v dx) atTop
      (𝓝 (-spatialDot v dx)) := by
    simpa using (tendsto_gamma_atTop v).neg.mul_const (spatialDot v dx)
  apply hlim.congr'
  filter_upwards [eventually_physical_domain v] with c hc
  rw [properTime_equal_time hc.1 v dx]
  field_simp [hc.1.ne']

/-- The actual rest-clock frequency has exact quadratic c scaling, with scaled limit m/hbar. -/
theorem tendsto_frequency_div_sq_atTop (m h : ℝ) :
    Tendsto (fun c : ℝ => frequency m c h / c ^ 2) atTop (𝓝 (m / h)) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => m / h) atTop (𝓝 (m / h))).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  unfold frequency
  field_simp

end FoliationQM.DeBroglieLimit
