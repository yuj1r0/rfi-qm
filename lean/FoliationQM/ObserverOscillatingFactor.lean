module

public import FoliationQM.ObserverGaussianFisher
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth observer factors with persistent Fisher scores

For the limiting statement of v13 Remark 5.2, a positive factor may tend
uniformly to one on the whole three-dimensional slice while its derivatives
continue to oscillate. The squared-amplitude representation gives its
Euclidean Fisher integrand as an explicit cosine square.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverOscillatingFactor

open LorentzCoordinates FisherNormalization ObserverGaussianFisher Filter
open scoped Topology ContDiff

/-- Positive integer spatial frequency, starting at two. -/
def frequency (n : ℕ) : ℝ := (n : ℝ) + 2

/-- Positive spatial amplitude varying only along the first coordinate. -/
def amplitude (n : ℕ) (x : Spatial) : ℝ :=
  1 + (1 + Real.sin (frequency n * x 0)) / frequency n

/-- The observer factor is the square of the oscillatory amplitude. -/
def factor (n : ℕ) (x : Spatial) : ℝ := (amplitude n x)^2

/-- Each spatial frequency is positive. -/
theorem frequency_pos (n : ℕ) : 0 < frequency n := by unfold frequency; positivity

/-- The amplitudes are bounded between one and one plus twice the reciprocal frequency. -/
theorem amplitude_bounds (n : ℕ) (x : Spatial) :
    1 ≤ amplitude n x ∧ amplitude n x ≤ 1+2/frequency n := by
  have hs := Real.neg_one_le_sin (frequency n*x 0)
  have ht := Real.sin_le_one (frequency n*x 0)
  unfold amplitude
  constructor
  · linarith [div_nonneg (by linarith : 0 ≤ 1 + Real.sin (frequency n*x 0)) (frequency_pos n).le]
  · exact add_le_add_right (div_le_div_of_nonneg_right
      (show 1+Real.sin (frequency n*x 0) ≤ 2 by linarith) (frequency_pos n).le) 1

/-- All factors are at least one, in particular strictly positive at every site. -/
theorem one_le_factor (n : ℕ) (x : Spatial) : 1 ≤ factor n x := by
  have ha := (amplitude_bounds n x).1
  unfold factor
  nlinarith [sq_nonneg (amplitude n x-1)]

/-- Each factor is smooth on the entire three-dimensional observer slice. -/
theorem factor_smooth (n : ℕ) : ContDiff ℝ ∞ (factor n) := by
  unfold factor amplitude
  fun_prop

/-- A uniform error envelope for the positive factors against the constant profile one. -/
theorem factor_error (n : ℕ) (x : Spatial) :
    |factor n x - 1| ≤ 4*(frequency n)⁻¹ + 4*((frequency n)⁻¹)^2 := by
  obtain ⟨hl, hu⟩ := amplitude_bounds n x
  rw [abs_of_nonneg (sub_nonneg.mpr (one_le_factor n x)), factor]
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ amplitude n x) hu 2
  rw [div_eq_mul_inv] at hsq
  nlinarith

/-- The displayed uniform envelope tends to zero as the spatial frequencies increase. -/
theorem envelope_tendsto : Tendsto (fun n => 4*(frequency n)⁻¹ + 4*((frequency n)⁻¹)^2)
    atTop (𝓝 0) := by
  have ht : Tendsto frequency atTop atTop :=
    tendsto_atTop_mono (fun n => by simp [frequency]) tendsto_natCast_atTop_atTop
  have hv := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ht
  simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    (hv.const_mul 4).add ((hv.pow 2).const_mul 4)

/-- Spatially uniform convergence of the smooth factors to one on the full slice. -/
theorem uniform_to_one : TendstoUniformly factor (fun _ => 1) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [envelope_tendsto.eventually (gt_mem_nhds hε)] with n hn
  intro x
  rw [Real.dist_eq, abs_sub_comm]
  exact (factor_error n x).trans_lt hn

/-- Differentiating the signed logarithmic factor in an actual spatial direction
retains the cosine of the oscillating phase in the first coordinate. -/
theorem score_eq (n : ℕ) (x v : Spatial) :
    score (factor n) x v = 2*Real.cos (frequency n*x 0)*v 0 / amplitude n x := by
  have k := frequency_pos n
  have ha : 0 < amplitude n x := lt_of_lt_of_le zero_lt_one (amplitude_bounds n x).1
  have hd := (((((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x).const_mul (frequency n)).sin).const_add 1).mul_const
    (frequency n)⁻¹).const_add 1
  have ham : HasFDerivAt (amplitude n)
      ((frequency n)⁻¹ • Real.cos (frequency n*x 0) • frequency n •
        (ContinuousLinearMap.proj 0 : Spatial →L[ℝ] ℝ)) x := by
    unfold amplitude
    simpa only [div_eq_mul_inv] using hd
  have hf := ham.pow 2
  rw [FisherNormalization.score_eq (factor_smooth n |>.differentiable (by decide) x)
    (lt_of_lt_of_le zero_lt_one (one_le_factor n x)), show fderiv ℝ (factor n) x = _ from hf.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  unfold factor
  norm_num
  field_simp [k.ne', ha.ne']

/-- Summing the true squared score over all three Cartesian unit directions gives
the persistent Fisher integrand 4 cos²(kx₀). -/
theorem trace_eq (n : ℕ) (x : Spatial) :
    traceIntegrand (factor n) axes x = 4*Real.cos (frequency n*x 0)^2 := by
  have ha : 0 < amplitude n x := lt_of_lt_of_le zero_lt_one (amplitude_bounds n x).1
  rw [traceIntegrand, Fin.sum_univ_three]
  simp [score_eq, axes, factor]
  field_simp [ha.ne']
  ring

end FoliationQM.ObserverOscillatingFactor
