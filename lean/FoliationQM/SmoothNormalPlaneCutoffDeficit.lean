module

public import FoliationQM.SmoothNormalPlaneCutoffSupport
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Vanishing deficit of the actual normal-plane cutoff

Source: v13 `eq:log_cutoff_l2_bound`, using the cutoff from
`eq:log_cutoff_wallstrom`, component kinds C and D. The same smooth plane cutoff
approaches one with a genuinely integrable deficit and squared deficit.
Their actual integrals are bounded by
the shrinking Euclidean disk volume. General tubular geometry remains separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothNormalPlaneCutoffDeficit

open Filter MeasureTheory Set
open scoped Topology
open SmoothNormalPlaneCutoff

/-- The actual cutoff deficit lies in L², has an integrable square, and its square and first integrals form a nonnegative chain bounded by π ε². -/
theorem deficit_bounds {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    MemLp (fun z : ℂ => 1 - profile ε z) 2 volume ∧
    Integrable (fun z : ℂ => (1 - profile ε z) ^ 2) volume ∧
    0 ≤ (∫ z : ℂ, (1 - profile ε z) ^ 2) ∧
    (∫ z : ℂ, (1 - profile ε z) ^ 2) ≤ (∫ z : ℂ, 1 - profile ε z) ∧
    (∫ z : ℂ, 1 - profile ε z) ≤ Real.pi * ε ^ 2 := by
  let d : ℂ → ℝ := fun z => 1 - profile ε z
  obtain ⟨hs, hc, hi⟩ := SmoothNormalPlaneCutoffSupport.deficit_data h0 h1
  have hd : Continuous d := continuous_const.sub (contDiff_profile h0 h1).continuous
  have hsq : HasCompactSupport (fun z => d z ^ 2) := by
    simpa only [pow_two, Pi.mul_apply] using! (hc.mul_right (f' := d))
  have hi2 : Integrable (fun z => d z ^ 2) volume :=
    (hd.pow 2).integrable_of_hasCompactSupport hsq
  have hrange (z : ℂ) : 0 ≤ d z ∧ d z ≤ 1 := by
    obtain ⟨hl, hu⟩ := (profile_spec h0 h1).2.2 z
    dsimp [d]
    constructor <;> linarith
  have hsqle (z : ℂ) : d z ^ 2 ≤ d z := by
    obtain ⟨hl, hu⟩ := hrange z
    nlinarith
  have hzero (z : ℂ) (hz : z ∉ Metric.ball (0 : ℂ) ε) : d z = 0 := by
    by_contra hd0
    exact hz (hs hd0)
  have hbound : (∫ z : ℂ, d z) ≤ Real.pi * ε ^ 2 := by
    calc
      (∫ z : ℂ, d z) = ∫ z in Metric.ball (0 : ℂ) ε, d z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ ≤ ∫ _z in Metric.ball (0 : ℂ) ε, (1 : ℝ) :=
        integral_mono hi.restrict (integrableOn_const measure_ball_ne_top)
          (fun z => (hrange z).2)
      _ = ε ^ 2 * Real.pi := by
        simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
          Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal h0.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
      _ = Real.pi * ε ^ 2 := mul_comm _ _
  exact ⟨hd.memLp_of_hasCompactSupport hc, hi2,
    integral_nonneg (fun z => sq_nonneg (d z)), integral_mono hi2 hi hsqle, hbound⟩

/-- The actual integrals of the cutoff deficit and its square both tend to zero as ε tends to zero through positive values. -/
theorem tendsto_deficit_integrals :
    Tendsto (fun ε : ℝ => ∫ z : ℂ, 1 - profile ε z) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ z : ℂ, (1 - profile ε z) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ (∫ z : ℂ, (1 - profile ε z) ^ 2) ∧
      (∫ z : ℂ, (1 - profile ε z) ^ 2) ≤ (∫ z : ℂ, 1 - profile ε z) ∧
      (∫ z : ℂ, 1 - profile ε z) ≤ Real.pi * ε ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (deficit_bounds hε.1 hε.2).2.2
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun ε : ℝ => Real.pi * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (he.pow 2).const_mul Real.pi
  exact ⟨squeeze_zero' (hb.mono fun _ h => h.1.trans h.2.1)
      (hb.mono fun _ h => h.2.2) hp,
    squeeze_zero' (hb.mono fun _ h => h.1)
      (hb.mono fun _ h => h.2.1.trans h.2.2) hp⟩

end FoliationQM.SmoothNormalPlaneCutoffDeficit
