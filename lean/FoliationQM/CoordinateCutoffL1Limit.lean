module

public import FoliationQM.SmoothCoordinateTubeCutoff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine L1 convergence for the constructed coordinate cutoff

Source: v13 `eq:log_cutoff_l2_bound` and its following compact-test
argument, component kinds C and D. Ordinary test terms are controlled by
the fixed integrable field, while the separate derivative commutator is
controlled by its already-proved energy estimate. The region is fixed;
neither finite volume nor compactness is needed for this L1 statement.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffL1Limit

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff
open scoped Topology

/-- On every fixed region, multiplying a genuinely integrable complex field by the actual cutoff or its error preserves integrability, with both norms bounded pointwise by the original field norm. -/
theorem cutoff_data (C : Set Covector) {F : Covector → ℂ}
    (hF : IntegrableOn F C volume) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun x => profile ε x • F x) C volume ∧
    IntegrableOn (fun x => (profile ε x - 1) • F x) C volume ∧
    ∀ x, ‖profile ε x • F x‖ ≤ ‖F x‖ ∧
      ‖(profile ε x - 1) • F x‖ ≤ ‖F x‖ := by
  have hb (x : Covector) : ‖profile ε x‖ ≤ 1 ∧ ‖profile ε x - 1‖ ≤ 1 := by
    obtain ⟨hl, hu⟩ := (profile_spec h0 h1).2.2 x
    constructor
    · rwa [Real.norm_eq_abs, abs_of_nonneg hl]
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  have hm := (contDiff_profile h0 h1).continuous
  refine ⟨hF.bdd_smul 1 hm.aestronglyMeasurable
      (Eventually.of_forall fun x => (hb x).1),
    hF.bdd_smul 1 (hm.sub continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun x => (hb x).2), ?_⟩
  intro x
  constructor
  · rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hb x).1 (norm_nonneg _)).trans_eq (one_mul _)
  · rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hb x).2 (norm_nonneg _)).trans_eq (one_mul _)

/-- For any fixed genuinely integrable complex field, the actual cutoff error tends to zero in integral norm and the actual cutoff integral tends to the original integral through positive radii. -/
theorem cutoff_limits (C : Set Covector) {F : Covector → ℂ}
    (hF : IntegrableOn F C volume) :
    Tendsto (fun ε : ℝ => ∫ x in C, ‖(profile ε x - 1) • F x‖)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ x in C, profile ε x • F x)
      (𝓝[>] 0) (𝓝 (∫ x in C, F x)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  have haxis : ∀ᵐ x : Covector ∂volume.restrict C, ¬ (x 2 = 0 ∧ x 3 = 0) :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp axis_null)
  constructor
  · have H := tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ))
      (μ := volume.restrict C) (F := fun ε x => ‖(profile ε x - 1) • F x‖)
      (f := fun _ => (0 : ℝ)) (fun x => ‖F x‖) ?_ ?_ hF.norm ?_
    · simpa only [integral_zero] using H
    · filter_upwards [he] with ε hε
      exact (cutoff_data C hF hε.1 hε.2).2.1.norm.aestronglyMeasurable
    · filter_upwards [he] with ε hε
      exact Eventually.of_forall fun x => by
        simpa only [norm_norm] using ((cutoff_data C hF hε.1 hε.2).2.2 x).2
    · filter_upwards [haxis] with x hx
      apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
        (𝓝[>] 0) (𝓝 0)).congr'
      filter_upwards [eventually_profile_eq_one hx] with ε hε
      simp only [hε, sub_self, zero_smul, norm_zero]
  · apply tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict C) (fun x => ‖F x‖) ?_ ?_ hF.norm ?_
    · filter_upwards [he] with ε hε
      exact (cutoff_data C hF hε.1 hε.2).1.aestronglyMeasurable
    · filter_upwards [he] with ε hε
      exact Eventually.of_forall fun x => ((cutoff_data C hF hε.1 hε.2).2.2 x).1
    · filter_upwards [haxis] with x hx
      apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => F x)
        (𝓝[>] 0) (𝓝 (F x))).congr'
      filter_upwards [eventually_profile_eq_one hx] with ε hε
      simp only [hε, one_smul]

end FoliationQM.CoordinateCutoffL1Limit
