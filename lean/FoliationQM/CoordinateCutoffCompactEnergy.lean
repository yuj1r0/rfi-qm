module

public import FoliationQM.SmoothCoordinateTubeCutoff

/-!
# Cutoff derivative energy on fixed compact coordinate regions

Source: v13 `eq:log_cutoff_l2_bound`, using the cutoff from
`eq:log_cutoff_wallstrom`, component kinds C and D. The actual compact region determines its tangential projection;
its finite volume permits restriction of the constructed tube estimates.
This localization does not require a field to be square integrable on an
unbounded tube and does not assert general curved auxiliary-metric geometry.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffCompactEnergy

open Filter MeasureTheory Set ProductTubeCoordinates SmoothCoordinateTubeCutoff
open scoped Topology

/-- On every compact coordinate region the actual cutoff derivative is genuinely in L², its square norm is integrable, and its finite seminorm equals the square root of energy bounded by the constructed tangential-projection tube energy. -/
theorem compact_derivative_data (C : Set Covector) (hC : IsCompact C)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    MemLp (fderiv ℝ (profile ε)) 2 (volume.restrict C) ∧
    IntegrableOn (fun x : Covector => ‖fderiv ℝ (profile ε) x‖ ^ 2) C volume ∧
    (eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict C)).toReal =
      Real.sqrt (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) ∧
    0 ≤ (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) ∧
    (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) ≤
      ∫ x in tube ((fun y : Covector => (coordinates y).fst) '' C),
        ‖fderiv ℝ (profile ε) x‖ ^ 2 := by
  let K : Set ℂ := (fun y : Covector => (coordinates y).fst) '' C
  have hK : volume K ≠ ⊤ :=
    (hC.image ((WithLp.continuous_fst 2 ℂ ℂ).comp coordinates.continuous)).measure_ne_top
  have hsub : C ⊆ tube K := by
    intro x hx
    change (coordinates x).fst ∈ K
    exact ⟨x, hx, rfl⟩
  have hμ : volume.restrict C ≤ volume.restrict (tube K) :=
    Measure.restrict_mono_set volume hsub
  have H := derivative_l2_data K hK h0 h1
  have hlp : MemLp (fderiv ℝ (profile ε)) 2 (volume.restrict C) :=
    MemLp.mono_measure hμ H.1
  have hi := (memLp_two_iff_integrable_sq_norm hlp.aestronglyMeasurable).1 hlp
  have hn : eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict C) =
      ENNReal.ofReal (Real.sqrt (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2)) := by
    simpa [Real.sqrt_eq_rpow, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hlp
  refine ⟨hlp, hi, ?_, integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  · rw [hn, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  · exact integral_mono_measure hμ (Eventually.of_forall fun _ => sq_nonneg _) H.2.1

/-- On each fixed compact coordinate region both the genuine cutoff derivative energy and its finite standard L² seminorm vanish as the positive cutoff radius tends to zero. -/
theorem compact_derivative_decay (C : Set Covector) (hC : IsCompact C) :
    Tendsto (fun ε : ℝ => ∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ =>
      (eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict C)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  let K : Set ℂ := (fun y : Covector => (coordinates y).fst) '' C
  have hK : volume K ≠ ⊤ :=
    (hC.image ((WithLp.continuous_fst 2 ℂ ℂ).comp coordinates.continuous)).measure_ne_top
  have he : Tendsto (fun ε : ℝ => ∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg (fun _ => sq_nonneg _))
      ?_ (tendsto_energy_and_l2_norm K hK).1
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (compact_derivative_data C hC hε.1 hε.2).2.2.2.2
  refine ⟨he, ?_⟩
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  have hs0 : Tendsto (fun ε : ℝ => Real.sqrt
      (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using hs
  apply hs0.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (compact_derivative_data C hC hε.1 hε.2).2.2.1.symm

end FoliationQM.CoordinateCutoffCompactEnergy
