module

public import FoliationQM.IntegralForceGronwall

/-!
# Integral Grönwall bounds derived from actual vector trajectories

The vector fundamental theorem of calculus gives an error integral inequality
from actual interior derivatives, endpoint continuity and an integrable
derivative. An almost-everywhere derivative bound is then integrated and fed
to the time-dependent forcing estimate. No derivative of the scalar norm is
assumed, and forcing is kept under its actual time integral.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntegralTrajectoryBound

open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual vector fundamental theorem of calculus bounds a trajectory by its initial norm and the integral of its derivative norm, with only interior derivative hypotheses. -/
theorem norm_le_initial_add_integral_norm {z z' : ℝ → E} {T : ℝ}
    (hc : ContinuousOn z (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt z (z' s) s)
    (hi : IntervalIntegrable z' volume 0 T) :
    ∀ t ∈ Icc 0 T, ‖z t‖ ≤ ‖z 0‖ + ∫ s in 0..t, ‖z' s‖ := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have huint : uIcc 0 t ⊆ uIcc 0 T := by
    simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono hsub) (fun s hs => hd s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
    (hi.mono_set huint)
  have he : z t = z 0 + ∫ s in 0..t, z' s := by
    rw [hFTC]
    abel
  calc
    ‖z t‖ = ‖z 0 + ∫ s in 0..t, z' s‖ := congrArg norm he
    _ ≤ ‖z 0‖ + ‖∫ s in 0..t, z' s‖ := norm_add_le _ _
    _ ≤ ‖z 0‖ + ∫ s in 0..t, ‖z' s‖ :=
      add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm ht.1)

/-- Integrating an almost-everywhere bound on the actual vector derivative gives the genuine trajectory integral inequality. -/
theorem integral_error_inequality {z z' : ℝ → E} {B : ℝ → ℝ} {T K : ℝ}
    (hc : ContinuousOn z (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt z (z' s) s)
    (hi : IntervalIntegrable z' volume 0 T)
    (hB : IntervalIntegrable B volume 0 T)
    (hae : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖z' s‖ ≤ K * ‖z s‖ + B s) :
    ∀ t ∈ Icc 0 T,
      ‖z t‖ ≤ ‖z 0‖ + K * (∫ s in 0..t, ‖z s‖) + ∫ s in 0..t, B s := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have huint : uIcc 0 t ⊆ uIcc 0 T := by
    simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using hsub
  have hz : IntervalIntegrable (fun s => ‖z s‖) volume 0 t :=
    (hc.norm.intervalIntegrable_of_Icc hT).mono_set huint
  have hb : IntervalIntegrable B volume 0 t := hB.mono_set huint
  have hmono := intervalIntegral.integral_mono_ae_restrict ht.1
    (hi.norm.mono_set huint) ((hz.const_mul K).add hb)
    (ae_restrict_of_ae_restrict_of_subset hsub hae)
  rw [intervalIntegral.integral_add (hz.const_mul K) hb,
    intervalIntegral.integral_const_mul] at hmono
  calc
    ‖z t‖ ≤ ‖z 0‖ + ∫ s in 0..t, ‖z' s‖ :=
      norm_le_initial_add_integral_norm hc hd hi t ht
    _ ≤ ‖z 0‖ + (K * (∫ s in 0..t, ‖z s‖) + ∫ s in 0..t, B s) :=
      add_le_add le_rfl hmono
    _ = _ := by ring

/-- An actual vector trajectory with an almost-everywhere linear derivative bound obeys Grönwall with the exact integrated forcing term. -/
theorem trajectory_bound {z z' : ℝ → E} {B : ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hc : ContinuousOn z (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt z (z' s) s)
    (hi : IntervalIntegrable z' volume 0 T)
    (hB : IntervalIntegrable B volume 0 T)
    (hBn : ∀ s ∈ Icc 0 T, 0 ≤ B s)
    (hae : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖z' s‖ ≤ K * ‖z s‖ + B s) :
    ∀ t ∈ Icc 0 T, ‖z t‖ ≤ Real.exp (K * T) * (‖z 0‖ + ∫ s in 0..T, B s) :=
  IntegralForceGronwall.error_bound hT hK (norm_nonneg _) hc.norm
    (fun _ _ => norm_nonneg _) hB hBn (integral_error_inequality hc hd hi hB hae)

end FoliationQM.IntegralTrajectoryBound
