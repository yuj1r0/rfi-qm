module

public import FoliationQM.CoordinateCutoffCompactEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Genuine localized cutoff-error estimates

Source: v13 `eq:log_cutoff_l2_bound` and its following first-derivative
commutator argument, component kinds C and D. The field is square integrable
only on the fixed compact region. The pairing uses the constructed cutoff's
actual derivative; no error bound or vanishing limit is assumed.
The metric-weighted PDE contraction and general curved geometry remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffPairing

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff CoordinateCutoffCompactEnergy
open scoped Topology

/-- On each fixed compact region the actual directional cutoff error and its norm are integrable, and its integral is controlled by the genuine cutoff and field energies through the localized Cauchy–Schwarz inequality. -/
theorem pairing_data (C : Set Covector) (hC : IsCompact C)
    {F : Covector → ℂ} (hF : MemLp F 2 (volume.restrict C))
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (v : Covector) :
    IntegrableOn (fun x => (fderiv ℝ (profile ε) x v) • F x) C volume ∧
    IntegrableOn (fun x => ‖(fderiv ℝ (profile ε) x v) • F x‖) C volume ∧
    ‖∫ x in C, (fderiv ℝ (profile ε) x v) • F x‖ ≤
      ∫ x in C, ‖(fderiv ℝ (profile ε) x v) • F x‖ ∧
    (∫ x in C, ‖(fderiv ℝ (profile ε) x v) • F x‖) ≤
      ‖v‖ * Real.sqrt (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
        Real.sqrt (∫ x in C, ‖F x‖ ^ 2) := by
  have hd := (compact_derivative_data C hC h0 h1).1
  have hv : MemLp (fun x => fderiv ℝ (profile ε) x v) 2 (volume.restrict C) :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp_memLp' hd
  have he : IntegrableOn (fun x => (fderiv ℝ (profile ε) x v) • F x) C volume :=
    memLp_one_iff_integrable.1 (hv.smul hF)
  have hm : IntegrableOn (fun x => ‖fderiv ℝ (profile ε) x‖ * ‖F x‖) C volume :=
    hd.norm.integrable_mul hF.norm
  have hholder : (∫ x in C, ‖fderiv ℝ (profile ε) x‖ * ‖F x‖) ≤
      Real.sqrt (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
        Real.sqrt (∫ x in C, ‖F x‖ ^ 2) := by
    have H := integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict C)
      Real.HolderConjugate.two_two
      (show MemLp (fun x => ‖fderiv ℝ (profile ε) x‖) (ENNReal.ofReal 2)
        (volume.restrict C) by simpa using hd.norm)
      (show MemLp (fun x => ‖F x‖) (ENNReal.ofReal 2)
        (volume.restrict C) by simpa using hF.norm)
    simpa only [norm_norm, Real.rpow_two, ← Real.sqrt_eq_rpow] using H
  refine ⟨he, he.norm, norm_integral_le_integral_norm _, ?_⟩
  calc
    (∫ x in C, ‖(fderiv ℝ (profile ε) x v) • F x‖) ≤
        ∫ x in C, ‖v‖ * (‖fderiv ℝ (profile ε) x‖ * ‖F x‖) := by
      apply integral_mono he.norm (hm.const_mul ‖v‖)
      intro x
      dsimp only
      rw [norm_smul]
      calc
        ‖fderiv ℝ (profile ε) x v‖ * ‖F x‖ ≤
            (‖fderiv ℝ (profile ε) x‖ * ‖v‖) * ‖F x‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (profile ε) x).le_opNorm v)
            (norm_nonneg _)
        _ = ‖v‖ * (‖fderiv ℝ (profile ε) x‖ * ‖F x‖) := by ring
    _ = ‖v‖ * (∫ x in C, ‖fderiv ℝ (profile ε) x‖ * ‖F x‖) :=
      integral_const_mul _ _
    _ ≤ ‖v‖ * (Real.sqrt (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
        Real.sqrt (∫ x in C, ‖F x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hholder (norm_nonneg _)
    _ = _ := by ring

/-- For every fixed locally square-integrable field and direction, the integral of the actual cutoff-error norm and the actual complex error integral both vanish on the same fixed compact region as the positive cutoff radius tends to zero. -/
theorem pairing_decay (C : Set Covector) (hC : IsCompact C)
    {F : Covector → ℂ} (hF : MemLp F 2 (volume.restrict C)) (v : Covector) :
    Tendsto (fun ε : ℝ => ∫ x in C, ‖(fderiv ℝ (profile ε) x v) • F x‖)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ x in C, (fderiv ℝ (profile ε) x v) • F x)
      (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (fun ε : ℝ => Real.sqrt
      (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (compact_derivative_decay C hC).1
  have hb : Tendsto (fun ε : ℝ =>
      ‖v‖ * Real.sqrt (∫ x in C, ‖fderiv ℝ (profile ε) x‖ ^ 2) *
        Real.sqrt (∫ x in C, ‖F x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hs).mul_const
      (Real.sqrt (∫ x in C, ‖F x‖ ^ 2))
  have hi : Tendsto (fun ε : ℝ => ∫ x in C, ‖(fderiv ℝ (profile ε) x v) • F x‖)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _)
      ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (pairing_data C hC hF hε.1 hε.2 v).2.2.2
  refine ⟨hi, tendsto_zero_iff_norm_tendsto_zero.2 ?_⟩
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_integral_le_integral_norm _) hi

end FoliationQM.CoordinateCutoffPairing
