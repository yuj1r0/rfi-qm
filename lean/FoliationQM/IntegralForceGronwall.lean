module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic

/-!
# Grönwall with the actual integrated forcing

A continuous nonnegative error satisfying its trajectory integral inequality
is bounded by exp(KT) times its initial error plus the actual force integral.
The forcing need only be interval integrable and nonnegative on the interval.
The proof uses a differentiable majorant built from the continuous error;
it neither differentiates the error norm nor replaces forcing by a supremum.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntegralForceGronwall

open Set Filter MeasureTheory
open scoped Topology

/-- The integral of a nonnegative forcing up to any intermediate time is bounded by its full time integral. -/
theorem forcing_integral_le {B : ℝ → ℝ} {T t : ℝ}
    (hB : IntervalIntegrable B volume 0 T)
    (hn : ∀ s ∈ Icc 0 T, 0 ≤ B s) (ht : t ∈ Icc 0 T) :
    (∫ s in 0..t, B s) ≤ ∫ s in 0..T, B s := by
  apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hn s ⟨hs.1.le, hs.2⟩
  · exact hB

/-- A continuous error with an actual integral inequality obeys Grönwall with a time-integrated, merely integrable forcing term. -/
theorem continuous_error_bound {D B : ℝ → ℝ} {T K δ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hD : Continuous D) (hDn : ∀ s ∈ Icc 0 T, 0 ≤ D s)
    (hB : IntervalIntegrable B volume 0 T) (hBn : ∀ s ∈ Icc 0 T, 0 ≤ B s)
    (hineq : ∀ s ∈ Icc 0 T,
      D s ≤ δ + K * (∫ r in 0..s, D r) + ∫ r in 0..s, B r) :
    ∀ t ∈ Icc 0 T, D t ≤ Real.exp (K * T) * (δ + ∫ s in 0..T, B s) := by
  let C : ℝ := δ + ∫ s in 0..T, B s
  let H : ℝ → ℝ := fun s => C + K * ∫ r in 0..s, D r
  have hC : 0 ≤ C := add_nonneg hδ (intervalIntegral.integral_nonneg hT hBn)
  have hHder (s : ℝ) : HasDerivAt H (K * D s) s := by
    have hd := intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable 0 s)
      hD.aestronglyMeasurable.stronglyMeasurableAtFilter (hD.continuousAt (x := s))
    exact (hd.const_mul K).const_add C
  have hHcont : Continuous H := continuous_iff_continuousAt.mpr fun s => (hHder s).continuousAt
  have hDH : ∀ s ∈ Icc 0 T, D s ≤ H s := by
    intro s hs
    have hb := forcing_integral_le hB hBn hs
    have hd := hineq s hs
    dsimp [H, C]
    linarith
  have hHn : ∀ s ∈ Icc 0 T, 0 ≤ H s := fun s hs => (hDn s hs).trans (hDH s hs)
  have hb : ∀ s ∈ Ico 0 T, ‖K * D s‖ ≤ K * ‖H s‖ + 0 := by
    intro s hs
    have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.le⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (hDn s hs')),
      abs_of_nonneg (hHn s hs'), add_zero]
    exact mul_le_mul_of_nonneg_left (hDH s hs') hK
  have hinit : ‖H 0‖ ≤ C := by
    simp only [H, intervalIntegral.integral_same, mul_zero, add_zero,
      Real.norm_eq_abs, abs_of_nonneg hC, le_refl]
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le hHcont.continuousOn
    (fun s _ => (hHder s).hasDerivWithinAt) hinit hb
  intro t ht
  have hh := hG t ht
  rw [gronwallBound_ε0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hHn t ht)] at hh
  calc
    D t ≤ H t := hDH t ht
    _ ≤ C * Real.exp (K * t) := hh
    _ ≤ C * Real.exp (K * T) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)) hC
    _ = _ := by dsimp [C]; ring

/-- Grönwall needs error continuity only on the physical time interval; a continuous clamped extension supplies the auxiliary primitive without changing any interval value or integral. -/
theorem error_bound {D B : ℝ → ℝ} {T K δ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hD : ContinuousOn D (Icc 0 T)) (hDn : ∀ s ∈ Icc 0 T, 0 ≤ D s)
    (hB : IntervalIntegrable B volume 0 T) (hBn : ∀ s ∈ Icc 0 T, 0 ≤ B s)
    (hineq : ∀ s ∈ Icc 0 T,
      D s ≤ δ + K * (∫ r in 0..s, D r) + ∫ r in 0..s, B r) :
    ∀ t ∈ Icc 0 T, D t ≤ Real.exp (K * T) * (δ + ∫ s in 0..T, B s) := by
  let E : ℝ → ℝ := fun s => D (projIcc 0 T hT s)
  have hEc : Continuous E := (continuousOn_iff_continuous_domRestrict.mp hD).comp continuous_projIcc
  have he : ∀ s ∈ Icc 0 T, E s = D s := by
    intro s hs
    simp only [E, projIcc_of_mem hT hs]
  have hei : ∀ s ∈ Icc 0 T, (∫ r in 0..s, E r) = ∫ r in 0..s, D r := by
    intro s hs
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.1] at hr
    exact he r ⟨hr.1, hr.2.trans hs.2⟩
  have H := continuous_error_bound hT hK hδ hEc
    (fun s hs => by rw [he s hs]; exact hDn s hs) hB hBn
    (fun s hs => by rw [he s hs, hei s hs]; exact hineq s hs)
  intro t ht
  simpa only [he t ht] using H t ht

/-- A fixed nonnegative time weight multiplies the actual force integral, giving the form needed for the weighted position-velocity error. -/
theorem weighted_error_bound {D A : ℝ → ℝ} {T K δ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hD : ContinuousOn D (Icc 0 T)) (hDn : ∀ s ∈ Icc 0 T, 0 ≤ D s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hineq : ∀ s ∈ Icc 0 T,
      D s ≤ δ + K * (∫ r in 0..s, D r) + T * ∫ r in 0..s, A r) :
    ∀ t ∈ Icc 0 T, D t ≤ Real.exp (K * T) * (δ + T * ∫ s in 0..T, A s) := by
  have H := error_bound hT hK hδ hD hDn (hA.const_mul T)
    (fun s hs => mul_nonneg hT (hAn s hs))
    (fun s hs => by simpa only [intervalIntegral.integral_const_mul] using hineq s hs)
  simpa only [intervalIntegral.integral_const_mul] using H

end FoliationQM.IntegralForceGronwall
