module

public import FoliationQM.ObserverOscillatingFactor
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform observer factors with a fixed positive Fisher trace

On the three-dimensional box (0,π] × (0,1] × (0,1], restrict the spatial
Lebesgue measure and keep the ambient smooth density and its spatial scores.
For the positive oscillating factors approaching one, the first directional
score contributes exactly 2π to the observed trace at every frequency.
This tests the spatial regularity needed in v13 Remark 5.2(a).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverOscillatingBox

open Set MeasureTheory Filter FisherNormalization LorentzCoordinates
open ObserverOscillatingFactor ObserverGaussianFisher
open scoped Topology

/-- The three upper endpoints of the spatial observation box. -/
def side (i : Fin 3) : ℝ := if i = 0 then Real.pi else 1

/-- The same spatial region is used for the entire sequence of multipliers. -/
def box : Set Spatial := univ.pi fun i => Ioc 0 (side i)

/-- The actual three-dimensional Lebesgue volume of the observation box is π. -/
theorem box_volume : volume box = ENNReal.ofReal Real.pi := by
  rw [box, volume_pi_pi]
  simp [side, Fin.prod_univ_three, Real.volume_Ioc]

private theorem integral_first (f : ℝ → ℝ) :
    (∫ y in box, f (y 0)) = ∫ u in Ioc 0 Real.pi, f u := by
  let μ : Fin 3 → Measure ℝ := fun i => volume.restrict (Ioc 0 (side i))
  let F : Fin 3 → ℝ → ℝ := fun i => if i = 0 then f else fun _ => 1
  have he := integral_fin_nat_prod_eq_prod (μ := μ) F
  change (∫ y : Spatial, f (y 0) ∂volume.restrict box) = _
  rw [box, volume_pi, Measure.restrict_pi_pi]
  change (∫ y : Spatial, f (y 0) ∂Measure.pi μ) = _
  have hu : (∫ _u in Ioc (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp [measureReal_def]
  simpa [F, μ, side, Fin.prod_univ_three, hu] using he

private theorem integral_cos_sq_first (n : ℕ) :
    (∫ u in Ioc 0 Real.pi, Real.cos (frequency n * u) ^ 2) = Real.pi / 2 := by
  have hf := (frequency_pos n).ne'
  have hs : Real.sin (frequency n * Real.pi) = 0 := by
    simpa [frequency] using Real.sin_nat_mul_pi (n + 2)
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_comp_mul_left (fun u => Real.cos u ^ 2) hf, mul_zero,
    integral_cos_sq, hs]
  simp only [Real.sin_zero, mul_zero, sub_zero, zero_add, smul_eq_mul]
  field_simp [hf]

/-- Each oscillatory trace is integrable for the restricted spatial volume. -/
theorem trace_integrable (n : ℕ) :
    Integrable (traceIntegrand (factor n) axes) (volume.restrict box) := by
  rw [funext (trace_eq n)]
  have hc : Continuous (fun y : Spatial => 4 * Real.cos (frequency n * y 0) ^ 2) := by fun_prop
  have hb : box ⊆ Icc (0 : Spatial) side := fun y hy =>
    ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2⟩
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hb

/-- On the fixed box the Fisher trace is exactly 2π at every frequency. -/
theorem trace_value (n : ℕ) : fisherTrace (factor n) axes (volume.restrict box) = 2 * Real.pi := by
  rw [fisherTrace, funext (trace_eq n), integral_const_mul,
    integral_first (fun u => Real.cos (frequency n * u) ^ 2), integral_cos_sq_first]
  ring

/-- The limiting constant density has zero spatial score and zero Fisher trace
with the same directions and restricted spatial volume. -/
theorem unit_trace : fisherTrace (fun _ : Spatial => 1) axes (volume.restrict box) = 0 := by
  simp [fisherTrace, traceIntegrand, score]

/-- Uniform convergence of the positive factors to one on all of space coexists
with failure of Fisher-trace convergence on this fixed finite-volume box. -/
theorem uniform_factor_fisher_counterexample :
    TendstoUniformly factor (fun _ : Spatial => 1) atTop ∧
    ¬ Tendsto (fun n => fisherTrace (factor n) axes (volume.restrict box)) atTop
      (𝓝 (fisherTrace (fun _ : Spatial => 1) axes (volume.restrict box))) := by
  refine ⟨uniform_to_one, ?_⟩
  intro h
  simp_rw [trace_value, unit_trace] at h
  have he := tendsto_nhds_unique h tendsto_const_nhds
  linarith [Real.pi_pos]

end FoliationQM.ObserverOscillatingBox
