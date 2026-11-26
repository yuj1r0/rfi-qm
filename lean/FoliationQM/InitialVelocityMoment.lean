module

public import FoliationQM.ProbabilityTransportMoment
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Initial velocity moments from actual local Lipschitz bounds

Labels carry an actual probability, while an explicit position map takes values
in its own normed space. Genuine scalar error integrability follows from actual
velocity measurability and a position-error majorant. A uniform local Lipschitz
constant and a vanishing anchor mismatch then give velocity concentration.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.InitialVelocityMoment

open MeasureTheory Set Filter
open scoped Topology NNReal

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  {x0 : E} {v0 b0 : F} {L : ℝ}

/-- An actual measurable velocity and integrable position-error majorant give genuine velocity-error integrability before its moment bound. -/
theorem velocity_error_integrable_and_bound
    (μ : Measure α) [IsProbabilityMeasure μ] (X : α → E) (B : α → F)
    (hB : AEMeasurable B μ)
    (hx : Integrable (fun a => ‖X a - x0‖) μ)
    (hpoint : ∀ᵐ a ∂μ, ‖B a - v0‖ ≤ L * ‖X a - x0‖ + ‖b0 - v0‖) :
    Integrable (fun a => ‖B a - v0‖) μ ∧
      (∫ a, ‖B a - v0‖ ∂μ) ≤ L * (∫ a, ‖X a - x0‖ ∂μ) + ‖b0 - v0‖ := by
  have hc : Continuous (fun v : F => ‖v - v0‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hm : AEStronglyMeasurable (fun a => ‖B a - v0‖) μ :=
    (hc.measurable.comp_aemeasurable hB).aestronglyMeasurable
  have hmajor : Integrable (fun a => L * ‖X a - x0‖ + ‖b0 - v0‖) μ :=
    (hx.const_mul L).add (integrable_const _)
  have hi := hmajor.mono_nonneg hm (Eventually.of_forall fun a => norm_nonneg _) hpoint
  refine ⟨hi, (integral_mono_ae hi hmajor hpoint).trans_eq ?_⟩
  rw [integral_add (hx.const_mul L) (integrable_const _), integral_const_mul]
  simp

/-- Local Lipschitz control on a conull position region containing the anchor derives the true velocity moment bound. -/
theorem velocity_error_bound_of_lipschitzOn
    (μ : Measure α) [IsProbabilityMeasure μ] (X : α → E) (b : E → F) (L : ℝ≥0)
    {K : Set E} (hb : AEMeasurable (fun a => b (X a)) μ)
    (hx : Integrable (fun a => ‖X a - x0‖) μ)
    (hK : ∀ᵐ a ∂μ, X a ∈ K) (hx0 : x0 ∈ K) (hLip : LipschitzOnWith L b K) :
    Integrable (fun a => ‖b (X a) - v0‖) μ ∧
      (∫ a, ‖b (X a) - v0‖ ∂μ) ≤
        (L : ℝ) * (∫ a, ‖X a - x0‖ ∂μ) + ‖b x0 - v0‖ := by
  apply velocity_error_integrable_and_bound μ X (fun a => b (X a)) hb hx
  filter_upwards [hK] with a ha
  have hl : ‖b (X a) - b x0‖ ≤ (L : ℝ) * ‖X a - x0‖ := by
    simpa only [dist_eq_norm] using hLip.dist_le_mul (X a) ha x0 hx0
  have ht : ‖b (X a) - v0‖ ≤ ‖b (X a) - b x0‖ + ‖b x0 - v0‖ := by
    simpa only [dist_eq_norm] using dist_triangle (b (X a)) (b x0) v0
  exact ht.trans (add_le_add hl le_rfl)

/-- Uniform local Lipschitz control and the actual anchor limit turn genuine position moments into velocity-moment concentration along an explicit filter. -/
theorem family_velocity_moment_tendsto_of_lipschitzOn
    {ι : Type*} (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ι → α → E) (b : ι → E → F) (l : Filter ι) (L : ℝ≥0) {K : ι → Set E}
    (hGood : ∀ᶠ i in l,
      AEMeasurable (fun a => b i (X i a)) (μ i) ∧
      Integrable (fun a => ‖X i a - x0‖) (μ i) ∧
      (∀ᵐ a ∂μ i, X i a ∈ K i) ∧ x0 ∈ K i ∧ LipschitzOnWith L (b i) (K i))
    (hdx : Tendsto (fun i => ∫ a, ‖X i a - x0‖ ∂μ i) l (𝓝 0))
    (hanchor : Tendsto (fun i => ‖b i x0 - v0‖) l (𝓝 0)) :
    (∀ᶠ i in l, Integrable (fun a => ‖b i (X i a) - v0‖) (μ i)) ∧
      Tendsto (fun i => ∫ a, ‖b i (X i a) - v0‖ ∂μ i) l (𝓝 0) := by
  have hbound := hGood.mono fun i hi =>
    velocity_error_bound_of_lipschitzOn (v0 := v0) (μ i) (X i) (b i) L
      hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
  refine ⟨hbound.mono fun _ hi => hi.1, ?_⟩
  have hlim : Tendsto (fun i => (L : ℝ) * (∫ a, ‖X i a - x0‖ ∂μ i) +
      ‖b i x0 - v0‖) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hdx.const_mul (L : ℝ)).add hanchor
  exact squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun a => norm_nonneg _)
    (hbound.mono fun _ hi => hi.2) hlim

end FoliationQM.InitialVelocityMoment
