module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic

/-!
# Genuine pushforward first moments from integrable initial errors

Actual measurability certifies the pushforward. An integrable pointwise
majorant first proves transported error integrability, then its integral
bound. Finite-measure averaging retains the total mass of the constant
forcing term; the probability specialization gives the exact source formula.
No assertion of finite moments relies only on a totalized real integral.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ProbabilityTransportMoment

open MeasureTheory Set Filter

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure α} {X : α → E} {y : E} {a b : α → ℝ} {C T F : ℝ}

section Finite
variable [IsFiniteMeasure μ]

/-- A genuine measurable position map and an integrable error majorant imply integrability of the actual transported error on labels. -/
theorem integrable_error_of_bound (hX : AEMeasurable X μ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hbound : ∀ᵐ x ∂μ, ‖X x - y‖ ≤ C * (a x + T * b x + F)) :
    Integrable (fun x => ‖X x - y‖) μ := by
  have hc : Continuous (fun x : E => ‖x - y‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hm : AEStronglyMeasurable (fun x => ‖X x - y‖) μ :=
    (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable
  have hmajor : Integrable (fun x => C * (a x + T * b x + F)) μ :=
    ((ha.add (hb.const_mul T)).add (integrable_const F)).const_mul C
  exact hmajor.mono_nonneg hm (Eventually.of_forall fun x => norm_nonneg _) hbound

/-- Averaging the actual error bound over a finite measure retains the exact total-mass factor on its constant forcing term. -/
theorem averaged_error_bound (hX : AEMeasurable X μ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hbound : ∀ᵐ x ∂μ, ‖X x - y‖ ≤ C * (a x + T * b x + F)) :
    (∫ x, ‖X x - y‖ ∂μ) ≤
      C * ((∫ x, a x ∂μ) + T * (∫ x, b x ∂μ) + μ.real univ * F) := by
  have he := integrable_error_of_bound hX ha hb hbound
  have hmajor : Integrable (fun x => C * (a x + T * b x + F)) μ :=
    ((ha.add (hb.const_mul T)).add (integrable_const F)).const_mul C
  have H := integral_mono_ae he hmajor hbound
  have hsplit : (∫ x, a x + T * b x + F ∂μ) =
      (∫ x, a x + T * b x ∂μ) + ∫ _ : α, F ∂μ :=
    integral_add (ha.add (hb.const_mul T)) (integrable_const F)
  have hsplit' : (∫ x, a x + T * b x ∂μ) =
      (∫ x, a x ∂μ) + ∫ x, T * b x ∂μ := integral_add ha (hb.const_mul T)
  rw [integral_const_mul C, hsplit, hsplit', integral_const_mul T,
    integral_const, smul_eq_mul] at H
  exact H

end Finite

/-- Actual measurability transfers a proved label-error moment to the genuine pushforward measure. -/
theorem mapped_error_integrable (hX : AEMeasurable X μ)
    (he : Integrable (fun x => ‖X x - y‖) μ) :
    Integrable (fun x => ‖x - y‖) (μ.map X) := by
  have hc : Continuous (fun x : E => ‖x - y‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  exact (integrable_map_measure hc.aestronglyMeasurable hX).2 he

/-- The actual pushforward error integral equals its label integral, using explicit measurability of the flow map. -/
theorem mapped_error_integral (hX : AEMeasurable X μ) :
    (∫ x, ‖x - y‖ ∂μ.map X) = ∫ x, ‖X x - y‖ ∂μ := by
  have hc : Continuous (fun x : E => ‖x - y‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  exact integral_map hX hc.aestronglyMeasurable

section Probability
variable [IsProbabilityMeasure μ]

/-- Actual initial error integrability and a probability trajectory bound give a finite genuine pushforward first moment and its exact averaged estimate. -/
theorem mapped_moment_bound (hX : AEMeasurable X μ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hbound : ∀ᵐ x ∂μ, ‖X x - y‖ ≤ C * (a x + T * b x + F)) :
    Integrable (fun x => ‖x - y‖) (μ.map X) ∧
      (∫ x, ‖x - y‖ ∂μ.map X) ≤
        C * ((∫ x, a x ∂μ) + T * (∫ x, b x ∂μ) + F) := by
  refine ⟨mapped_error_integrable hX (integrable_error_of_bound hX ha hb hbound), ?_⟩
  rw [mapped_error_integral hX]
  simpa only [probReal_univ, one_mul] using averaged_error_bound hX ha hb hbound

end Probability

/-- For a finite measure, a genuine finite error moment around any fixed point implies a finite first norm moment about the origin. -/
theorem norm_integrable_of_error {ν : Measure E} [IsFiniteMeasure ν] {y : E}
    (he : Integrable (fun x => ‖x - y‖) ν) : Integrable (fun x : E => ‖x‖) ν := by
  apply (he.add (integrable_const ‖y‖)).mono_nonneg continuous_norm.aestronglyMeasurable
    (Eventually.of_forall fun x => norm_nonneg _)
  apply Eventually.of_forall
  intro x
  calc
    ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _

end FoliationQM.ProbabilityTransportMoment
