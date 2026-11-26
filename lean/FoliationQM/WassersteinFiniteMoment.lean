module

public import FoliationQM.WassersteinCoupling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite transport cost from genuine first moments

Every coupling with the specified actual marginals has transport cost at
most the sum of their first moments around any fixed basepoint. Probability
product couplings then witness a finite extended transport infimum when
both first moments are finite. The bridge to real distance integrability
is proved before any conversion to real integral values.

These statements do not assert unproved general metric axioms for the
transport infimum. The normed corollaries use a fresh type whose metric
comes only from its normed additive group structure.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WassersteinFiniteMoment

open MeasureTheory Filter WassersteinCoupling
open scoped ENNReal

section Metric

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ ν : Measure E}

/-- The extended first distance moment about an arbitrary basepoint, retaining possible infinite mass and moment. -/
def moment (μ : Measure E) (z : E) : ℝ≥0∞ := ∫⁻ x, edist x z ∂μ

/-- Every genuine coupling has extended cost bounded by the two marginal moments about the same basepoint. -/
theorem cost_le_moments (π : Coupling μ ν) (z : E) :
    cost π ≤ moment μ z + moment ν z := by
  have hfst : (∫⁻ p : E × E, edist p.1 z ∂π.measure) = moment μ z := by
    rw [← lintegral_map measurable_edist_left measurable_fst, π.fst_marginal]
    rfl
  have hsnd : (∫⁻ p : E × E, edist p.2 z ∂π.measure) = moment ν z := by
    rw [← lintegral_map measurable_edist_left measurable_snd, π.snd_marginal]
    rfl
  calc
    cost π ≤ ∫⁻ p : E × E, edist p.1 z + edist p.2 z ∂π.measure := by
      apply lintegral_mono
      intro p
      simpa only [edist_comm z p.2] using edist_triangle p.1 z p.2
    _ = (∫⁻ p : E × E, edist p.1 z ∂π.measure) +
        ∫⁻ p : E × E, edist p.2 z ∂π.measure :=
      lintegral_add_left (measurable_edist_left.comp measurable_fst) _
    _ = moment μ z + moment ν z := by rw [hfst, hsnd]

/-- Finite marginal moments make the cost of every actual coupling finite, without assuming probability or finite total mass. -/
theorem cost_lt_top_of_moments (π : Coupling μ ν) {z : E}
    (hμ : moment μ z < ∞) (hν : moment ν z < ∞) : cost π < ∞ :=
  (cost_le_moments π z).trans_lt (ENNReal.add_lt_top.mpr ⟨hμ, hν⟩)

/-- Genuine probability product couplings bound the infimum over all couplings by the two marginal moments. -/
theorem eW1_le_moments (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (z : E) : eW1 μ ν ≤ moment μ z + moment ν z :=
  (eW1_le_cost (Coupling.prod μ ν)).trans (cost_le_moments (Coupling.prod μ ν) z)

/-- Finite marginal moments of actual probabilities imply finite extended transport cost; the product coupling witnesses nonemptiness of the infimum. -/
theorem eW1_lt_top_of_moments [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {z : E} (hμ : moment μ z < ∞) (hν : moment ν z < ∞) : eW1 μ ν < ∞ :=
  (eW1_le_moments μ ν z).trans_lt (ENNReal.add_lt_top.mpr ⟨hμ, hν⟩)

/-- An extended distance moment is finite exactly when the actual real distance function is integrable; distance measurability is derived from continuity. -/
theorem moment_lt_top_iff_integrable_dist (μ : Measure E) (z : E) :
    moment μ z < ∞ ↔ Integrable (fun x => dist x z) μ := by
  have hm : AEStronglyMeasurable (fun x : E => dist x z) μ :=
    (continuous_id.dist continuous_const).aestronglyMeasurable
  have hn : 0 ≤ᵐ[μ] fun x : E => dist x z := Eventually.of_forall fun _ => dist_nonneg
  constructor
  · intro h
    refine ⟨hm, (hasFiniteIntegral_iff_ofReal hn).2 ?_⟩
    simpa only [moment, edist_dist] using h
  · intro h
    simpa only [moment, edist_dist] using (hasFiniteIntegral_iff_ofReal hn).1 h.2

omit [BorelSpace E] in
/-- A proved integrable distance moment equals the nonnegative-real embedding of its actual integral; finiteness is not inferred from a totalized real value. -/
theorem moment_eq_ofReal_integral_dist (μ : Measure E) (z : E)
    (h : Integrable (fun x => dist x z) μ) :
    moment μ z = ENNReal.ofReal (∫ x, dist x z ∂μ) := by
  simpa only [moment, edist_dist] using
    (ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun _ => dist_nonneg)).symm

/-- Genuine integrability of both marginal distance functions gives finite extended transport cost for probabilities. -/
theorem eW1_lt_top_of_integrable_dist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {z : E} (hμ : Integrable (fun x => dist x z) μ)
    (hν : Integrable (fun x => dist x z) ν) : eW1 μ ν < ∞ :=
  eW1_lt_top_of_moments ((moment_lt_top_iff_integrable_dist μ z).2 hμ)
    ((moment_lt_top_iff_integrable_dist ν z).2 hν)

end Metric

section Normed

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  {μ ν : Measure F}

/-- With the metric supplied by the normed structure, the extended origin moment is finite exactly when the actual norm is integrable. -/
theorem moment_zero_lt_top_iff_integrable_norm (μ : Measure F) :
    moment μ 0 < ∞ ↔ Integrable (fun x : F => ‖x‖) μ := by
  simpa only [dist_zero_right] using moment_lt_top_iff_integrable_dist μ (0 : F)

/-- The genuine origin first moments already derived for transported probabilities imply finite extended transport cost in their actual norm metric. -/
theorem eW1_lt_top_of_integrable_norm [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : F => ‖x‖) μ)
    (hν : Integrable (fun x : F => ‖x‖) ν) : eW1 μ ν < ∞ :=
  eW1_lt_top_of_moments ((moment_zero_lt_top_iff_integrable_norm μ).2 hμ)
    ((moment_zero_lt_top_iff_integrable_norm ν).2 hν)

end Normed
end FoliationQM.WassersteinFiniteMoment
