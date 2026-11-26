module

public import FoliationQM.WassersteinCoupling
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Genuine transport cost to a Dirac measure

Every actual coupling to a Dirac measure has its second coordinate equal to
the Dirac point almost everywhere. Its cost therefore equals the actual
first moment of its first marginal. For probability measures an admissible
product coupling exists, so the infimum over all couplings has that same
value, including when the extended cost is infinite.

Real-valued identities below require actual integrability. Finiteness is
proved through equality with `ENNReal.ofReal` before exposing `toReal`.
No general metric structure or optimal-transport existence assertion is made.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WassersteinDirac

open WassersteinCoupling MeasureTheory Filter
open scoped ENNReal

section Metric

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {y : E}

/-- An actual coupling with a Dirac second marginal has that point as its second coordinate almost everywhere. -/
theorem snd_ae_eq (π : Coupling μ (Measure.dirac y)) :
    ∀ᵐ z ∂π.measure, z.2 = y := by
  apply ae_of_ae_map (μ := π.measure) (f := Prod.snd) (p := fun z : E => z = y)
    measurable_snd.aemeasurable
  rw [π.snd_marginal]
  simpa only [EventuallyEq, Function.const_apply, id_eq] using
    (ae_eq_dirac (a := y) (id : E → E))

/-- Every coupling to a Dirac measure has exactly the actual extended first-moment cost of its first marginal. -/
theorem cost_eq_dirac_moment (π : Coupling μ (Measure.dirac y)) :
    cost π = ∫⁻ x, edist x y ∂μ := by
  calc
    cost π = ∫⁻ z, edist z.1 y ∂π.measure :=
      lintegral_congr_ae ((snd_ae_eq π).mono fun _ h => by simp only [h])
    _ = ∫⁻ x, edist x y ∂π.measure.map Prod.fst :=
      (lintegral_map measurable_edist_left measurable_fst).symm
    _ = ∫⁻ x, edist x y ∂μ := by rw [π.fst_marginal]

/-- Actual integrability identifies every Dirac coupling cost with the embedded finite real distance moment. -/
theorem cost_eq_ofReal_integral (π : Coupling μ (Measure.dirac y))
    (h : Integrable (fun x => dist x y) μ) :
    cost π = ENNReal.ofReal (∫ x, dist x y ∂μ) := by
  rw [cost_eq_dirac_moment]
  simpa only [edist_dist] using
    (ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun _ => dist_nonneg)).symm

/-- Every coupling to a Dirac measure has finite cost when its actual first distance moment is integrable. -/
theorem cost_ne_top (π : Coupling μ (Measure.dirac y))
    (h : Integrable (fun x => dist x y) μ) : cost π ≠ ∞ := by
  rw [cost_eq_ofReal_integral π h]
  exact ENNReal.ofReal_ne_top

section Probability

variable [IsProbabilityMeasure μ]

/-- The genuine infimum over all probability couplings to a Dirac measure equals its extended first distance moment. -/
theorem eW1_dirac (μ : Measure E) [IsProbabilityMeasure μ] (y : E) :
    eW1 μ (Measure.dirac y) = ∫⁻ x, edist x y ∂μ := by
  apply le_antisymm
  · exact (eW1_le_cost (Coupling.prod μ (Measure.dirac y))).trans_eq
      (cost_eq_dirac_moment _)
  · apply le_iInf
    intro π
    exact (cost_eq_dirac_moment π).ge

/-- Actual distance integrability identifies the genuine Dirac transport infimum with the embedded finite real moment. -/
theorem eW1_dirac_eq_ofReal_integral (h : Integrable (fun x => dist x y) μ) :
    eW1 μ (Measure.dirac y) = ENNReal.ofReal (∫ x, dist x y ∂μ) := by
  rw [eW1_dirac]
  simpa only [edist_dist] using
    (ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun _ => dist_nonneg)).symm

/-- The genuine Dirac transport cost is finite because the actual distance moment is integrable. -/
theorem eW1_dirac_ne_top (h : Integrable (fun x => dist x y) μ) :
    eW1 μ (Measure.dirac y) ≠ ∞ := by
  rw [eW1_dirac_eq_ofReal_integral h]
  exact ENNReal.ofReal_ne_top

/-- After actual integrability proves finiteness, the real value of the genuine Dirac transport cost equals the real distance moment. -/
theorem eW1_dirac_toReal (h : Integrable (fun x => dist x y) μ) :
    (eW1 μ (Measure.dirac y)).toReal = ∫ x, dist x y ∂μ := by
  rw [eW1_dirac_eq_ofReal_integral h,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => dist_nonneg)]

/-- Finiteness and the exact real Dirac-cost identity are available together from the same genuine integrable moment. -/
theorem eW1_dirac_finite_and_toReal (h : Integrable (fun x => dist x y) μ) :
    eW1 μ (Measure.dirac y) ≠ ∞ ∧
      (eW1 μ (Measure.dirac y)).toReal = ∫ x, dist x y ∂μ :=
  ⟨eW1_dirac_ne_top h, eW1_dirac_toReal h⟩

end Probability
end Metric

section Normed

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [IsProbabilityMeasure μ] {y : F}

/-- In a normed space with its own induced metric, the finite real Dirac transport cost is the actual norm-error moment. -/
theorem eW1_dirac_toReal_norm (h : Integrable (fun x => ‖x - y‖) μ) :
    (eW1 μ (Measure.dirac y)).toReal = ∫ x, ‖x - y‖ ∂μ := by
  simpa only [dist_eq_norm] using
    eW1_dirac_toReal (μ := μ) (y := y) (by simpa only [dist_eq_norm] using h)

/-- A genuine integrable norm-error moment supplies both finite transport cost and its exact real value, using the norm-induced metric throughout. -/
theorem eW1_dirac_finite_and_toReal_norm (h : Integrable (fun x => ‖x - y‖) μ) :
    eW1 μ (Measure.dirac y) ≠ ∞ ∧
      (eW1 μ (Measure.dirac y)).toReal = ∫ x, ‖x - y‖ ∂μ := by
  simpa only [dist_eq_norm] using
    eW1_dirac_finite_and_toReal (μ := μ) (y := y)
      (by simpa only [dist_eq_norm] using h)

end Normed
end FoliationQM.WassersteinDirac
