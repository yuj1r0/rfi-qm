module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conserved weighted mass and genuine probability transport

An actual almost-everywhere measurable pushforward conserves extended total
mass. Positive finite initial mass gives genuine source and target probability
measures using the same initial normalization constant. The real-density
bridge requires actual integrability and nonnegativity before identifying
its extended mass with a finite real integral.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WeightedProbabilityTransport

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {ρ₀ : Measure α} {ρt : Measure β} {Φ : α → β}

/-- An actual measurable pushforward preserves total extended mass. -/
theorem mass_conserved (hf : AEMeasurable Φ ρ₀) (hmap : ρ₀.map Φ = ρt) :
    ρt univ = ρ₀ univ := by
  rw [← hmap, Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, preimage_univ]

/-- Genuine positive finite initial mass remains positive and finite under the actual pushforward. -/
theorem finite_positive_mass_conserved (hf : AEMeasurable Φ ρ₀)
    (hmap : ρ₀.map Φ = ρt) (hpos : 0 < ρ₀ univ) (hfin : ρ₀ univ < ∞) :
    0 < ρt univ ∧ ρt univ < ∞ := by
  rw [mass_conserved hf hmap]
  exact ⟨hpos, hfin⟩

/-- Actual integrability and nonnegativity identify the extended density mass with its real integral. -/
theorem withDensity_mass_eq_ofReal_integral (μ : Measure α) {D : α → ℝ}
    (hD : Integrable D μ) (hn : 0 ≤ᵐ[μ] D) :
    (μ.withDensity (fun x => ENNReal.ofReal (D x))) univ =
      ENNReal.ofReal (∫ x, D x ∂μ) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hD hn).symm

/-- A genuinely integrable nonnegative density with positive integral has positive finite extended mass. -/
theorem withDensity_finite_positive_mass (μ : Measure α) {D : α → ℝ}
    (hD : Integrable D μ) (hn : 0 ≤ᵐ[μ] D) (hpos : 0 < ∫ x, D x ∂μ) :
    0 < (μ.withDensity (fun x => ENNReal.ofReal (D x))) univ ∧
      (μ.withDensity (fun x => ENNReal.ofReal (D x))) univ < ∞ := by
  rw [withDensity_mass_eq_ofReal_integral μ hD hn]
  exact ⟨ENNReal.ofReal_pos.mpr hpos, ENNReal.ofReal_lt_top⟩

/-- Positive measure of the density's nonzero set gives positive finite mass when integrability is genuine. -/
theorem withDensity_finite_positive_mass_of_support (μ : Measure α) {D : α → ℝ}
    (hD : Integrable D μ) (hn : 0 ≤ᵐ[μ] D) (hsupp : 0 < μ (Function.support D)) :
    0 < (μ.withDensity (fun x => ENNReal.ofReal (D x))) univ ∧
      (μ.withDensity (fun x => ENNReal.ofReal (D x))) univ < ∞ :=
  withDensity_finite_positive_mass μ hD hn
    ((integral_pos_iff_support_of_nonneg_ae hn hD).mpr hsupp)

/-- Positive finite actual mass normalizes the source to a genuine probability. -/
theorem normalized_probability (hpos : 0 < ρ₀ univ) (hfin : ρ₀ univ < ∞) :
    IsProbabilityMeasure ((ρ₀ univ)⁻¹ • ρ₀) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-- The same initial mass normalizes the actual target to a genuine probability. -/
theorem normalized_target_probability (hf : AEMeasurable Φ ρ₀)
    (hmap : ρ₀.map Φ = ρt) (hpos : 0 < ρ₀ univ) (hfin : ρ₀ univ < ∞) :
    IsProbabilityMeasure ((ρ₀ univ)⁻¹ • ρt) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, mass_conserved hf hmap]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-- Actual map measurability passes to the source normalized by its initial mass. -/
theorem aemeasurable_normalized (hf : AEMeasurable Φ ρ₀) :
    AEMeasurable Φ ((ρ₀ univ)⁻¹ • ρ₀) :=
  hf.smul_measure ((ρ₀ univ)⁻¹)

/-- Scaling both actual measures by the same initial mass preserves their genuine pushforward identity. -/
theorem normalized_map (hf : AEMeasurable Φ ρ₀) (hmap : ρ₀.map Φ = ρt) :
    ((ρ₀ univ)⁻¹ • ρ₀).map Φ = (ρ₀ univ)⁻¹ • ρt := by
  rw [Measure.map_smul ((ρ₀ univ)⁻¹) hf, hmap]

/-- Positive finite initial mass yields both actual probabilities, actual map measurability and their normalized pushforward law. -/
theorem normalized_pushforward (hf : AEMeasurable Φ ρ₀) (hmap : ρ₀.map Φ = ρt)
    (hpos : 0 < ρ₀ univ) (hfin : ρ₀ univ < ∞) :
    IsProbabilityMeasure ((ρ₀ univ)⁻¹ • ρ₀) ∧
      IsProbabilityMeasure ((ρ₀ univ)⁻¹ • ρt) ∧
      AEMeasurable Φ ((ρ₀ univ)⁻¹ • ρ₀) ∧
      ((ρ₀ univ)⁻¹ • ρ₀).map Φ = (ρ₀ univ)⁻¹ • ρt :=
  ⟨normalized_probability hpos hfin,
    normalized_target_probability hf hmap hpos hfin,
    aemeasurable_normalized hf, normalized_map hf hmap⟩

end FoliationQM.WeightedProbabilityTransport
