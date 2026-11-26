module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Exact coordinate and Euclidean density measures

Source: v13 `cor:macroscopic_geodesics`. The canonical coordinate-to-Euclidean
map preserves the actual volume measure. Restriction, density and scalar
normalization therefore transfer exactly, and actual measurable flow maps
compose with this realization.

The real-density formulas use their nonnegative parts. Actual current
positivity and finite positive normalization belong to the physical layer;
the measure identities here do not assert probability at zero or infinite mass.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EuclideanDensityTransport

open MeasureTheory Set
open scoped ENNReal

section Equivalence

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A measurable equivalence transports an actual density measure without requiring a globally measurable density. -/
theorem map_withDensity_equiv (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map μ s, lintegral_map_equiv]
  simp only [e.symm_apply_apply]

/-- The actual restriction transports to the image under a measurable equivalence. -/
theorem map_restrict_equiv (e : α ≃ᵐ β) (μ : Measure α) (S : Set α) :
    (μ.restrict S).map e = (μ.map e).restrict (e '' S) := by
  rw [e.restrict_map μ (e '' S), preimage_image_eq S e.injective]

end Equivalence

section Coordinates

variable {n : ℕ}

/-- The canonical map to Euclidean space preserves the actual restricted coordinate volume. -/
theorem map_restrict_volume_toLp (S : Set (Fin n → ℝ)) :
    ((volume : Measure (Fin n → ℝ)).restrict S).map (WithLp.toLp 2) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (WithLp.toLp 2 '' S) := by
  have h := map_restrict_equiv (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    (volume : Measure (Fin n → ℝ)) S
  simpa only [MeasurableEquiv.coe_toLp, (PiLp.volume_preserving_toLp (Fin n)).map_eq] using h

/-- The coordinate density becomes the literal density with respect to canonical Euclidean volume. -/
theorem map_coordinate_density_toLp (S : Set (Fin n → ℝ)) (D : (Fin n → ℝ) → ℝ) :
    (((volume : Measure (Fin n → ℝ)).restrict S).withDensity
      (fun x => ENNReal.ofReal (D x))).map (WithLp.toLp 2) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (WithLp.toLp 2 '' S)).withDensity
        (fun y => ENNReal.ofReal (D (WithLp.ofLp y))) := by
  have h := map_withDensity_equiv (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    ((volume : Measure (Fin n → ℝ)).restrict S) (fun x => ENNReal.ofReal (D x))
  simpa only [MeasurableEquiv.coe_toLp, MeasurableEquiv.coe_toLp_symm,
    map_restrict_volume_toLp] using h

/-- The same initial mass scalar normalizes both exact volume realizations. -/
theorem map_normalized_coordinate_density_toLp (Z : ℝ≥0∞)
    (S : Set (Fin n → ℝ)) (D : (Fin n → ℝ) → ℝ) :
    (Z⁻¹ • ((volume : Measure (Fin n → ℝ)).restrict S).withDensity
      (fun x => ENNReal.ofReal (D x))).map (WithLp.toLp 2) =
      Z⁻¹ • ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (WithLp.toLp 2 '' S)).withDensity (fun y => ENNReal.ofReal (D (WithLp.ofLp y))) := by
  rw [Measure.map_smul Z⁻¹ (PiLp.volume_preserving_toLp (Fin n)).measurable.aemeasurable,
    map_coordinate_density_toLp]

section Flow

variable {α : Type*} [MeasurableSpace α]
  {μ μ₀ : Measure α} {μt : Measure (Fin n → ℝ)} {Phi : α → (Fin n → ℝ)}

/-- Actual flow measurability gives actual measurability of its Euclidean realization. -/
theorem aemeasurable_toLp_after_flow (hPhi : AEMeasurable Phi μ) :
    AEMeasurable (fun a => WithLp.toLp 2 (Phi a)) μ :=
  (PiLp.volume_preserving_toLp (Fin n)).measurable.comp_aemeasurable hPhi

/-- A proved coordinate pushforward composes with the exact Euclidean realization using actual map measurability. -/
theorem map_toLp_after_pushforward (hPhi : AEMeasurable Phi μ₀)
    (hmap : μ₀.map Phi = μt) :
    μ₀.map (fun a => WithLp.toLp 2 (Phi a)) = μt.map (WithLp.toLp 2) := by
  rw [← hmap]
  exact (AEMeasurable.map_map_of_aemeasurable
    (PiLp.volume_preserving_toLp (Fin n)).measurable.aemeasurable hPhi).symm

end Flow
end Coordinates
end FoliationQM.EuclideanDensityTransport
