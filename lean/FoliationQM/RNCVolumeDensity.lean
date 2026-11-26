module

public import FoliationQM.LorentzMatrixGroup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The coordinate volume and metric half-density

In Lemma 9.1 the metric determinant multiplies the coordinate measure by
its positive square root. Multiplying a scalar amplitude by the positive
fourth root gives the same measure on every measurable region.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCVolumeDensity

open LorentzMatrixGroup MeasureTheory

/-- The coordinate volume factor of the Lorentz metric. -/
def volumeFactor (G : Mat4) : ℝ := Real.sqrt (-G.det)

/-- The metric multiplier of the scalar amplitude in the normal-coordinate prescription. -/
def metricWeight (G : Mat4) : ℝ := Real.sqrt (volumeFactor G)

/-- On the Lorentzian determinant domain the weight is the positive real fourth root. -/
theorem weight_eq_rpow {G : Mat4} (h : G.det ≤ 0) :
    metricWeight G = (-G.det) ^ (1 / 4 : ℝ) := by
  rw [metricWeight, volumeFactor, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (neg_nonneg.mpr h)]
  norm_num

/-- A negative metric determinant gives a strictly positive weight. -/
theorem weight_pos {G : Mat4} (h : G.det < 0) : 0 < metricWeight G :=
  Real.sqrt_pos.2 (Real.sqrt_pos.2 (neg_pos.mpr h))

/-- The square of the metric half-density equals the coordinate volume factor. -/
theorem weight_sq (G : Mat4) : (metricWeight G) ^ 2 = volumeFactor G :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

/-- The squared weighted amplitude is the probability density relative to coordinate volume. -/
theorem amplitude_sq (G : Mat4) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (metricWeight G * Real.sqrt ρ) ^ 2 = volumeFactor G * ρ := by
  rw [mul_pow, weight_sq, Real.sq_sqrt hρ]

/-- Minkowski normalization fixes the coordinate volume factor and the metric weight at one. -/
theorem center_values : volumeFactor eta = 1 ∧ metricWeight eta = 1 := by
  simp [metricWeight, volumeFactor, eta_det]

/-- Weighting a coordinate measure by the squared half-density gives the same measure
as weighting metric volume by the scalar density. Almost-everywhere nonnegativity suffices. -/
theorem amplitude_measure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → Mat4) (ρ : X → ℝ)
    (hg : AEMeasurable (fun x => ENNReal.ofReal (volumeFactor (g x))) μ)
    (hρ : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ ρ x) :
    μ.withDensity (fun x => ENNReal.ofReal ((metricWeight (g x) * Real.sqrt (ρ x)) ^ 2)) =
      (μ.withDensity (fun x => ENNReal.ofReal (volumeFactor (g x)))).withDensity
        (fun x => ENNReal.ofReal (ρ x)) := by
  rw [← withDensity_mul₀ hg hρ]
  apply withDensity_congr_ae
  filter_upwards [hpos] with x hx
  simp only [Pi.mul_apply, amplitude_sq (g x) hx]
  exact ENNReal.ofReal_mul (show 0 ≤ volumeFactor (g x) from Real.sqrt_nonneg _)

end FoliationQM.RNCVolumeDensity
