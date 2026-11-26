module

public import FoliationQM.ObserverFisherTrace

/-!
# Stability of the integrated Fisher weight

In the slowly varying observer regime of v13 Remark 5.2(a), the
observed density multiplies the invariant density by a spatial factor.
A uniform deviation from one controls the change of the weight in the
finite score-square integrals. Derivatives of the factor enter separately
through its own score in the observed Fisher expansion.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverWeightStability

open MeasureTheory ObserverFisherTrace
open scoped BigOperators

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {g : E → ℝ} {δ : ℝ}

/-- A multiplier within δ of one preserves integrability of a nonnegative
baseline. Its signed change in integral has absolute value at most δ times
the original integral. -/
theorem weighted_integral_stability {k : E → ℝ}
    (hg : AEMeasurable g μ) (hδ : ∀ᵐ x ∂μ, |g x - 1| ≤ δ)
    (hkpos : ∀ᵐ x ∂μ, 0 ≤ k x) (hki : Integrable k μ) :
    Integrable (fun x => g x * k x) μ ∧
    |(∫ x, g x * k x ∂μ) - ∫ x, k x ∂μ| ≤ δ * ∫ x, k x ∂μ ∧
    (∫ x, g x * k x ∂μ) ≤ (1 + δ) * ∫ x, k x ∂μ := by
  have hi : Integrable (fun x => g x * k x) μ := by
    apply (hki.const_mul (1 + δ)).mono' ((hg.mul hki.aemeasurable).aestronglyMeasurable)
    filter_upwards [hδ, hkpos] with x hx hpos
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    apply mul_le_mul_of_nonneg_right _ hpos
    obtain ⟨h₁, h₂⟩ := abs_le.mp hx
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hupper := integral_mono_ae hi (hki.const_mul (1 + δ)) <| by
    filter_upwards [hδ, hkpos] with x hx hpos
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hx).2]) hpos
  have hlower := integral_mono_ae (hki.const_mul (1 - δ)) hi <| by
    filter_upwards [hδ, hkpos] with x hx hpos
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hx).1]) hpos
  rw [integral_const_mul] at hlower hupper
  exact ⟨hi, abs_le.mpr ⟨by linarith, by linarith⟩, hupper⟩

/-- A bounded change in observer weight preserves every finite directional
square integral and controls their sum by the baseline Fisher energy. -/
theorem squareEnergy_stability {ρ : E → ℝ} {n : ℕ} {a : Fin n → E → ℝ}
    (hg : AEMeasurable g μ) (hδ : ∀ᵐ x ∂μ, |g x - 1| ≤ δ)
    (hr : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hi : ∀ i, Integrable (fun x => ρ x * a i x ^ 2) μ) :
    (∀ i, Integrable (fun x => g x * ρ x * a i x ^ 2) μ) ∧
    |squareEnergy μ (fun x => g x * ρ x) a - squareEnergy μ ρ a| ≤ δ * squareEnergy μ ρ a ∧
    squareEnergy μ (fun x => g x * ρ x) a ≤ (1 + δ) * squareEnergy μ ρ a := by
  have he (i : Fin n) := weighted_integral_stability hg hδ
    (hr.mono fun x hx => mul_nonneg hx (sq_nonneg (a i x))) (hi i)
  simp only [← mul_assoc] at he
  refine ⟨fun i => (he i).1, ?_, ?_⟩
  · rw [squareEnergy, squareEnergy, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => (he i).2.1)
  · rw [squareEnergy, squareEnergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (he i).2.2

end FoliationQM.ObserverWeightStability
