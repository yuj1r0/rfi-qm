module

public import FoliationQM.UniformWeakConcentration
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Genuine good and bad label restrictions

Actual measurable maps preserve the label restriction decomposition and its
masses. Centering bounded tests keeps the missing reference mass explicit.
Good first moments and bad mass then give quantitative test errors, without
requiring any bad first moment or identifying a bad-label image with a target
set complement.

Source: v13 `rem:wkb_rates_tails` (Kinds C/D).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GoodBadTransport

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {α E : Type*} [MeasurableSpace α]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {S : Set α} {X : α → E}

omit [MetricSpace E] [BorelSpace E] in
/-- A genuine measurable pushforward splits over the good and bad label restrictions. -/
theorem map_restrict_add_compl (μ : Measure α) (hs : MeasurableSet S)
    (hX : AEMeasurable X μ) :
    μ.map X = (μ.restrict S).map X + (μ.restrict Sᶜ).map X := by
  simpa only [Measure.restrict_add_restrict_compl hs] using
    (hX.restrict (s := S)).map_add₀ (hX.restrict (s := Sᶜ))

omit [MetricSpace E] [BorelSpace E] in
/-- The actual mapped restriction has exactly the original label mass. -/
theorem mapped_restriction_mass (μ : Measure α) (S : Set α)
    (hX : AEMeasurable X μ) : ((μ.restrict S).map X) univ = μ S := by
  rw [Measure.map_apply_of_aemeasurable hX.restrict MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

section Finite

variable (μ : Measure α) [IsFiniteMeasure μ]

/-- An actual measurable map pulls each bounded continuous test back to a genuinely integrable label function. -/
theorem test_integrable_labels (hX : AEMeasurable X μ) (f : E →ᵇ ℝ) :
    Integrable (fun a => f (X a)) μ := by
  simpa only [Function.comp_def] using (f.integrable (μ.map X)).comp_aemeasurable hX

/-- Centered bounded tests are genuinely integrable on finite label measures. -/
theorem centered_test_integrable (hX : AEMeasurable X μ) (f : E →ᵇ ℝ) (y : E) :
    Integrable (fun a => f (X a) - f y) μ :=
  (test_integrable_labels μ hX f).sub (integrable_const _)

/-- A centered restriction retains its exact reference mass under the genuine mapped measure. -/
theorem restricted_centered_test_eq (S : Set α) (hX : AEMeasurable X μ)
    (f : E →ᵇ ℝ) (y : E) :
    (∫ a, f (X a) - f y ∂μ.restrict S) =
      (∫ x, f x ∂(μ.restrict S).map X) - μ.real S * f y := by
  rw [integral_sub (test_integrable_labels (μ.restrict S) hX.restrict f)
    (integrable_const _), integral_map hX.restrict f.continuous.aestronglyMeasurable,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul]

/-- Bad labels contribute at most twice the test norm times their actual mass, without a bad distance moment. -/
theorem bad_test_error_le (S : Set α) (hX : AEMeasurable X μ) (f : E →ᵇ ℝ) (y : E) :
    |∫ a, f (X a) - f y ∂μ.restrict Sᶜ| ≤ 2 * ‖f‖ * μ.real Sᶜ := by
  have hi := centered_test_integrable (μ.restrict Sᶜ) hX.restrict f y
  calc
    |∫ a, f (X a) - f y ∂μ.restrict Sᶜ| =
        ‖∫ a, f (X a) - f y ∂μ.restrict Sᶜ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ a, ‖f (X a) - f y‖ ∂μ.restrict Sᶜ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : α, 2 * ‖f‖ ∂μ.restrict Sᶜ := by
      apply integral_mono_ae hi.norm (integrable_const _)
      exact Eventually.of_forall fun a => by
        simpa only [Real.norm_eq_abs, Real.dist_eq] using f.dist_le_two_norm (X a) y
    _ = 2 * ‖f‖ * μ.real Sᶜ := by
      rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]

/-- An affine distance majorant controls the good centered test with the exact good mass factor. -/
theorem good_affine_test_error_le (S : Set α) (hX : AEMeasurable X μ)
    (f : E →ᵇ ℝ) (y : E)
    (hGoodInt : Integrable (fun a => dist (X a) y) (μ.restrict S)) {η C : ℝ}
    (hpoint : ∀ x, |f x - f y| ≤ η + C * dist x y) :
    |∫ a, f (X a) - f y ∂μ.restrict S| ≤
      η * μ.real S + C * (∫ a, dist (X a) y ∂μ.restrict S) := by
  have hi := centered_test_integrable (μ.restrict S) hX.restrict f y
  have hmajor : Integrable (fun a => η + C * dist (X a) y) (μ.restrict S) :=
    (integrable_const η).add (hGoodInt.const_mul C)
  calc
    |∫ a, f (X a) - f y ∂μ.restrict S| =
        ‖∫ a, f (X a) - f y ∂μ.restrict S‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ a, ‖f (X a) - f y‖ ∂μ.restrict S := norm_integral_le_integral_norm _
    _ ≤ ∫ a, η + C * dist (X a) y ∂μ.restrict S := by
      apply integral_mono_ae hi.norm hmajor
      exact Eventually.of_forall fun a => by
        simpa only [Real.norm_eq_abs] using hpoint (X a)
    _ = η * μ.real S + C * (∫ a, dist (X a) y ∂μ.restrict S) := by
      rw [integral_add (integrable_const η) (hGoodInt.const_mul C),
        integral_const, measureReal_restrict_apply_univ, smul_eq_mul, integral_const_mul]
      rw [mul_comm (μ.real S) η]

end Finite

section Probability

variable (μ : Measure α) [IsProbabilityMeasure μ]

/-- Centering before splitting preserves the full reference mass across the two label restrictions. -/
theorem centered_test_split (hs : MeasurableSet S) (hX : AEMeasurable X μ)
    (f : E →ᵇ ℝ) (y : E) :
    (∫ x, f x ∂μ.map X) - f y =
      (∫ a, f (X a) - f y ∂μ.restrict S) +
      (∫ a, f (X a) - f y ∂μ.restrict Sᶜ) := by
  rw [integral_map hX f.continuous.aestronglyMeasurable]
  have hc : (∫ a, f (X a) - f y ∂μ) = (∫ a, f (X a) ∂μ) - f y := by
    rw [integral_sub (test_integrable_labels μ hX f) (integrable_const _)]
    simp
  rw [← hc]
  exact (integral_add_compl hs (centered_test_integrable μ hX f y)).symm

/-- The expanded centered split displays both exact reference masses under the actual mapped restrictions. -/
theorem centered_test_split_with_masses (hs : MeasurableSet S) (hX : AEMeasurable X μ)
    (f : E →ᵇ ℝ) (y : E) :
    (∫ x, f x ∂μ.map X) - f y =
      ((∫ x, f x ∂(μ.restrict S).map X) - μ.real S * f y) +
      ((∫ x, f x ∂(μ.restrict Sᶜ).map X) - μ.real Sᶜ * f y) := by
  rw [centered_test_split μ hs hX f y,
    restricted_centered_test_eq μ S hX f y, restricted_centered_test_eq μ Sᶜ hX f y]

/-- Actual good first moments and bad mass control a bounded test through any proved affine distance majorant. -/
theorem test_error_le_good_affine (hs : MeasurableSet S) (hX : AEMeasurable X μ)
    (f : E →ᵇ ℝ) (y : E)
    (hGoodInt : Integrable (fun a => dist (X a) y) (μ.restrict S)) {η C : ℝ}
    (hpoint : ∀ x, |f x - f y| ≤ η + C * dist x y) :
    |(∫ x, f x ∂μ.map X) - f y| ≤
      η * μ.real S + C * (∫ a, dist (X a) y ∂μ.restrict S) +
        2 * ‖f‖ * μ.real Sᶜ := by
  rw [centered_test_split μ hs hX f y]
  exact (abs_add_le _ _).trans (add_le_add
    (good_affine_test_error_le μ S hX f y hGoodInt hpoint)
    (bad_test_error_le μ S hX f y))

/-- A bounded Lipschitz test has the exact good-moment error plus twice its norm times bad mass. -/
theorem test_error_le_good_lipschitz (hs : MeasurableSet S) (hX : AEMeasurable X μ)
    (f : E →ᵇ ℝ) (y : E) (L : ℝ≥0) (hL : LipschitzWith L (f : E → ℝ))
    (hGoodInt : Integrable (fun a => dist (X a) y) (μ.restrict S)) :
    |(∫ x, f x ∂μ.map X) - f y| ≤
      (L : ℝ) * (∫ a, dist (X a) y ∂μ.restrict S) + 2 * ‖f‖ * μ.real Sᶜ := by
  have hp : ∀ x, |f x - f y| ≤ (0 : ℝ) + (L : ℝ) * dist x y := by
    intro x
    simpa only [Real.dist_eq, zero_add] using hL.dist_le_mul x y
  simpa only [zero_mul, zero_add] using
    test_error_le_good_affine μ hs hX f y hGoodInt hp

end Probability
end FoliationQM.GoodBadTransport
