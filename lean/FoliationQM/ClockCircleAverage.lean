module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Actual normalized physical-circle averages

Sources: v13 `thm:clock_sideband`, `eq:s1_circle_variance`, and
`eq:sideband_averaged_lagrangian`. The average is the actual interval integral
over one physical phase turn divided by `2*pi`. Its trigonometric moments are
computed from genuine antiderivatives, not postulated. Continuity proves the
integrability of every quadrature and product used below. Iterating this
normalized average supplies the independent-axis probe model separately.
-/
@[expose] public section
noncomputable section

namespace FoliationQM.ClockCircleAverage

open MeasureTheory
open scoped BigOperators

/-- Normalized integration over one complete physical phase turn. -/
def average (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, f θ)

/-- A constant retains its value under the actual normalized circle integral. -/
theorem average_const (c : ℝ) : average (fun _ => c) = c := by
  simp only [average, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

/-- Additivity requires actual interval integrability of both summands. -/
theorem average_add {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    average (fun θ => f θ + g θ) = average f + average g := by
  rw [average, intervalIntegral.integral_add hf hg]
  exact mul_add _ _ _

/-- Subtraction commutes with averaging for genuinely integrable functions. -/
theorem average_sub {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) :
    average (fun θ => f θ - g θ) = average f - average g := by
  rw [average, intervalIntegral.integral_sub hf hg]
  exact mul_sub _ _ _

/-- Real scalar multiplication commutes with normalized integration. -/
theorem average_const_mul (c : ℝ) (f : ℝ → ℝ) :
    average (fun θ => c * f θ) = c * average f := by
  simp only [average, intervalIntegral.integral_const_mul]
  ring

/-- A constant right factor can be removed from the actual integral. -/
theorem average_mul_const (f : ℝ → ℝ) (c : ℝ) :
    average (fun θ => f θ * c) = average f * c := by
  simp only [average, intervalIntegral.integral_mul_const]
  ring

/-- Finite sums commute with normalized integration under actual integrability. -/
theorem average_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 (2 * Real.pi)) :
    average (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, average (f i) := by
  simp only [average, intervalIntegral.integral_finsetSum hf, Finset.mul_sum]

/-- A full-turn integral of a genuinely periodic function is independent of
the chosen real phase origin. This is an identity of actual integrals. -/
theorem average_shift {f : ℝ → ℝ} (hf : Function.Periodic f (2 * Real.pi)) (φ : ℝ) :
    average (fun θ => f (φ + θ)) = average f := by
  unfold average
  rw [intervalIntegral.integral_comp_add_left]
  simpa only [add_zero, zero_add] using congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
    (hf.intervalIntegral_add_eq φ 0)

/-- Shifted cosine is genuinely integrable on the phase interval. -/
theorem intervalIntegrable_cos (φ : ℝ) :
    IntervalIntegrable (fun θ => Real.cos (φ + θ)) volume 0 (2 * Real.pi) :=
  (Real.continuous_cos.comp (continuous_const.add continuous_id)).intervalIntegrable _ _

/-- Shifted sine is genuinely integrable on the phase interval. -/
theorem intervalIntegrable_sin (φ : ℝ) :
    IntervalIntegrable (fun θ => Real.sin (φ + θ)) volume 0 (2 * Real.pi) :=
  (Real.continuous_sin.comp (continuous_const.add continuous_id)).intervalIntegrable _ _

/-- The squared cosine quadrature is genuinely integrable. -/
theorem intervalIntegrable_cos_sq (φ : ℝ) :
    IntervalIntegrable (fun θ => Real.cos (φ + θ) ^ 2) volume 0 (2 * Real.pi) :=
  ((Real.continuous_cos.comp (continuous_const.add continuous_id)).pow 2).intervalIntegrable _ _

/-- The squared sine quadrature is genuinely integrable. -/
theorem intervalIntegrable_sin_sq (φ : ℝ) :
    IntervalIntegrable (fun θ => Real.sin (φ + θ) ^ 2) volume 0 (2 * Real.pi) :=
  ((Real.continuous_sin.comp (continuous_const.add continuous_id)).pow 2).intervalIntegrable _ _

/-- The mixed sine/cosine quadrature is genuinely integrable. -/
theorem intervalIntegrable_cos_mul_sin (φ : ℝ) :
    IntervalIntegrable (fun θ => Real.cos (φ + θ) * Real.sin (φ + θ)) volume 0 (2 * Real.pi) :=
  ((Real.continuous_cos.comp (continuous_const.add continuous_id)).mul
    (Real.continuous_sin.comp (continuous_const.add continuous_id))).intervalIntegrable _ _

/-- Every real linear quadrature is genuinely integrable. -/
theorem intervalIntegrable_quadrature (φ a b : ℝ) :
    IntervalIntegrable (fun θ => a * Real.cos (φ + θ) + b * Real.sin (φ + θ))
      volume 0 (2 * Real.pi) :=
  ((intervalIntegrable_cos φ).const_mul a).add ((intervalIntegrable_sin φ).const_mul b)

/-- Products of arbitrary real quadratures have actual interval integrability. -/
theorem intervalIntegrable_quadrature_product (φ a b c d : ℝ) :
    IntervalIntegrable (fun θ =>
      (a * Real.cos (φ + θ) + b * Real.sin (φ + θ)) *
      (c * Real.cos (φ + θ) + d * Real.sin (φ + θ))) volume 0 (2 * Real.pi) := by
  have h : Continuous (fun θ =>
      (a * Real.cos (φ + θ) + b * Real.sin (φ + θ)) *
      (c * Real.cos (φ + θ) + d * Real.sin (φ + θ))) := by fun_prop
  exact h.intervalIntegrable _ _

/-- Actual integration gives zero cosine mean at every initial phase. -/
theorem average_cos (φ : ℝ) : average (fun θ => Real.cos (φ + θ)) = 0 := by
  rw [average_shift Real.cos_periodic φ]
  simp [average]

/-- Actual integration gives zero sine mean at every initial phase. -/
theorem average_sin (φ : ℝ) : average (fun θ => Real.sin (φ + θ)) = 0 := by
  rw [average_shift Real.sin_periodic φ]
  simp [average]

/-- The squared cosine moment is one half, computed from its actual integral. -/
theorem average_cos_sq (φ : ℝ) : average (fun θ => Real.cos (φ + θ) ^ 2) = 1 / 2 := by
  have hp : Function.Periodic (fun θ => Real.cos θ ^ 2) (2 * Real.pi) := by
    intro θ
    simp only [Real.cos_add_two_pi]
  rw [average_shift hp φ]
  simp [average]
  field_simp

/-- The squared sine moment is one half, computed from its actual integral. -/
theorem average_sin_sq (φ : ℝ) : average (fun θ => Real.sin (φ + θ) ^ 2) = 1 / 2 := by
  have hp : Function.Periodic (fun θ => Real.sin θ ^ 2) (2 * Real.pi) := by
    intro θ
    simp only [Real.sin_add_two_pi]
  rw [average_shift hp φ]
  simp [average]
  field_simp

/-- Mixed quadratures cancel under the actual full-turn average. -/
theorem average_cos_mul_sin (φ : ℝ) :
    average (fun θ => Real.cos (φ + θ) * Real.sin (φ + θ)) = 0 := by
  have hp : Function.Periodic (fun θ => Real.cos θ * Real.sin θ) (2 * Real.pi) := by
    intro θ
    simp only [Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [average_shift hp φ]
  simp only [average]
  simp_rw [mul_comm (Real.cos _) (Real.sin _)]
  rw [integral_sin_mul_cos₁]
  simp

/-- Every real linear clock quadrature has zero actual mean. -/
theorem average_quadrature (φ a b : ℝ) :
    average (fun θ => a * Real.cos (φ + θ) + b * Real.sin (φ + θ)) = 0 := by
  rw [average_add ((intervalIntegrable_cos φ).const_mul a)
    ((intervalIntegrable_sin φ).const_mul b), average_const_mul, average_const_mul,
    average_cos, average_sin]
  ring

/-- The actual full-turn average of two quadratures is half their coefficient
dot product. The absence of mixed terms is proved by integration. -/
theorem average_quadrature_product (φ a b c d : ℝ) :
    average (fun θ =>
      (a * Real.cos (φ + θ) + b * Real.sin (φ + θ)) *
      (c * Real.cos (φ + θ) + d * Real.sin (φ + θ))) = (a * c + b * d) / 2 := by
  have h : (fun θ =>
      (a * Real.cos (φ + θ) + b * Real.sin (φ + θ)) *
      (c * Real.cos (φ + θ) + d * Real.sin (φ + θ))) =
      (fun θ => (a * c) * Real.cos (φ + θ) ^ 2 +
        (a * d + b * c) * (Real.cos (φ + θ) * Real.sin (φ + θ)) +
        (b * d) * Real.sin (φ + θ) ^ 2) := by funext θ; ring
  rw [h, average_add
    (((intervalIntegrable_cos_sq φ).const_mul (a * c)).add
      ((intervalIntegrable_cos_mul_sin φ).const_mul (a * d + b * c)))
    ((intervalIntegrable_sin_sq φ).const_mul (b * d)),
    average_add ((intervalIntegrable_cos_sq φ).const_mul (a * c))
      ((intervalIntegrable_cos_mul_sin φ).const_mul (a * d + b * c)),
    average_const_mul, average_const_mul, average_const_mul,
    average_cos_sq, average_cos_mul_sin, average_sin_sq]
  ring

/-- The second moment of a real clock quadrature is half its squared amplitude. -/
theorem average_quadrature_sq (φ a b : ℝ) :
    average (fun θ => (a * Real.cos (φ + θ) + b * Real.sin (φ + θ)) ^ 2) =
      (a ^ 2 + b ^ 2) / 2 := by
  simpa only [pow_two] using average_quadrature_product φ a b a b

end FoliationQM.ClockCircleAverage
