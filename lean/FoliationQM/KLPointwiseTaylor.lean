module

public import FoliationQM.FourthOrderTaylor
public import FoliationQM.IteratedLogDerivatives

/-!
# The actual cubic Taylor expansion of the translated KL density

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's finite-displacement refinement following `prop:audit11_kl`.
The actual log-ratio integrand has a derived cubic expansion with an
integrable fourth-order remainder along each translation segment. The third
coefficient retains the negative weighted log-derivative sign. A supplied
bound on the actual fourth derivative controls the remainder; the Taylor
formula or its error is never an assumption. Spatial integration and phase
cancellation are subsequent steps.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KLPointwiseTaylor

open MeasureTheory Set Metric TranslatedKL IteratedLogDerivatives FourthOrderTaylor
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise cubic KL polynomial, with the actual first and second
translation differentials and the actual weighted third log derivative. -/
def densityPolynomial (f : E → ℝ) (a x : E) : ℝ :=
  firstIntegrand f 0 x a + (1 / 2 : ℝ) * secondIntegrand f 0 x a a +
    (1 / 6 : ℝ) * weightedLogDerivative f 3 0 x (fun _ => a)

/-- The displayed density polynomial equals the genuine cubic Taylor
polynomial of the actual translated KL integrand. -/
theorem densityPolynomial_eq_cubic {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hpos : ∀ x, 0 < f x) (a x : E) :
    densityPolynomial f a x = cubicPolynomial (fun b => integrand f b x) 0 a := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  rw [cubicPolynomial, integrand_zero, zero_add,
    (hasFDerivAt_integrand hf2 hpos 0 x).fderiv,
    iteratedFDeriv_integrand (by norm_num : (2 : ℕ) ≠ 0) hf2 hpos,
    iteratedFDeriv_integrand (by norm_num : (3 : ℕ) ≠ 0) hf hpos,
    weightedLogDerivative_two_diagonal]
  rfl

/-- Scaling the translation displays the linear, quadratic and cubic powers. -/
theorem densityPolynomial_smul (f : E → ℝ) (a x : E) (ε : ℝ) :
    densityPolynomial f (ε • a) x =
      ε * firstIntegrand f 0 x a + (ε ^ 2 / 2) * secondIntegrand f 0 x a a +
        (ε ^ 3 / 6) * weightedLogDerivative f 3 0 x (fun _ => a) := by
  simp [densityPolynomial, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  ring

/-- The cubic coefficient has the source's negative weighted third log derivative. -/
theorem cubic_coefficient_eq_log (f : E → ℝ) (a x : E) :
    (1 / 6 : ℝ) * weightedLogDerivative f 3 0 x (fun _ => a) =
      -(f x / 6) * iteratedFDeriv ℝ 3 (logDensity f) x (fun _ => a) := by
  rw [weightedLogDerivative_apply, add_zero]
  ring

/-- As a function of translation the density polynomial is genuinely continuous. -/
theorem continuous_densityPolynomial_translation (f : E → ℝ) (x : E) :
    Continuous (fun a => densityPolynomial f a x) := by
  unfold densityPolynomial
  fun_prop

/-- Actual C4 density regularity gives an exact fourth-order integral
remainder for the pointwise translated KL integrand. -/
theorem integrand_sub_densityPolynomial_eq_integral {f : E → ℝ}
    (hf : ContDiff ℝ 4 f) (hpos : ∀ x, 0 < f x) (a x : E) :
    integrand f a x - densityPolynomial f a x =
      (1 / 6 : ℝ) * ∫ t in (0 : ℝ)..1, (1-t)^3 *
        weightedLogDerivative f 4 (t • a) x (fun _ => a) := by
  have h := sub_cubic_eq_integral (g := fun b => integrand f b x) 0 a
    (fun _ _ => (contDiff_integrand_order hf hpos x).contDiffAt)
  rw [← densityPolynomial_eq_cubic (hf.of_le (by norm_num)) hpos a x] at h
  simpa only [zero_add, iteratedFDeriv_integrand (by norm_num : (4 : ℕ) ≠ 0) hf hpos] using h

/-- The exact fourth-order remainder is a genuinely integrable segment integral. -/
theorem intervalIntegrable_density_remainder {f : E → ℝ}
    (hf : ContDiff ℝ 4 f) (hpos : ∀ x, 0 < f x) (a x : E) :
    IntervalIntegrable (fun t : ℝ => (1-t)^3 *
      weightedLogDerivative f 4 (t • a) x (fun _ => a)) volume 0 1 := by
  have h := intervalIntegrable_remainder (g := fun b => integrand f b x) 0 a
    (fun _ _ => (contDiff_integrand_order hf hpos x).contDiffAt)
  simpa only [zero_add, iteratedFDeriv_integrand (by norm_num : (4 : ℕ) ≠ 0) hf hpos] using h

/-- A bound on the actual weighted fourth derivative along a segment gives
an explicit pointwise fourth-order KL remainder bound. -/
theorem norm_integrand_sub_densityPolynomial_le {f : E → ℝ}
    (hf : ContDiff ℝ 4 f) (hpos : ∀ x, 0 < f x) (a x : E) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖weightedLogDerivative f 4 (t • a) x‖ ≤ B) :
    ‖integrand f a x - densityPolynomial f a x‖ ≤ B * ‖a‖ ^ 4 / 24 := by
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 4 (fun b => integrand f b x) (0 + t • a)‖ ≤ B := by
    intro t ht
    simpa only [zero_add, iteratedFDeriv_integrand (by norm_num : (4 : ℕ) ≠ 0) hf hpos]
      using hB t ht
  have h := norm_sub_cubic_le_of_contDiff (contDiff_integrand_order hf hpos x) 0 a hb
  rw [← densityPolynomial_eq_cubic (hf.of_le (by norm_num)) hpos a x] at h
  simpa only [zero_add] using h

/-- A common fourth-derivative envelope on a positive-radius translation
ball supplies the actual segment bounds for every displacement in that ball. -/
theorem norm_integrand_sub_densityPolynomial_le_of_ball {f : E → ℝ}
    (hf : ContDiff ℝ 4 f) (hpos : ∀ x, 0 < f x) {r : ℝ} (hr : 0 < r)
    (a x : E) (ha : a ∈ ball (0 : E) r) {B : ℝ}
    (hB : ∀ b ∈ ball (0 : E) r, ‖weightedLogDerivative f 4 b x‖ ≤ B) :
    ‖integrand f a x - densityPolynomial f a x‖ ≤ B * ‖a‖ ^ 4 / 24 :=
  norm_integrand_sub_densityPolynomial_le hf hpos a x (fun t ht =>
    hB (t • a) ((convex_ball (0 : E) r).smul_mem_of_zero_mem (mem_ball_self hr) ha ht))

/-- Scaling an actual displacement yields the explicit epsilon-four factor
without assuming a Taylor remainder for KL. -/
theorem norm_integrand_sub_densityPolynomial_smul_le {f : E → ℝ}
    (hf : ContDiff ℝ 4 f) (hpos : ∀ x, 0 < f x) (a x : E) (ε : ℝ) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖weightedLogDerivative f 4 (t • (ε • a)) x‖ ≤ B) :
    ‖integrand f (ε • a) x - densityPolynomial f (ε • a) x‖ ≤
      B * ε ^ 4 * ‖a‖ ^ 4 / 24 := by
  have h := norm_integrand_sub_densityPolynomial_le hf hpos (ε • a) x hB
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, pow_abs,
    abs_of_nonneg (by positivity : 0 ≤ ε^4), mul_assoc] using h

end FoliationQM.KLPointwiseTaylor
