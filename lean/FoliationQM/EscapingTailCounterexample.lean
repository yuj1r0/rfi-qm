module

public import FoliationQM.ConcentrationCounterexamples
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Vanishing tail mass without a vanishing first moment

Source: v13 `rem:wkb_rates_tails` (Kinds C/D).

The actual probability places reciprocal mass at a linearly escaping point.
Its bounded continuous tests converge to the origin, while its bad first
moment and extended Dirac transport cost stay one. This is a probability
counterexample, with no claim that it is a Klein–Gordon solution family.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EscapingTailCounterexample

open MeasureTheory Set Filter WassersteinCoupling WassersteinDirac
  ConcentrationCounterexamples
open scoped Topology ENNReal BoundedContinuousFunction

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The actual outlier moves linearly along the chosen direction. -/
def escapePoint (v : E) (n : ℕ) : E := ((n : ℝ) + 1) • v

/-- The actual two-atom probability has reciprocal outlier weight. -/
def escapingProbability (v : E) (n : ℕ) : ProbabilityMeasure E :=
  mixProbability (reciprocalWidth n) (reciprocalWidth_pos n).le
    (reciprocalWidth_le_one n) 0 (escapePoint v n)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A unit direction gives the exact escaping distance. -/
theorem norm_escapePoint {v : E} (hv : ‖v‖ = 1) (n : ℕ) :
    ‖escapePoint v n‖ = (n : ℝ) + 1 := by
  rw [escapePoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), hv, mul_one]

/-- Restriction to the bad complement is literally the weighted escaping atom. -/
theorem bad_restriction {v : E} (hv : ‖v‖ = 1) (n : ℕ) :
    (escapingProbability v n : Measure E).restrict ({0} : Set E)ᶜ =
      ENNReal.ofReal (reciprocalWidth n) • Measure.dirac (escapePoint v n) := by
  classical
  have hn : escapePoint v n ≠ 0 := by
    intro h
    have he := norm_escapePoint hv n
    rw [h, norm_zero] at he
    have hp : 0 < (n : ℝ) + 1 := by positivity
    linarith
  change (mix (reciprocalWidth n) 0 (escapePoint v n)).restrict _ = _
  simp only [mix, Measure.restrict_add, Measure.restrict_smul, restrict_dirac]
  simp [hn]

/-- The actual bad mass equals the shrinking reciprocal weight. -/
theorem bad_mass {v : E} (hv : ‖v‖ = 1) (n : ℕ) :
    (escapingProbability v n : Measure E).real ({0} : Set E)ᶜ = reciprocalWidth n := by
  rw [← measureReal_restrict_apply_univ, bad_restriction hv n]
  simp only [Measure.real, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (reciprocalWidth_pos n).le]

/-- The actual bad mass tends to zero. -/
theorem bad_mass_tendsto_zero {v : E} (hv : ‖v‖ = 1) :
    Tendsto (fun n => (escapingProbability v n : Measure E).real ({0} : Set E)ᶜ)
      atTop (𝓝 0) := by
  simpa only [bad_mass hv] using reciprocalWidth_tendsto_zero

/-- The actual good restriction has a genuine zero distance moment, including when its mass is zero. -/
theorem good_integrable_and_first_moment (v : E) (n : ℕ) :
    Integrable (fun x : E => dist x 0)
        ((escapingProbability v n : Measure E).restrict {0}) ∧
      (∫ x, dist x 0 ∂(escapingProbability v n : Measure E).restrict {0}) = 0 := by
  have hi : Integrable (fun x : E => dist x 0) (escapingProbability v n : Measure E) :=
    mix_integrable _
  refine ⟨hi.mono_measure Measure.restrict_le_self, integral_eq_zero_of_ae ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : E))] with x hx
  simp only [mem_singleton_iff.mp hx, dist_self, Pi.zero_apply]

/-- The bad restriction has a genuine finite first moment equal to one at every index. -/
theorem bad_integrable_and_first_moment {v : E} (hv : ‖v‖ = 1) (n : ℕ) :
    Integrable (fun x : E => dist x 0)
        ((escapingProbability v n : Measure E).restrict ({0} : Set E)ᶜ) ∧
      (∫ x, dist x 0 ∂(escapingProbability v n : Measure E).restrict ({0} : Set E)ᶜ) = 1 := by
  have hi : Integrable (fun x : E => dist x 0) (escapingProbability v n : Measure E) :=
    mix_integrable _
  refine ⟨hi.mono_measure Measure.restrict_le_self, ?_⟩
  rw [bad_restriction hv n, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (reciprocalWidth_pos n).le, smul_eq_mul,
    dist_zero_right, norm_escapePoint hv n, mul_comm, coefficient_mul_width]

/-- The full probability also has a genuine finite first moment equal to one. -/
theorem integrable_and_first_moment {v : E} (hv : ‖v‖ = 1) (n : ℕ) :
    Integrable (fun x : E => dist x 0) (escapingProbability v n : Measure E) ∧
      (∫ x, dist x 0 ∂(escapingProbability v n : Measure E)) = 1 := by
  refine ⟨mix_integrable _, ?_⟩
  change (∫ x, dist x 0 ∂mix (reciprocalWidth n) 0 (escapePoint v n)) = 1
  rw [mix_integral (reciprocalWidth_pos n).le (reciprocalWidth_le_one n)]
  simp only [dist_self, mul_zero, zero_add, dist_zero_right, norm_escapePoint hv n]
  rw [mul_comm, coefficient_mul_width]

/-- The actual extended transport cost equals one, after genuine moment integrability is established. -/
theorem cost_eq_one {v : E} (hv : ‖v‖ = 1) (n : ℕ) :
    eW1 (escapingProbability v n : Measure E) (Measure.dirac (0 : E)) = 1 := by
  obtain ⟨hi, he⟩ := integrable_and_first_moment hv n
  rw [eW1_dirac_eq_ofReal_integral hi, he, ENNReal.ofReal_one]

/-- Every bounded continuous test has the exact twice-norm tail-mass majorant. -/
theorem integral_error_le (v : E) (n : ℕ) (f : E →ᵇ ℝ) :
    |(∫ x, f x ∂(escapingProbability v n : Measure E)) - f 0| ≤
      2 * ‖f‖ * reciprocalWidth n := by
  change |(∫ x, f x ∂mix (reciprocalWidth n) 0 (escapePoint v n)) - f 0| ≤ _
  rw [mix_integral (reciprocalWidth_pos n).le (reciprocalWidth_le_one n)]
  have he : (1 - reciprocalWidth n) * f 0 + reciprocalWidth n * f (escapePoint v n) - f 0 =
      reciprocalWidth n * (f (escapePoint v n) - f 0) := by ring
  rw [he, abs_mul, abs_of_pos (reciprocalWidth_pos n)]
  have hb : |f (escapePoint v n) - f 0| ≤ 2 * ‖f‖ := by
    simpa only [Real.dist_eq] using f.dist_le_two_norm (escapePoint v n) 0
  exact (mul_le_mul_of_nonneg_left hb (reciprocalWidth_pos n).le).trans_eq (mul_comm _ _)

/-- Actual integrals of every bounded continuous test converge to its value at the origin. -/
theorem boundedContinuous_integral_tendsto (v : E) (f : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(escapingProbability v n : Measure E))
      atTop (𝓝 (f 0)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : Tendsto (fun n => 2 * ‖f‖ * reciprocalWidth n) atTop (𝓝 0) := by
    simpa only [mul_zero] using reciprocalWidth_tendsto_zero.const_mul (2 * ‖f‖)
  apply squeeze_zero (fun _ => dist_nonneg) ?_ hb
  intro n
  simpa only [Real.dist_eq] using integral_error_le v n f

/-- The bundled probabilities converge in their genuine weak topology to the origin Dirac measure. -/
theorem weak_tendsto (v : E) :
    Tendsto (escapingProbability v) atTop
      (𝓝 (Measure.dirac (0 : E)).toProbabilityMeasure) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simpa only [Measure.coe_toProbabilityMeasure, integral_dirac] using
    boundedContinuous_integral_tendsto v f

/-- The real transport costs cannot tend to zero despite the actual weak and bad-mass limits. -/
theorem not_cost_tendsto_zero {v : E} (hv : ‖v‖ = 1) :
    ¬ Tendsto (fun n => (eW1 (escapingProbability v n : Measure E)
      (Measure.dirac (0 : E))).toReal) atTop (𝓝 0) := by
  intro h
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [cost_eq_one hv, ENNReal.toReal_one] using h)
  exact one_ne_zero he

end Normed

/-- The concrete Euclidean unit direction gives a nonvacuous weak-convergence counterexample with exact unit cost. -/
theorem euclidean_escaping_counterexample :
    Tendsto (fun n => Measure.real
      (escapingProbability euclideanUnit n : Measure (EuclideanSpace ℝ (Fin 3)))
      ({0} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ) atTop (𝓝 0) ∧
    Tendsto (escapingProbability euclideanUnit) atTop
      (𝓝 (Measure.dirac (0 : EuclideanSpace ℝ (Fin 3))).toProbabilityMeasure) ∧
    (∀ n, Integrable (fun x : EuclideanSpace ℝ (Fin 3) => dist x 0)
        ((escapingProbability euclideanUnit n : Measure (EuclideanSpace ℝ (Fin 3))).restrict {0}) ∧
      (∫ x, dist x 0 ∂Measure.restrict
        (escapingProbability euclideanUnit n : Measure (EuclideanSpace ℝ (Fin 3))) {0}) = 0) ∧
    (∀ n, eW1 (escapingProbability euclideanUnit n : Measure (EuclideanSpace ℝ (Fin 3)))
      (Measure.dirac 0) = 1) :=
  ⟨bad_mass_tendsto_zero euclideanUnit_norm, weak_tendsto euclideanUnit,
    good_integrable_and_first_moment euclideanUnit, cost_eq_one euclideanUnit_norm⟩

end FoliationQM.EscapingTailCounterexample
