module

public import FoliationQM.WassersteinDirac
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concentration does not imply velocity or support control

These are actual probability and smooth kinematic examples. They are not
asserted to arise from Klein–Gordon solutions. Every transport-cost identity
uses a genuine finite first moment, and support means actual measure support.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConcentrationCounterexamples

open MeasureTheory Set Filter WassersteinCoupling WassersteinDirac
open scoped Topology ENNReal

section Measures
variable {E : Type*} [MeasurableSpace E]

/-- The literal weighted sum of two Dirac measures. -/
def mix (eps : ℝ) (x y : E) : Measure E :=
  ENNReal.ofReal (1 - eps) • Measure.dirac x + ENNReal.ofReal eps • Measure.dirac y

/-- Nonnegative complementary weights give actual probability mass one. -/
theorem mix_probability {eps : ℝ} {x y : E} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) :
    IsProbabilityMeasure (mix eps x y) := by
  rw [isProbabilityMeasure_iff]
  simp only [mix, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr h1) h0]
  simp only [sub_add_cancel, ENNReal.ofReal_one]

/-- The bundled probability contains exactly the proved two-atom measure. -/
def mixProbability (eps : ℝ) (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (x y : E) :
    ProbabilityMeasure E := ⟨mix eps x y, mix_probability h0 h1⟩

variable [MeasurableSingletonClass E]

/-- Every real-valued function is genuinely integrable under the finite two-atom measure. -/
theorem mix_integrable {eps : ℝ} {x y : E} (f : E → ℝ) :
    Integrable f (mix eps x y) :=
  ((integrable_dirac (by simp) : Integrable f (Measure.dirac x)).smul_measure
    ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp) : Integrable f (Measure.dirac y)).smul_measure
      ENNReal.ofReal_ne_top)

/-- Actual integration against the mixture equals the two weighted values. -/
theorem mix_integral {eps : ℝ} {x y : E} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (f : E → ℝ) :
    (∫ z, f z ∂mix eps x y) = (1 - eps) * f x + eps * f y := by
  rw [mix, integral_add_measure
    ((integrable_dirac (by simp) : Integrable f (Measure.dirac x)).smul_measure
      ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp) : Integrable f (Measure.dirac y)).smul_measure
      ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr h1), smul_eq_mul]

end Measures

section Support
variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]

/-- Any positive right-hand atomic weight keeps that atom in the actual measure support. -/
theorem right_mem_support {eps : ℝ} {x y : E} (hpos : 0 < eps) :
    y ∈ (mix eps x y).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hy : y ∈ U := mem_of_mem_nhds hU
  have hr : (ENNReal.ofReal eps • Measure.dirac y) U = ENNReal.ofReal eps := by
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem hy, smul_eq_mul, mul_one]
  have hp : 0 < (ENNReal.ofReal eps • Measure.dirac y) U := by
    rw [hr]
    exact ENNReal.ofReal_pos.mpr hpos
  apply hp.trans_le
  change (ENNReal.ofReal eps • Measure.dirac y) U ≤
    (ENNReal.ofReal (1 - eps) • Measure.dirac x + ENNReal.ofReal eps • Measure.dirac y) U
  rw [Measure.add_apply]
  exact le_add_of_nonneg_left zero_le

end Support

/-- A strictly positive width sequence, including its initial index. -/
def reciprocalWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Every reciprocal width is positive. -/
theorem reciprocalWidth_pos (n : ℕ) : 0 < reciprocalWidth n := by
  unfold reciprocalWidth
  positivity

/-- The widths are valid mixture weights. -/
theorem reciprocalWidth_le_one (n : ℕ) : reciprocalWidth n ≤ 1 := by
  unfold reciprocalWidth
  apply (div_le_one (by positivity)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The actual reciprocal sequence tends to zero. -/
theorem reciprocalWidth_tendsto_zero : Tendsto reciprocalWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The growing velocity coefficient exactly cancels the shrinking position scale. -/
theorem coefficient_mul_width (n : ℕ) : ((n : ℝ) + 1) * reciprocalWidth n = 1 := by
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  simp [reciprocalWidth, hn]

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Each initial velocity field is an actual scalar linear map. -/
def scalingVelocity (n : ℕ) (x : E) : E := ((n : ℝ) + 1) • x

/-- Each field is smooth, with a coefficient growing with the index. -/
theorem scalingVelocity_smooth (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (scalingVelocity (E := E) n) :=
  contDiff_const.smul contDiff_id

/-- Every field agrees with zero at the reference anchor. -/
theorem scalingVelocity_zero (n : ℕ) : scalingVelocity n (0 : E) = 0 := by
  simp only [scalingVelocity, smul_zero]

/-- The velocity at the shrinking initial point remains the fixed vector. -/
theorem scalingVelocity_at_width (n : ℕ) (v : E) :
    scalingVelocity n (reciprocalWidth n • v) = v := by
  rw [scalingVelocity, smul_smul, coefficient_mul_width, one_smul]

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual initial position first moment shrinks with the reciprocal width. -/
theorem dirac_position_moment (n : ℕ) (v : E) :
    (∫ x, ‖x‖ ∂Measure.dirac (reciprocalWidth n • v)) = reciprocalWidth n * ‖v‖ := by
  rw [integral_dirac, norm_smul, Real.norm_eq_abs, abs_of_pos (reciprocalWidth_pos n)]

/-- The actual initial velocity first moment stays equal to the fixed vector norm. -/
theorem dirac_velocity_moment (n : ℕ) (v : E) :
    (∫ x, ‖scalingVelocity n x‖ ∂Measure.dirac (reciprocalWidth n • v)) = ‖v‖ := by
  rw [integral_dirac, scalingVelocity_at_width]

/-- Actual initial position moments converge to zero for every fixed vector. -/
theorem dirac_position_moment_tendsto_zero (v : E) :
    Tendsto (fun n => ∫ x, ‖x‖ ∂Measure.dirac (reciprocalWidth n • v)) atTop (𝓝 0) := by
  simpa only [dirac_position_moment, zero_mul] using reciprocalWidth_tendsto_zero.mul_const ‖v‖

/-- A nonzero velocity moment does not tend to zero despite smooth individual fields and shrinking position moments. -/
theorem dirac_velocity_moment_not_tendsto_zero {v : E} (hv : v ≠ 0) :
    ¬ Tendsto (fun n => ∫ x, ‖scalingVelocity n x‖
      ∂Measure.dirac (reciprocalWidth n • v)) atTop (𝓝 0) := by
  intro h
  have hn : ‖v‖ = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [dirac_velocity_moment] using h)
  exact hv (norm_eq_zero.mp hn)

end Normed

section Moments
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The actual mixture first moment is precisely its distant weight times distance. -/
theorem mix_norm_moment {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1) (v : E) :
    (∫ x, ‖x‖ ∂mix eps 0 v) = eps * ‖v‖ := by
  rw [mix_integral h0 h1]
  simp only [norm_zero, mul_zero, zero_add]

/-- A fixed unit outlier with shrinking positive weight has a genuine finite transport cost equal to that weight. -/
theorem fixed_outlier_cost (n : ℕ) {v : E} (hv : ‖v‖ = 1) :
    eW1 (mix (reciprocalWidth n) 0 v) (Measure.dirac 0) ≠ ∞ ∧
      (eW1 (mix (reciprocalWidth n) 0 v) (Measure.dirac 0)).toReal = reciprocalWidth n := by
  let := mix_probability (x := (0 : E)) (y := v)
    (reciprocalWidth_pos n).le (reciprocalWidth_le_one n)
  have hi : Integrable (fun x : E => ‖x - 0‖) (mix (reciprocalWidth n) 0 v) := by
    simpa only [sub_zero] using
      (mix_integrable (eps := reciprocalWidth n) (x := (0 : E)) (y := v) (fun x => ‖x‖))
  have hw := eW1_dirac_finite_and_toReal_norm hi
  simpa only [sub_zero, mix_norm_moment (reciprocalWidth_pos n).le
    (reciprocalWidth_le_one n), hv, mul_one] using hw

/-- The genuine finite Wasserstein cost to the origin tends to zero. -/
theorem fixed_outlier_cost_tendsto_zero {v : E} (hv : ‖v‖ = 1) :
    Tendsto (fun n => (eW1 (mix (reciprocalWidth n) 0 v) (Measure.dirac 0)).toReal)
      atTop (𝓝 0) := by
  have he : (fun n => (eW1 (mix (reciprocalWidth n) 0 v) (Measure.dirac 0)).toReal) =
      reciprocalWidth := funext fun n => (fixed_outlier_cost n hv).2
  rw [he]
  exact reciprocalWidth_tendsto_zero

end Moments

section NormedSupport
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The same fixed outlier remains in the measure support at every index. -/
theorem fixed_outlier_mem_support (n : ℕ) (v : E) :
    v ∈ (mix (reciprocalWidth n) 0 v).support :=
  right_mem_support (reciprocalWidth_pos n)

/-- No fixed multiple of the shrinking width eventually contains these actual supports. -/
theorem eventually_not_support_subset_closedBall {v : E} (hv : ‖v‖ = 1) (C : ℝ) :
    ∀ᶠ n in atTop, ¬ (mix (reciprocalWidth n) 0 v).support ⊆
      Metric.closedBall 0 (C * reciprocalWidth n) := by
  have hlim : Tendsto (fun n => C * reciprocalWidth n) atTop (𝓝 0) := by
    simpa only [mul_zero] using reciprocalWidth_tendsto_zero.const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  intro hs
  have hm := hs (fixed_outlier_mem_support n v)
  have hb : ‖v‖ ≤ C * reciprocalWidth n := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hm
  rw [hv] at hb
  exact (not_le_of_gt hn) hb

end NormedSupport

/-- An actual unit direction in physical Euclidean three-space witnesses the examples. -/
def euclideanUnit : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.basisFun (Fin 3) ℝ 0

/-- The concrete Euclidean direction has the required genuine Euclidean norm. -/
theorem euclideanUnit_norm : ‖euclideanUnit‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0

end FoliationQM.ConcentrationCounterexamples
