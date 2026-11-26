module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-!
# Proper-time representation of the massive Gaussian normal multiplier

For the positive-frequency Gaussian in v13 lines 752–767, the temporal
frequency is √(μ²+|k|²). The expression below represents its increment above
rest mass by a convergent proper-time integral. The factor 1−exp(−s t)
retains the cancellation at the lower endpoint t=0.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianProperTimeMultiplier

open Set MeasureTheory Real

/-- Massive proper-time weight for the difference between the square-root
frequency at squared wave number s and its rest value. -/
def kernel (μ t : ℝ) : ℝ := t ^ (-(3/2) : ℝ) * Real.exp (-(μ^2*t))

/-- The proper-time kernel is strictly positive at every positive time. -/
theorem kernel_pos (μ : ℝ) {t : ℝ} (ht : 0 < t) : 0 < kernel μ t :=
  mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

private theorem time_kernel_eq (μ : ℝ) {t : ℝ} (ht : 0 < t) :
    t*kernel μ t = t ^ (-(1/2) : ℝ) * Real.exp (-(μ^2*t)) := by
  rw [kernel, show (-(3/2) : ℝ) = -(1/2)-1 by norm_num, Real.rpow_sub_one ht.ne']
  field_simp [ht.ne']

/-- Multiplication by the time variable gives an integrable weight despite
the original kernel's singularity at zero. -/
theorem integrable_time_kernel {μ : ℝ} (hμ : 0 < μ) :
    IntegrableOn (fun t => t * kernel μ t) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1/2)) (p := 1) (b := μ^2)
    (by norm_num) (by norm_num) (sq_pos_of_pos hμ)
  have h' : IntegrableOn (fun t : ℝ => t^(-(1/2) : ℝ) * Real.exp (-(μ^2*t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using h
  exact h'.congr_fun (fun t ht => (time_kernel_eq μ ht).symm) measurableSet_Ioi

/-- The cancellation is nonnegative and bounded by s times the integrable
time-weighted kernel on positive proper time. -/
theorem cancelled_bounds (μ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    0 ≤ kernel μ t * (1-Real.exp (-(s*t))) ∧
      kernel μ t * (1-Real.exp (-(s*t))) ≤ s*(t*kernel μ t) := by
  have hk := (kernel_pos μ ht).le
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs ht.le))
  refine ⟨mul_nonneg hk (sub_nonneg.mpr he), ?_⟩
  calc
    _ ≤ kernel μ t * (s*t) := mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-(s*t))]) hk
    _ = _ := by ring

/-- The cancelled proper-time representation is absolutely integrable for every
nonnegative squared wave number, including the rest mode s=0. -/
theorem integrable_cancelled {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    IntegrableOn (fun t => kernel μ t * (1-Real.exp (-(s*t)))) (Ioi 0) := by
  apply ((integrable_time_kernel hμ).const_mul s).mono'
    (by unfold kernel; fun_prop)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (cancelled_bounds μ hs ht).1]
  exact (cancelled_bounds μ hs ht).2

private def laplace (μ u t : ℝ) : ℝ := t^(-(1/2) : ℝ) * Real.exp (-((μ^2+u)*t))

private theorem laplace_integral {μ u : ℝ} (hμ : 0 < μ) (hu : 0 ≤ u) :
    (∫ t in Ioi 0, laplace μ u t) = Real.sqrt Real.pi / Real.sqrt (μ^2+u) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1/2) (by norm_num)
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hμ) hu)
  rw [show (1/2 : ℝ)-1 = -(1/2) by norm_num, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, one_div (μ^2+u), Real.sqrt_inv] at h
  simpa only [laplace, div_eq_inv_mul] using h

private theorem laplace_prod_integrable {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    Integrable (Function.uncurry (laplace μ))
      ((volume.restrict (uIoc 0 s)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [uIoc_of_le hs]
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 s) := integrableOn_const measure_Ioc_lt_top.ne
  have hprod := h1.mul_prod (integrable_time_kernel hμ)
  apply hprod.mono' (by unfold Function.uncurry laplace; fun_prop)
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (μ := volume.prod volume) (measurableSet_Ioc.prod measurableSet_Ioi)]
    with z hz
  obtain ⟨hu,ht⟩ := hz
  have hp : 0 ≤ z.2^(-(1/2) : ℝ) := Real.rpow_nonneg (le_of_lt ht) _
  change ‖laplace μ z.1 z.2‖ ≤ 1 * (z.2 * kernel μ z.2)
  rw [laplace, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (Real.exp_pos _).le),
    one_mul, time_kernel_eq μ ht]
  apply mul_le_mul_of_nonneg_left _ hp
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hu.1.le ht.le]

private theorem laplace_interval (μ s : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ u in 0..s, laplace μ u t) = kernel μ t * (1-Real.exp (-(s*t))) := by
  have hin : (∫ u in 0..s, Real.exp (-(u*t))) = (1-Real.exp (-(s*t)))/t := by
    let F := fun u : ℝ => -Real.exp (-(u*t))/t
    have hd (u : ℝ) : HasDerivAt F (Real.exp (-(u*t))) u := by
      have h := ((((hasDerivAt_id u).mul_const t).neg.exp).neg.div_const t)
      convert h using 1
      · rfl
      · change Real.exp (-(u*t)) = -(Real.exp (-(u*t)) * -(1*t))/t
        field_simp [ht.ne']
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s) (fun u _ => hd u)
      (f' := fun u => Real.exp (-(u*t))) (by apply Continuous.intervalIntegrable; fun_prop)
    rw [h]
    simp [F]
    ring
  have he (u : ℝ) : laplace μ u t = (t*kernel μ t) * Real.exp (-(u*t)) := by
    rw [laplace, time_kernel_eq μ ht, show -((μ^2+u)*t) = -(μ^2*t) + -(u*t) by ring,
      Real.exp_add, mul_assoc]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, hin]
  field_simp [ht.ne']

private theorem integral_inverse_sqrt {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    (∫ u in 0..s, Real.sqrt Real.pi / Real.sqrt (μ^2+u)) =
      2*Real.sqrt Real.pi * (Real.sqrt (μ^2+s)-μ) := by
  have hr (u : ℝ) (hu : u ∈ uIcc 0 s) : 0 < μ^2+u := by
    rw [uIcc_of_le hs] at hu
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hμ) hu.1
  let F := fun u : ℝ => 2*Real.sqrt Real.pi*Real.sqrt (μ^2+u)
  have hd (u : ℝ) (hu : u ∈ uIcc 0 s) :
      HasDerivAt F (Real.sqrt Real.pi / Real.sqrt (μ^2+u)) u := by
    have h := (((hasDerivAt_id u).const_add (μ^2)).sqrt (hr u hu).ne').const_mul (2*Real.sqrt Real.pi)
    convert h using 1
    · rfl
    · change _ = 2*Real.sqrt Real.pi * (1/(2*Real.sqrt (μ^2+u)))
      ring
  have hi : IntervalIntegrable (fun u : ℝ => Real.sqrt Real.pi / Real.sqrt (μ^2+u)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    exact fun u hu => (Real.sqrt_pos_of_pos (hr u hu)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [F, Real.sqrt_sq hμ.le]
  ring

/-- Integrating the cancellation over all positive proper times gives exactly
2√π times the massive frequency increment. -/
theorem integral_cancelled {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    (∫ t in Ioi 0, kernel μ t*(1-Real.exp (-(s*t)))) =
      2*Real.sqrt Real.pi*(Real.sqrt (μ^2+s)-μ) := by
  calc
    _ = ∫ t in Ioi 0, ∫ u in 0..s, laplace μ u t :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => (laplace_interval μ s ht).symm
    _ = ∫ u in 0..s, ∫ t in Ioi 0, laplace μ u t :=
      (intervalIntegral_integral_swap (laplace_prod_integrable hμ hs)).symm
    _ = ∫ u in 0..s, Real.sqrt Real.pi / Real.sqrt (μ^2+u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hs] at hu
      exact laplace_integral hμ hu.1
    _ = _ := integral_inverse_sqrt hμ hs

/-- The massive square-root multiplier equals its rest mass plus the normalized
proper-time integral with the cancellation kept inside the integral. -/
theorem sqrt_eq_integral {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    Real.sqrt (μ^2+s) = μ + (1/(2*Real.sqrt Real.pi)) *
      ∫ t in Ioi 0, kernel μ t*(1-Real.exp (-(s*t))) := by
  rw [integral_cancelled hμ hs]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos_of_pos Real.pi_pos
  field_simp [hpi.ne']
  ring

end FoliationQM.GaussianProperTimeMultiplier
