module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual means and centered variances of real L² observables

This supplies the probability-integral component of v13 `eq:p_var_decomp`
and `thm:uncertainty` (component kinds C and D). Square integrability gives
the genuine first and second moments used in each integral expansion.
The observable is arbitrary; the analytic identification with momentum
and with a density score is a separate obligation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CenteredL2Variance

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The actual expectation of a real observable. -/
def mean (f : α → ℝ) : ℝ := ∫ x, f x ∂μ

/-- Subtraction of the observable's actual expectation. -/
def centered (f : α → ℝ) (x : α) : ℝ := f x - mean μ f

/-- The integral of the centered square. -/
def variance (f : α → ℝ) : ℝ := ∫ x, (centered μ f x) ^ 2 ∂μ

/-- Every centered-square integral is nonnegative. -/
theorem variance_nonneg (f : α → ℝ) : 0 ≤ variance μ f :=
  integral_nonneg fun _ => sq_nonneg _

/-- Means respect equality almost everywhere. -/
theorem mean_congr {f g : α → ℝ} (h : f =ᵐ[μ] g) : mean μ f = mean μ g :=
  integral_congr_ae h

/-- Centered variances respect equality almost everywhere. -/
theorem variance_congr {f g : α → ℝ} (h : f =ᵐ[μ] g) : variance μ f = variance μ g := by
  have hm := mean_congr μ h
  apply integral_congr_ae
  filter_upwards [h] with x hx
  simp only [centered, hx, hm]

/-- Multiplication by a real scalar scales the actual expectation. -/
theorem mean_const_mul (c : ℝ) (f : α → ℝ) :
    mean μ (fun x => c * f x) = c * mean μ f :=
  integral_const_mul c f

/-- Centering commutes with scalar multiplication. -/
theorem centered_const_mul (c : ℝ) (f : α → ℝ) (x : α) :
    centered μ (fun y => c * f y) x = c * centered μ f x := by
  rw [centered, mean_const_mul, centered]
  ring

/-- Scaling an observable scales its centered-square integral quadratically. -/
theorem variance_const_mul (c : ℝ) (f : α → ℝ) :
    variance μ (fun x => c * f x) = c ^ 2 * variance μ f := by
  simp only [variance, centered_const_mul, mul_pow]
  exact integral_const_mul _ _

/-- For a zero-mean observable, the variance is its actual second moment. -/
theorem variance_eq_integral_sq_of_mean_zero {f : α → ℝ} (h : mean μ f = 0) :
    variance μ f = ∫ x, f x ^ 2 ∂μ := by
  simp only [variance, centered, h, sub_zero]

variable [IsProbabilityMeasure μ] {f g : α → ℝ}

/-- An L² observable on the probability space has a genuine first moment. -/
theorem integrable (hf : MemLp f 2 μ) : Integrable f μ :=
  hf.integrable (by norm_num)

/-- The centered observable remains in L². -/
theorem memLp_centered (hf : MemLp f 2 μ) : MemLp (centered μ f) 2 μ :=
  hf.sub (memLp_const _)

/-- The centered square is genuinely integrable. -/
theorem integrable_centered_sq (hf : MemLp f 2 μ) :
    Integrable (fun x => (centered μ f x) ^ 2) μ :=
  (memLp_centered μ hf).integrable_sq

/-- The expectation of a constant is that constant. -/
theorem mean_const (c : ℝ) : mean μ (fun _ : α => c) = c := by
  simp [mean]

/-- The actual centered observable has zero expectation. -/
theorem integral_centered (hf : MemLp f 2 μ) : (∫ x, centered μ f x ∂μ) = 0 := by
  simp only [centered]
  rw [integral_sub (integrable μ hf) (integrable_const _)]
  simp [mean]

/-- Addition of integrable observables adds their actual means. -/
theorem mean_add (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    mean μ (fun x => f x + g x) = mean μ f + mean μ g :=
  integral_add (integrable μ hf) (integrable μ hg)

/-- A constant shift changes the actual expectation by the same constant. -/
theorem mean_add_const (hf : MemLp f 2 μ) (c : ℝ) :
    mean μ (fun x => f x + c) = mean μ f + c := by
  rw [mean_add μ hf (memLp_const c), mean_const]

/-- Centering removes a constant shift of an L² observable. -/
theorem centered_add_const (hf : MemLp f 2 μ) (c : ℝ) (x : α) :
    centered μ (fun y => f y + c) x = centered μ f x := by
  rw [centered, mean_add_const μ hf, centered]
  ring

/-- Constant shifts preserve the actual variance. -/
theorem variance_add_const (hf : MemLp f 2 μ) (c : ℝ) :
    variance μ (fun x => f x + c) = variance μ f := by
  simp only [variance, centered_add_const μ hf]

/-- Expansion into the genuine second moment minus the squared mean. -/
theorem variance_eq_integral_sq_sub_sq_mean (hf : MemLp f 2 μ) :
    variance μ f = (∫ x, f x ^ 2 ∂μ) - (mean μ f) ^ 2 := by
  have heq (x : α) : (centered μ f x) ^ 2 =
      f x ^ 2 - 2 * mean μ f * f x + (mean μ f) ^ 2 := by
    simp only [centered]
    ring
  have hc : Integrable (fun x => 2 * mean μ f * f x) μ :=
    (integrable μ hf).const_mul (2 * mean μ f)
  have hsub : Integrable (fun x => f x ^ 2 - 2 * mean μ f * f x) μ :=
    hf.integrable_sq.sub hc
  simp_rw [variance, heq]
  rw [integral_add hsub (integrable_const _), integral_sub hf.integrable_sq hc,
    integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change (∫ x, f x ^ 2 ∂μ) - 2 * mean μ f * mean μ f + (mean μ f) ^ 2 = _
  ring

/-- Variance vanishes exactly when the observable equals its actual mean almost everywhere. -/
theorem variance_eq_zero_iff (hf : MemLp f 2 μ) :
    variance μ f = 0 ↔ ∀ᵐ x ∂μ, f x = mean μ f := by
  rw [variance, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    (integrable_centered_sq μ hf)]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    filter_upwards [h] with x hx
    simp [centered, hx]

/-- Positive variance means precisely that the observable is not almost everywhere constant
at its actual mean. -/
theorem variance_pos_iff (hf : MemLp f 2 μ) :
    0 < variance μ f ↔ ¬ (∀ᵐ x ∂μ, f x = mean μ f) := by
  rw [← variance_eq_zero_iff μ hf]
  exact lt_iff_le_and_ne.trans (by simp [variance_nonneg μ f, ne_comm])

end FoliationQM.CenteredL2Variance
