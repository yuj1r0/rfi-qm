module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Actual real L² pairings and quadratic residuals

Sources: v13 eq:cramer_rao and thm:uncertainty. Kind C, analytic core.
Every integral below is the actual Bochner integral. The L² hypotheses supply
genuine square and product integrability. The statements do not identify an
arbitrary observable with a density score or a weak derivative.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RealL2Pairing
open MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

/-- The genuine L² inner product agrees with the integral of the original representatives. -/
theorem inner_toLp (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- Cauchy–Schwarz for actual real integrals of two genuinely square-integrable functions. -/
theorem integral_mul_sq_le (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [inner_toLp, pow_two] using h

/-- A genuine square integral vanishes exactly when its original representative vanishes almost everywhere. -/
theorem integral_sq_eq_zero_iff (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = 0 ↔ f =ᵐ[μ] 0 := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf.integrable_sq]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact sq_eq_zero_iff.mp hx
  · intro h
    filter_upwards [h] with x hx
    simp only [hx, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0)]

/-- A nonzero actual pairing forces the first square integral to be strictly positive. -/
theorem integral_sq_pos_of_pairing_ne_zero (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hpair : (∫ x, f x * g x ∂μ) ≠ 0) :
    0 < ∫ x, f x ^ 2 ∂μ := by
  have hnon : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (f x)
  have hcs := integral_mul_sq_le hf hg
  have hsq := sq_pos_of_ne_zero hpair
  by_contra h
  have hz : (∫ x, f x ^ 2 ∂μ) = 0 := le_antisymm (le_of_not_gt h) hnon
  rw [hz, zero_mul] at hcs
  exact (not_le_of_gt hsq) hcs

/-- A true square-integrable affine combination has the exact quadratic integral, with an integrable cross term. -/
theorem integral_add_mul_sq (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (c : ℝ) :
    (∫ x, (f x + c * g x) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) + 2 * c * (∫ x, f x * g x ∂μ) +
        c ^ 2 * (∫ x, g x ^ 2 ∂μ) := by
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hsum : Integrable (fun x => f x ^ 2 + 2 * c * (f x * g x)) μ := by
    simpa only [Pi.add_apply] using! hf.integrable_sq.add (hfg.const_mul (2 * c))
  have he : (fun x => (f x + c * g x) ^ 2) =
      (fun x => (f x ^ 2 + 2 * c * (f x * g x)) + c ^ 2 * g x ^ 2) := by
    funext x
    ring
  rw [he, integral_add hsum (hg.integrable_sq.const_mul (c ^ 2)),
    integral_add hf.integrable_sq (hfg.const_mul (2 * c)),
    integral_const_mul, integral_const_mul]

end FoliationQM.RealL2Pairing
