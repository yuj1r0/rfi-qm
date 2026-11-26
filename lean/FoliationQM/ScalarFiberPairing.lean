module

public import FoliationQM.HilbertFiberObservables
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Scalar integral formulas for the Born marginal and its current

In v13's marginal continuity equation the remote variable is integrated
over its full spatial volume. For square-integrable scalar representatives,
their complex overlap is a Bochner integral with the bra conjugated.
Representing the directional derivative of a retained spatial section in
the same L² space identifies its Hilbert current with the scalar formula.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ScalarFiberPairing

open MeasureTheory HilbertFiberObservables

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {ψ φ : Y → ℂ}

private theorem pair_ae (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) :
    (fun y => inner ℂ (hψ.toLp ψ y) (hφ.toLp φ y)) =ᵐ[μ]
      fun y => star (ψ y) * φ y := by
  filter_upwards [hψ.coeFn_toLp, hφ.coeFn_toLp] with y hy hz
  rw [hy, hz]
  exact RCLike.inner_apply' _ _

/-- Products of two square-integrable scalar representatives are absolutely integrable. -/
theorem integrable_pair (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) :
    Integrable (fun y => star (ψ y) * φ y) μ :=
  (L2.integrable_inner (𝕜 := ℂ) (hψ.toLp ψ) (hφ.toLp φ)).congr (pair_ae hψ hφ)

/-- The L² pairing of the representative classes is the scalar overlap integral. -/
theorem inner_toLp (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) :
    inner ℂ (hψ.toLp ψ) (hφ.toLp φ) = ∫ y, star (ψ y) * φ y ∂μ :=
  (L2.inner_def ..).trans (integral_congr_ae (pair_ae hψ hφ))

/-- A square-integrable representative has integrable Born density. -/
theorem integrable_born (hψ : MemLp ψ 2 μ) : Integrable (fun y => ‖ψ y‖ ^ 2) μ :=
  hψ.norm.integrable_sq

/-- The squared norm of an L² fiber is its integrated scalar Born density. -/
theorem norm_sq_toLp (hψ : MemLp ψ 2 μ) :
    ‖hψ.toLp ψ‖ ^ 2 = ∫ y, ‖ψ y‖ ^ 2 ∂μ := by
  calc
    _ = (inner ℂ (hψ.toLp ψ) (hψ.toLp ψ)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∫ y, star (ψ y) * ψ y ∂μ).re := congrArg Complex.re (inner_toLp hψ hψ)
    _ = ∫ y, (star (ψ y) * ψ y).re ∂μ := (integral_re (integrable_pair hψ hψ)).symm
    _ = _ := by simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Cauchy–Schwarz bounds the size of the scalar overlap by the two L² norms. -/
theorem norm_integral_pair_le (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) :
    ‖∫ y, star (ψ y) * φ y ∂μ‖ ≤ ‖hψ.toLp ψ‖ * ‖hφ.toLp φ‖ := by
  rw [← inner_toLp hψ hφ]
  exact norm_inner_le_norm _ _

/-- The scalar current integrand, including its physical coefficient, is in L¹. -/
theorem integrable_current (hbar m : ℝ) (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) :
    Integrable (fun y => (hbar / m) * (star (ψ y) * φ y).im) μ :=
  (integrable_pair hψ hφ).im.const_mul _

/-- The imaginary part of the L² pairing is the integral of the imaginary
part of the scalar overlap. -/
theorem im_inner_toLp (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) :
    (inner ℂ (hψ.toLp ψ) (hφ.toLp φ)).im = ∫ y, (star (ψ y) * φ y).im ∂μ := by
  rw [inner_toLp hψ hφ]
  exact (integral_im (integrable_pair hψ hφ)).symm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Substituting scalar representatives into the Hilbert marginal current gives
the integral in v13, with the spatial derivative represented in L². -/
theorem current_eq_integral (hbar m : ℝ) (F : X → Lp ℂ 2 μ) (x v : X)
    (hψ : MemLp ψ 2 μ) (hφ : MemLp φ 2 μ) (hx : F x = hψ.toLp ψ)
    (hD : fderiv ℝ F x v = hφ.toLp φ) :
    current hbar m F x v = (hbar / m) * ∫ y, (star (ψ y) * φ y).im ∂μ := by
  rw [current, hx, hD, im_inner_toLp hψ hφ]

/-- The magnitude of the current is bounded by the L² norms of the state and
its represented spatial derivative, with the source coefficient in absolute value. -/
theorem abs_current_le (hbar m : ℝ) (F : X → Lp ℂ 2 μ) (x v : X) :
    |current hbar m F x v| ≤ |hbar / m| * (‖F x‖ * ‖fderiv ℝ F x v‖) := by
  rw [current, abs_mul]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _))
    (abs_nonneg _)

end FoliationQM.ScalarFiberPairing
