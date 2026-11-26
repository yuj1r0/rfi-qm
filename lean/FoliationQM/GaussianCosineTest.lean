module

public import FoliationQM.GaussianSpatialFourier

/-!
# Testing the sign of the Gaussian normal coefficient

For the free Gaussian clause following v13 `eq:dilatation_coercivity_bound`,
a future-oriented normal datum on the initial slice requires a nonnegative
normal coefficient. A nonnegative trigonometric polynomial tests that sign
using three values of the angular cosine transform on the same spatial axis.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCosineTest
open MeasureTheory LorentzCoordinates

/-- Spatial cosine transform of a real coefficient with angular wave number `u`. -/
def cosineTransform (f : Spatial → ℝ) (u : Spatial) : ℝ :=
  ∫ x, f x * Real.cos (spatialDot x u)

/-- Three-frequency difference measured at zero, `u`, and `2u`. -/
def difference (f : Spatial → ℝ) (u : Spatial) : ℝ :=
  3 * cosineTransform f 0 - 4 * cosineTransform f u + cosineTransform f ((2 : ℝ) • u)

/-- Trigonometric test on the physical spatial slice. -/
def kernel (θ : ℝ) : ℝ := 3 - 4 * Real.cos θ + Real.cos (2 * θ)

/-- The three-term test is exactly a nonnegative square. -/
theorem kernel_eq_square (θ : ℝ) : kernel θ = 2 * (1 - Real.cos θ)^2 := by
  rw [kernel, Real.cos_two_mul]
  ring

/-- The test is bounded between zero and eight for every real angle. -/
theorem kernel_bounds (θ : ℝ) : 0 ≤ kernel θ ∧ kernel θ ≤ 8 := by
  constructor
  · rw [kernel_eq_square]; positivity
  · unfold kernel
    linarith [Real.neg_one_le_cos θ, Real.cos_le_one (2*θ)]

/-- Multiplication by the cosine character preserves spatial integrability. -/
theorem integrable_cosine {f : Spatial → ℝ} (hf : Integrable f) (u : Spatial) :
    Integrable (fun x => f x * Real.cos (spatialDot x u)) := by
  exact hf.mul_bdd (by unfold spatialDot; fun_prop)
    (ae_of_all _ fun x => (Real.abs_cos_le_one (spatialDot x u)))

/-- The polynomial test times an integrable real spatial coefficient is integrable. -/
theorem integrable_test {f : Spatial → ℝ} (hf : Integrable f) (u : Spatial) :
    Integrable (fun x => f x * kernel (spatialDot x u)) := by
  refine hf.mul_bdd (c := 8) (by unfold kernel spatialDot; fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_bounds _).1]
  exact (kernel_bounds _).2

/-- At zero wave number the cosine transform is the total integral of the coefficient. -/
theorem cosineTransform_zero (f : Spatial → ℝ) : cosineTransform f 0 = ∫ x, f x := by
  simp [cosineTransform, spatialDot]

/-- On the full spatial slice the Fourier difference is the integral of the coefficient
against the nonnegative test, with every term integrable. -/
theorem difference_eq_integral {f : Spatial → ℝ} (hf : Integrable f) (u : Spatial) :
    difference f u = ∫ x, f x * kernel (spatialDot x u) := by
  have he (x : Spatial) : f x * kernel (spatialDot x u) =
      (3 * f x - 4 * (f x * Real.cos (spatialDot x u))) +
       f x * Real.cos (spatialDot x ((2 : ℝ) • u)) := by
    rw [spatialDot_smul_right]; unfold kernel; ring
  have hi : Integrable (fun x => 3 * f x - 4 * (f x * Real.cos (spatialDot x u))) :=
    (hf.const_mul 3).sub ((integrable_cosine hf u).const_mul 4)
  rw [funext he, integral_add hi
    (integrable_cosine hf ((2 : ℝ) • u)), integral_sub (hf.const_mul 3) ((integrable_cosine hf u).const_mul 4),
    integral_const_mul, integral_const_mul, difference, cosineTransform_zero]
  rfl

/-- Nonnegativity almost everywhere forces the three-frequency difference to be nonnegative. -/
theorem difference_nonneg {f : Spatial → ℝ} (hf : Integrable f)
    (hp : ∀ᵐ x ∂volume, 0 ≤ f x) (u : Spatial) : 0 ≤ difference f u := by
  rw [difference_eq_integral hf]
  exact integral_nonneg_of_ae (hp.mono fun x hx => mul_nonneg hx (kernel_bounds _).1)

/-- A strict spectral failure forces the negative set to have positive spatial measure. -/
theorem volume_neg_pos_of_difference_neg {f : Spatial → ℝ} (hf : Integrable f)
    {u : Spatial} (hneg : difference f u < 0) : 0 < volume {x | f x < 0} := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hp : ∀ᵐ x ∂volume, 0 ≤ f x := by
    rw [ae_iff]; simpa only [not_le] using hz
  exact (not_lt_of_ge (difference_nonneg hf hp u)) hneg

/-- A negative three-frequency difference rules out a coefficient nonnegative at every point. -/
theorem exists_neg_of_difference_neg {f : Spatial → ℝ} (hf : Integrable f)
    {u : Spatial} (hneg : difference f u < 0) : ∃ x, f x < 0 := by
  by_contra! hp
  exact (not_lt_of_ge (difference_nonneg hf (ae_of_all _ hp) u)) hneg

end FoliationQM.GaussianCosineTest
