module

public import FoliationQM.TwoParticleMarginals
public import FoliationQM.GaussianSliceMoments
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Group.Integral

/-!
# A correlated Gaussian density on two laboratory slices

Independent standard Gaussian vectors X and Z give the joint positions
(X, X+Z). The conditional distribution of the second position is centered at
the first position, while the second marginal has coordinate variance two.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoParticleGaussianModel

open MeasureTheory LorentzCoordinates GaussianSliceMoments TwoParticleMarginals
open scoped ContDiff

/-- The Gaussian of coordinate standard deviation σ divided by its spatial integral. -/
def gaussian (σ : ℝ) (x : Spatial) : ℝ := density σ x / normalization σ

/-- The normalized Gaussian density is positive at every point for positive width. -/
theorem gaussian_pos {σ : ℝ} (hσ : 0 < σ) (x : Spatial) : 0 < gaussian σ x :=
  div_pos (density_pos σ x) (normalization_pos hσ)

/-- The normalized spatial Gaussian is smooth. -/
theorem gaussian_smooth (σ : ℝ) : ContDiff ℝ ∞ (gaussian σ) :=
  ((smooth_density σ).of_le le_top).div_const _

/-- A Gaussian with positive width has finite spatial mass. -/
theorem gaussian_integrable {σ : ℝ} (hσ : 0 < σ) : Integrable (gaussian σ) :=
  (integrable_density hσ).div_const _

/-- The spatial integral of the normalized Gaussian is one. -/
theorem integral_gaussian {σ : ℝ} (hσ : 0 < σ) : (∫ x, gaussian σ x) = 1 := by
  unfold gaussian
  rw [integral_div, integral_density hσ, div_self (normalization_pos hσ).ne']

/-- Joint density of the first position and its sum with independent Gaussian noise. -/
def joint (z : Spatial × Spatial) : ℝ := gaussian 1 z.1 * gaussian 1 (z.2 - z.1)

/-- The joint density is strictly positive on the entire product. -/
theorem joint_pos (z : Spatial × Spatial) : 0 < joint z :=
  mul_pos (gaussian_pos one_pos _) (gaussian_pos one_pos _)

/-- The sheared Gaussian is smooth as a function of both positions. -/
theorem joint_smooth : ContDiff ℝ ∞ joint :=
  ((gaussian_smooth 1).comp contDiff_fst).mul ((gaussian_smooth 1).comp (contDiff_snd.sub contDiff_fst))

/-- The joint density is integrable under six-dimensional product Lebesgue volume. -/
theorem joint_integrable : Integrable joint (volume.prod volume) :=
  (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable
    ((gaussian_integrable one_pos).mul_prod (gaussian_integrable one_pos))

/-- Every fixed first position has an integrable fiber in the second position. -/
theorem integrable_at_first (x : Spatial) : Integrable (fun y => joint (x, y)) :=
  ((gaussian_integrable one_pos).comp_sub_right x).const_mul (gaussian 1 x)

/-- The first marginal is the normalized Gaussian of unit coordinate variance. -/
theorem left_eq : left joint = gaussian 1 := by
  funext x
  change (∫ y, gaussian 1 x * gaussian 1 (y - x)) = gaussian 1 x
  rw [integral_const_mul, integral_sub_right_eq_self, integral_gaussian one_pos, mul_one]

/-- The joint distribution has total mass one. -/
theorem integral_joint : (∫ z, joint z ∂volume.prod volume) = 1 := by
  rw [integral_prod joint joint_integrable]
  change (∫ x, left joint x) = 1
  rw [left_eq, integral_gaussian one_pos]

/-- Given the first position, the second is a unit-width Gaussian centered there. -/
theorem conditional_eq (x y : Spatial) : conditional joint x y = gaussian 1 (y - x) := by
  unfold conditional
  rw [left_eq]
  change (gaussian 1 x * gaussian 1 (y - x)) / gaussian 1 x = _
  field_simp [(gaussian_pos one_pos x).ne']

private theorem normalization_product : normalization 1 * normalization 1 =
    normalization (Real.sqrt 2) * normalization (Real.sqrt (1/2)) := by
  unfold normalization
  rw [← mul_pow, ← mul_pow, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 2
  rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  ring

/-- Completing the square gives the reverse Gaussian factorization, with
first-position conditional mean y/2 and coordinate variance 1/2. -/
theorem joint_complete_square (x y : Spatial) : joint (x, y) =
    gaussian (Real.sqrt 2) y * gaussian (Real.sqrt (1/2)) (x - (1/2 : ℝ) • y) := by
  simp only [joint, gaussian, div_mul_div_comm, normalization_product]
  congr 1
  simp only [density, ← Real.exp_add, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  simp only [speedSq, spatialDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every fixed second position has an integrable fiber in the first position. -/
theorem integrable_at_second (y : Spatial) : Integrable (fun x => joint (x, y)) := by
  simp only [joint_complete_square]
  exact ((gaussian_integrable (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1/2))).comp_sub_right _).const_mul _

/-- The second marginal is the normalized Gaussian of coordinate variance two. -/
theorem right_eq : right joint = gaussian (Real.sqrt 2) := by
  funext y
  unfold right
  simp only [joint_complete_square, integral_const_mul, integral_sub_right_eq_self,
    integral_gaussian (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1/2)), mul_one]

/-- The joint density differs from the product of its two marginals. -/
theorem not_factorized : ¬ ∀ x y, joint (x, y) = left joint x * right joint y := by
  intro he
  have hc (x : Spatial) : gaussian 1 (0 - x) = right joint 0 := by
    apply mul_left_cancel₀ (gaussian_pos one_pos x).ne'
    simpa only [left_eq, joint] using he x 0
  have h := (hc (fun _ => 1)).trans (hc 0).symm
  simp only [gaussian, div_left_inj' (normalization_pos (σ := 1) one_pos).ne', density,
    Real.exp_eq_exp, speedSq, spatialDot, Pi.sub_apply, Pi.zero_apply] at h
  norm_num at h

end FoliationQM.TwoParticleGaussianModel
