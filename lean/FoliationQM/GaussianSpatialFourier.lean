module

public import FoliationQM.GaussianCauchySlice
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourier reconstruction of the three-dimensional Gaussian Cauchy profile

The free Gaussian in v13, lines 762–767, can be specified by its initial
angular wave-number spectrum. We integrate against Lebesgue volume on the
same three spatial coordinates as the observer slice. The Fourier convention
is exp(i k·y), with no cycle-to-radian factor in k.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianSpatialFourier

open LorentzCoordinates MeasureTheory

/-- Real spectral weight with inverse variance parameter a. -/
def weight (a : ℝ) (k : Spatial) : ℝ := Real.exp (-a * speedSq k)

/-- Total mass of the three-dimensional Gaussian spectrum. -/
def mass (a : ℝ) : ℝ := (Real.sqrt (Real.pi / a)) ^ 3

/-- The angular Fourier character for the positive spatial sign convention. -/
def character (y k : Spatial) : ℂ := Complex.exp (Complex.I * (spatialDot k y : ℝ))

/-- The spectral mass is positive for every positive decay parameter. -/
theorem mass_pos {a : ℝ} (ha : 0 < a) : 0 < mass a := by
  unfold mass
  positivity

private theorem weight_prod (a : ℝ) (k : Spatial) :
    weight a k = ∏ i, Real.exp (-a * (k i)^2) := by
  rw [Fin.prod_univ_three, ← Real.exp_add, ← Real.exp_add]
  unfold weight
  rw [speedSq_eq_sum]
  congr 1
  ring

/-- Gaussian decay makes the spectral weight integrable on the whole wave-number space. -/
theorem integrable_weight {a : ℝ} (ha : 0 < a) : Integrable (weight a) := by
  rw [funext (weight_prod a)]
  exact Integrable.fintype_prod (μ := fun _ => volume) (fun _ => integrable_exp_neg_mul_sq ha)

/-- The integral of the real spectral weight is its positive Gaussian mass. -/
theorem integral_weight {a : ℝ} (_ha : 0 < a) : (∫ k, weight a k) = mass a := by
  rw [funext (weight_prod a), integral_fintype_prod_volume_eq_prod (fun (_ : Fin 3) (u : ℝ) => Real.exp (-a * u^2)), Fin.prod_univ_three]
  simp only [integral_gaussian, mass]
  ring

private theorem complex_factor (a t : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, Complex.exp (Complex.I * t * u) * Complex.exp (-(a : ℂ) * u^2)) =
      (Real.sqrt (Real.pi/a) : ℂ) * (Real.exp (-(t^2) / (4*a)) : ℂ) := by
  rw [fourierIntegral_gaussian (show 0 < (a : ℂ).re from ha)]
  have hc : ((Real.sqrt (Real.pi/a)) : ℂ) = (Real.pi / (a : ℂ)) ^ (1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le ha.le)]
    push_cast
    rfl
  rw [← hc, Complex.ofReal_exp]
  push_cast
  rfl

private theorem product_integrand (a : ℝ) (y k : Spatial) :
    character y k * (weight a k : ℂ) =
    ∏ i, Complex.exp (Complex.I * y i * k i) * Complex.exp (-(a : ℂ) * k i ^ 2) := by
  rw [Fin.prod_univ_three]
  unfold character weight spatialDot
  rw [Complex.ofReal_exp, speedSq_eq_sum]
  simp only [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The actual inverse angular Fourier integral of the Gaussian spectrum factorizes
on ℝ³, giving the exact Gaussian spatial amplitude and its normalization. -/
theorem integral_character_weight {a : ℝ} (ha : 0 < a) (y : Spatial) :
    (∫ k, character y k * (weight a k : ℂ)) =
      (mass a : ℂ) * (Real.exp (-speedSq y / (4*a)) : ℂ) := by
  rw [funext (product_integrand a y), integral_fintype_prod_volume_eq_prod (fun (i : Fin 3) (u : ℝ) =>
    Complex.exp (Complex.I * y i * u) * Complex.exp (-(a : ℂ) * u^2)), Fin.prod_univ_three]
  simp only [complex_factor a _ ha, speedSq_eq_sum, mass]
  norm_cast
  have h := Real.exp_add (-(y 0 ^ 2)/(4*a)) (-(y 1 ^ 2)/(4*a))
  have h' := Real.exp_add (-(y 0 ^ 2)/(4*a) + -(y 1 ^ 2)/(4*a)) (-(y 2 ^ 2)/(4*a))
  rw [show -(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)/(4*a) =
    (-(y 0 ^ 2)/(4*a) + -(y 1 ^ 2)/(4*a)) + -(y 2 ^ 2)/(4*a) by ring, h', h]
  ring

/-- The unit-modulus character preserves absolute integrability of the spectral weight. -/
theorem integrable_character_weight {a : ℝ} (ha : 0 < a) (y : Spatial) :
    Integrable (fun k => character y k * (weight a k : ℂ)) := by
  apply (integrable_weight ha).mono' (by unfold character weight speedSq spatialDot; fun_prop)
  refine ae_of_all _ fun k => ?_
  simp only [norm_mul, character, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_pos (Real.exp_pos _ : 0 < weight a k)).le

/-- The cosine transform of the real Gaussian has the same positive normalization. -/
theorem integral_cosine_weight {a : ℝ} (ha : 0 < a) (y : Spatial) :
    (∫ k, Real.cos (spatialDot k y) * weight a k) = mass a * Real.exp (-speedSq y / (4*a)) := by
  have he := integral_re (integrable_character_weight ha y)
  rw [integral_character_weight ha y] at he
  simpa only [RCLike.re_eq_complex_re, character, Complex.mul_re, mul_comm Complex.I,
    Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using he

/-- Dividing by total spectral mass recovers the exact Cauchy amplitude used in the
physical slice theorems, for every positive width. -/
theorem reconstruct_amplitude {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    (∫ k, character y k * (weight (σ^2) k : ℂ)) / (mass (σ^2) : ℂ) =
      (GaussianCauchySlice.amplitude σ y : ℂ) := by
  have ha := sq_pos_of_pos hσ
  rw [integral_character_weight ha]
  unfold GaussianCauchySlice.amplitude
  have hm : (mass (σ^2) : ℂ) ≠ 0 := by exact_mod_cast (mass_pos ha).ne'
  field_simp

end FoliationQM.GaussianSpatialFourier
