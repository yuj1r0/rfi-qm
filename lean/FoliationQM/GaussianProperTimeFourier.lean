module

public import FoliationQM.GaussianProperTimeMultiplier
public import FoliationQM.GaussianPositiveFrequencyPacket
public import FoliationQM.GaussianCosineTest
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proper-time heat representation of the Gaussian normal Fourier datum

In the positive-frequency Gaussian used to test v13 line 767, the actual
normal coefficient is a spatial angular transform of the massive rate.
The proper-time representation of that rate gives a difference of two
explicit heat profiles. Its cancellation at small positive proper time
supplies an integrable bound before the two integrations are interchanged.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianProperTimeFourier

open LorentzCoordinates GaussianKGMode GaussianSpatialFourier GaussianProperTimeMultiplier
open GaussianPositiveFrequencyPacket Set MeasureTheory

/-- Unnormalised three-dimensional heat profile at squared spatial radius u. -/
def heatProfile (a u : ℝ) : ℝ := mass a * Real.exp (-u/(4*a))

/-- The joint proper-time and angular-frequency integrand for the massive
correction to the unnormalised initial normal coefficient. -/
def joint (μ a : ℝ) (y : Spatial) (t : ℝ) (k : Spatial) : ℝ :=
  Real.cos (spatialDot k y) * weight a k * (kernel μ t * (1 - Real.exp (-(speedSq k*t))))

/-- The cancelled integrand is bounded by the product of an integrable
time factor and the spatial Gaussian second moment, uniformly in position. -/
theorem joint_bound (μ a : ℝ) (y : Spatial) {t : ℝ} (ht : 0 < t) (k : Spatial) :
    ‖joint μ a y t k‖ ≤ (t * kernel μ t) * (speedSq k * weight a k) := by
  obtain ⟨hl, hu⟩ := cancelled_bounds μ (speedSq_nonneg k) ht
  have hw : 0 < weight a k := Real.exp_pos _
  rw [joint, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, abs_of_nonneg hl]
  calc
    _ ≤ (1 * weight a k) * (speedSq k * (t * kernel μ t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hw.le) hu hl (by positivity)
    _ = _ := by ring

/-- The product majorant has finite integral over positive proper time and
all spatial frequencies for every positive mass and Gaussian parameter. -/
theorem integrable_majorant {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Integrable (fun z : ℝ × Spatial => (z.1 * kernel μ z.1) * (speedSq z.2 * weight a z.2))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hk : Integrable (fun k : Spatial => speedSq k * weight a k) := by
    simpa only [rate_sq, zero_pow (by decide : 2 ≠ 0), zero_add] using
      GaussianMassShellMoments.integrable_rate_pow_weight ha 0 2
  exact (integrable_time_kernel hμ).mul_prod hk

/-- The full joint integrand is absolutely integrable, legitimating Fubini
for the Fourier and proper-time integrals on their unbounded domains. -/
theorem integrable_joint {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (y : Spatial) :
    Integrable (Function.uncurry (joint μ a y)) ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_majorant hμ ha).mono'
  · apply Measurable.aestronglyMeasurable
    unfold Function.uncurry joint kernel weight speedSq spatialDot
    fun_prop
  · have ht : ∀ᵐ z : ℝ × Spatial ∂(volume.restrict (Ioi 0)).prod volume, 0 < z.1 :=
      Measure.quasiMeasurePreserving_fst.ae (self_mem_ae_restrict measurableSet_Ioi)
    filter_upwards [ht] with z hz
    exact joint_bound μ a y hz z.2

private theorem integrable_cosine_weight {a : ℝ} (ha : 0 < a) (y : Spatial) :
    Integrable (fun k => Real.cos (spatialDot k y) * weight a k) := by
  simpa only [mul_comm] using GaussianCosineTest.integrable_cosine (integrable_weight ha) y

private theorem weight_times_heat (a t : ℝ) (k : Spatial) :
    weight a k * Real.exp (-(speedSq k*t)) = weight (a+t) k := by
  unfold weight
  rw [← Real.exp_add]
  congr 1
  ring

/-- Integrating out the angular frequency gives the difference between the
Gaussian heat profiles at parameters a and a+t at the same spatial point. -/
theorem spatial_integral (μ : ℝ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (y : Spatial) :
    (∫ k, joint μ a y t k) =
      kernel μ t * (heatProfile a (speedSq y) - heatProfile (a+t) (speedSq y)) := by
  have h (k : Spatial) : joint μ a y t k = kernel μ t *
      (Real.cos (spatialDot k y) * weight a k - Real.cos (spatialDot k y) * weight (a+t) k) := by
    rw [joint, ← weight_times_heat]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_sub (integrable_cosine_weight ha y)
    (integrable_cosine_weight (add_pos ha ht) y), integral_cosine_weight ha,
    integral_cosine_weight (add_pos ha ht)]
  rfl

/-- The proper-time heat difference itself is integrable at each spatial
point, including the cancellation at t=0 in the singular kernel. -/
theorem integrable_heat_difference {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (y : Spatial) :
    IntegrableOn (fun t => kernel μ t *
      (heatProfile a (speedSq y) - heatProfile (a+t) (speedSq y))) (Ioi 0) := by
  apply (integrable_joint hμ ha y).integral_prod_left.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact spatial_integral μ ha ht y

/-- The unnormalised normal angular integral is the rest mass term plus
the proper-time integral of the explicit heat difference. -/
theorem integral_rate_weight {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (y : Spatial) :
    (∫ k, Real.cos (spatialDot k y) * (rate μ k * weight a k)) =
      μ * heatProfile a (speedSq y) + (1/(2*Real.sqrt Real.pi)) *
        ∫ t in Ioi 0, kernel μ t * (heatProfile a (speedSq y) - heatProfile (a+t) (speedSq y)) := by
  let C := 1/(2*Real.sqrt Real.pi)
  have hj := integrable_joint hμ ha y
  have he (k : Spatial) : Real.cos (spatialDot k y) * (rate μ k * weight a k) =
      μ * (Real.cos (spatialDot k y) * weight a k) + C * ∫ t in Ioi 0, joint μ a y t k := by
    simp_rw [joint, integral_const_mul]
    rw [rate, sqrt_eq_integral hμ (speedSq_nonneg k)]
    dsimp only [C]
    ring
  have hinner : Integrable (fun k => ∫ t in Ioi 0, joint μ a y t k) := hj.integral_prod_right
  simp_rw [he]
  rw [integral_add ((integrable_cosine_weight ha y).const_mul μ) (hinner.const_mul C),
    integral_const_mul, integral_const_mul, integral_cosine_weight ha, ← integral_integral_swap hj]
  congr 2
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact spatial_integral μ ha ht y

/-- The actual normalized normal coefficient of the positive-frequency packet equals
μ times the initial amplitude plus its normalized proper-time heat difference. -/
theorem normal_eq_heat_difference {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (y : Spatial) :
    normalCoefficient μ σ y = μ * GaussianCauchySlice.amplitude σ y +
      ((1/(2*Real.sqrt Real.pi)) / mass (σ^2)) *
        ∫ t in Ioi 0, kernel μ t * (heatProfile (σ^2) (speedSq y) -
          heatProfile (σ^2+t) (speedSq y)) := by
  have ha := sq_pos_of_pos hσ
  have hm := (mass_pos ha).ne'
  rw [normalCoefficient, integral_rate_weight hμ ha, heatProfile, GaussianCauchySlice.amplitude]
  field_simp [hm]

end FoliationQM.GaussianProperTimeFourier
