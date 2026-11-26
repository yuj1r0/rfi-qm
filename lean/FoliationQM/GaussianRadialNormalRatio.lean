module

public import FoliationQM.GaussianRadialHeatLoss
public import FoliationQM.GaussianNormalOrientation

/-!
# Strict radial decrease of the Gaussian normal-to-amplitude ratio

For the initial positive-frequency rest packet of v13 Theorem 5.8(ii),
the quotient of the normal coefficient by the positive amplitude depends
on the spatial radius. The proper-time loss is strictly increasing in the
squared radius because its integrand grows at every positive proper time.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianRadialNormalRatio

open Set MeasureTheory LorentzCoordinates GaussianNormalOrientation GaussianCauchySlice
open GaussianPositiveFrequencyPacket GaussianRadialHeatLoss GaussianHeatProfile
open GaussianProperTimeMultiplier
open scoped ContDiff

/-- The normal coefficient divided by the amplitude along a signed spatial axis. -/
def ratio (μ σ r : ℝ) : ℝ := normalCoefficient μ σ (axis r) / amplitude σ (axis r)

/-- At the rest center the initial amplitude is one. -/
theorem ratio_zero (μ σ : ℝ) : ratio μ σ 0 = normalCoefficient μ σ 0 := by
  simp [ratio, axis, amplitude, speedSq_eq_sum]

/-- The center-subtracted proper-time representation at physical radius `r`. -/
theorem ratio_eq {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (r : ℝ) :
    ratio μ σ r = normalCoefficient μ σ 0 - (1/(2*Real.sqrt Real.pi)) *
      ∫ t in Ioi (0 : ℝ), kernel μ t * lossFactor (σ^2) t (r^2) := by
  have hr : speedSq (axis r) = r^2 := by simp [axis, speedSq_eq_sum]
  simpa only [ratio, hr] using normal_ratio_eq_center_sub_loss hμ hσ (axis r)

/-- The axis quotient represents the normal-to-amplitude ratio at every spatial point. -/
theorem normal_div_amplitude_eq_ratio {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (y : Spatial) :
    normalCoefficient μ σ y / amplitude σ y = ratio μ σ (euclideanSpeed y) := by
  rw [normal_ratio_eq_center_sub_loss hμ hσ, ratio_eq hμ hσ, euclideanSpeed_sq]

/-- The signed-axis quotient is smooth because the amplitude is everywhere positive. -/
theorem smooth_ratio (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : ContDiff ℝ ∞ (ratio μ σ) := by
  have haxis : ContDiff ℝ ∞ axis := contDiff_single (fun _ : Fin 3 => ℝ) ∞ 0
  exact ((smooth_normalCoefficient μ hσ).comp haxis).div ((smooth_amplitude σ).comp haxis)
    fun r => (amplitude_pos σ (axis r)).ne'

/-- The ratio varies continuously with the signed axis coordinate. -/
theorem continuous_ratio (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : Continuous (ratio μ σ) :=
  (smooth_ratio μ hσ).continuous

/-- The integrated heat loss increases strictly with the squared spatial radius. -/
theorem integral_loss_strictMonoOn {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    StrictMonoOn (fun u : ℝ => ∫ t in Ioi (0 : ℝ), kernel μ t * lossFactor a t u) (Ici 0) := by
  intro u hu v hv huv
  let f (t : ℝ) := kernel μ t * lossFactor a t v - kernel μ t * lossFactor a t u
  have hpos (t : ℝ) (ht : 0 < t) : 0 < f t :=
    sub_pos.mpr (mul_lt_mul_of_pos_left (lossFactor_strictMono ha ht huv) (kernel_pos μ ht))
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using (hpos t ht).le
  have hs : Function.support f ∩ Ioi 0 = Ioi 0 := inter_eq_right.mpr fun t ht => (hpos t ht).ne'
  have hdiff : IntegrableOn f (Ioi 0) := (integrable_loss hμ ha hv).sub (integrable_loss hμ ha hu)
  have h : 0 < ∫ t in Ioi (0 : ℝ), f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hn hdiff, hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  simpa only [f, integral_sub (integrable_loss hμ ha hv) (integrable_loss hμ ha hu), sub_pos] using h

/-- The normal-to-amplitude ratio decreases strictly with nonnegative physical radius. -/
theorem ratio_strictAntiOn {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    StrictAntiOn (ratio μ σ) (Ici 0) := by
  intro r hr s hs hrs
  rw [ratio_eq hμ hσ s, ratio_eq hμ hσ r]
  apply sub_lt_sub_left
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact integral_loss_strictMonoOn hμ (sq_pos_of_pos hσ) (sq_nonneg r) (sq_nonneg s)
    ((sq_lt_sq₀ hr hs).mpr hrs)

end FoliationQM.GaussianRadialNormalRatio
