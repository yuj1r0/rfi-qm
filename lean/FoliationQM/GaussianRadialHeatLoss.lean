module

public import FoliationQM.GaussianHeatProfile
public import FoliationQM.GaussianProperTimeFourier

/-!
# Center subtraction for the Gaussian normal coefficient

For the initial positive-frequency rest packet in v13 Theorem 5.8(ii),
the product of the massive proper-time kernel and two broadened Gaussian
profiles is integrated as a difference. Subtracting the value at the
center after division by the positive amplitude gives a radial loss
with a finite Lebesgue integral for every nonnegative squared radius.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianRadialHeatLoss

open Set MeasureTheory LorentzCoordinates GaussianSpatialFourier GaussianProperTimeMultiplier
open GaussianHeatProfile GaussianProperTimeFourier GaussianCauchySlice GaussianPositiveFrequencyPacket

private abbrev weightedDifference (μ a u t : ℝ) : ℝ :=
  kernel μ t * (heatProfile a u - heatProfile (a+t) u)

private theorem integrable_difference {μ a u : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hu : 0 ≤ u) :
    IntegrableOn (weightedDifference μ a u) (Ioi 0) := by
  let y : Spatial := Pi.single 0 (Real.sqrt u)
  have hy : speedSq y = u := by simp [speedSq_eq_sum, y, Real.sq_sqrt hu]
  simpa only [hy] using integrable_heat_difference hμ ha y

private theorem centered_identity (μ : ℝ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (u : ℝ) :
    (weightedDifference μ a 0 t - weightedDifference μ a u t / Real.exp (-u/(4*a))) / mass a =
      kernel μ t * lossFactor a t u := by
  have hh : (heatProfile a 0 - heatProfile (a+t) 0) -
      (heatProfile a u - heatProfile (a+t) u)/Real.exp (-u/(4*a)) = mass a * lossFactor a t u := by
    simpa [heatProfile] using center_difference ha ht u
  calc
    _ = kernel μ t * ((heatProfile a 0 - heatProfile (a+t) 0) -
      (heatProfile a u - heatProfile (a+t) u)/Real.exp (-u/(4*a))) / mass a := by
      unfold weightedDifference
      ring
    _ = _ := by rw [hh]; field_simp [(mass_pos ha).ne']

/-- For every nonnegative squared radius the center-subtracted proper-time
loss has an absolutely integrable kernel on the positive real half-line. -/
theorem integrable_loss {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (fun t => kernel μ t * lossFactor a t u) (Ioi 0) := by
  have h0 := integrable_difference hμ ha (le_refl (0 : ℝ))
  have hu' := integrable_difference hμ ha hu
  have hi := (h0.sub (hu'.div_const (Real.exp (-u/(4*a))))).div_const (mass a)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  exact fun t ht => centered_identity μ ha ht u

/-- Subtracting the two integrable heat differences gives the loss integral.
The center subtraction preserves the cancellation at small proper time. -/
theorem integral_loss_eq {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in Ioi (0 : ℝ), kernel μ t * lossFactor a t u) =
      ((∫ t in Ioi (0 : ℝ), kernel μ t * (heatProfile a 0 - heatProfile (a+t) 0)) -
        (∫ t in Ioi (0 : ℝ), kernel μ t * (heatProfile a u - heatProfile (a+t) u)) /
          Real.exp (-u/(4*a))) / mass a := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), (weightedDifference μ a 0 t -
        weightedDifference μ a u t / Real.exp (-u/(4*a))) / mass a :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => (centered_identity μ ha ht u).symm
    _ = _ := by
      rw [integral_div, integral_sub (integrable_difference hμ ha (le_refl (0 : ℝ)))
          ((integrable_difference hμ ha hu).div_const _), integral_div]

/-- For the actual normalized positive-frequency Gaussian, the ratio H/R at
a spatial point is its central coefficient minus the proper-time loss at the
squared radius, with prefactor 1/(2√π). -/
theorem normal_ratio_eq_center_sub_loss {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (y : Spatial) :
    normalCoefficient μ σ y / amplitude σ y = normalCoefficient μ σ 0 -
      (1/(2*Real.sqrt Real.pi)) *
        ∫ t in Ioi (0 : ℝ), kernel μ t * lossFactor (σ^2) t (speedSq y) := by
  have ha := sq_pos_of_pos hσ
  have hz : speedSq (0 : Spatial) = 0 := by simp [speedSq_eq_sum]
  have hr : amplitude σ 0 = 1 := by simp [amplitude,hz]
  have h0 := normal_eq_heat_difference hμ hσ (0 : Spatial)
  rw [hr,hz,mul_one] at h0
  rw [h0,normal_eq_heat_difference hμ hσ y,integral_loss_eq hμ ha (speedSq_nonneg y)]
  change (_ * amplitude σ y + _ * _) / amplitude σ y = _ + _ * _ - _ * ((_ - _ / amplitude σ y) / _)
  field_simp [(mass_pos ha).ne', (amplitude_pos σ y).ne']
  ring

end FoliationQM.GaussianRadialHeatLoss
