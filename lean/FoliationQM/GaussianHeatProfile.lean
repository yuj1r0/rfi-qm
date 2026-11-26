module

public import FoliationQM.GaussianSpatialFourier

/-!
# Radial comparison of two Gaussian heat profiles

Multiplying the angular spectrum by a heat factor changes its decay
parameter from a to a+t. Dividing the two explicit Fourier profiles
isolates their dependence on the squared Euclidean radius u.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianHeatProfile

open GaussianSpatialFourier

/-- Ratio of the broadened spectral mass to the original spectral mass. -/
def massRatio (a t : ℝ) : ℝ := mass (a+t) / mass a

/-- Difference of the Gaussian decay rates on the spatial slice. -/
def growthRate (a t : ℝ) : ℝ := 1/(4*a) - 1/(4*(a+t))

/-- Change of the broadened-to-original ratio from the center to squared radius u. -/
def lossFactor (a t u : ℝ) : ℝ :=
  massRatio a t * (Real.exp (growthRate a t * u) - 1)

/-- Both spectral masses are positive along proper time. -/
theorem massRatio_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) : 0 < massRatio a t :=
  div_pos (mass_pos (add_pos ha ht)) (mass_pos ha)

/-- The radial exponential grows at a strictly positive rate for t>0. -/
theorem growthRate_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) : 0 < growthRate a t := by
  apply sub_pos.mpr
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- Increasing proper time increases the radial growth rate. -/
theorem growthRate_mono {a s t : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hst : s ≤ t) :
    growthRate a s ≤ growthRate a t := by
  apply sub_le_sub_left
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private theorem exponent_difference (a t u : ℝ) :
    growthRate a t*u = -u/(4*(a+t)) - (-u/(4*a)) := by
  unfold growthRate
  ring

/-- The two positive Gaussian Fourier profiles have an explicit exponential ratio. -/
theorem broadened_ratio {a t : ℝ} (_ha : 0 < a) (_ht : 0 < t) (u : ℝ) :
    (mass (a+t)*Real.exp (-u/(4*(a+t)))) / (mass a*Real.exp (-u/(4*a))) =
      massRatio a t * Real.exp (growthRate a t*u) := by
  rw [exponent_difference, Real.exp_sub]
  unfold massRatio
  ring

/-- Subtracting the center before integration keeps the heat difference finite
and gives exactly the radial loss times the original spectral mass. -/
theorem center_difference {a t : ℝ} (ha : 0 < a) (_ht : 0 < t) (u : ℝ) :
    (mass a - mass (a+t)) -
      (mass a * Real.exp (-u/(4*a)) - mass (a+t) * Real.exp (-u/(4*(a+t)))) /
        Real.exp (-u/(4*a)) = mass a * lossFactor a t u := by
  rw [lossFactor, exponent_difference, Real.exp_sub, massRatio]
  field_simp [(mass_pos ha).ne', Real.exp_ne_zero]
  ring

/-- At each positive proper time the heat loss strictly increases with squared radius. -/
theorem lossFactor_strictMono {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    StrictMono (lossFactor a t) := by
  intro u v huv
  apply mul_lt_mul_of_pos_left _ (massRatio_pos ha ht)
  exact sub_lt_sub_right (Real.exp_lt_exp.mpr
    (mul_lt_mul_of_pos_left huv (growthRate_pos ha ht))) _

/-- The radial loss is nonnegative on every physical squared radius. -/
theorem lossFactor_nonneg {a t u : ℝ} (ha : 0 < a) (ht : 0 < t) (hu : 0 ≤ u) :
    0 ≤ lossFactor a t u := by
  simpa [lossFactor] using (lossFactor_strictMono ha ht).monotone hu

end FoliationQM.GaussianHeatProfile
