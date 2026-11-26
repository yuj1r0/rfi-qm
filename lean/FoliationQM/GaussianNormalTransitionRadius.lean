module

public import FoliationQM.GaussianRadialNormalRatio
public import FoliationQM.GaussianHeatLossTail

/-!
# Unique transition radius of the positive-frequency Gaussian

On the initial slice of the massive rest packet in v13 Theorem 5.8(ii),
the normal coefficient divided by the positive Gaussian amplitude falls
from a positive central value to negative infinity along any ray. For
each positive mass parameter and width there is exactly one radius
where the normal coefficient vanishes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianNormalTransitionRadius

open Filter Set MeasureTheory LorentzCoordinates GaussianCauchySlice GaussianPositiveFrequencyPacket
open GaussianRadialNormalRatio GaussianProperTimeMultiplier GaussianHeatProfile GaussianHeatLossTail

/-- The ratio of normal coefficient to amplitude tends to negative infinity as the
ordinary radius increases, for every positive mass parameter and width. -/
theorem ratio_tendsto_atBot {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    Tendsto (ratio μ σ) atTop atBot := by
  let C := 1 / (2 * Real.sqrt Real.pi)
  have hC : 0 < C := by dsimp [C]; positivity
  have ht := (tendsto_integral_loss_atTop hμ (sq_pos_of_pos hσ)).comp
    (tendsto_pow_atTop (by decide : 2 ≠ 0))
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [ht.eventually_ge_atTop ((normalCoefficient μ σ 0 - b) / C)] with r hr
  rw [ratio_eq hμ hσ r]
  change normalCoefficient μ σ 0 - C * _ ≤ b
  rw [sub_le_iff_le_add, mul_comm C]
  exact sub_le_iff_le_add'.mp ((div_le_iff₀ hC).mp hr)

/-- The transition radius is the infimum of nonnegative radii where the initial
normal-to-amplitude ratio is zero. For positive mass and width this set is a singleton. -/
def transitionRadius (μ σ : ℝ) : ℝ := sInf {r : ℝ | 0 ≤ r ∧ ratio μ σ r = 0}

private theorem transition_spec {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    0 < transitionRadius μ σ ∧ ratio μ σ (transitionRadius μ σ) = 0 := by
  have h0 : 0 < ratio μ σ 0 := by rw [ratio_zero]; exact normal_center_pos hμ hσ
  obtain ⟨R, hR, hzero⟩ := intermediate_value_Ioi' (continuous_ratio μ hσ).continuousOn
    (ratio_tendsto_atBot hμ hσ) (show (0 : ℝ) ∈ Iio (ratio μ σ 0) from h0)
  have hset : {r : ℝ | 0 ≤ r ∧ ratio μ σ r = 0} = {R} := by
    ext r
    constructor
    · rintro ⟨hr, hz⟩
      exact (ratio_strictAntiOn hμ hσ).injOn hr (le_of_lt hR) (hz.trans hzero.symm)
    · rintro (rfl : r = R)
      exact ⟨le_of_lt hR, hzero⟩
  rw [transitionRadius, hset, csInf_singleton]
  exact ⟨hR, hzero⟩

/-- Every positive mass parameter and packet width have a strictly positive transition radius. -/
theorem transitionRadius_pos {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    0 < transitionRadius μ σ := (transition_spec hμ hσ).1

/-- Among all nonnegative ordinary radii, vanishing of the ratio characterizes
the unique transition radius. -/
theorem ratio_eq_zero_iff {μ σ r : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (hr : 0 ≤ r) :
    ratio μ σ r = 0 ↔ r = transitionRadius μ σ := by
  obtain ⟨hR, hz⟩ := transition_spec hμ hσ
  constructor
  · intro h
    exact (ratio_strictAntiOn hμ hσ).injOn hr hR.le (h.trans hz.symm)
  · rintro rfl
    exact hz

/-- For every positive mass parameter and width, exactly one positive ordinary radius
has zero initial normal-to-amplitude ratio. -/
theorem existsUnique_positive_zero {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    ∃! r : ℝ, 0 < r ∧ ratio μ σ r = 0 := by
  refine ⟨transitionRadius μ σ, transition_spec hμ hσ, ?_⟩
  exact fun r hr => (ratio_eq_zero_iff hμ hσ hr.1.le).mp hr.2

/-- The initial normal coefficient is positive exactly inside the transition sphere,
zero exactly on the sphere and negative exactly outside it. -/
theorem normal_signs {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (y : Spatial) :
    (0 < normalCoefficient μ σ y ↔ euclideanSpeed y < transitionRadius μ σ) ∧
    (normalCoefficient μ σ y = 0 ↔ euclideanSpeed y = transitionRadius μ σ) ∧
    (normalCoefficient μ σ y < 0 ↔ transitionRadius μ σ < euclideanSpeed y) := by
  have hr : euclideanSpeed y ∈ Ici 0 := Real.sqrt_nonneg _
  obtain ⟨hR, hz⟩ := transition_spec hμ hσ
  have hanti := ratio_strictAntiOn hμ hσ
  have hp := hanti.lt_iff_gt hR.le hr
  have hn := hanti.lt_iff_gt hr hR.le
  have he := ratio_eq_zero_iff hμ hσ hr
  rw [hz] at hp hn
  have ha := amplitude_pos σ y
  rw [← normal_div_amplitude_eq_ratio hμ hσ y] at hp he hn
  simpa only [lt_div_iff₀ ha, div_eq_iff ha.ne', div_lt_iff₀ ha, zero_mul] using
    And.intro hp (And.intro he hn)

end FoliationQM.GaussianNormalTransitionRadius
